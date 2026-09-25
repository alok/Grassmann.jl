/-
Generated kernels against the reference kernels, at run time.

For every standard space and every kernel the emission policy selects (the
specifications `planAll` returns, i.e. every emitted kernel and every shared
projection), random `Int` and `Float` operands go through the space's
`Kernels` instance (the generated dispatch, called with run-time operation and
layouts, so through the generic compiled kernels) and through the reference
kernel (`refBin`/`refBinProj`/`refUn`, the interpreted plans); the results
must be equal. `Int` results are exact. `Float` results are compared with `==`
as well: a generated kernel sums in the reference order, so the two agree bit
for bit up to the sign of zero (`==` identifies `±0`).

Also checked: `buildFrom` (plans sliced from blade tables, used at elaboration
time) equals `build` (the reference plan builder) on every specification, and
the policy covers the shapes DESIGN.md §5.2 promises; the fused sandwiches (`⊘`, `>>>`,
`R * x * ~R`) against the kernel-by-kernel computation; every linear kernel (`Kernels.add` …
`convSub`) against the reference bit for bit, sign of zero included; and the dynamic layer's
compiled loops and unary fast paths (`DynKernels`) against Julia's interpreted loops, kind and
bits, in every generated space (the degenerate and conformal ones included).
-/
import Tests.Codegen.Common
import Tests.Codegen.Diag

open Grassmann DirectSum StaticVectors AbstractTensors Grassmann.Kernel Grassmann.Kernel.Codegen

namespace CodegenTests.Kernels

/-- Compare one specification of `V` through the instance and the reference, on random
inputs of coefficient type `α` (generic: the instance is a run-time value here). -/
@[nospecialize] def checkSpec {α : Type} [Coeff α] [BEq α] (V : TensorBundle) [Kernels V]
    (rand : (n : Nat) → Tests.Gen (Values α n)) (s : Spec) : Tests.Gen Bool := do
  let n := V.n
  let k := s.key
  match s.field, k.op with
  | .bin, .bin op =>
    let x ← rand (k.la.size n)
    let y ← rand (k.lb.size n)
    return (Kernels.bin (V := V) op k.la k.lb k.lc x y).toArray == (refBin V op k.la k.lb k.lc x y).toArray
  | .binProj, .bin op =>
    let x ← rand (k.la.size n)
    let y ← rand (k.lb.size n)
    return (Kernels.binProj (V := V) op k.la k.lb k.lc x y).toArray ==
      (refBinProj V op k.la k.lb k.lc x y).toArray
  | .un, .un op =>
    let x ← rand (k.la.size n)
    return (Kernels.un (V := V) op k.la k.lc x).toArray == (refUn V op k.la k.lc x).toArray
  | _, _ => return false

/-- Every specification of `V`, `trials` random inputs each, at `Int` and at `Float`. -/
@[nospecialize] def checkSpace (name : String) (V : TensorBundle) [Kernels V] (trials : Nat)
    (seed : Nat) (t : Tally) : Tally := Id.run do
  let mut t := t
  let mut rng := Tests.Rng.ofSeed seed
  for pl in planAll V (Policy.default V.n) do
    for _ in [0:trials] do
      let (okI, r) := StateT.run (checkSpec V randInt pl.spec) rng
      let (okF, r) := StateT.run (checkSpec V randFloat pl.spec) r
      rng := r
      t := t.check okI s!"{name} {describe pl.spec}: Int kernel ≠ reference"
      t := t.check okF s!"{name} {describe pl.spec}: Float kernel ≠ reference"
  return t

/-- Every fused sandwich of `V` through the instance against the two-kernel sandwich of the
reference kernels (`sandwichCore` over `Kernels.reference`), `trials` random inputs each, at
`Int` and at `Float`. -/
@[nospecialize] def checkSandwiches (name : String) (V : TensorBundle) [SandwichKernels V] (trials : Nat)
    (seed : Nat) (t : Tally) : Tally := Id.run do
  let n := V.n
  let mut t := t
  let mut rng := Tests.Rng.ofSeed seed
  let one {α : Type} [Coeff α] [BEq α] (rand : (k : Nat) → Tests.Gen (Values α k)) (sp : SandwichPlan) :
      Tests.Gen Bool := do
    let r ← rand (sp.lr.size n)
    let x ← rand (sp.lx.size n)
    match sp.kind with
    | .sandwich =>
      return (SandwichKernels.sandwich (V := V) sp.lr sp.lx r x).toArray ==
        (@sandwichTwo V α _ (Kernels.reference V) sp.lr sp.lx r x).toArray
    | .tsandwich =>
      return (SandwichKernels.tsandwich (V := V) sp.lr sp.lx r x).toArray ==
        (@tsandwichTwo V α _ (Kernels.reference V) sp.lr sp.lx r x).toArray
    | .rsandwich =>
      return (SandwichKernels.rsandwich (V := V) sp.lr sp.lx sp.lc r x).toArray ==
        (@rsandwichThree V α _ (Kernels.reference V) sp.lr sp.lx sp.lc r x).toArray
  let sps := planSandwiches V
  let graded := (gradedLayouts n).length
  t := t.check (sps.size == 2 * graded ^ 2 + (rsandwichVersors n).length * graded)
    s!"{name}: {sps.size} fused sandwiches"
  for sp in sps do
    for _ in [0:trials] do
      let (okI, r) := StateT.run (one randInt sp) rng
      let (okF, r) := StateT.run (one randFloat sp) r
      rng := r
      let what := s!"{name} {sp.describe} {layoutTag sp.lr} {layoutTag sp.lx}"
      t := t.check okI s!"{what}: Int fused ≠ reference"
      t := t.check okF s!"{what}: Float fused ≠ reference"
  return t

/-- The reference value of a linear kernel (the defaults of `Kernels`: `Values` arithmetic and
`convertLayout`). -/
def refLinear {α : Type} [Coeff α] (n : Nat) (s : LinSpec) (k : α) (x : Values α (s.la.size n))
    (y : Values α (s.lb.size n)) : Array α :=
  match s.op with
  | .add => (x + (convertLayout n s.lb s.la y)).toArray
  | .sub => (x - (convertLayout n s.lb s.la y)).toArray
  | .neg => (-x).toArray
  | .smul => (x.map (k * ·)).toArray
  | .muls => (x.map (· * k)).toArray
  | .conv => (convertLayout n s.la s.lc x).toArray
  | .convAdd => (convertLayout n s.la s.lc x + convertLayout n s.lb s.lc y).toArray
  | .convSub => (convertLayout n s.la s.lc x - convertLayout n s.lb s.lc y).toArray

/-- A linear kernel through the instance (`y` re-indexed into `la` for the one-layout sums,
where `la = lb`). -/
def viaLinear {α : Type} [Coeff α] (V : TensorBundle) [Kernels V] (s : LinSpec) (k : α)
    (x : Values α (s.la.size V.n)) (y : Values α (s.lb.size V.n)) : Array α :=
  match s.op with
  | .add => (Kernels.add (V := V) s.la x (convertLayout V.n s.lb s.la y)).toArray
  | .sub => (Kernels.sub (V := V) s.la x (convertLayout V.n s.lb s.la y)).toArray
  | .neg => (Kernels.neg (V := V) s.la x).toArray
  | .smul => (Kernels.smul (V := V) s.la k x).toArray
  | .muls => (Kernels.muls (V := V) s.la x k).toArray
  | .conv => (Kernels.conv (V := V) s.la s.lc x).toArray
  | .convAdd => (Kernels.convAdd (V := V) s.la s.lb s.lc x y).toArray
  | .convSub => (Kernels.convSub (V := V) s.la s.lb s.lc x y).toArray

/-- Every linear kernel of `V` (and every identity conversion) through the instance against the
reference, `trials` random inputs each, at `Int` and at `Float`: bit for bit, sign of zero
included (the linear kernels perform exactly the reference's operations). -/
@[nospecialize] def checkLinear (name : String) (V : TensorBundle) [Kernels V] (trials : Nat) (seed : Nat)
    (t : Tally) : Tally := Id.run do
  let n := V.n
  let mut t := t
  let mut rng := Tests.Rng.ofSeed seed
  let specs := linearSpecs n (Policy.default n) ++ (allLayouts n).toArray.map fun l => { op := .conv, la := l, lb := l, lc := l }
  t := t.check (specs.size == 5 * (n + 4) + 3 * (n + 4) * (n + 3) + (n + 4)) s!"{name}: {specs.size} linear kernels"
  for s in specs do
    for _ in [0:trials] do
      let ((xi, yi, ki), r) := StateT.run (do
        return (← randInt (s.la.size n), ← randInt (s.lb.size n), ← Tests.Gen.int (-3) 3) : Tests.Gen _) rng
      let ((xf, yf, kf), r) := StateT.run (do
        return (← randFloat (s.la.size n), ← randFloat (s.lb.size n), ← Tests.Gen.floatIn (-2) 2) : Tests.Gen _) r
      rng := r
      let bits (a : Array Float) := a.map Float.toBits
      t := t.check (viaLinear V s ki xi yi == refLinear n s ki xi yi) s!"{name} {s.describe}: Int ≠ reference"
      t := t.check (bits (viaLinear V s kf xf yf) == bits (refLinear n s kf xf yf))
        s!"{name} {s.describe}: Float ≠ reference"
  return t

/-- A random `Float` entry for the dynamic checks: `±0.0`, a small integer or a fraction. -/
def dynEntry : Tests.Gen Float := do
  match ← Tests.Gen.nat 8 with
  | 0 => return 0.0
  | 1 => return -0.0
  | 2 | 3 | 4 => return Float.ofInt (← Tests.Gen.int (-3) 3)
  | _ => return (Float.ofInt (← Tests.Gen.int (-1000) 1000)) / 7.0

/-- A random container or term of `V` for the dynamic checks. -/
def dynOperand (V : TensorBundle) : Tests.Gen (TA V Float) := do
  let vals (k : Nat) : Tests.Gen (Values Float k) := do
    let mut xs : Array Float := #[]
    for _ in [0:k] do xs := xs.push (← dynEntry)
    return Values.ofFn fun i => xs[i.1]!
  match ← Tests.Gen.nat 5 with
  | 4 => return .single (← Tests.Gen.nat (2 ^ V.n)).toUInt64 (← dynEntry)
  | 0 => let g ← Tests.Gen.nat (V.n + 1); return .chain g ⟨← vals _⟩
  | 1 => return .spinor ⟨← vals _⟩
  | 2 => return .cospinor ⟨← vals _⟩
  | _ => return .multi ⟨← vals _⟩

/-- Same kind and the same bits (sign of zero included). -/
def sameTA {V : TensorBundle} (x y : TA V Float) : Bool :=
  x.kind == y.kind && x.grade? == y.grade? &&
    x.toDense.v.toList.map Float.toBits == y.toDense.v.toList.map Float.toBits

/-- The dynamic layer's compiled loops and unary fast paths (`DynKernels`, every generated
space, the degenerate and conformal ones included) against Julia's interpreted loops: the same
kind and bits on `count` random operand pairs. -/
@[nospecialize] def checkDyn (name : String) (V : TensorBundle) [Kernels V] [DynKernels V] (seed count : Nat)
    (t : Tally) : Tally := Id.run do
  let mut t := t
  t := t.check (DynKernels.loops V) s!"{name}: no compiled dynamic loops"
  let xs := Tests.Gen.run seed (Tests.Gen.array (2 * count) (dynOperand V))
  for k in [0:count] do
    let a := xs[2 * k]!
    let b := xs[2 * k + 1]!
    let bin := [("*", TA.mulF a b, TA.mul a b), ("∧", TA.wedgeF a b, TA.wedge a b),
      ("∨", TA.veeF a b, TA.vee a b), ("⋅", TA.contractionF a b, TA.contraction a b)]
    for (op, fast, slow) in bin do
      t := t.check (sameTA fast slow) s!"{name} {op}: `{fast}` vs `{slow}` for `{a}`, `{b}`"
    let un := [("~", TA.reverseF a, TA.reverse a), ("involute", TA.involuteF a, TA.involute a),
      ("clifford", TA.cliffordF a, TA.clifford a), ("⋆", TA.hodgeF a, TA.hodge a),
      ("!", TA.complementrightF a, TA.complementright a),
      ("complementleft", TA.complementleftF a, TA.complementleft a)]
    for (op, fast, slow) in un do
      t := t.check (sameTA fast slow) s!"{name} {op}: `{fast}` vs `{slow}` for `{a}`"
  return t

/-- The flags of the generated `DynKernels` instances: every generated space has compiled
loops and exact sign maps and plain complements; the Hodge complements are exact in the
non-degenerate diagonal spaces; `fast` exactly in those. -/
def checkDynFlags (t : Tally) : Tally :=
  let flags (V : TensorBundle) [DynKernels V] : Bool × Bool × Bool × Bool :=
    (DynKernels.fast V, DynKernels.signs V, DynKernels.hodges V, DynKernels.loops V)
  t.check (flags ℝ2 == (true, true, true, true) && flags ℝ3 == (true, true, true, true) &&
      flags ℝ4 == (true, true, true, true) && flags STA == (true, true, true, true) &&
      flags PGA2 == (false, true, false, true) && flags PGA3 == (false, true, false, true) &&
      flags CGA2 == (false, true, false, true) && flags CGA3 == (false, true, false, true))
    "DynKernels flags of the standard spaces"

/-- `buildFrom` (blade tables) agrees with `build` on every specification of `V`. -/
def checkPlans (name : String) (V : TensorBundle) (t : Tally) : Tally := Id.run do
  let mut t := t
  for pl in planAll V (Policy.default V.n) do
    let same := match build pl.spec.key with
      | .ok p => p.entries == pl.plan.entries
      | .error _ => false
    t := t.check same s!"{name} {describe pl.spec}: buildFrom ≠ build"
  return t

/-- The emission policy covers DESIGN.md §5.2's shapes: every chain pair and half pair of
the main products, `Multivector×Multivector` of `*` (for `n ≤ 5` also the other dense
families), every unary map on every layout. -/
def checkCoverage (name : String) (V : TensorBundle) (t : Tally) : Tally := Id.run do
  let n := V.n
  let ps := planAll V (Policy.default n)
  let has := fun (f : Field) (op : KOp) (la lb lc : Layout) =>
    ps.any fun pl => pl.spec.field == f && pl.spec.key.op == op && pl.spec.key.la == la &&
      (f == .un || pl.spec.key.lb == lb) && pl.spec.key.lc == lc
  let mut t := t
  for op in [BinOp.mul, .wedge, .vee, .contraction, .reverseMul] do
    for la in gradedLayouts n do
      for lb in gradedLayouts n do
        if let some lc := typedResult n op la lb then
          t := t.check (has .bin (.bin op) la lb lc) s!"{name}: no {opTag (.bin op)} {layoutTag la}×{layoutTag lb}"
    if n ≤ 5 then
      for l in allLayouts n do
        t := t.check (has .bin (.bin op) .full l .full && has .bin (.bin op) l .full .full)
          s!"{name}: no dense {opTag (.bin op)} with {layoutTag l}"
  t := t.check (has .bin (.bin .mul) .full .full .full) s!"{name}: no Multivector×Multivector"
  for op in UnOp.all do
    for la in allLayouts n do
      t := t.check (has .un (.un op) la la (unaryResult n op la)) s!"{name}: no {opTag (.un op)} {layoutTag la}"
  return t

/-- Run the suite. -/
def run : IO Tally := do
  let mut t : Tally := {}
  t := checkPlans "ℝ2" ℝ2 t |> checkPlans "ℝ3" ℝ3 |> checkPlans "ℝ4" ℝ4 |> checkPlans "STA" STA
    |> checkPlans "PGA2" PGA2 |> checkPlans "PGA3" PGA3 |> checkPlans "CGA2" CGA2 |> checkPlans "CGA3" CGA3
  for (name, V) in standardSpaces do t := checkCoverage name V t
  t := checkSpace "ℝ2" ℝ2 4 1 t
  t := checkSpace "ℝ3" ℝ3 4 2 t
  t := checkSpace "ℝ4" ℝ4 3 3 t
  t := checkSpace "STA" STA 3 4 t
  t := checkSpace "PGA2" PGA2 4 5 t
  t := checkSpace "PGA3" PGA3 3 6 t
  t := checkSpace "CGA2" CGA2 3 7 t
  t := checkSpace "CGA3" CGA3 2 8 t
  t := checkSandwiches "ℝ2" ℝ2 4 21 t
  t := checkSandwiches "ℝ3" ℝ3 4 22 t
  t := checkSandwiches "ℝ4" ℝ4 3 23 t
  t := checkSandwiches "STA" STA 3 24 t
  t := checkSandwiches "PGA2" PGA2 4 25 t
  t := checkSandwiches "PGA3" PGA3 3 26 t
  t := checkSandwiches "CGA2" CGA2 3 27 t
  t := checkSandwiches "CGA3" CGA3 3 28 t
  -- a diagonal metric (non-unit coefficients), generated in `Tests.Codegen.Typed`'s dependency
  t := checkSpace "D⟨1,2,-3⟩" D!"1,2,-3" 3 9 t
  t := checkSandwiches "D⟨1,2,-3⟩" D!"1,2,-3" 3 29 t
  -- the linear kernels (sums, scalar multiples, conversions)
  t := checkLinear "ℝ2" ℝ2 3 41 t
  t := checkLinear "ℝ3" ℝ3 3 42 t
  t := checkLinear "ℝ4" ℝ4 2 43 t
  t := checkLinear "STA" STA 2 44 t
  t := checkLinear "PGA2" PGA2 2 45 t
  t := checkLinear "PGA3" PGA3 2 46 t
  t := checkLinear "CGA2" CGA2 2 47 t
  t := checkLinear "CGA3" CGA3 2 48 t
  t := checkLinear "D⟨1,2,-3⟩" D!"1,2,-3" 2 49 t
  -- the dynamic layer's compiled loops and unary maps, and the flags
  t := checkDynFlags t
  t := checkDyn "ℝ3" ℝ3 51 200 t
  t := checkDyn "PGA2" PGA2 52 300 t
  t := checkDyn "PGA3" PGA3 53 300 t
  t := checkDyn "CGA2" CGA2 54 300 t
  t := checkDyn "CGA3" CGA3 55 300 t
  t := checkDyn "D⟨1,2,-3⟩" D!"1,2,-3" 56 200 t
  return t

end CodegenTests.Kernels
