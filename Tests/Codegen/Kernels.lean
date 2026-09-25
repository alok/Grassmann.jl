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
the policy covers the shapes DESIGN.md §5.2 promises.
-/
import Tests.Codegen.Common

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
    let got := if sp.shift then SandwichKernels.tsandwich (V := V) sp.lr sp.lx r x
      else SandwichKernels.sandwich (V := V) sp.lr sp.lx r x
    let want := if sp.shift then @tsandwichTwo V α _ (Kernels.reference V) sp.lr sp.lx r x
      else @sandwichTwo V α _ (Kernels.reference V) sp.lr sp.lx r x
    return got.toArray == want.toArray
  let sps := planSandwiches V
  t := t.check (sps.size == 2 * (gradedLayouts n).length ^ 2) s!"{name}: {sps.size} fused sandwiches"
  for sp in sps do
    for _ in [0:trials] do
      let (okI, r) := StateT.run (one randInt sp) rng
      let (okF, r) := StateT.run (one randFloat sp) r
      rng := r
      let what := s!"{name} {if sp.shift then ">>>" else "⊘"} {layoutTag sp.lr} {layoutTag sp.lx}"
      t := t.check okI s!"{what}: Int fused ≠ reference"
      t := t.check okF s!"{what}: Float fused ≠ reference"
  return t

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
  return t

end CodegenTests.Kernels
