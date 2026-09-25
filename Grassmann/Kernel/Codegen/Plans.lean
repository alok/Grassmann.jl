/-
What the kernel generator emits (DESIGN.md §5.2): the emission policy, the
kernel specifications of a space, and their plans.

A *kernel specification* (`Spec`) names one field of `Kernels V` (`bin`,
`binProj` or `un`), an operation and a triple of storage layouts; its plan is
the reference plan of `Grassmann.Kernel.build` for the same key, so a generated
kernel computes exactly what the reference kernel computes, entry by entry and
in the same summation order.

Plans are built from *blade tables*: the container-level terms of every blade
pair (`binTermsC`) or blade (`unTermsC`) of the space, computed once per
operation and sliced for every layout triple (`buildFrom`). `buildFrom` is
`build` with the term computation hoisted out of the layout loops (the test
suite checks that the two agree on every emitted key). This matters because the
generator runs at elaboration time in the interpreter.

## Emission policy (Julia's `@generated` thresholds, grassmann-products.md §8.2)

* **Typed families** for the main products `*`, `∧`, `∨`, `⋅` and the
  sandwich's `∗` (`reverseMul`): every `Chain×Chain` pair with
  `binomial(n,G)·binomial(n,H) < 4096`, and `Chain×Half`, `Half×Chain`,
  `Half×Half` for `n < 12`, each into the static result layout of the typed
  instances (`Grassmann.Algebra.Products`).
* **Dense families** (`Multivector` operands, result `.full`): `full×X` and
  `X×full` for every layout `X` when `n < 12`, subject to the per-kernel entry
  cap `maxEntries`; `Multivector×Multivector` is the cap's main victim.
* **Sandwich projections** (`binProj .mul`): a half on the left, a chain or
  half on the right, projected onto a chain or half of consistent parity: the
  second product of `x ⊘ R` and `R >>> x`, and `Half.inv?`.
* **Other binary operations** (`⨼`, `<<`, `>>`, `⊛`, `×`, `⟇`, `antidot`):
  `Chain×Chain` into `TensorBundle.chainResult`.
* **Unary maps**: every `UnOp` on every layout, type-preserving or (for the
  complements) into the complementary chain/half.

Anything a space does not emit, and any key whose plan fails to build (Julia's
errors: complements in dyadic spaces), falls through to the reference kernels.
-/
import Grassmann.Kernel.Reference

namespace Grassmann.Kernel.Codegen

open DirectSum DirectSum.Bits Leibniz

/-- The field of `Kernels V` a generated kernel implements. -/
inductive Field where
  /-- `Kernels.bin` (strict binary). -/
  | bin
  /-- `Kernels.binProj` (projecting binary). -/
  | binProj
  /-- `Kernels.un` (unary). -/
  | un
  deriving DecidableEq, Repr, Hashable, Inhabited

/-- One kernel to emit: a field and its plan key. -/
structure Spec where
  /-- The `Kernels` field. -/
  field : Field
  /-- The plan key (space, operation, layouts, projection). -/
  key : PlanKey
  deriving Inhabited

/-- What the generator emits for a space (see the module doc). -/
structure Policy where
  /-- Operations with the typed and dense families. -/
  mainOps : List BinOp := [.mul, .wedge, .vee, .contraction, .reverseMul]
  /-- Operations with `Chain×Chain` kernels only. -/
  chainOps : List BinOp :=
    [.contractionLeft, .contractionRevLeft, .contractionRevRight, .scalarContraction, .cross,
     .veedot, .antidot]
  /-- Unary operations. -/
  unOps : List UnOp := UnOp.all
  /-- Emit the dense (`Multivector`-operand) families. -/
  dense : Bool := true
  /-- Emit the sandwich projections. -/
  sandwich : Bool := true
  /-- `Chain×Chain` pairs are emitted when `binomial(n,G)·binomial(n,H)` is below this (Julia: 4096). -/
  chainPairLimit : Nat := 4096
  /-- Half and dense families are emitted when `n` is below this (Julia: 12). -/
  halfLimit : Nat := 12
  /-- Kernels with more multiply-accumulate entries than this are left to the reference. -/
  maxEntries : Nat := 4096
  deriving Inhabited

/-- The default policy for an `n`-generator space (DESIGN.md §5.2). For `n ≥ 6`
the dense mixed families are dropped (their compile cost grows as `4ⁿ`) and
only `Multivector×Multivector` of the geometric product stays dense. -/
def Policy.default (n : Nat) : Policy :=
  if n ≤ 5 then {} else { dense := false }

/-- The layout of a half (`false` even, `true` odd). -/
@[inline] def halfL (odd : Bool) : Layout := if odd then .odd else .even

/-- The parity of a graded or half layout (`none` for `.full`). -/
def parityOf : Layout → Option Bool
  | .chain g => some (g % 2 == 1)
  | .even => some false
  | .odd => some true
  | .full => none

/-- The result layout of the typed product instances (`Grassmann.Algebra.Products`,
`sandwichCore`) for `op` on `la × lb`, or `none` if the typed layer has no such
instance. -/
def typedResult (n : Nat) (op : BinOp) (la lb : Layout) : Option Layout :=
  match la, lb with
  | .chain g, .chain h => match op with
    | .mul | .reverseMul => some (halfL ((g + h) % 2 == 1))
    | .wedge => some (.chain (g + h))
    | .vee => some (.chain (g + h - n))
    | .contraction => some (.chain (g - h))
    | _ => none
  | .full, _ | _, .full => none
  | la, lb => do
    let p ← parityOf la
    let q ← parityOf lb
    match op with
    | .mul | .reverseMul | .wedge | .contraction => some (halfL (p ^^ q))
    | .vee => some (halfL (p ^^ q ^^ (n % 2 == 1)))
    | _ => none

/-- Whether a unary operation maps grade `G` to grade `n - G` (the complements). -/
def UnOp.isComplement : UnOp → Bool
  | .complementright | .complementleft | .complementrighthodge | .complementlefthodge
  | .complementrightanti | .complementleftanti => true
  | _ => false

/-- The result layout of the typed unary instance of `op` on `la` (`Grassmann.Algebra.Unary`). -/
def unaryResult (n : Nat) (op : UnOp) (la : Layout) : Layout :=
  if UnOp.isComplement op then
    match la with
    | .chain g => .chain (n - g)
    | .even => halfL (n % 2 == 1)
    | .odd => halfL (n % 2 == 0)
    | .full => .full
  else la

/-- Every storage layout of an `n`-generator space: the chains, the halves, the full layout. -/
def allLayouts (n : Nat) : List Layout :=
  (List.range (n + 1)).map Layout.chain ++ [.even, .odd, .full]

/-- The chain and half layouts. -/
def gradedLayouts (n : Nat) : List Layout :=
  (List.range (n + 1)).map Layout.chain ++ [.even, .odd]

/-- The kernel specifications of `V` under a policy (plans not yet built; keys may repeat
between `bin` and `binProj`, which the emitter shares). -/
def specs (V : TensorBundle) (pol : Policy) : Array Spec := Id.run do
  let n := V.n
  let mut out : Array Spec := #[]
  let bin := fun (op : BinOp) (la lb lc : Layout) =>
    ({ field := .bin, key := { V, op := .bin op, la, lb, lc } } : Spec)
  -- typed families of the main operations
  for op in pol.mainOps do
    for la in gradedLayouts n do
      for lb in gradedLayouts n do
        let ok : Bool := match la, lb with
          | .chain g, .chain h => choose n g * choose n h < pol.chainPairLimit
          | _, _ => n < pol.halfLimit
        if ok then
          if let some lc := typedResult n op la lb then out := out.push (bin op la lb lc)
    -- dense families
    if n < pol.halfLimit then
      for l in allLayouts n do
        let full := l == .full
        if pol.dense || (full && op == .mul) then
          out := out.push (bin op .full l .full)
          if !full then out := out.push (bin op l .full .full)
  -- chain × chain of the other operations
  for op in pol.chainOps do
    for g in [0:n + 1] do
      for h in [0:n + 1] do
        if choose n g * choose n h < pol.chainPairLimit then
          out := out.push (bin op (.chain g) (.chain h) (V.chainResult op g h))
  -- sandwich projections
  if pol.sandwich && n < pol.halfLimit then
    for p in [false, true] do
      for lb in gradedLayouts n do
        for lc in gradedLayouts n do
          if (parityOf lb).map (· ^^ p) == parityOf lc then
            out := out.push { field := .binProj, key := { V, op := .bin .mul, la := halfL p, lb, lc, project := true } }
  -- unary maps
  for op in pol.unOps do
    for la in allLayouts n do
      let lc := unaryResult n op la
      out := out.push { field := .un, key := { V, op := .un op, la, lb := la, lc } }
  return out

/-! ## Blade tables -/

/-- The container-level terms of every blade pair (`binary`, indexed `a * 2ⁿ + b` by the
blade masks) or blade (unary, indexed by the mask) of one operation. -/
structure Table where
  /-- The number of generators. -/
  n : Nat
  /-- Whether the operation is binary. -/
  binary : Bool
  /-- The terms, or Julia's error for that blade (pair). -/
  terms : Array (Except String (Array BladeTerm))
  deriving Inhabited

/-- The blade table of an operation. -/
def table (V : TensorBundle) : KOp → Table
  | .bin op =>
    let m := 2 ^ V.n
    { n := V.n, binary := true
      terms := (Array.range (m * m)).map fun k =>
        binTermsC V op (k / m).toUInt64 (k % m).toUInt64 }
  | .un op =>
    { n := V.n, binary := false
      terms := (Array.range (2 ^ V.n)).map fun k => unTermsC V op k.toUInt64 }

/-- `build k` from a blade table of `k.op` (same entries in the same order: rows by
result position, entries by operand positions, then by term order). -/
def buildFrom (t : Table) (k : PlanKey) : Except String Plan := do
  let n := t.n
  let m := 2 ^ n
  let as := k.la.blades n
  let bs : Array UInt64 := if t.binary then k.lb.blades n else #[0]
  let mut rows : Array (Array (Nat × Nat × Rat)) := Array.replicate (k.lc.size n) #[]
  let mut nested := 0
  for a in as, i in [0:as.size] do
    for b in bs, j in [0:bs.size] do
      let idx := if t.binary then a.toNat * m + b.toNat else a.toNat
      let ts ← t.terms[idx]?.getD (.error "blade outside the space")
      for tm in ts do
        if tm.z != 0 then nested := nested + 1
        else if tm.coef == 0 then pure ()
        else if k.lc.contains n tm.bits then
          rows := rows.modify (k.lc.rank n tm.bits) (·.push (i, j, tm.coef))
        else if !k.project then
          throw s!"{k.V.bladeLabel tm.bits} lies outside the result layout {repr k.lc} of {repr k.op}"
  return Plan.ofRows rows nested

/-- A specification with its plan. -/
structure Planned where
  /-- The specification. -/
  spec : Spec
  /-- Its plan. -/
  plan : Plan
  deriving Inhabited

/-- Plan every specification of `V` under `pol`, dropping keys whose plan fails
(Julia's errors), carries dropped tangent terms, or exceeds `maxEntries`, and
duplicate keys. Tables are computed once per operation. -/
def planAll (V : TensorBundle) (pol : Policy) : Array Planned := Id.run do
  let ss := specs V pol
  let mut tables : Array (KOp × Table) := #[]
  let mut out : Array Planned := #[]
  let mut seen : Std.HashSet (Field × KOp × Layout × Layout × Layout) := {}
  for s in ss do
    let k := s.key
    let id := (s.field, k.op, k.la, k.lb, k.lc)
    if seen.contains id then continue
    seen := seen.insert id
    let t ← match tables.find? (·.1 == k.op) with
      | some (_, t) => pure t
      | none =>
        let t := table V k.op
        tables := tables.push (k.op, t)
        pure t
    match buildFrom t k with
    | .ok p =>
      if p.nested == 0 && p.size ≤ pol.maxEntries then out := out.push { spec := s, plan := p }
    | .error _ => pure ()
  return out

end Grassmann.Kernel.Codegen
