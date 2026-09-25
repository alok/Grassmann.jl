/-
The reference kernels (DESIGN.md §5.1, §5.3): every binary and unary
operation between any two storage layouts, built from DirectSum's blade-level
rules and interpreted over `Values` storage.

## Semantics

Products are the bilinear (maps: linear) extension of the blade rules of
`DirectSum.Ops` (`TensorBundle.terms₂`/`terms₁`), with Grassmann's
**container-level** complement semantics wherever Julia's `Chain`/`Multivector`
kernels differ from its blade-level ones (oracle defect
`conformal-blade-complement`, grassmann-products.md §4.9):

* `complementright`/`complementleft` use the plain complement (no conformal
  null factors `2`/`½`): `TensorBundle.complementrightChain`/`...leftChain`;
* `hodge`/`complementlefthodge` are `complement ∘ metric` with the Gram metric
  (`...righthodgeChain`/`...lefthodgeChain`);
* `metric` is the Gram outermorphism (`metricChain`) and `antimetric` is
  `g(complement B)·e_B` in diagonal spaces (no projective zeroing, defect
  `projective-blade-metric`), `hodge ∘ complementleft` otherwise (Julia throws
  there, defect `conformal-antimetric`);
* `cross`, `veedot`, `antidot` compose the products with these complements
  exactly as Julia's generic definitions do on containers.

In non-conformal spaces all of these coincide with the blade-level rules.
Contributions carrying a repeated tangent generator (DirectSum's `z ≠ 0`, a
coefficient that is itself a blade of `loworder(V)`) cannot be held by a scalar
coefficient and are dropped (counted in `Plan.nested`); tangent spaces are
otherwise supported only as far as their products stay scalar-valued.

## Plans and the cache

`build` turns `(V, op, layouts)` into a `Plan`, failing when a contribution
lands outside the result layout (strict mode: the static result types of the
algebra layer guarantee it never does) or dropping it (projecting mode, for the
grade projections of the sandwich products). `plan` memoizes `build` in a
process-global `IO.Ref (Std.HashMap PlanKey _)` read through `unsafeBaseIO`: it
is referentially transparent (`plan = build`, `@[implemented_by]`), exactly like
Julia's parity caches, and every plan is built once per process. A lookup
costs about 50 ns (measured, Apple Silicon); at a call site whose space,
operation and layouts are closed terms the compiler can hoist it into a
module-initialization constant (it does for `ℝ3` multivector products, but not
when a layout is computed from a parity inside a loop, as in the sandwich
instances). Generated kernels (DESIGN.md §5.2) bypass the cache entirely.
-/
import Grassmann.Kernel.Plan
import Std.Data.HashMap

namespace Grassmann.Kernel

open DirectSum DirectSum.Bits StaticVectors AbstractTensors

/-- A kernel operation as data. -/
inductive KOp where
  /-- A binary operation. -/
  | bin (op : BinOp)
  /-- A unary operation. -/
  | un (op : UnOp)
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- The cache key of a plan: space, operation, operand and result layouts, and
whether contributions outside the result layout are dropped (`project`) or an
error. -/
structure PlanKey where
  /-- The space. -/
  V : TensorBundle
  /-- The operation. -/
  op : KOp
  /-- Layout of the first operand. -/
  la : Layout
  /-- Layout of the second operand (ignored by unary operations). -/
  lb : Layout
  /-- Layout of the result. -/
  lc : Layout
  /-- Drop contributions outside `lc` (a grade projection) instead of failing. -/
  project : Bool := false
  deriving Repr, Inhabited

/-- Key equality for the cache: the cheap fields first, the space last. -/
instance : BEq PlanKey where
  beq a b := a.op == b.op && a.la == b.la && a.lb == b.lb && a.lc == b.lc && a.project == b.project
    && a.V.n == b.V.n && a.V == b.V

/-- Key hash for the cache: the operation, layouts and dimension only (keys that
differ only in the metric share a bucket and are told apart by `==`; a process
holds few such spaces). Cheap to compute on every lookup. -/
instance : Hashable PlanKey where
  hash k := mixHash (hash k.V.n) (mixHash (hash k.op)
    (mixHash (hash k.la) (mixHash (hash k.lb) (mixHash (hash k.lc) (hash k.project)))))

/-! ## Container-level term semantics -/

/-- Nonzero `Terms` as `BladeTerm`s. -/
def ofTerms (t : Terms) : Array BladeTerm :=
  (t.filter (·.2 != 0)).map fun (b, c) => { bits := b, coef := c }

/-- The `Terms` of scalar-valued `BladeTerm`s (repeated-tangent terms dropped). -/
def scalarTerms (ts : Array BladeTerm) : Terms :=
  ts.foldl (fun acc t => if t.z == 0 then acc.add t.bits t.coef else acc) #[]

/-- Linear extension of a blade map to a term list. -/
def linMap (f : UInt64 → Except String Terms) (t : Terms) : Except String Terms :=
  t.foldlM (init := #[]) fun acc (k, c) => do
    return (← f k).foldl (fun acc (k', x) => acc.add k' (c * x)) acc

/-- Bilinear extension of a blade-pair operation to two term lists. -/
def bilinMap (f : UInt64 → UInt64 → Except String (Array BladeTerm)) (x y : Terms) :
    Except String Terms :=
  x.foldlM (init := #[]) fun acc (a, c) =>
    y.foldlM (init := acc) fun acc (b, d) => do
      return (scalarTerms (← f a b)).foldl (fun acc (k, v) => acc.add k (c * d * v)) acc

section Container

variable (V : TensorBundle)

/-- Container-level `antimetric` of one blade: `g(complement B)·e_B` in diagonal
spaces (Grassmann `src/products.jl:1630-1815`), `hodge(complementleft(e_B))`
(the Gram-complement outermorphism) otherwise. -/
def antimetricChain (b : UInt64) : Except String Terms :=
  if V.isdiag then .ok #[(b, V.parityanti b)]
  else do linMap V.complementrighthodgeChain (← V.complementleftChain b)

/-- Container-level (Julia `Chain`/`Multivector` kernel) image of blade `b`
under a unary operation. -/
def unTermsC (op : UnOp) (b : UInt64) : Except String (Array BladeTerm) :=
  match op with
  | .complementright => ofTerms <$> V.complementrightChain b
  | .complementleft => ofTerms <$> V.complementleftChain b
  | .complementrighthodge => ofTerms <$> V.complementrighthodgeChain b
  | .complementlefthodge => ofTerms <$> V.complementlefthodgeChain b
  | .metric => .ok (ofTerms (V.metricChain b))
  | .antimetric => ofTerms <$> antimetricChain V b
  | .complementrightanti => do ofTerms <$> linMap V.complementrightChain (← antimetricChain V b)
  | .complementleftanti => do ofTerms <$> linMap V.complementleftChain (← antimetricChain V b)
  | op => V.terms₁ op b

/-- Container-level image of the blade pair `(a, b)` under a binary operation:
the blade products, with `cross = ⋆(a ∧ b)`, `veedot = cl(!a * !b)` and
`antidot = cl(contraction(!a, !b))` composed from the container complements. -/
def binTermsC (op : BinOp) (a b : UInt64) : Except String (Array BladeTerm) :=
  match op with
  | .cross => do
    ofTerms <$> linMap V.complementrighthodgeChain (scalarTerms (← V.terms₂ .wedge a b))
  | .veedot => do
    let p ← bilinMap (V.terms₂ .mul) (← V.complementrightChain a) (← V.complementrightChain b)
    ofTerms <$> linMap V.complementleftChain p
  | .antidot => do
    let p ← bilinMap (V.terms₂ .contraction) (← V.complementrightChain a) (← V.complementrightChain b)
    ofTerms <$> linMap V.complementleftChain p
  | op => V.terms₂ op a b

end Container

/-! ## Building plans -/

/-- Build the plan of `k` from the container-level blade rules. -/
def build (k : PlanKey) : Except String Plan := do
  let V := k.V
  let n := V.n
  let as := k.la.blades n
  let bs : Array UInt64 := match k.op with | .bin _ => k.lb.blades n | .un _ => #[0]
  let mut rows : Array (Array (Nat × Nat × Rat)) := Array.replicate (k.lc.size n) #[]
  let mut nested := 0
  for a in as, i in [0:as.size] do
    for b in bs, j in [0:bs.size] do
      let ts ← match k.op with
        | .bin op => binTermsC V op a b
        | .un op => unTermsC V op a
      for t in ts do
        if t.z != 0 then nested := nested + 1
        else if t.coef == 0 then pure ()
        else if k.lc.contains n t.bits then
          rows := rows.modify (k.lc.rank n t.bits) (·.push (i, j, t.coef))
        else if !k.project then
          throw s!"{V.bladeLabel t.bits} lies outside the result layout {repr k.lc} of {repr k.op}"
  return Plan.ofRows rows nested

private unsafe def planCacheImpl : IO.Ref (Std.HashMap PlanKey (Except String Plan)) :=
  unsafeBaseIO (IO.mkRef {})

/-- The process-global plan cache. -/
@[implemented_by planCacheImpl]
private opaque planCache : IO.Ref (Std.HashMap PlanKey (Except String Plan))

private unsafe def planImpl (k : PlanKey) : Except String Plan := unsafeBaseIO do
  match (← planCache.get).get? k with
  | some p => return p
  | none =>
    let p := build k
    planCache.modify (·.insert k p)
    return p

/-- The plan of `k`, built once per process (logically `build k`). -/
@[implemented_by planImpl]
def plan (k : PlanKey) : Except String Plan := build k

private unsafe def cachedPlanCountImpl (_ : Unit) : Nat :=
  unsafeBaseIO do return (← planCache.get).size

/-- Number of plans in the cache (diagnostics; logically `0`). -/
@[implemented_by cachedPlanCountImpl]
def cachedPlanCount (_ : Unit) : Nat := 0

/-! ## The reference kernels -/

variable {α : Type} [Coeff α]

/-- The reference binary kernel: `op` from layouts `la × lb` into `lc`, every
contribution landing in `lc` (Julia throws where the plan cannot be built:
complements in dyadic spaces; so does this, with Julia's message). -/
@[inline] def refBin (V : TensorBundle) (op : BinOp) (la lb lc : Layout)
    (x : Values α (la.size V.n)) (y : Values α (lb.size V.n)) : Values α (lc.size V.n) :=
  match plan { V, op := .bin op, la, lb, lc } with
  | .ok p => p.eval₂ x y
  | .error e => panic! e

/-- The reference projecting binary kernel: the part of `op` that lies in `lc`
(the other contributions are dropped: a grade projection of the result). -/
@[inline] def refBinProj (V : TensorBundle) (op : BinOp) (la lb lc : Layout)
    (x : Values α (la.size V.n)) (y : Values α (lb.size V.n)) : Values α (lc.size V.n) :=
  match plan { V, op := .bin op, la, lb, lc, project := true } with
  | .ok p => p.eval₂ x y
  | .error e => panic! e

/-- The reference unary kernel: `op` from layout `la` into `lc`. -/
@[inline] def refUn (V : TensorBundle) (op : UnOp) (la lc : Layout)
    (x : Values α (la.size V.n)) : Values α (lc.size V.n) :=
  match plan { V, op := .un op, la, lb := la, lc } with
  | .ok p => p.eval₁ x
  | .error e => panic! e

/-- The reference projecting unary kernel. -/
@[inline] def refUnProj (V : TensorBundle) (op : UnOp) (la lc : Layout)
    (x : Values α (la.size V.n)) : Values α (lc.size V.n) :=
  match plan { V, op := .un op, la, lb := la, lc, project := true } with
  | .ok p => p.eval₁ x
  | .error e => panic! e

end Grassmann.Kernel
