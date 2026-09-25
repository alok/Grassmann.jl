/-
Julia's generated product loops, bit for bit (Grassmann.jl `src/algebra.jl:1152-1790`,
`src/products.jl:140-360, 1146-1330`, `src/algebra.jl:1828-1900`).

The static layer's plans (`Grassmann.Kernel.Plan`) compute every output as
`0 + t₁ + t₂ + ⋯` in DirectSum's operand order. Julia's generated product methods compute
the same bilinear map, but spell each output as the expression `∑(t₁, t₂, …)` with
`tₖ = ∏(g, x·y)` (StaticVectors `∑ = +`, a left fold that starts from `t₁`, and an entry
with no contribution is the literal `zero(t)`), in the order of the generator's loops.
With `Float` coefficients the two agree up to the sign of zero (`0.0 + (-0.0) = 0.0`,
Julia keeps the `-0.0` of a single negative contribution) and the rounding of sums in a
different order. The dynamic layer reproduces Julia's printed values, so its products
evaluate through the plans here:

* a `JSrc` operand is a container of some layout (all stored entries, zeros included:
  Julia's generated code reads them all) or a single term (Julia `Single`/`Submanifold`);
* the rows of a `JKey` plan list the contributions in Julia's loop order: first operand
  outermost (`outerFirst`: chain × chain and container × container) or second operand
  outermost (a graded element with a `Spinor`/`CoSpinor`/`Multivector`, whose generator
  loops over the container);
* the blade-level contributions `(C, g)` are DirectSum's (`TensorBundle.apply₂`), keeping
  the zero metric factor of a degenerate geometric product (Julia's diagonal
  `geomaddmulti!_pre` emits `∏(0, x·y)`; contractions and `∨` drop such terms, `t = false`);
* `pre` selects Julia's expression form (`∑` from the first term) or its runtime loop
  (`out = zeros(…)`, `out[k] += …`: the generators above `cache_limit`, equal to the
  plan semantics).

Sandwich products (`SKey`) are the two passes of Julia's `product_sandwich`: the first
pass multiplies the versor's entries into the graded element, the second multiplies the
nonempty first-pass entries (`!isnull(val)`) by the versor again and keeps the grade of
the element.

Plans are built once per process and cached like the static layer's plans
(`@[implemented_by]` over an `IO.Ref` cache; logically `build`).
-/
import Grassmann.Kernel.Reference

namespace Grassmann.Loops

open DirectSum DirectSum.Bits StaticVectors AbstractTensors Grassmann.Kernel

/-- An operand of a generated loop: a container of layout `l` (every stored entry) or
the terms Julia's loop visits, in its order (a `Single`/`Submanifold`: one; the versor
`Couple`/`PseudoCouple` of a sandwich: its `B` part, then its scalar/volume part). -/
inductive JSrc where
  /-- A `Chain`/`Spinor`/`CoSpinor`/`Multivector` of this layout. -/
  | dense (l : Layout)
  /-- Terms of these blades. -/
  | terms (bs : Array UInt64)
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- The blades of an operand, in storage order. -/
def JSrc.blades (n : Nat) : JSrc → Array UInt64
  | .dense l => l.blades n
  | .terms bs => bs

/-- A generated product loop: space, operation, operands, result layout (contributions
outside it are dropped, as Julia's `Chain{V,G}(out[…])` slices do), loop nesting. -/
structure JKey where
  /-- The space. -/
  V : TensorBundle
  /-- The core product. -/
  op : BinOp
  /-- The first operand. -/
  a : JSrc
  /-- The second operand. -/
  b : JSrc
  /-- The result layout. -/
  lc : Layout
  /-- The first operand is the outer loop (else the second one is). -/
  outerFirst : Bool
  deriving Repr, Inhabited

instance : BEq JKey where
  beq x y := x.op == y.op && x.a == y.a && x.b == y.b && x.lc == y.lc &&
    x.outerFirst == y.outerFirst && x.V.n == y.V.n && x.V == y.V

instance : Hashable JKey where
  hash k := mixHash (hash k.V.n) (mixHash (hash k.op) (mixHash (hash k.a)
    (mixHash (hash k.b) (mixHash (hash k.lc) (hash k.outerFirst)))))

/-- The contributions `(C, g)` of the blade pair `(A, B)` to Julia's generated loops:
DirectSum's blade result, keeping the zero factor of a degenerate diagonal geometric
product (`∏(0, x·y)`), dropping the other zero terms and the repeated-tangent ones. -/
def contribs (V : TensorBundle) (op : BinOp) (A B : UInt64) : Array (UInt64 × Rat) :=
  match V.apply₂ op A B with
  | .ok (.nested ..) | .error _ => #[]
  | .ok r =>
    let keepZero := op == .mul && V.isdiag
    r.terms.filter fun (_, c) => keepZero || c != 0

/-- A plan with the given rows (zero coefficients kept: they are Julia terms). -/
def ofRowsKeep (rows : Array (Array (Nat × Nat × Rat))) : Plan :=
  rows.foldl (init := {}) fun p row =>
    let p := row.foldl (init := p) fun p (a, b, r) =>
      { p with
        ia := p.ia.push a.toUInt32, ib := p.ib.push b.toUInt32
        code := p.code.push (if r == 1 then 0 else if r == -1 then 1 else 2)
        coef := p.coef.push r }
    { p with rowStart := p.rowStart.push p.ia.size.toUInt32 }

/-- The rows of a loop over the entry pairs `(i, j)` of `as × bs` in Julia's nesting
(`keepA i` filters first-operand entries). -/
def loopRows (V : TensorBundle) (op : BinOp) (as bs : Array UInt64) (lc : Layout)
    (outerFirst : Bool) (keepA : Nat → Bool := fun _ => true) :
    Array (Array (Nat × Nat × Rat)) := Id.run do
  let n := V.n
  let mut rows : Array (Array (Nat × Nat × Rat)) := Array.replicate (lc.size n) #[]
  let (no, ni) := if outerFirst then (as.size, bs.size) else (bs.size, as.size)
  for o in [0:no] do
    for k in [0:ni] do
      let (i, j) := if outerFirst then (o, k) else (k, o)
      if keepA i then
        for (C, g) in contribs V op as[i]! bs[j]! do
          if lc.contains n C then
            rows := rows.modify (lc.rank n C) (·.push (i, j, g))
  return rows

/-- Build the plan of a generated loop. -/
def build (k : JKey) : Plan :=
  ofRowsKeep (loopRows k.V k.op (k.a.blades k.V.n) (k.b.blades k.V.n) k.lc k.outerFirst)

private unsafe def cacheImpl : IO.Ref (Std.HashMap JKey Plan) :=
  unsafeBaseIO (IO.mkRef {})

/-- The process-global cache of loop plans. -/
@[implemented_by cacheImpl]
private opaque cache : IO.Ref (Std.HashMap JKey Plan)

private unsafe def planImpl (k : JKey) : Plan := unsafeBaseIO do
  match (← cache.get).get? k with
  | some p => return p
  | none =>
    let p := build k
    cache.modify (·.insert k p)
    return p

/-- The plan of `k`, built once per process (logically `build k`). -/
@[implemented_by planImpl]
def plan (k : JKey) : Plan := build k

/-! ## Sandwich plans -/

/-- Julia's two-pass `product_sandwich` of a graded `x` (grade `G`) by a versor `y`: the
first pass `y ⟑ x` into the half layout `mid`, the second pass `mid ⟑ y` onto grade `G`,
over the first-pass entries that received a contribution. -/
structure SKey where
  /-- The space. -/
  V : TensorBundle
  /-- The versor. -/
  y : JSrc
  /-- The graded element. -/
  x : JSrc
  /-- The first-pass (half) layout. -/
  mid : Layout
  /-- The grade of the result. -/
  G : Nat
  deriving Repr, Inhabited

instance : BEq SKey where
  beq p q := p.y == q.y && p.x == q.x && p.mid == q.mid && p.G == q.G && p.V.n == q.V.n &&
    p.V == q.V

instance : Hashable SKey where
  hash k := mixHash (hash k.V.n) (mixHash (hash k.y) (mixHash (hash k.x)
    (mixHash (hash k.mid) (hash k.G))))

/-- The two plans of a sandwich. -/
def buildS (k : SKey) : Plan × Plan :=
  let n := k.V.n
  let ys := k.y.blades n
  let p₁ := ofRowsKeep (loopRows k.V .mul ys (k.x.blades n) k.mid true)
  let live := fun (c : Nat) => (p₁.rowStart[c]?.getD 0) != (p₁.rowStart[c + 1]?.getD 0)
  let p₂ := ofRowsKeep (loopRows k.V .mul (k.mid.blades n) ys (.chain k.G) true live)
  (p₁, p₂)

private unsafe def sCacheImpl : IO.Ref (Std.HashMap SKey (Plan × Plan)) :=
  unsafeBaseIO (IO.mkRef {})

/-- The process-global cache of sandwich plans. -/
@[implemented_by sCacheImpl]
private opaque sCache : IO.Ref (Std.HashMap SKey (Plan × Plan))

private unsafe def splanImpl (k : SKey) : Plan × Plan := unsafeBaseIO do
  match (← sCache.get).get? k with
  | some p => return p
  | none =>
    let p := buildS k
    sCache.modify (·.insert k p)
    return p

/-- The plans of `k`, built once per process (logically `buildS k`). -/
@[implemented_by splanImpl]
def splan (k : SKey) : Plan × Plan := buildS k

/-! ## Metric plans -/

/-- Julia's `metric` of a container in a non-diagonal space (Grassmann
`src/products.jl:1630-1700`: `contraction(metrictensor(V, G), b)` for a `Chain`, the
`Outermorphism` of the metric for a `Spinor`/`CoSpinor`/`Multivector`,
`src/forms.jl:942-968, 1044-1063`): each grade block is multiplied by the compound Gram
matrix with the generated `matmul`, output `j` being `+(M[1][j]*y[1], M[2][j]*y[2], …)`
over every entry of the block (zero matrix entries included); the scalar entry is copied. -/
def buildM (V : TensorBundle) (l : Layout) : Plan := Id.run do
  let n := V.n
  let bs := l.blades n
  let mut rows : Array (Array (Nat × Nat × Rat)) := #[]
  for β in bs do
    let g := popcount β
    if g == 0 then
      rows := rows.push #[(l.rank n β, 0, 1)]
    else
      let mut row := #[]
      for a in bs, i in [0:bs.size] do
        if popcount a == g then
          let c := ((V.metricChain a).find? (·.1 == β)).map (·.2) |>.getD 0
          row := row.push (i, 0, c)
      rows := rows.push row
  return ofRowsKeep rows

private unsafe def mCacheImpl : IO.Ref (Std.HashMap (Layout × TensorBundle) Plan) :=
  unsafeBaseIO (IO.mkRef {})

/-- The process-global cache of metric plans. -/
@[implemented_by mCacheImpl]
private opaque mCache : IO.Ref (Std.HashMap (Layout × TensorBundle) Plan)

private unsafe def mplanImpl (V : TensorBundle) (l : Layout) : Plan := unsafeBaseIO do
  match (← mCache.get).get? (l, V) with
  | some p => return p
  | none =>
    let p := buildM V l
    mCache.modify (·.insert (l, V) p)
    return p

/-- The metric plan of layout `l`, built once per process (logically `buildM V l`). -/
@[implemented_by mplanImpl]
def mplan (V : TensorBundle) (l : Layout) : Plan := buildM V l

/-! ## Evaluation -/

variable {α : Type} [Coeff α]

/-- Julia's term `∏(g, v)` of entry `t` (`g = ±1` exactly `±v`). -/
@[inline] def first (p : Plan) (ha : p.Aligned) (t : Nat) (ht : t < p.ia.size) (v : α) : α :=
  let c := p.code[t]'(by have := ha.2.1; omega)
  if c == 0 then v
  else if c == 1 then -v
  else Coeff.ofRat (p.coef[t]'(by have := ha.2.2; omega)) * v

/-- One output: Julia's `∑(t₁, …)` (`pre`, starting from the first term; `zero` when the
row is empty) or its runtime `0 + t₁ + ⋯`. -/
@[specialize] def row (pre : Bool) (p : Plan) (ha : p.Aligned) (x y : Packed.Arr α) (s e : Nat)
    (he : e ≤ p.ia.size) : α :=
  if pre then
    if hs : s < e then
      have h1 : s < p.ia.size := by omega
      let v := Plan.rd x (p.ia[s]'h1).toNat * Plan.rd y (p.ib[s]'(by have := ha.1; omega)).toNat
      Plan.row₂ p ha x y e he (s + 1) (first p ha s h1 v)
    else Coeff.zero
  else Plan.row₂ p ha x y e he s Coeff.zero

/-- The outputs `c, …, k-1`, pushed onto `out`. -/
@[specialize] def rows (pre : Bool) (p : Plan) (ha : p.Aligned) (x y : Packed.Arr α) (k c : Nat)
    (out : Packed.Arr α) : Packed.Arr α :=
  if c < k then
    let s := (p.rowStart[c]?.getD 0).toNat
    let e := min (p.rowStart[c + 1]?.getD 0).toNat p.ia.size
    rows pre p ha x y k (c + 1) (Packed.push out (row pre p ha x y s e (Nat.min_le_right _ _)))
  else out
termination_by k - c

/-- Run a loop plan on raw operand storage into a length-`k` vector. -/
@[specialize] def eval (pre : Bool) {k : Nat} (p : Plan) (x y : Packed.Arr α) : Values α k :=
  if ha : p.Aligned then Plan.finish (rows pre p ha x y k 0 (Packed.mkEmpty k)) else zeroValues k

/-- The raw storage of a one-term operand. -/
@[inline] def termArr (x : α) : Packed.Arr α := Packed.push (Packed.mkEmpty 1) x

/-- The raw storage of a two-term operand. -/
@[inline] def termArr₂ (x y : α) : Packed.Arr α := Packed.push (Packed.push (Packed.mkEmpty 2) x) y

/-- `op(a, b)` by Julia's generated loop `k` (`pre`: the expression form). -/
@[inline] def run (pre : Bool) (k : JKey) (x y : Packed.Arr α) : Values α (k.lc.size k.V.n) :=
  eval pre (plan k) x y

/-- Julia's `metric` of a container of layout `l` in a non-diagonal space (`mplan`). -/
@[inline] def runM (V : TensorBundle) (l : Layout) (x : Packed.Arr α) : Values α (l.size V.n) :=
  eval true (mplan V l) x (termArr Coeff.one)

/-- Julia's `product_sandwich` of `x` by the versor `y`: first pass with the versor
entries `y₁` (Julia negates them per `parityclifford` for `⊘`), second pass with `y₂`. -/
@[inline] def runS (k : SKey) (y₁ x y₂ : Packed.Arr α) : Values α ((Layout.chain k.G).size k.V.n) :=
  let (p₁, p₂) := splan k
  let m : Values α (k.mid.size k.V.n) := eval true p₁ y₁ x
  eval true p₂ m.data y₂

end Grassmann.Loops
