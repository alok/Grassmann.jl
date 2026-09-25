import Grassmann

/-!
# `SparseChain`: sparse homogeneous elements

Clifford.jl (`src/multivectors.jl:12-64`, `src/algebra.jl:7-24`, `src/products.jl:5-16`; never
loaded upstream, port-notes/applied-misc.md §2.3, §4.3) stores a grade-`G` element as a
`SparseVector` over the `binomial(n, G)` blades of the grade. Here that is a sorted array of
`(index, value)` pairs, the index being the position in `Leibniz.indexBasis n G` (Julia's
`bladeindex` order, the storage order of `Grassmann.Chain`), with no stored zeros.

`chainValues` is Julia's `chainvalues` densify rule (Leibniz's `fill_limit = 0.5`): a grade that
is at least half nonzero, or the scalar or pseudoscalar grade, stays a dense `Chain`.

Every operation has the intended semantics of port-notes §4.3; the Julia sign bugs (`Term -
SparseChain` losing the sign of the right operand) are not reproduced. The dense containers of
`Grassmann` are the reference: `toChain`/`toMultivector` are homomorphisms for every operation
(`Tests.Clifford`).
-/

namespace Clifford

open Grassmann DirectSum StaticVectors AbstractTensors JuliaBase

/-- Leibniz's `fill_limit` (`src/utilities.jl:107`): a grade stays dense unless more than this
fraction of its coefficients is zero. -/
def fillLimit : Rat := 1 / 2

/-- Julia `SparseChain{V,G,T}`: the nonzero coefficients of a grade-`G` element as
`(index, value)` pairs, indices strictly increasing and below `binomial(n, G)`. -/
structure SparseChain (V : TensorBundle) (G : Nat) (α : Type) [Coeff α] where
  /-- the stored coefficients -/
  terms : Array (Nat × α)

namespace SparseChain

variable {V : TensorBundle} {G : Nat} {α : Type} [Coeff α]

/-- The empty (zero) sparse chain. -/
def zero : SparseChain V G α := ⟨#[]⟩

instance : Inhabited (SparseChain V G α) := ⟨zero⟩

/-- Number of stored coefficients (Julia `nnz`). -/
@[inline] def nnz (s : SparseChain V G α) : Nat := s.terms.size

/-- Is it zero (no stored coefficient)? -/
@[inline] def isZero (s : SparseChain V G α) : Bool := s.terms.isEmpty

/-- The nonzero coefficients of a dense chain (Julia `SparseChain(m::Chain)`). -/
def ofChain (c : Chain V G α) : SparseChain V G α :=
  ⟨c.v.toArray.zipIdx.filterMap fun (x, i) => if Coeff.isZero x then none else some (i, x)⟩

/-- From `(blade, value)` terms (Julia `SparseChain{V}(v::Vector{<:TensorTerm})`): blades not
of grade `G` are ignored, repeated blades add up. -/
def ofTerms (ts : List (UInt64 × α)) : SparseChain V G α :=
  let c : Chain V G α := Chain.ofFn fun i =>
    ts.foldl (fun acc (b, x) =>
      if DirectSum.Bits.popcount b == G && Leibniz.bladeRank V.n b == i.1 then acc + x else acc) Coeff.zero
  ofChain c

/-- The coefficient at index `i` (zero when not stored). -/
def get (s : SparseChain V G α) (i : Nat) : α :=
  match s.terms.find? (·.1 == i) with
  | some (_, x) => x
  | none => Coeff.zero

/-- The dense chain. -/
def toChain (s : SparseChain V G α) : Chain V G α := Chain.ofFn fun i => s.get i.1

/-- The dense multivector (Julia `Multivector(t)`): the coefficients scattered at
`binomsum(n, G) + index`. -/
def toMultivector (s : SparseChain V G α) : Multivector V α := Grassmann.toMultivector s.toChain

/-- The `(blade, value)` terms, in storage order. -/
def bladeTerms (s : SparseChain V G α) : List (UInt64 × α) :=
  s.terms.toList.map fun (i, x) => (Leibniz.unrank V.n G i, x)

/-- The two-pointer merge of two sparse chains: `f` on common indices, `l`/`r` on indices
present on one side only; zero results are dropped (sparse add/subtract). -/
def merge (l r : α → α) (f : α → α → α) (a b : SparseChain V G α) : SparseChain V G α :=
  ⟨go a.terms.toList b.terms.toList #[] (a.nnz + b.nnz + 1)⟩
where
  /-- One merge step, fuelled by the total length. -/
  go : List (Nat × α) → List (Nat × α) → Array (Nat × α) → Nat → Array (Nat × α)
    | [], [], acc, _ => acc
    | _, _, acc, 0 => acc
    | (i, x) :: xs, [], acc, fuel + 1 => go xs [] (push acc i (l x)) fuel
    | [], (j, y) :: ys, acc, fuel + 1 => go [] ys (push acc j (r y)) fuel
    | (i, x) :: xs, (j, y) :: ys, acc, fuel + 1 =>
      if i < j then go xs ((j, y) :: ys) (push acc i (l x)) fuel
      else if j < i then go ((i, x) :: xs) ys (push acc j (r y)) fuel
      else go xs ys (push acc i (f x y)) fuel
  /-- Append a coefficient unless it is zero. -/
  push (acc : Array (Nat × α)) (i : Nat) (x : α) : Array (Nat × α) :=
    if Coeff.isZero x then acc else acc.push (i, x)

/-- Map the stored coefficients, dropping the ones that become zero. -/
def mapValues (f : α → α) (s : SparseChain V G α) : SparseChain V G α :=
  ⟨s.terms.filterMap fun (i, x) => let y := f x; if Coeff.isZero y then none else some (i, y)⟩

/-- Julia `a + b` (`src/algebra.jl:7-15`). -/
def add (a b : SparseChain V G α) : SparseChain V G α := merge id id (· + ·) a b
/-- Julia `a - b`, the right operand negated (the intended semantics). -/
def sub (a b : SparseChain V G α) : SparseChain V G α := merge id (- ·) (· - ·) a b
/-- Julia `-a`. -/
def neg (a : SparseChain V G α) : SparseChain V G α := mapValues (- ·) a
/-- Julia `x * a` (termwise). -/
def smul (x : α) (a : SparseChain V G α) : SparseChain V G α := mapValues (x * ·) a

instance : Add (SparseChain V G α) := ⟨add⟩
instance : Sub (SparseChain V G α) := ⟨sub⟩
instance : Neg (SparseChain V G α) := ⟨neg⟩
instance : HMul α (SparseChain V G α) (SparseChain V G α) := ⟨smul⟩

/-- Julia `a ± t` for a single term `t` of the same grade (`src/algebra.jl:16-20`): scatter-add at
the term's blade index. -/
def addSingle (a : SparseChain V G α) (t : Single V G α) : SparseChain V G α :=
  a + ofChain (Chain.ofSingle t)

/-- Julia `t - a` (`src/algebra.jl:22-24`) with the sign of `a` kept (Julia loses it). -/
def singleSub (t : Single V G α) (a : SparseChain V G α) : SparseChain V G α :=
  ofChain (Chain.ofSingle t) - a

variable [Kernels V]

/-- Julia `reverse(a)` (termwise, `src/products.jl:11-16`). -/
def reverse (a : SparseChain V G α) : SparseChain V G α := ofChain a.toChain.reverse
/-- Julia `involute(a)`. -/
def involute (a : SparseChain V G α) : SparseChain V G α := ofChain a.toChain.involute
/-- Julia `conj(a)` (= `clifford`, Grassmann's conjugation on tensors). -/
def clifford (a : SparseChain V G α) : SparseChain V G α := ofChain a.toChain.clifford
/-- Julia `complementright(a)` (`src/products.jl:5-10`): grade `G ↦ n - G`. -/
def complementright (a : SparseChain V G α) : SparseChain V (V.n - G) α :=
  ofChain a.toChain.complementright
/-- Julia `complementleft(a)`. -/
def complementleft (a : SparseChain V G α) : SparseChain V (V.n - G) α :=
  ofChain a.toChain.complementleft

end SparseChain

/-! ## `chainvalues`: dense or sparse -/

/-- A homogeneous part, stored densely (a `Chain`) or sparsely (Julia's `chainvalues` result
type: `Chain` or `SparseChain`). The grade is a runtime value (a part of a `MultiGrade`). -/
inductive Graded (V : TensorBundle) (α : Type) [Coeff α] where
  /-- a dense chain of grade `g` -/
  | dense (g : Nat) (c : Chain V g α)
  /-- a sparse chain of grade `g` -/
  | sparse (g : Nat) (s : SparseChain V g α)

namespace Graded

variable {V : TensorBundle} {α : Type} [Coeff α]

/-- The grade. -/
def grade : Graded V α → Nat
  | dense g _ => g
  | sparse g _ => g

/-- The dense chain of the part's grade. -/
def chain : (p : Graded V α) → Chain V p.grade α
  | dense _ c => c
  | sparse _ s => s.toChain

/-- The part as a dense multivector. -/
def toMultivector (p : Graded V α) : Multivector V α := Grassmann.toMultivector p.chain

/-- Is it zero? -/
def isZero (p : Graded V α) : Bool := p.chain.isZero

/-- Is it stored sparsely? -/
def isSparse : Graded V α → Bool
  | dense .. => false
  | sparse .. => true

/-- The stored values (Julia `value`): all coefficients of a dense part, the nonzero ones of a
sparse part. -/
def values : Graded V α → Array α
  | dense _ c => c.v.toArray
  | sparse _ s => s.terms.map (·.2)

end Graded

/-- Julia `chainvalues(V, m, Val(G))` (`src/multivectors.jl:18-28`): a dense `Chain` for the
scalar and pseudoscalar grades and whenever at most half of the coefficients are zero (Leibniz
`fill_limit`), a `SparseChain` otherwise. -/
def chainValues {V : TensorBundle} {G : Nat} {α : Type} [Coeff α] (c : Chain V G α) : Graded V α :=
  let size := Leibniz.binomial V.n G
  let zeros := c.v.toList.filter Coeff.isZero |>.length
  if G == 0 || G == V.n || (zeros : Rat) / (max size 1 : Nat) < fillLimit then .dense G c
  else .sparse G (SparseChain.ofChain c)

end Clifford
