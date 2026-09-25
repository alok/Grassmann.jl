/-
Unary maps on the typed elements (Grassmann.jl `src/products.jl:1324-1976`,
DirectSum.jl `src/operations.jl`; port-notes/grassmann-products.md §4.9,
grassmann-algebra.md §4.6-4.8, grassmann-types.md §4.4).

All of them are linear and evaluate through the space's `Kernels` (`un` plans),
with the container-level semantics of `Grassmann.Kernel.Reference`.

| map | `Chain V G` | `Half V p` | `Multivector V` | others |
|---|---|---|---|---|
| `~` reverse, `involute`, `clifford`, `conj`, `antireverse`, `metric`, `antimetric`, `real`, `imag` | same type | same type | same type | `Single`/`Couple`/`PseudoCouple`: same type (sign flips) for the involutions |
| `⋆` hodge, `!` complementright, `complementleft`, `complementlefthodge`, `complementrightanti`, `complementleftanti` | `Chain V (n-G)` | `Half V (p ^^ n odd)` | `Multivector V` | as their chain, else `Multivector` |
| `even`/`odd` (`₊`/`₋`) | `Chain V G` (zero unless the parity matches) | `Half V false`/`Half V true` | `Half V false`/`Half V true` | as their chain, else a half |
| grade projection `G` (`scalar`, `vector`, ...), `volume` | `Chain V G` / `Chain V n` for every element type |

Julia's `conj` on tensors is the reverse (no complex conjugation of the
coefficients), and so is `Conj.conj` here. The Hodge complement of Julia's
`Chain` kernels conjugates complex coefficients (`src/products.jl:1330`); the plan
kernels do not (complex coefficients follow the `Multivector` kernels, which use
plain `*`, grassmann-products.md §4.12).

Tangent spaces: the complement of a blade copies its tangent generators, so the
complement of a grade-`G` chain is not of grade `n-G` there; the typed
complements reject tangent spaces (the plan fails; Julia throws too, defect
`tangent-container-complement`). Use `toMultivector` first.
-/
import Grassmann.Algebra.Arith
import Grassmann.Kernel.Class

namespace Grassmann

open DirectSum DirectSum.Bits StaticVectors AbstractTensors

variable {V : TensorBundle} {G : Nat} {p : Bool} {α : Type} [Coeff α] [Kernels V]

/-! ## Type-preserving linear maps on the dense containers -/

namespace Chain

/-- A type-preserving linear map `op` on a chain. -/
@[inline] def unop (op : UnOp) (c : Chain V G α) : Chain V G α :=
  ⟨Kernels.un op (.chain G) (.chain G) c.v⟩

/-- Julia `reverse(t)` (`~t`): grade `k` scaled by `(-1)^{k(k-1)/2}`. -/
@[inline] def reverse (c : Chain V G α) : Chain V G α := unop .reverse c
/-- Julia `involute(t)`: grade `k` scaled by `(-1)^k`. -/
@[inline] def involute (c : Chain V G α) : Chain V G α := unop .involute c
/-- Julia `clifford(t)` = `involute ∘ reverse`. -/
@[inline] def clifford (c : Chain V G α) : Chain V G α := unop .clifford c
/-- Julia `antireverse(t)` (`pseudoreverse`): reverse by the pseudograde `n-k`. -/
@[inline] def antireverse (c : Chain V G α) : Chain V G α := unop .antireverse c
/-- Julia `pseudoinvolute(t)`. -/
@[inline] def antiinvolute (c : Chain V G α) : Chain V G α := unop .antiinvolute c
/-- Julia `pseudoclifford(t)`. -/
@[inline] def anticlifford (c : Chain V G α) : Chain V G α := unop .anticlifford c
/-- Julia `metric(t)`: the Gram outermorphism (`g(B)·e_B` for a diagonal metric). -/
@[inline] def metric (c : Chain V G α) : Chain V G α := unop .metric c
/-- Julia `antimetric(t)` (`cometric`): `g(complement B)·e_B` for a diagonal metric. -/
@[inline] def antimetric (c : Chain V G α) : Chain V G α := unop .antimetric c
/-- Julia `real(t)`: the grades fixed by the reverse (`k mod 4 ∈ {0,1}`). -/
@[inline] def realPart (c : Chain V G α) : Chain V G α := unop .real c
/-- Julia `imag(t)`: the grades negated by the reverse (`k mod 4 ∈ {2,3}`). -/
@[inline] def imagPart (c : Chain V G α) : Chain V G α := unop .imag c

/-- A complement-type map on a chain: grade `G` to grade `n - G`. -/
@[inline] def comp (op : UnOp) (c : Chain V G α) : Chain V (V.n - G) α :=
  ⟨Kernels.un op (.chain G) (.chain (V.n - G)) c.v⟩

/-- Julia `complementright(t)` (`!t`): the metric-free right complement. -/
@[inline] def complementright (c : Chain V G α) : Chain V (V.n - G) α := comp .complementright c
/-- Julia `complementleft(t)`: the inverse of `complementright`. -/
@[inline] def complementleft (c : Chain V G α) : Chain V (V.n - G) α := comp .complementleft c
/-- Julia `hodge(t)` (`⋆t`, `complementrighthodge`) = `(~t) ⟑ I`. -/
@[inline] def hodge (c : Chain V G α) : Chain V (V.n - G) α := comp .complementrighthodge c
/-- Julia `complementlefthodge(t)` = `I ⟑ (~t)`. -/
@[inline] def complementlefthodge (c : Chain V G α) : Chain V (V.n - G) α := comp .complementlefthodge c
/-- Julia `complementrightanti(t) = complementright(antimetric(t))`. -/
@[inline] def complementrightanti (c : Chain V G α) : Chain V (V.n - G) α := comp .complementrightanti c
/-- Julia `complementleftanti(t) = complementleft(antimetric(t))`. -/
@[inline] def complementleftanti (c : Chain V G α) : Chain V (V.n - G) α := comp .complementleftanti c

end Chain

namespace Half

/-- A type-preserving linear map `op` on a half. -/
@[inline] def unop (op : UnOp) (h : Half V p α) : Half V p α :=
  ⟨Kernels.un op (halfLayout p) (halfLayout p) h.v⟩

/-- Julia `reverse(t)`. -/
@[inline] def reverse (h : Half V p α) : Half V p α := unop .reverse h
/-- Julia `involute(t)`. -/
@[inline] def involute (h : Half V p α) : Half V p α := unop .involute h
/-- Julia `clifford(t)`. -/
@[inline] def clifford (h : Half V p α) : Half V p α := unop .clifford h
/-- Julia `antireverse(t)`. -/
@[inline] def antireverse (h : Half V p α) : Half V p α := unop .antireverse h
/-- Julia `pseudoinvolute(t)`. -/
@[inline] def antiinvolute (h : Half V p α) : Half V p α := unop .antiinvolute h
/-- Julia `pseudoclifford(t)`. -/
@[inline] def anticlifford (h : Half V p α) : Half V p α := unop .anticlifford h
/-- Julia `metric(t)`. -/
@[inline] def metric (h : Half V p α) : Half V p α := unop .metric h
/-- Julia `antimetric(t)`. -/
@[inline] def antimetric (h : Half V p α) : Half V p α := unop .antimetric h
/-- Julia `real(t)`. -/
@[inline] def realPart (h : Half V p α) : Half V p α := unop .real h
/-- Julia `imag(t)`. -/
@[inline] def imagPart (h : Half V p α) : Half V p α := unop .imag h

/-- A complement-type map on a half: the parity flips when `n` is odd
(Julia `src/products.jl:1324-1487`). -/
@[inline] def comp (op : UnOp) (h : Half V p α) : Half V (p ^^ (V.n % 2 == 1)) α :=
  ⟨Kernels.un op (halfLayout p) (halfLayout (p ^^ (V.n % 2 == 1))) h.v⟩

/-- Julia `complementright(t)`. -/
@[inline] def complementright (h : Half V p α) : Half V (p ^^ (V.n % 2 == 1)) α := comp .complementright h
/-- Julia `complementleft(t)`. -/
@[inline] def complementleft (h : Half V p α) : Half V (p ^^ (V.n % 2 == 1)) α := comp .complementleft h
/-- Julia `hodge(t)`. -/
@[inline] def hodge (h : Half V p α) : Half V (p ^^ (V.n % 2 == 1)) α := comp .complementrighthodge h
/-- Julia `complementlefthodge(t)`. -/
@[inline] def complementlefthodge (h : Half V p α) : Half V (p ^^ (V.n % 2 == 1)) α :=
  comp .complementlefthodge h
/-- Julia `complementrightanti(t)`. -/
@[inline] def complementrightanti (h : Half V p α) : Half V (p ^^ (V.n % 2 == 1)) α :=
  comp .complementrightanti h
/-- Julia `complementleftanti(t)`. -/
@[inline] def complementleftanti (h : Half V p α) : Half V (p ^^ (V.n % 2 == 1)) α :=
  comp .complementleftanti h

end Half

namespace Multivector

/-- A linear map `op` on a multivector. -/
@[inline] def unop (op : UnOp) (m : Multivector V α) : Multivector V α :=
  ⟨Kernels.un op .full .full m.v⟩

/-- Julia `reverse(t)`. -/
@[inline] def reverse (m : Multivector V α) : Multivector V α := unop .reverse m
/-- Julia `involute(t)`. -/
@[inline] def involute (m : Multivector V α) : Multivector V α := unop .involute m
/-- Julia `clifford(t)`. -/
@[inline] def clifford (m : Multivector V α) : Multivector V α := unop .clifford m
/-- Julia `antireverse(t)`. -/
@[inline] def antireverse (m : Multivector V α) : Multivector V α := unop .antireverse m
/-- Julia `pseudoinvolute(t)`. -/
@[inline] def antiinvolute (m : Multivector V α) : Multivector V α := unop .antiinvolute m
/-- Julia `pseudoclifford(t)`. -/
@[inline] def anticlifford (m : Multivector V α) : Multivector V α := unop .anticlifford m
/-- Julia `metric(t)`. -/
@[inline] def metric (m : Multivector V α) : Multivector V α := unop .metric m
/-- Julia `antimetric(t)`. -/
@[inline] def antimetric (m : Multivector V α) : Multivector V α := unop .antimetric m
/-- Julia `real(t)`. -/
@[inline] def realPart (m : Multivector V α) : Multivector V α := unop .real m
/-- Julia `imag(t)`. -/
@[inline] def imagPart (m : Multivector V α) : Multivector V α := unop .imag m
/-- Julia `complementright(t)`. -/
@[inline] def complementright (m : Multivector V α) : Multivector V α := unop .complementright m
/-- Julia `complementleft(t)`. -/
@[inline] def complementleft (m : Multivector V α) : Multivector V α := unop .complementleft m
/-- Julia `hodge(t)`. -/
@[inline] def hodge (m : Multivector V α) : Multivector V α := unop .complementrighthodge m
/-- Julia `complementlefthodge(t)`. -/
@[inline] def complementlefthodge (m : Multivector V α) : Multivector V α := unop .complementlefthodge m
/-- Julia `complementrightanti(t)`. -/
@[inline] def complementrightanti (m : Multivector V α) : Multivector V α := unop .complementrightanti m
/-- Julia `complementleftanti(t)`. -/
@[inline] def complementleftanti (m : Multivector V α) : Multivector V α := unop .complementleftanti m

end Multivector

/-! ## Involutions of the single-term elements

The involutions scale each blade by a sign (the blade-level rule of
`DirectSum.BladeAlgebra`); `Couple`/`PseudoCouple` scale both parts, which fixes
Julia's `antireverse(::Couple)` (defect `antireverse-couple`). -/

/-- The factor by which the sign-only map `op` scales blade `b`. -/
def bladeFactor (V : TensorBundle) (op : UnOp) (b : UInt64) : Rat :=
  match V.terms₁ op b with
  | .ok ts => (ts.find? (·.bits == b)).map (·.coef) |>.getD 0
  | .error _ => 0

/-- Scale a coefficient by an exact factor (`±1` without a multiplication). -/
@[inline] def scaleBy (c : Rat) (x : α) : α :=
  if c == 1 then x else if c == -1 then -x else Coeff.ofRat c * x

namespace Single

/-- A sign-only map on a single term. -/
@[inline] def unop {G : Nat} (op : UnOp) (s : Single V G α) : Single V G α :=
  ⟨s.bits, scaleBy (bladeFactor V op s.bits) s.val⟩

end Single

namespace Couple

/-- A sign-only map on a couple (both parts). -/
@[inline] def unop (op : UnOp) (z : Couple V α) : Couple V α :=
  ⟨z.bits, scaleBy (bladeFactor V op 0) z.re, scaleBy (bladeFactor V op z.bits) z.im⟩

end Couple

namespace PseudoCouple

/-- A sign-only map on a pseudo-couple (both parts). -/
@[inline] def unop (op : UnOp) (z : PseudoCouple V α) : PseudoCouple V α :=
  ⟨z.bits, scaleBy (bladeFactor V op z.bits) z.re, scaleBy (bladeFactor V op (lowMask V.n)) z.im⟩

end PseudoCouple

/-! ## Class instances (AbstractTensors operator vocabulary) -/

instance : Reverse (Chain V G α) := ⟨Chain.reverse⟩
instance : Reverse (Half V p α) := ⟨Half.reverse⟩
instance : Reverse (Multivector V α) := ⟨Multivector.reverse⟩
instance : Reverse (Single V G α) := ⟨Single.unop .reverse⟩
instance : Reverse (Couple V α) := ⟨Couple.unop .reverse⟩
instance : Reverse (PseudoCouple V α) := ⟨PseudoCouple.unop .reverse⟩

instance : Involute (Chain V G α) := ⟨Chain.involute⟩
instance : Involute (Half V p α) := ⟨Half.involute⟩
instance : Involute (Multivector V α) := ⟨Multivector.involute⟩
instance : Involute (Single V G α) := ⟨Single.unop .involute⟩
instance : Involute (Couple V α) := ⟨Couple.unop .involute⟩
instance : Involute (PseudoCouple V α) := ⟨PseudoCouple.unop .involute⟩

instance : Clifford (Chain V G α) := ⟨Chain.clifford⟩
instance : Clifford (Half V p α) := ⟨Half.clifford⟩
instance : Clifford (Multivector V α) := ⟨Multivector.clifford⟩
instance : Clifford (Single V G α) := ⟨Single.unop .clifford⟩
instance : Clifford (Couple V α) := ⟨Couple.unop .clifford⟩
instance : Clifford (PseudoCouple V α) := ⟨PseudoCouple.unop .clifford⟩

/-- Julia `conj(t)` of a tensor is its reverse (`DirectSum.jl src/generic.jl:187`). -/
instance : Conj (Chain V G α) := ⟨Chain.reverse⟩
instance : Conj (Half V p α) := ⟨Half.reverse⟩
instance : Conj (Multivector V α) := ⟨Multivector.reverse⟩
instance : Conj (Single V G α) := ⟨Single.unop .reverse⟩
instance : Conj (Couple V α) := ⟨Couple.unop .reverse⟩
instance : Conj (PseudoCouple V α) := ⟨PseudoCouple.unop .reverse⟩

section Complements

variable {X : Type}

instance [AsChain X V G α] : Hodge X (Chain V (V.n - G) α) := ⟨fun x => (AsChain.toChain x).hodge⟩
instance : Hodge (Half V p α) (Half V (p ^^ (V.n % 2 == 1)) α) := ⟨Half.hodge⟩
instance (priority := low) [DenseLayout X V α] : Hodge X (Multivector V α) :=
  ⟨fun x => ⟨Kernels.un .complementrighthodge (layoutOf X) .full (DenseLayout.values x)⟩⟩

instance [AsChain X V G α] : ComplementRight X (Chain V (V.n - G) α) :=
  ⟨fun x => (AsChain.toChain x).complementright⟩
instance : ComplementRight (Half V p α) (Half V (p ^^ (V.n % 2 == 1)) α) := ⟨Half.complementright⟩
instance (priority := low) [DenseLayout X V α] : ComplementRight X (Multivector V α) :=
  ⟨fun x => ⟨Kernels.un .complementright (layoutOf X) .full (DenseLayout.values x)⟩⟩

instance [AsChain X V G α] : ComplementLeft X (Chain V (V.n - G) α) :=
  ⟨fun x => (AsChain.toChain x).complementleft⟩
instance : ComplementLeft (Half V p α) (Half V (p ^^ (V.n % 2 == 1)) α) := ⟨Half.complementleft⟩
instance (priority := low) [DenseLayout X V α] : ComplementLeft X (Multivector V α) :=
  ⟨fun x => ⟨Kernels.un .complementleft (layoutOf X) .full (DenseLayout.values x)⟩⟩

end Complements

section Parts

variable {X : Type}

/-- Julia `even(t)` of a homogeneous element: itself if its grade is even, else zero. -/
instance [AsChain X V G α] : Even X (Chain V G α) :=
  ⟨fun x => if G % 2 == 0 then AsChain.toChain x else Chain.zero⟩
/-- Julia `odd(t)` of a homogeneous element. -/
instance [AsChain X V G α] : Odd X (Chain V G α) :=
  ⟨fun x => if G % 2 == 1 then AsChain.toChain x else Chain.zero⟩
/-- Julia `even(m)`: the even part as a `Spinor` (`src/products.jl:1488-1522`). -/
instance (priority := low) [DenseLayout X V α] : Even X (Half V false α) := ⟨fun x => toHalf x false⟩
/-- Julia `odd(m)`: the odd part as a `CoSpinor`. -/
instance (priority := low) [DenseLayout X V α] : Odd X (Half V true α) := ⟨fun x => toHalf x true⟩

/-- Julia `grade(t, G)` / `t(G)`: the grade-`G` part of any element as a chain
(`scalar`, `vector`, `bivector`, `trivector` are `G = 0, 1, 2, 3`). -/
instance [DenseLayout X V α] : GradeProj X G (Chain V G α) := ⟨fun x => gradePart x G⟩

/-- Julia `volume(t)` (`pseudoscalar`): the top-grade part. -/
instance [DenseLayout X V α] : Volume X (Chain V V.n α) := ⟨fun x => gradePart x V.n⟩

end Parts

end Grassmann
