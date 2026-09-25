/-
Julia's `==` on dynamic elements (AbstractTensors `src/AbstractTensors.jl:298`
`==(a, b) = equal(a, b)`; Grassmann `src/multivectors.jl:120-186, 355-373, 449-453,
616-646, 765-812, 941-957`; DirectSum `src/DirectSum.jl:510, 607-670`; Leibniz
`src/Leibniz.jl:91-96`).

Julia compares two elements coefficient by coefficient with the coefficient type's `==`
(so `-0.0 == 0.0` and `NaN ≠ NaN`) after bringing them to a common kind, except:

* `∞`: `a == ∞` iff `isinf(norm(a))` (and `∞ == ∞`);
* `𝟎`: `a == 𝟎` iff `iszero(a)`, i.e. `norm(a) ≈ 0`, i.e. `norm(a) == 0` (an entry whose
  square underflows counts as zero);
* a `Couple` against a scalar term: `isscalar(z) && realvalue(z) == value(t)` (Julia's
  `isscalar` is approximate: `norm(z) ≈ |realvalue(z)|`);
* a `Couple{B}` against a term of another grade: `B == basis(t) && iszero(realvalue(z)) &&
  imagvalue(z) == value(t)` (a zero couple is *not* equal to a zero term on another blade);
* a `PseudoCouple{B}` against a term: on the pseudoscalar, `iszero(realvalue(z))` and the
  volume parts agree (Julia compares `imagvalue(t)` with `value(t)` there, a typo; the
  intent is implemented); otherwise `B == basis(t) && iszero(imagvalue(z)) &&
  realvalue(z) == value(t)`;
* phasors: amplitude and angle (a phasor against a `Couple` goes through `complexify`,
  not supported here: `false`).

`denseEq` is the plain coefficientwise comparison; `denseEq_iff` shows it decides equality
of the dense values for a lawful `==`, and `equal` is `denseEq` on every pair of containers
(`equal_of_dense`).
-/
import Grassmann.Dynamic.Norms
import Grassmann.Dynamic.Laws

namespace Grassmann

open DirectSum DirectSum.Bits StaticVectors AbstractTensors JuliaBase

namespace TA

variable {V : TensorBundle} {α : Type} [Coeff α]

/-- The dense coefficients agree under the coefficient type's `==`. -/
def denseEq [BEq α] (a b : TA V α) : Bool :=
  (List.finRange (2 ^ V.n)).all fun i => a.dget i == b.dget i

/-- For a lawful `==`, `denseEq` decides equality of the dense values. -/
theorem denseEq_iff [BEq α] [LawfulBEq α] (a b : TA V α) :
    a.denseEq b = true ↔ a.toDense = b.toDense := by
  constructor
  · intro h
    apply toDense_ext
    intro i
    have := (List.all_eq_true.mp h) i (List.mem_finRange i)
    exact eq_of_beq this
  · intro h
    refine List.all_eq_true.mpr fun i _ => ?_
    simp [dget, h]

/-- The value of a term (Julia `value(t)`: `1` for `One` and a basis blade). -/
def termValue? : TA V α → Option (UInt64 × α)
  | one => some (0, Coeff.one)
  | blade b => some (b, Coeff.one)
  | single b x => some (b, x)
  | _ => none

/-- Julia `a == b` (see the module docstring). -/
def equal [BEq α] [JNorm α] (a b : TA V α) : Bool :=
  let isZero := fun (x : α) => x == Coeff.zero
  let coupleTerm := fun (B : UInt64) (re im : α) (t : TA V α) =>
    match termValue? t with
    | some (0, v) => isscalar (couple B re im : TA V α) && re == v
    | some (C, v) => B == C && isZero re && im == v
    | none => denseEq (couple B re im) t
  let pseudoTerm := fun (B : UInt64) (re im : α) (t : TA V α) =>
    match termValue? t with
    | some (C, v) =>
      if C == pseudoBits V then isZero re && im == v else B == C && isZero im && re == v
    | none => denseEq (pseudo B re im) t
  match a, b with
  | infinity, infinity => true
  | infinity, x | x, infinity => (norm x).isInf
  | zero, x | x, zero => norm x == 0
  | phasor r θ, phasor s φ => r == s && denseEq θ φ
  | phasor .., _ | _, phasor .. => false
  | couple B re im, t@(one) | couple B re im, t@(blade _) | couple B re im, t@(single ..) =>
    coupleTerm B re im t
  | t@(one), couple B re im | t@(blade _), couple B re im | t@(single ..), couple B re im =>
    coupleTerm B re im t
  | pseudo B re im, t@(one) | pseudo B re im, t@(blade _) | pseudo B re im, t@(single ..) =>
    pseudoTerm B re im t
  | t@(one), pseudo B re im | t@(blade _), pseudo B re im | t@(single ..), pseudo B re im =>
    pseudoTerm B re im t
  | _, _ => denseEq a b

/-- Two containers (chains, halves, multivectors) are Julia-equal iff their coefficients
agree. -/
theorem equal_of_dense [BEq α] [JNorm α] (a b : TA V α)
    (ha : a.kind ∈ [.chain, .spinor, .cospinor, .multivector])
    (hb : b.kind ∈ [.chain, .spinor, .cospinor, .multivector]) :
    a.equal b = a.denseEq b := by
  cases a <;> cases b <;> simp_all [kind, equal]

end TA

end Grassmann
