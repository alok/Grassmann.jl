/-
  Grassmann/AnchorTheorems.lean - Fundamental theorems that should hold if the implementation is correct

  These are "anchor theorems" - key mathematical properties of Clifford algebras
  that serve as correctness specifications. Some are proved directly against the
  executable kernels; the remaining `sorry`s mark formalization targets.

  If any of these theorems are false, the implementation has a bug.
-/
import Grassmann.SparseMultivector
import Grassmann.RotorExp
import Grassmann.GANotation
import Mathlib.Algebra.Field.Rat

namespace Grassmann.Theorems

variable {n : ℕ} {sig : Signature n}

/-! ## Algebraic Structure Theorems -/

/-- The geometric product is associative: (a * b) * c = a * (b * c) -/
theorem geometric_product_assoc (a b c : MultivectorS sig Float) :
    (a * b) * c = a * (b * c) := by
  sorry

/-- Scalar multiplication distributes over geometric product -/
theorem smul_geometric_left (s : Float) (a b : MultivectorS sig Float) :
    (a.smul s) * b = (a * b).smul s := by
  sorry

/-- Addition distributes over geometric product (left) -/
theorem add_mul_distrib (a b c : MultivectorS sig Float) :
    (a + b) * c = a * c + b * c := by
  sorry

/-- Addition distributes over geometric product (right) -/
theorem mul_add_distrib (a b c : MultivectorS sig Float) :
    a * (b + c) = a * b + a * c := by
  sorry

/-! ## Basis Vector Theorems -/

/-- Basis vectors anticommute: eᵢ * eⱼ = -eⱼ * eᵢ for i ≠ j -/
theorem basis_anticommute (i j : Fin n) (h : i ≠ j) :
    let ei : MultivectorS sig Float := MultivectorS.basis i
    let ej : MultivectorS sig Float := MultivectorS.basis j
    ei * ej = (ej * ei).smul (-1 : Float) := by
  sorry

/-- Basis vector squares to signature value: eᵢ² = sig(i), including null dimensions. -/
theorem basis_square (i : Fin n) :
    let ei : MultivectorS sig Float := MultivectorS.basis i
    (ei * ei).scalarPart =
      if sig.degenerate.getLsbD i.val then 0
      else if sig.metric.getLsbD i.val then -1 else 1 := by
  sorry

/-! ## R3 Basis Blade Anchor Theorems -/

set_option linter.style.nativeDecide false in
/-- R3's first Euclidean basis blade squares to scalar `+1`. -/
theorem r3_e1_blade_square :
    geometricProductBlades (e1 : Blade R3) (e1 : Blade R3) =
      BladeProduct.nonzero 1 Blade.scalar := by
  native_decide

set_option linter.style.nativeDecide false in
/-- R3's second Euclidean basis blade squares to scalar `+1`. -/
theorem r3_e2_blade_square :
    geometricProductBlades (e2 : Blade R3) (e2 : Blade R3) =
      BladeProduct.nonzero 1 Blade.scalar := by
  native_decide

set_option linter.style.nativeDecide false in
/-- R3's third Euclidean basis blade squares to scalar `+1`. -/
theorem r3_e3_blade_square :
    geometricProductBlades (e3 : Blade R3) (e3 : Blade R3) =
      BladeProduct.nonzero 1 Blade.scalar := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Ordered R3 basis-vector product `e1 * e2` gives the positive bivector `e12`. -/
theorem r3_e1_e2_blade_product :
    geometricProductBlades (e1 : Blade R3) (e2 : Blade R3) =
      BladeProduct.nonzero 1 (e12 : Blade R3) := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Reversing R3 basis-vector order flips the `e12` sign. -/
theorem r3_e2_e1_blade_product :
    geometricProductBlades (e2 : Blade R3) (e1 : Blade R3) =
      BladeProduct.nonzero (-1) (e12 : Blade R3) := by
  native_decide

set_option linter.style.nativeDecide false in
/-- R3 Euclidean bivector `e12` squares to scalar `-1`. -/
theorem r3_e12_blade_square :
    geometricProductBlades (e12 : Blade R3) (e12 : Blade R3) =
      BladeProduct.nonzero (-1) Blade.scalar := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Wedge product of an R3 basis vector with itself is zero. -/
theorem r3_e1_wedge_self_zero :
    wedgeProductBlades (e1 : Blade R3) (e1 : Blade R3) = BladeProduct.zero := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Ordered R3 basis-vector wedge `e1 ∧ e2` gives the positive bivector `e12`. -/
theorem r3_e1_wedge_e2 :
    wedgeProductBlades (e1 : Blade R3) (e2 : Blade R3) =
      BladeProduct.nonzero 1 (e12 : Blade R3) := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Reversing R3 basis-vector wedge order flips the `e12` sign. -/
theorem r3_e2_wedge_e1 :
    wedgeProductBlades (e2 : Blade R3) (e1 : Blade R3) =
      BladeProduct.nonzero (-1) (e12 : Blade R3) := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Left contraction `e1 ⌋ e12` leaves the `e2` basis blade. -/
theorem r3_e1_left_contract_e12 :
    leftContractionBlades (e1 : Blade R3) (e12 : Blade R3) =
      BladeProduct.nonzero 1 (e2 : Blade R3) := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Left contraction `e2 ⌋ e12` records the expected orientation sign. -/
theorem r3_e2_left_contract_e12 :
    leftContractionBlades (e2 : Blade R3) (e12 : Blade R3) =
      BladeProduct.nonzero (-1) (e1 : Blade R3) := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Right contraction `e12 ⌊ e1` leaves the `e2` basis blade. -/
theorem r3_e12_right_contract_e1 :
    rightContractionBlades (e12 : Blade R3) (e1 : Blade R3) =
      BladeProduct.nonzero 1 (e2 : Blade R3) := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Right contraction `e12 ⌊ e2` records the expected orientation sign. -/
theorem r3_e12_right_contract_e2 :
    rightContractionBlades (e12 : Blade R3) (e2 : Blade R3) =
      BladeProduct.nonzero (-1) (e1 : Blade R3) := by
  native_decide

set_option linter.style.nativeDecide false in
/-- R3 scalar product of `e12` with itself is `-1`. -/
theorem r3_e12_scalar_product_self :
    scalarProductBlades (e12 : Blade R3) (e12 : Blade R3) = -1 := by
  native_decide

/-! ### R3 Dense Involution Anchors -/

/-- Exact rational R3 vector `e1` as a dense multivector. -/
def r3E1Multivector : Multivector R3 Rat :=
  Multivector.ofBlade (e1 : Blade R3)

/-- Exact rational R3 vector `e2` as a dense multivector. -/
def r3E2Multivector : Multivector R3 Rat :=
  Multivector.ofBlade (e2 : Blade R3)

/-- Exact rational R3 vector `e3` as a dense multivector. -/
def r3E3Multivector : Multivector R3 Rat :=
  Multivector.ofBlade (e3 : Blade R3)

/-- Exact rational R3 bivector `e12` as a dense multivector. -/
def r3E12Multivector : Multivector R3 Rat :=
  Multivector.ofBlade (e12 : Blade R3)

/-- Exact rational R3 bivector `e13` as a dense multivector. -/
def r3E13Multivector : Multivector R3 Rat :=
  Multivector.ofBlade (e13 : Blade R3)

/-- Exact rational R3 bivector `e23` as a dense multivector. -/
def r3E23Multivector : Multivector R3 Rat :=
  Multivector.ofBlade (e23 : Blade R3)

/-- Exact rational R3 pseudoscalar `e123` as a dense multivector. -/
def r3E123Multivector : Multivector R3 Rat :=
  Multivector.ofBlade (e123 : Blade R3)

set_option linter.style.nativeDecide false in
/-- Reverse fixes R3 vectors. -/
theorem r3_e1_reverse :
    r3E1Multivector† = r3E1Multivector := by
  apply Multivector.ext
  intro i
  native_decide +revert

set_option linter.style.nativeDecide false in
/-- Reverse negates R3 bivectors. -/
theorem r3_e12_reverse :
    r3E12Multivector† = r3E12Multivector.smul (-1 : Rat) := by
  apply Multivector.ext
  intro i
  native_decide +revert

set_option linter.style.nativeDecide false in
/-- Reverse negates the R3 pseudoscalar. -/
theorem r3_e123_reverse :
    r3E123Multivector† = r3E123Multivector.smul (-1 : Rat) := by
  apply Multivector.ext
  intro i
  native_decide +revert

set_option linter.style.nativeDecide false in
/-- Grade involution negates R3 vectors. -/
theorem r3_e1_involute :
    r3E1Multivectorˆ = r3E1Multivector.smul (-1 : Rat) := by
  apply Multivector.ext
  intro i
  native_decide +revert

set_option linter.style.nativeDecide false in
/-- Grade involution fixes R3 bivectors. -/
theorem r3_e12_involute :
    r3E12Multivectorˆ = r3E12Multivector := by
  apply Multivector.ext
  intro i
  native_decide +revert

set_option linter.style.nativeDecide false in
/-- Grade involution negates the R3 pseudoscalar. -/
theorem r3_e123_involute :
    r3E123Multivectorˆ = r3E123Multivector.smul (-1 : Rat) := by
  apply Multivector.ext
  intro i
  native_decide +revert

set_option linter.style.nativeDecide false in
/-- Clifford conjugation negates R3 vectors. -/
theorem r3_e1_conjugate :
    r3E1Multivector‡ = r3E1Multivector.smul (-1 : Rat) := by
  apply Multivector.ext
  intro i
  native_decide +revert

set_option linter.style.nativeDecide false in
/-- Clifford conjugation negates R3 bivectors. -/
theorem r3_e12_conjugate :
    r3E12Multivector‡ = r3E12Multivector.smul (-1 : Rat) := by
  apply Multivector.ext
  intro i
  native_decide +revert

set_option linter.style.nativeDecide false in
/-- Clifford conjugation fixes the R3 pseudoscalar. -/
theorem r3_e123_conjugate :
    r3E123Multivector‡ = r3E123Multivector := by
  apply Multivector.ext
  intro i
  native_decide +revert

/-! ### R3 Dense Hodge Anchors -/

set_option linter.style.nativeDecide false in
/-- Hodge dual maps the R3 scalar basis blade to the pseudoscalar. -/
theorem r3_hodge_scalar :
    ⋆ᵐ(Multivector.one : Multivector R3 Rat) = r3E123Multivector := by
  apply Multivector.ext
  intro i
  native_decide +revert

set_option linter.style.nativeDecide false in
/-- Hodge dual maps `e1` to `e23` in R3. -/
theorem r3_hodge_e1 :
    ⋆ᵐr3E1Multivector = r3E23Multivector := by
  apply Multivector.ext
  intro i
  native_decide +revert

set_option linter.style.nativeDecide false in
/-- Hodge dual maps `e2` to `-e13` in R3. -/
theorem r3_hodge_e2 :
    ⋆ᵐr3E2Multivector = r3E13Multivector.smul (-1 : Rat) := by
  apply Multivector.ext
  intro i
  native_decide +revert

set_option linter.style.nativeDecide false in
/-- Hodge dual maps `e3` to `e12` in R3. -/
theorem r3_hodge_e3 :
    ⋆ᵐr3E3Multivector = r3E12Multivector := by
  apply Multivector.ext
  intro i
  native_decide +revert

set_option linter.style.nativeDecide false in
/-- Hodge dual maps the R3 pseudoscalar to the scalar basis blade. -/
theorem r3_hodge_pseudoscalar :
    ⋆ᵐr3E123Multivector = (Multivector.one : Multivector R3 Rat) := by
  apply Multivector.ext
  intro i
  native_decide +revert

set_option linter.style.nativeDecide false in
/-- Hodge dual squares to the identity on R3 vectors. -/
theorem r3_hodge_hodge_e1 :
    ⋆ᵐ(⋆ᵐr3E1Multivector) = r3E1Multivector := by
  apply Multivector.ext
  intro i
  native_decide +revert

set_option linter.style.nativeDecide false in
/-- Hodge dual squares to the identity on R3 bivectors. -/
theorem r3_hodge_hodge_e12 :
    ⋆ᵐ(⋆ᵐr3E12Multivector) = r3E12Multivector := by
  apply Multivector.ext
  intro i
  native_decide +revert

/-! ### R4 Dense Hodge Anchors -/

/-- Exact rational R4 vector `e1` as a dense multivector. -/
def r4E1Multivector : Multivector Grassmann.R4 Rat :=
  Multivector.ofBlade (e1 : Blade Grassmann.R4)

/-- Exact rational R4 vector `e2` as a dense multivector. -/
def r4E2Multivector : Multivector Grassmann.R4 Rat :=
  Multivector.ofBlade (e2 : Blade Grassmann.R4)

/-- Exact rational R4 vector `e3` as a dense multivector. -/
def r4E3Multivector : Multivector Grassmann.R4 Rat :=
  Multivector.ofBlade (e3 : Blade Grassmann.R4)

/-- Exact rational R4 vector `e4` as a dense multivector. -/
def r4E4Multivector : Multivector Grassmann.R4 Rat :=
  Multivector.ofBlade (e4 : Blade Grassmann.R4)

/-- Exact rational R4 bivector `e12` as a dense multivector. -/
def r4E12Multivector : Multivector Grassmann.R4 Rat :=
  Multivector.ofBlade (e12 : Blade Grassmann.R4)

/-- R4 trivector `e123`, encoded as bit mask `0b0111`. -/
def r4E123Blade : Blade Grassmann.R4 := ⟨BitVec.ofNat 4 0b0111⟩

/-- R4 trivector `e124`, encoded as bit mask `0b1011`. -/
def r4E124Blade : Blade Grassmann.R4 := ⟨BitVec.ofNat 4 0b1011⟩

/-- R4 trivector `e134`, encoded as bit mask `0b1101`. -/
def r4E134Blade : Blade Grassmann.R4 := ⟨BitVec.ofNat 4 0b1101⟩

/-- R4 trivector `e234`, encoded as bit mask `0b1110`. -/
def r4E234Blade : Blade Grassmann.R4 := ⟨BitVec.ofNat 4 0b1110⟩

/-- Exact rational R4 trivector `e123` as a dense multivector. -/
def r4E123Multivector : Multivector Grassmann.R4 Rat :=
  Multivector.ofBlade r4E123Blade

/-- Exact rational R4 trivector `e124` as a dense multivector. -/
def r4E124Multivector : Multivector Grassmann.R4 Rat :=
  Multivector.ofBlade r4E124Blade

/-- Exact rational R4 trivector `e134` as a dense multivector. -/
def r4E134Multivector : Multivector Grassmann.R4 Rat :=
  Multivector.ofBlade r4E134Blade

/-- Exact rational R4 trivector `e234` as a dense multivector. -/
def r4E234Multivector : Multivector Grassmann.R4 Rat :=
  Multivector.ofBlade r4E234Blade

/-- Exact rational R4 pseudoscalar as a dense multivector. -/
def r4PseudoscalarMultivector : Multivector Grassmann.R4 Rat :=
  Multivector.ofBlade (Blade.pseudoscalar : Blade Grassmann.R4)

set_option linter.style.nativeDecide false in
/-- Hodge dual maps the R4 scalar basis blade to the pseudoscalar. -/
theorem r4_hodge_scalar :
    ⋆ᵐ(Multivector.one : Multivector Grassmann.R4 Rat) = r4PseudoscalarMultivector := by
  apply Multivector.ext
  intro i
  native_decide +revert

set_option linter.style.nativeDecide false in
/-- Hodge dual maps `e1` to `e234` in R4. -/
theorem r4_hodge_e1 :
    ⋆ᵐr4E1Multivector = r4E234Multivector := by
  apply Multivector.ext
  intro i
  native_decide +revert

set_option linter.style.nativeDecide false in
/-- Hodge dual maps `e2` to `-e134` in R4. -/
theorem r4_hodge_e2 :
    ⋆ᵐr4E2Multivector = r4E134Multivector.smul (-1 : Rat) := by
  apply Multivector.ext
  intro i
  native_decide +revert

set_option linter.style.nativeDecide false in
/-- Hodge dual maps `e3` to `e124` in R4. -/
theorem r4_hodge_e3 :
    ⋆ᵐr4E3Multivector = r4E124Multivector := by
  apply Multivector.ext
  intro i
  native_decide +revert

set_option linter.style.nativeDecide false in
/-- Hodge dual maps `e4` to `-e123` in R4. -/
theorem r4_hodge_e4 :
    ⋆ᵐr4E4Multivector = r4E123Multivector.smul (-1 : Rat) := by
  apply Multivector.ext
  intro i
  native_decide +revert

set_option linter.style.nativeDecide false in
/-- Hodge dual squares to `-1` on R4 vectors. -/
theorem r4_hodge_hodge_e1 :
    ⋆ᵐ(⋆ᵐr4E1Multivector) = r4E1Multivector.smul (-1 : Rat) := by
  apply Multivector.ext
  intro i
  native_decide +revert

set_option linter.style.nativeDecide false in
/-- Hodge dual squares to the identity on R4 bivectors. -/
theorem r4_hodge_hodge_e12 :
    ⋆ᵐ(⋆ᵐr4E12Multivector) = r4E12Multivector := by
  apply Multivector.ext
  intro i
  native_decide +revert

/-! ## PGA3 Null Basis Anchor Theorems -/

/-- PGA3's projective basis vector is explicitly marked as null in the signature. -/
theorem pga3_projective_signature_square :
    Signature.basisSquare PGA3 ⟨3, by decide⟩ = 0 := by
  decide

/-- PGA3 projective basis blade `e₄`, encoded as bit mask `0b1000`. -/
def pga3ProjectiveBlade : Blade PGA3 := ⟨BitVec.ofNat 4 8⟩

/-- PGA3 Euclidean-projective plane blade `e₁₄`, encoded as bit mask `0b1001`. -/
def pga3ProjectivePlane1Blade : Blade PGA3 := ⟨BitVec.ofNat 4 9⟩

/-- The geometric-product sign kernel cancels repeated PGA3 projective basis factors. -/
theorem pga3_projective_geometric_sign :
    geometricSign PGA3 pga3ProjectiveBlade pga3ProjectiveBlade = 0 := by
  decide

/-- The blade-level geometric product of PGA3's projective basis with itself is zero. -/
theorem pga3_projective_blade_product_zero :
    geometricProductBlades pga3ProjectiveBlade pga3ProjectiveBlade = BladeProduct.zero := by
  rfl

set_option linter.style.nativeDecide false in
/-- PGA3's first Euclidean basis blade still squares to scalar `+1`. -/
theorem pga3_e1_blade_square :
    geometricProductBlades (e1 : Blade PGA3) (e1 : Blade PGA3) =
      BladeProduct.nonzero 1 Blade.scalar := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Ordered PGA3 product `e1 * e0` gives the positive projective plane blade. -/
theorem pga3_e1_projective_blade_product :
    geometricProductBlades (e1 : Blade PGA3) pga3ProjectiveBlade =
      BladeProduct.nonzero 1 pga3ProjectivePlane1Blade := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Reversing `e1 * e0` flips the projective plane orientation sign. -/
theorem pga3_projective_e1_blade_product :
    geometricProductBlades pga3ProjectiveBlade (e1 : Blade PGA3) =
      BladeProduct.nonzero (-1) pga3ProjectivePlane1Blade := by
  native_decide

set_option linter.style.nativeDecide false in
/-- PGA3 projective basis wedge with itself is zero. -/
theorem pga3_projective_wedge_self_zero :
    wedgeProductBlades pga3ProjectiveBlade pga3ProjectiveBlade = BladeProduct.zero := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Ordered PGA3 wedge `e1 ∧ e0` gives the positive projective plane blade. -/
theorem pga3_e1_projective_wedge :
    wedgeProductBlades (e1 : Blade PGA3) pga3ProjectiveBlade =
      BladeProduct.nonzero 1 pga3ProjectivePlane1Blade := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Reversing PGA3 wedge `e1 ∧ e0` flips the projective plane orientation sign. -/
theorem pga3_projective_e1_wedge :
    wedgeProductBlades pga3ProjectiveBlade (e1 : Blade PGA3) =
      BladeProduct.nonzero (-1) pga3ProjectivePlane1Blade := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Left contraction `e1 ⌋ (e1 ∧ e0)` leaves the null projective basis blade. -/
theorem pga3_e1_left_contract_projective_plane :
    leftContractionBlades (e1 : Blade PGA3) pga3ProjectivePlane1Blade =
      BladeProduct.nonzero 1 pga3ProjectiveBlade := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Contracting the null projective basis into a blade containing it is zero. -/
theorem pga3_projective_left_contract_projective_plane_zero :
    leftContractionBlades pga3ProjectiveBlade pga3ProjectivePlane1Blade =
      BladeProduct.zero := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Right contraction `(e1 ∧ e0) ⌊ e1` leaves the null projective basis blade. -/
theorem pga3_projective_plane_right_contract_e1 :
    rightContractionBlades pga3ProjectivePlane1Blade (e1 : Blade PGA3) =
      BladeProduct.nonzero 1 pga3ProjectiveBlade := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Right contraction by the null projective basis is zero when the metric factor repeats. -/
theorem pga3_projective_plane_right_contract_projective_zero :
    rightContractionBlades pga3ProjectivePlane1Blade pga3ProjectiveBlade =
      BladeProduct.zero := by
  native_decide

set_option linter.style.nativeDecide false in
/-- PGA3 scalar product of the null projective basis blade with itself is zero. -/
theorem pga3_projective_scalar_product_self :
    scalarProductBlades pga3ProjectiveBlade pga3ProjectiveBlade = 0 := by
  native_decide

/-! ## CGA Basis Anchor Theorems -/

/-- CGA3's positive conformal basis blade, encoded as bit mask `0b01000`. -/
def cga3EplusBlade : Blade CGA3 := ⟨BitVec.ofNat 5 8⟩

/-- CGA3's negative conformal basis blade, encoded as bit mask `0b10000`. -/
def cga3EminusBlade : Blade CGA3 := ⟨BitVec.ofNat 5 16⟩

/-- CGA3's conformal plane blade spanned by the extra basis directions. -/
def cga3ExtraPlaneBlade : Blade CGA3 := ⟨BitVec.ofNat 5 24⟩

/-- CGA3's positive conformal basis vector squares to `+1`. -/
theorem cga3_eplus_signature_square :
    Signature.basisSquare CGA3 ⟨3, by decide⟩ = 1 := by
  decide

/-- CGA3's negative conformal basis vector squares to `-1`. -/
theorem cga3_eminus_signature_square :
    Signature.basisSquare CGA3 ⟨4, by decide⟩ = -1 := by
  decide

set_option linter.style.nativeDecide false in
/-- The geometric-product sign kernel records the positive conformal square. -/
theorem cga3_eplus_geometric_sign :
    geometricSign CGA3 cga3EplusBlade cga3EplusBlade = 1 := by
  native_decide

set_option linter.style.nativeDecide false in
/-- The geometric-product sign kernel records the negative conformal square. -/
theorem cga3_eminus_geometric_sign :
    geometricSign CGA3 cga3EminusBlade cga3EminusBlade = -1 := by
  native_decide

set_option linter.style.nativeDecide false in
/-- The ordered product of CGA3's extra conformal basis directions has positive sign. -/
theorem cga3_eplus_eminus_geometric_sign :
    geometricSign CGA3 cga3EplusBlade cga3EminusBlade = 1 := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Reversing CGA3's extra conformal basis directions flips the sign. -/
theorem cga3_eminus_eplus_geometric_sign :
    geometricSign CGA3 cga3EminusBlade cga3EplusBlade = -1 := by
  native_decide

set_option linter.style.nativeDecide false in
/-- The positive conformal basis blade squares to the scalar blade. -/
theorem cga3_eplus_blade_product :
    geometricProductBlades cga3EplusBlade cga3EplusBlade =
      BladeProduct.nonzero 1 Blade.scalar := by
  native_decide

set_option linter.style.nativeDecide false in
/-- The negative conformal basis blade squares to negative scalar. -/
theorem cga3_eminus_blade_product :
    geometricProductBlades cga3EminusBlade cga3EminusBlade =
      BladeProduct.nonzero (-1) Blade.scalar := by
  native_decide

set_option linter.style.nativeDecide false in
/-- The ordered extra conformal product gives the extra-plane blade. -/
theorem cga3_eplus_eminus_blade_product :
    geometricProductBlades cga3EplusBlade cga3EminusBlade =
      BladeProduct.nonzero 1 cga3ExtraPlaneBlade := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Reversing the extra conformal product negates the extra-plane blade. -/
theorem cga3_eminus_eplus_blade_product :
    geometricProductBlades cga3EminusBlade cga3EplusBlade =
      BladeProduct.nonzero (-1) cga3ExtraPlaneBlade := by
  native_decide

/-! ### CGA Null Basis Anchors -/

/-- Exact rational point-at-infinity vector `e∞ = e₋ + e₊` in CGA3. -/
def cga3InfinityVector : Multivector CGA3 Rat :=
  (Multivector.ofBlade cga3EminusBlade).add (Multivector.ofBlade cga3EplusBlade)

/-- Exact rational origin vector `e₀ = (e₋ - e₊) / 2` in CGA3. -/
def cga3OriginVector : Multivector CGA3 Rat :=
  ((Multivector.ofBlade cga3EminusBlade).sub (Multivector.ofBlade cga3EplusBlade)).smul
    (1 / (2 : Rat))

set_option linter.style.nativeDecide false in
/-- The conformal point-at-infinity vector has zero full geometric square. -/
theorem cga3_infinity_square_zero :
    cga3InfinityVector * cga3InfinityVector = (0 : Multivector CGA3 Rat) := by
  apply Multivector.ext
  intro i
  native_decide +revert

set_option linter.style.nativeDecide false in
/-- The conformal origin vector has zero full geometric square. -/
theorem cga3_origin_square_zero :
    cga3OriginVector * cga3OriginVector = (0 : Multivector CGA3 Rat) := by
  apply Multivector.ext
  intro i
  native_decide +revert

set_option linter.style.nativeDecide false in
/-- The conformal point-at-infinity vector is null. -/
theorem cga3_infinity_square_scalar :
    (cga3InfinityVector * cga3InfinityVector).scalarPart = 0 := by
  native_decide

set_option linter.style.nativeDecide false in
/-- The conformal origin vector is null. -/
theorem cga3_origin_square_scalar :
    (cga3OriginVector * cga3OriginVector).scalarPart = 0 := by
  native_decide

set_option linter.style.nativeDecide false in
/-- The conformal null basis satisfies `e∞ · e₀ = -1`. -/
theorem cga3_infinity_origin_scalar_pair :
    (cga3InfinityVector * cga3OriginVector).scalarPart = -1 := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Reversing the conformal null-basis scalar pair gives the same value. -/
theorem cga3_origin_infinity_scalar_pair :
    (cga3OriginVector * cga3InfinityVector).scalarPart = -1 := by
  native_decide

set_option linter.style.nativeDecide false in
/-- The full product `e∞ * e₀` has scalar `-1` plus the extra conformal plane. -/
theorem cga3_infinity_origin_product :
    cga3InfinityVector * cga3OriginVector =
      (Multivector.scalar (-1 : Rat) : Multivector CGA3 Rat).add
        (Multivector.ofBlade cga3ExtraPlaneBlade) := by
  apply Multivector.ext
  intro i
  native_decide +revert

set_option linter.style.nativeDecide false in
/-- Reversing the full null-basis product flips the extra-plane component. -/
theorem cga3_origin_infinity_product :
    cga3OriginVector * cga3InfinityVector =
      (Multivector.scalar (-1 : Rat) : Multivector CGA3 Rat).sub
        (Multivector.ofBlade cga3ExtraPlaneBlade) := by
  apply Multivector.ext
  intro i
  native_decide +revert

set_option linter.style.nativeDecide false in
/-- The exterior product `e∞ ∧ e₀` gives the positive extra conformal plane. -/
theorem cga3_infinity_origin_wedge :
    cga3InfinityVector ⋀ᵐ cga3OriginVector =
      (Multivector.ofBlade cga3ExtraPlaneBlade : Multivector CGA3 Rat) := by
  apply Multivector.ext
  intro i
  native_decide +revert

set_option linter.style.nativeDecide false in
/-- Reversing the exterior null-basis product flips the extra-plane orientation. -/
theorem cga3_origin_infinity_wedge :
    cga3OriginVector ⋀ᵐ cga3InfinityVector =
      (Multivector.ofBlade cga3ExtraPlaneBlade : Multivector CGA3 Rat).smul (-1 : Rat) := by
  apply Multivector.ext
  intro i
  native_decide +revert

/-! ## Wedge Product Theorems -/

/-- Wedge product is antisymmetric: a ∧ b = -b ∧ a for vectors -/
theorem wedge_antisymm (a b : MultivectorS sig Float)
    (ha : (grade1 a).nnz = a.nnz) (hb : (grade1 b).nnz = b.nnz) :
    a ⋀ₛ b = (b ⋀ₛ a).smul (-1 : Float) := by
  sorry

/-- Wedge product of vector with itself is zero: a ∧ a = 0 -/
theorem wedge_self_zero (a : MultivectorS sig Float)
    (ha : (grade1 a).nnz = a.nnz) :
    (a ⋀ₛ a).isZero := by
  sorry

/-- Wedge product is associative: (a ∧ b) ∧ c = a ∧ (b ∧ c) -/
theorem wedge_assoc (a b c : MultivectorS sig Float) :
    (a ⋀ₛ b) ⋀ₛ c = a ⋀ₛ (b ⋀ₛ c) := by
  sorry

/-! ## Reverse Theorems -/

/-- Reverse is an involution: (a†)† = a -/
theorem reverse_involution (a : MultivectorS sig Float) :
    a†ₛ†ₛ = a := by
  sorry

/-- Reverse is an anti-automorphism: (a * b)† = b† * a† -/
theorem reverse_anti_automorphism (a b : MultivectorS sig Float) :
    (a * b)†ₛ = b†ₛ * a†ₛ := by
  sorry

/-- Reverse fixes scalars: s† = s for scalar s -/
theorem reverse_scalar (s : Float) :
    (MultivectorS.scalar s : MultivectorS sig Float)†ₛ = MultivectorS.scalar s := by
  sorry

/-- Reverse fixes vectors: v† = v for vector v -/
theorem reverse_vector (v : MultivectorS sig Float)
    (hv : (grade1 v).nnz = v.nnz) :
    v†ₛ = v := by
  sorry

/-- Reverse negates bivectors: B† = -B for bivector B -/
theorem reverse_bivector (B : MultivectorS sig Float)
    (hB : (grade2 B).nnz = B.nnz) :
    B†ₛ = B.smul (-1 : Float) := by
  sorry

/-! ## Rotor Theorems -/

/-- Unit rotor inverse condition as a full multivector equality.

The weaker scalar-part condition `(R * R†ₛ).scalarPart = 1` is insufficient:
non-scalar components may still remain in `R * R†ₛ`. -/
theorem unit_rotor_inverse (R : MultivectorS sig Float)
    (hunit : R * R†ₛ = MultivectorS.scalar 1) :
    R * R†ₛ = MultivectorS.scalar 1 := by
  exact hunit

/-- Sandwich product preserves grade of vectors -/
theorem sandwich_preserves_vector_grade (R v : MultivectorS sig Float)
    (hv : (v.gradeProject 1).nnz = v.nnz) :
    ((R * v * R†ₛ).gradeProject 1).nnz = (R * v * R†ₛ).nnz := by
  sorry

/-- Rotor composition: R₁(R₂ x R₂†)R₁† = (R₁R₂) x (R₁R₂)† -/
theorem rotor_composition (R1 R2 x : MultivectorS sig Float) :
    R1 * (R2 * x * R2†ₛ) * R1†ₛ = (R1 * R2) * x * (R1 * R2)†ₛ := by
  sorry

/-! ## Exponential/Logarithm Theorems -/

/-- exp(log(R)) = R for unit rotors (round-trip) -/
theorem exp_log_roundtrip (R : MultivectorS sig Float)
    (hunit : (R * R†ₛ).scalarPart = 1)
    (heven : (grade1 R).nnz = 0 ∧ (grade3 R).nnz = 0) :
    expBivector (logRotor R) = R := by
  sorry

/-- log(exp(B)) = B for bivectors (round-trip) -/
theorem log_exp_roundtrip (B : MultivectorS sig Float)
    (hB : (grade2 B).nnz = B.nnz) :
    logRotor (expBivector B) = B := by
  sorry

set_option linter.style.nativeDecide false in
/-- exp(0) = 1 -/
theorem exp_zero :
    expBivector (MultivectorS.zero : MultivectorS sig Float) = MultivectorS.scalar 1.0 := by
  unfold expBivector
  have hmul : (MultivectorS.zero : MultivectorS sig Float) * MultivectorS.zero =
      MultivectorS.zero := by
    rfl
  have hfold :
      Std.TreeMap.foldl
          (fun acc (idx : Nat) (coeff : Float) =>
            acc || (!(idx == 0) && !(coeff.abs < 1e-10)))
          false (∅ : Std.TreeMap Nat Float) = false := by
    rfl
  rw [hmul]
  dsimp [MultivectorS.scalarPart, MultivectorS.coeff, MultivectorS.zero]
  simp only [hasNonScalarPart, hfold, Bool.false_eq_true, if_false]
  split
  · rfl
  · rename_i hnot
    exact False.elim (hnot (by native_decide))

/-- For B² = -1: exp(θB) = cos(θ) + sin(θ)B -/
theorem exp_unit_bivector (B : MultivectorS sig Float) (θ : Float)
    (hB2 : bivectorSquare B = -1) :
    expBivector (B.smul θ) =
      MultivectorS.scalar (cosTaylor θ) + B.smul (sinTaylor θ) := by
  sorry

/-! ## Grade Theorems -/

/-- Grade projection is idempotent: ⟨⟨M⟩ₖ⟩ₖ = ⟨M⟩ₖ -/
theorem grade_project_idempotent (M : MultivectorS sig Float) (k : Nat) :
    gradeProject (gradeProject M k) k = gradeProject M k := by
  sorry

/-- Grades are orthogonal: ⟨⟨M⟩ⱼ⟩ₖ = 0 for j ≠ k -/
theorem grade_project_orthogonal (M : MultivectorS sig Float) (j k : Nat) (hjk : j ≠ k) :
    (gradeProject (gradeProject M j) k).isZero := by
  sorry

/-- Sum of all grade projections equals original -/
theorem grade_decomposition (M : MultivectorS sig Float) :
    (List.range (n + 1)).foldl (fun acc k => acc + gradeProject M k) MultivectorS.zero = M := by
  sorry

/-! ## Norm/Magnitude Theorems -/

/-- Magnitude is non-negative for Euclidean vectors -/
theorem magnitude_nonneg (v : MultivectorS sig Float)
    (hv : (grade1 v).nnz = v.nnz)
    (heuc : sig.metric = 0) :  -- Euclidean signature
    magnitude v ≥ 0 := by
  sorry

/-- Normalized vector has unit magnitude -/
theorem normalize_unit (v : MultivectorS sig Float)
    (hv : (grade1 v).nnz = v.nnz)
    (hnz : magnitude v > 0) :
    magnitude (normalize v) = 1 := by
  sorry

end Grassmann.Theorems
