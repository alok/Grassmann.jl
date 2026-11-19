/-
Formal kernel-verified proofs for Projective (`PGA2`, `PGA3`), Conformal (`CGA2`, `CGA3`),
`GanjaCompat` duality, and exact rational `ℝ3` rotors.

Credits:
- Michael Reed (`chakravala` / `Grassmann.jl`): core Clifford/Grassmann algebra architecture.
- Steven De Keninck (`enkimute` / `ganja.js`): metric-free PGA duality, Study motors, CGA null model.

Every theorem in this module has ZERO `sorry`, ZERO custom `axiom`, and ZERO `native_decide`,
and is audited by `#print axioms` in `Tests/Proofs/Axioms.lean`.

## Headline Theorems

1. **Metric-free Poincaré duality involution (`!!x = ±x`)**:
   - `poincare_invol_PGA2`: `!!x = x` for every homogeneous `k`-vector in `PGA2` (`n = 3`).
   - `poincare_invol_PGA3`: `!!x = (-1)^{k(4-k)} x` in `PGA3` (`n = 4`; `+x` for even, `-x` for odd).
2. **`GanjaCompat` degenerate `PGA3` `!e0 = e123 ≠ 0` vs Hodge `⋆e0 = 0`**:
   - `pga3_poincare_e0_eq_e123`, `pga3_poincare_e0_ne_zero`, `pga3_hodge_e0_eq_zero` (spec & `implUnary`).
   - `ganjaCompat_pga3_dualChain_e0_ne_zero`, `ganjaCompat_pga3_undual_dual_e0`,
     `ganjaCompat_pga3_hodge_e0_eq_zero` (executable `GanjaCompat` + generated `PGA3` kernels over `Rat`).
3. **`PGA3` Study invariant & reverse norm invariance**:
   - `pga3_motor_mul_reverse`: exact polynomial identity `M * ~M = normSq(M) + 2·study(M)·e0123`
     for all 8 rational coefficients `(s, b01, b02, b03, b12, b13, b23, p)`.
   - `pga3_motor_reverse_norm_inv`: `(~M) * M = M * (~M)` (reverse norm & Study invariance).
   - `pga3_study_quadric_iff`: `M * ~M = 1 ↔ normSq(M) = 1 ∧ study(M) = 0`.
   - `pga3_unit_motor_mul_closed`: closure of unit Study motors under geometric composition.
   - `pga3_impl_motor_mul_reverse`: transported to the executable `implMul PGA3` blade algebra.
4. **`CGA` null-point identity (`P * P = 0`, `P · P = 0`) & Euclidean distance inner product**:
   - `cga3_point_mul_self` & `cga3_point_dot_self`: `P(x, y, z)² = 0` in `CGA3` (`S!"∞∅+++"`)
     for all rational `(x, y, z)`.
   - `cga3_point_distance_sq`: `P(x₁, y₁, z₁) * P(x₂, y₂, z₂) + P(x₂, y₂, z₂) * P(x₁, y₁, z₁)`
     has scalar part `-((x₁ - x₂)² + (y₁ - y₂)² + (z₁ - z₂)²)`.
   - `cga2_point_mul_self` & `cga2_point_dot_self`: `P(x, y)² = 0` in `CGA2` (`S!"∞∅++"`).
5. **`ℝ3` exact rational rotor unit norm & Euclidean isometry**:
   - `r3_rotor_mul_reverse`: `R * ~R = (s² + b12² + b13² + b23²) · 1` for all rational spinors.
   - `r3_unit_rotor_preserves_norm_sq`: `(R * v * ~R)² = v²` for all unit rational rotors `R`
     and all vectors `v ∈ ℝ³`.
   - `r3_concrete_rational_rotor_unit`: exact unit norm `R * ~R = 1` for the executable
     `Grassmann.Kernel.R3Rotor.rotor` (`3/5 + 4/5·e12`).
-/
import Grassmann.Proofs.Complements
import Grassmann.Proofs.Conformal
import Grassmann.Tactic
import Grassmann.GanjaCompat
import Grassmann.Kernel.Generated.PGA3
import Grassmann.Kernel.R3RotorLaws

namespace Grassmann.Proofs.ProjectiveConformal

open DirectSum DirectSum.Proofs StaticVectors Grassmann Grassmann.Spec
open Grassmann.Proofs Grassmann.GanjaCompat Lean.Grind

/-! ## 1. Metric-Free Poincaré Duality Involution & Degenerate `PGA3` vs Hodge `⋆` -/

/-- `PGA2 = D!"0,1,1"` is a plain diagonal space. -/
theorem pga2_isPlain : IsPlainSpace PGA2 := ⟨rfl, rfl, rfl, rfl⟩

/-- `PGA3 = D!"0,1,1,1"` is a plain diagonal space. -/
theorem pga3_isPlain : IsPlainSpace PGA3 := ⟨rfl, rfl, rfl, rfl⟩

/-- **Poincaré duality involution in `PGA2`**: for every homogeneous `k`-vector `x`,
`!!x = x` (since `k(3 - k)` is always even). -/
theorem poincare_invol_PGA2 {k : Nat} {x : Cl (gPGA 3)} (hx : Cl.IsGrade k x) :
    implUnary PGA2 .complementright (implUnary PGA2 .complementright x) = x := by
  rw [implCompl_implCompl pga2_isPlain (n := 3) rfl (by decide) hx]
  have hpow : (-1 : Rat) ^ (k * (3 - k)) = 1 := by
    by_cases hk : k ≤ 3
    · have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl <;> decide
    · have h3 : 3 - k = 0 := by omega
      rw [h3, Nat.mul_zero]; decide
  rw [hpow]
  ext c
  show (1 : Rat) * x.coeff c = x.coeff c
  grind

/-- **Poincaré duality involution in `PGA3`**: for every homogeneous `k`-vector `x`,
`!!x = (-1)^{k(4 - k)} x` (`+x` for even grades, `-x` for odd grades). -/
theorem poincare_invol_PGA3 {k : Nat} {x : Cl (gPGA 4)} (hx : Cl.IsGrade k x) :
    implUnary PGA3 .complementright (implUnary PGA3 .complementright x)
      = (-1 : Rat) ^ (k * (4 - k)) • x :=
  implCompl_implCompl pga3_isPlain (n := 4) rfl (by decide) hx

/-- In `PGA3`, `implUnary PGA3 .complementrighthodge` agrees with the spec Hodge star `Cl.hodge`
for the degenerate metric `gPGA 4 = (0, 1, 1, 1)`. -/
theorem pga3_hodge_eq (x : Cl (gPGA 4)) :
    implUnary PGA3 .complementrighthodge x = Cl.hodge x :=
  implHodge_eq_hodge pga3_isPlain (n := 4) rfl (by decide) rfl
    (fun i h => by
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hi with rfl | rfl | rfl | rfl
      · change PGA3.metricAt 1 = gPGA 4 ⟨0, by decide⟩; decide +kernel
      · change PGA3.metricAt 2 = gPGA 4 ⟨1, by decide⟩; decide +kernel
      · change PGA3.metricAt 3 = gPGA 4 ⟨2, by decide⟩; decide +kernel
      · change PGA3.metricAt 4 = gPGA 4 ⟨3, by decide⟩; decide +kernel) x

/-- Generator `e0` (mask `0001 = 1#4`) in `PGA3`. -/
abbrev pga3E0 : Cl (gPGA 4) := Cl.gen 0

/-- Pseudoscalar of the Euclidean subalgebra `e123` (mask `1110 = 14#4`) in `PGA3`. -/
abbrev pga3E123 : Cl (gPGA 4) := Cl.blade (14 : BitVec 4)

/-- **Degenerate `PGA3` metric-free Poincaré dual preserves `e0`**: `!e0 = e123` (non-zero!). -/
theorem pga3_poincare_e0_eq_e123 :
    implUnary PGA3 .complementright pga3E0 = pga3E123 := by
  rw [implCompl_eq_compl pga3_isPlain (n := 4) rfl (by decide)]
  change Cl.compl (Cl.blade (1 : BitVec 4) : Cl (gPGA 4)) = Cl.blade (14 : BitVec 4)
  rw [Cl.compl_blade]
  have hs : (signOf (sign (1 : BitVec 4) (~~~(1 : BitVec 4))) : Rat) = 1 := by decide +kernel
  have hn : ~~~(1 : BitVec 4) = (14 : BitVec 4) := by decide +kernel
  rw [hs, hn]
  ext c
  show (1 : Rat) * (Cl.blade (14 : BitVec 4) : Cl (gPGA 4)).coeff c = _
  grind

/-- **Degenerate `PGA3` metric-free Poincaré dual `!e0 ≠ 0`**. -/
theorem pga3_poincare_e0_ne_zero :
    implUnary PGA3 .complementright pga3E0 ≠ 0 := by
  rw [pga3_poincare_e0_eq_e123]
  intro h
  have h14 := congrArg (fun m : Cl (gPGA 4) => m.coeff (14 : BitVec 4)) h
  have hne : pga3E123.coeff (14 : BitVec 4) ≠ (0 : Cl (gPGA 4)).coeff (14 : BitVec 4) := by
    decide +kernel
  exact hne h14

/-- **Degenerate `PGA3` metric Hodge star annihilates `e0`**: `⋆e0 = 0` (because `e0² = 0`). -/
theorem pga3_hodge_e0_eq_zero :
    implUnary PGA3 .complementrighthodge pga3E0 = 0 := by
  rw [pga3_hodge_eq]
  change Cl.hodge (Cl.blade (1 : BitVec 4) : Cl (gPGA 4)) = 0
  rw [Cl.hodge_blade]
  have hm : (signOf (sign (1 : BitVec 4) (~~~(1 : BitVec 4))) * mf (gPGA 4) (1 : BitVec 4) : Rat) = 0 := by
    decide +kernel
  rw [hm]
  ext c
  show (0 : Rat) * (Cl.blade (~~~(1 : BitVec 4)) : Cl (gPGA 4)).coeff c = 0
  grind

/-- Executable `PGA3` unit plane `e0` over `Rat` (`[1, 0, 0, 0]`). -/
def execPga3E0 : Chain PGA3 1 Rat :=
  ⟨Values.ofFn fun i => if i.1 == 0 then 1 else 0⟩

/-- **Executable `GanjaCompat.dualChain` on degenerate `PGA3` `e0`**: `!e0 = e123` (slot 3 = `1 ≠ 0`). -/
theorem ganjaCompat_pga3_dualChain_e0_ne_zero :
    (GanjaCompat.dualChain execPga3E0).v.get ⟨3, by decide⟩ = (1 : Rat) ∧
    (GanjaCompat.dualChain execPga3E0).v.get ⟨3, by decide⟩ ≠ (0 : Rat) := by
  constructor <;> decide +kernel

/-- **Executable `GanjaCompat` undual-of-dual round-trip on `PGA3` `e0`**: `undualChain (dualChain e0) = e0`. -/
theorem ganjaCompat_pga3_undual_dual_e0 :
    GanjaCompat.undualChain (GanjaCompat.dualChain execPga3E0) = execPga3E0 := by
  apply congrArg Chain.mk
  apply Values.ext
  intro ⟨i, hi⟩
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
    have hlt : i < 4 := hi
    omega
  rcases h with rfl | rfl | rfl | rfl
  · change (GanjaCompat.undualChain (GanjaCompat.dualChain execPga3E0)).v.get ⟨0, by decide⟩ = 1
    decide +kernel
  · change (GanjaCompat.undualChain (GanjaCompat.dualChain execPga3E0)).v.get ⟨1, by decide⟩ = 0
    decide +kernel
  · change (GanjaCompat.undualChain (GanjaCompat.dualChain execPga3E0)).v.get ⟨2, by decide⟩ = 0
    decide +kernel
  · change (GanjaCompat.undualChain (GanjaCompat.dualChain execPga3E0)).v.get ⟨3, by decide⟩ = 0
    decide +kernel

/-- **Executable Hodge star on `PGA3` `e0` vanishes**: `e0.hodge = 0`. -/
theorem ganjaCompat_pga3_hodge_e0_eq_zero :
    (execPga3E0.hodge).v.get ⟨3, by decide⟩ = (0 : Rat) := by
  decide +kernel

/-! ## 2. `PGA3` Study Invariant & Reverse Norm Invariance -/

/-- General even `PGA3` motor `M` in exact `ganja.js` / `GSIR` wire order
`[s, e01, e02, e03, e12, e13, e23, e0123]`. -/
abbrev pga3Motor (s b01 b02 b03 b12 b13 b23 p : Rat) : Cl (gPGA 4) :=
  Cl.scalar s
    + b01 • (Cl.gen 0 * Cl.gen 1)
    + b02 • (Cl.gen 0 * Cl.gen 2)
    + b03 • (Cl.gen 0 * Cl.gen 3)
    + b12 • (Cl.gen 1 * Cl.gen 2)
    + b13 • (Cl.gen 1 * Cl.gen 3)
    + b23 • (Cl.gen 2 * Cl.gen 3)
    + p • Cl.pseudoscalar

/-- Squared Euclidean rotor norm `s² + b12² + b13² + b23²` of a `PGA3` motor. -/
abbrev pga3NormSq (s b12 b13 b23 : Rat) : Rat :=
  s ^ 2 + b12 ^ 2 + b13 ^ 2 + b23 ^ 2

/-- Study invariant `s·p - b01·b23 + b02·b13 - b03·b12` of a `PGA3` motor. -/
abbrev pga3Study (s b01 b02 b03 b12 b13 b23 p : Rat) : Rat :=
  s * p - b01 * b23 + b02 * b13 - b03 * b12

/-- **`PGA3` Study dual-number identity**: for EVERY rational even motor `M`,
`M * ~M = (s² + b12² + b13² + b23²) + 2·(s·p - b01·b23 + b02·b13 - b03·b12)·e0123`
(all 6 bivector and 8 odd components vanish identically). -/
theorem pga3_motor_mul_reverse (s b01 b02 b03 b12 b13 b23 p : Rat) :
    let M := pga3Motor s b01 b02 b03 b12 b13 b23 p
    M * Cl.reverse M =
      Cl.scalar (pga3NormSq s b12 b13 b23)
        + (2 * pga3Study s b01 b02 b03 b12 b13 b23 p) • Cl.pseudoscalar := by
  clifford [gPGA]

/-- **`PGA3` reverse norm invariance**: `(~M) * M = M * (~M)` for every even motor `M`,
so reversing a motor leaves both `normSq` and the Study invariant unchanged. -/
theorem pga3_motor_reverse_norm_inv (s b01 b02 b03 b12 b13 b23 p : Rat) :
    let M := pga3Motor s b01 b02 b03 b12 b13 b23 p
    Cl.reverse M * M = M * Cl.reverse M := by
  clifford [gPGA]

/-- **Exact Study quadric characterization**: a `PGA3` motor satisfies `M * ~M = 1`
if and only if `normSq(M) = 1` and `study(M) = 0`. -/
theorem pga3_study_quadric_iff (s b01 b02 b03 b12 b13 b23 p : Rat) :
    let M := pga3Motor s b01 b02 b03 b12 b13 b23 p
    M * Cl.reverse M = 1 ↔
      pga3NormSq s b12 b13 b23 = 1 ∧ pga3Study s b01 b02 b03 b12 b13 b23 p = 0 := by
  dsimp only
  rw [pga3_motor_mul_reverse]
  constructor
  · intro h
    have h0 := congrArg (fun m : Cl (gPGA 4) => m.coeff (0 : BitVec 4)) h
    have h15 := congrArg (fun m : Cl (gPGA 4) => m.coeff (15 : BitVec 4)) h
    have c0 : (Cl.scalar (pga3NormSq s b12 b13 b23) +
        (2 * pga3Study s b01 b02 b03 b12 b13 b23 p) • (Cl.pseudoscalar : Cl (gPGA 4))).coeff (0 : BitVec 4)
        = pga3NormSq s b12 b13 b23 := by
      show (if (0 : BitVec 4) = 0 then pga3NormSq s b12 b13 b23 else 0) +
        (2 * pga3Study s b01 b02 b03 b12 b13 b23 p) * (if (0 : BitVec 4) = BitVec.allOnes 4 then 1 else 0) = _
      simp; grind
    have c15 : (Cl.scalar (pga3NormSq s b12 b13 b23) +
        (2 * pga3Study s b01 b02 b03 b12 b13 b23 p) • (Cl.pseudoscalar : Cl (gPGA 4))).coeff (15 : BitVec 4)
        = 2 * pga3Study s b01 b02 b03 b12 b13 b23 p := by
      show (if (15 : BitVec 4) = 0 then pga3NormSq s b12 b13 b23 else 0) +
        (2 * pga3Study s b01 b02 b03 b12 b13 b23 p) * (if (15 : BitVec 4) = BitVec.allOnes 4 then 1 else 0) = _
      simp; grind
    have one0 : (1 : Cl (gPGA 4)).coeff (0 : BitVec 4) = 1 := by decide +kernel
    have one15 : (1 : Cl (gPGA 4)).coeff (15 : BitVec 4) = 0 := by decide +kernel
    rw [c0, one0] at h0
    rw [c15, one15] at h15
    exact ⟨h0, by grind⟩
  · rintro ⟨hn, hs⟩
    rw [hn, hs]
    clifford

/-- **Unit Study motors are closed under geometric composition**:
if `M₁ * ~M₁ = 1` and `M₂ * ~M₂ = 1` in `PGA3`, then `(M₁ * M₂) * ~(M₁ * M₂) = 1`. -/
theorem pga3_unit_motor_mul_closed {M₁ M₂ : Cl (gPGA 4)}
    (h1 : M₁ * Cl.reverse M₁ = 1) (h2 : M₂ * Cl.reverse M₂ = 1) :
    (M₁ * M₂) * Cl.reverse (M₁ * M₂) = 1 := by
  rw [Cl.reverse_mul, Cl.mul_assoc, ← Cl.mul_assoc M₂, h2, Cl.one_mul, h1]

/-- **Implementation transport**: DirectSum's `implMul PGA3` satisfies the exact Study
dual-number identity on every rational even motor. -/
theorem pga3_impl_motor_mul_reverse (s b01 b02 b03 b12 b13 b23 p : Rat) :
    let M := pga3Motor s b01 b02 b03 b12 b13 b23 p
    implMul PGA3 M (Cl.reverse M) =
      Cl.scalar (pga3NormSq s b12 b13 b23)
        + (2 * pga3Study s b01 b02 b03 b12 b13 b23 p) • Cl.pseudoscalar := by
  dsimp only
  rw [PGA3_mul]
  exact pga3_motor_mul_reverse s b01 b02 b03 b12 b13 b23 p

/-! ## 3. `CGA` Null-Point Identity (`P · P = 0`) & Euclidean Distance Inner Product -/

/-- Exact conformal embedding `P(x, y, z) = ½(x²+y²+z²)∞ + ∅ + x e₁ + y e₂ + z e₃`
in `CGA3 = S!"∞∅+++"` (null basis: bit 0 = `∞`, bit 1 = `∅`, bits 2..4 = `e₁..e₃`). -/
abbrev cga3Point (x y z : Rat) : Cl (gConf 5) :=
  ((x ^ 2 + y ^ 2 + z ^ 2) / 2) • Cl.gen 0
    + Cl.gen 1
    + x • Cl.gen 2
    + y • Cl.gen 3
    + z • Cl.gen 4

/-- Exact diagonal-basis image `T(P(x, y, z))` in `Cl(4, 1)` (`e₊² = 1`, `e₋² = -1`). -/
abbrev cga3PointDiag (x y z : Rat) : Cl (gConf 5) :=
  ((x ^ 2 + y ^ 2 + z ^ 2 - 1) / 2) • Cl.gen 0
    + ((x ^ 2 + y ^ 2 + z ^ 2 + 1) / 2) • Cl.gen 1
    + x • Cl.gen 2
    + y • Cl.gen 3
    + z • Cl.gen 4

private theorem toDiag_add {n : Nat} {g : Fin n → Rat} (x y : Cl g) :
    toDiag (x + y) = toDiag x + toDiag y := by
  ext c
  show (bsum n fun a => (x.coeff a + y.coeff a) * sfun (toDiagBlade a) c) =
    (bsum n fun a => x.coeff a * sfun (toDiagBlade a) c) +
    (bsum n fun a => y.coeff a * sfun (toDiagBlade a) c)
  rw [← bsum_add]
  exact bsum_congr fun a => by grind

private theorem toDiag_smul {n : Nat} {g : Fin n → Rat} (r : Rat) (x : Cl g) :
    toDiag (r • x) = r • toDiag x := by
  ext c
  show (bsum n fun a => (r * x.coeff a) * sfun (toDiagBlade a) c) =
    r * (bsum n fun a => x.coeff a * sfun (toDiagBlade a) c)
  rw [mul_bsum]
  exact bsum_congr fun a => by grind

private theorem toDiag_blade {n : Nat} {g : Fin n → Rat} (a : BitVec n) :
    (toDiag (Cl.blade a : Cl g)).coeff = sfun (toDiagBlade a) := by
  show lmap toDiagBlade (delta a) = sfun (toDiagBlade a)
  exact lmap_delta toDiagBlade a

private theorem toDiag_cga3_gen0 : toDiag (Cl.gen 0 : Cl (gConf 5)) = Cl.gen 0 + Cl.gen 1 := by
  ext c
  have h : (toDiag (Cl.blade (1 : BitVec 5) : Cl (gConf 5))).coeff c = sfun (toDiagBlade (1 : BitVec 5)) c :=
    congrFun (toDiag_blade (1 : BitVec 5)) c
  have hb : toDiagBlade (1 : BitVec 5) = [(1, 1), (2, 1)] := by decide +kernel
  change (toDiag (Cl.blade (1 : BitVec 5) : Cl (gConf 5))).coeff c =
    (Cl.blade (1 : BitVec 5) : Cl (gConf 5)).coeff c + (Cl.blade (2 : BitVec 5) : Cl (gConf 5)).coeff c
  rw [h, hb]
  show 1 * delta 1 c + (1 * delta 2 c + 0) = delta 1 c + delta 2 c
  grind

private theorem toDiag_cga3_gen1 :
    toDiag (Cl.gen 1 : Cl (gConf 5)) = (-1 / 2 : Rat) • Cl.gen 0 + (1 / 2 : Rat) • Cl.gen 1 := by
  ext c
  have h : (toDiag (Cl.blade (2 : BitVec 5) : Cl (gConf 5))).coeff c = sfun (toDiagBlade (2 : BitVec 5)) c :=
    congrFun (toDiag_blade (2 : BitVec 5)) c
  have hb : toDiagBlade (2 : BitVec 5) = [(1, -1/2), (2, 1/2)] := by decide +kernel
  change (toDiag (Cl.blade (2 : BitVec 5) : Cl (gConf 5))).coeff c =
    (-1 / 2 : Rat) * (Cl.blade (1 : BitVec 5) : Cl (gConf 5)).coeff c +
    (1 / 2 : Rat) * (Cl.blade (2 : BitVec 5) : Cl (gConf 5)).coeff c
  rw [h, hb]
  show (-1 / 2) * delta 1 c + ((1 / 2) * delta 2 c + 0) = (-1 / 2) * delta 1 c + (1 / 2) * delta 2 c
  grind

private theorem toDiag_cga3_gen2 : toDiag (Cl.gen 2 : Cl (gConf 5)) = Cl.gen 2 := by
  ext c
  have h : (toDiag (Cl.blade (4 : BitVec 5) : Cl (gConf 5))).coeff c = sfun (toDiagBlade (4 : BitVec 5)) c :=
    congrFun (toDiag_blade (4 : BitVec 5)) c
  have hb : toDiagBlade (4 : BitVec 5) = [(4, 1)] := by decide +kernel
  change (toDiag (Cl.blade (4 : BitVec 5) : Cl (gConf 5))).coeff c =
    (Cl.blade (4 : BitVec 5) : Cl (gConf 5)).coeff c
  rw [h, hb]
  show 1 * delta 4 c + 0 = delta 4 c
  grind

private theorem toDiag_cga3_gen3 : toDiag (Cl.gen 3 : Cl (gConf 5)) = Cl.gen 3 := by
  ext c
  have h : (toDiag (Cl.blade (8 : BitVec 5) : Cl (gConf 5))).coeff c = sfun (toDiagBlade (8 : BitVec 5)) c :=
    congrFun (toDiag_blade (8 : BitVec 5)) c
  have hb : toDiagBlade (8 : BitVec 5) = [(8, 1)] := by decide +kernel
  change (toDiag (Cl.blade (8 : BitVec 5) : Cl (gConf 5))).coeff c =
    (Cl.blade (8 : BitVec 5) : Cl (gConf 5)).coeff c
  rw [h, hb]
  show 1 * delta 8 c + 0 = delta 8 c
  grind

private theorem toDiag_cga3_gen4 : toDiag (Cl.gen 4 : Cl (gConf 5)) = Cl.gen 4 := by
  ext c
  have h : (toDiag (Cl.blade (16 : BitVec 5) : Cl (gConf 5))).coeff c = sfun (toDiagBlade (16 : BitVec 5)) c :=
    congrFun (toDiag_blade (16 : BitVec 5)) c
  have hb : toDiagBlade (16 : BitVec 5) = [(16, 1)] := by decide +kernel
  change (toDiag (Cl.blade (16 : BitVec 5) : Cl (gConf 5))).coeff c =
    (Cl.blade (16 : BitVec 5) : Cl (gConf 5)).coeff c
  rw [h, hb]
  show 1 * delta 16 c + 0 = delta 16 c
  grind

private theorem toDiag_cga3Point (x y z : Rat) :
    toDiag (cga3Point x y z) = cga3PointDiag x y z := by
  simp only [cga3Point, toDiag_add, toDiag_smul,
    toDiag_cga3_gen0, toDiag_cga3_gen1, toDiag_cga3_gen2, toDiag_cga3_gen3, toDiag_cga3_gen4]
  ext c
  show ((x ^ 2 + y ^ 2 + z ^ 2) / 2 * ((Cl.gen 0 : Cl (gConf 5)).coeff c + (Cl.gen 1 : Cl (gConf 5)).coeff c)
        + ((-1 / 2 : Rat) * (Cl.gen 0 : Cl (gConf 5)).coeff c + (1 / 2 : Rat) * (Cl.gen 1 : Cl (gConf 5)).coeff c))
        + x * (Cl.gen 2 : Cl (gConf 5)).coeff c
        + y * (Cl.gen 3 : Cl (gConf 5)).coeff c
        + z * (Cl.gen 4 : Cl (gConf 5)).coeff c
      = ((x ^ 2 + y ^ 2 + z ^ 2 - 1) / 2 * (Cl.gen 0 : Cl (gConf 5)).coeff c
        + (x ^ 2 + y ^ 2 + z ^ 2 + 1) / 2 * (Cl.gen 1 : Cl (gConf 5)).coeff c)
        + x * (Cl.gen 2 : Cl (gConf 5)).coeff c
        + y * (Cl.gen 3 : Cl (gConf 5)).coeff c
        + z * (Cl.gen 4 : Cl (gConf 5)).coeff c
  grind

private theorem cga3_vec_sq (a b x y z : Rat) :
    let v : Cl (gConf 5) := a • Cl.gen 0 + b • Cl.gen 1 + x • Cl.gen 2 + y • Cl.gen 3 + z • Cl.gen 4
    v * v = Cl.scalar (a ^ 2 - b ^ 2 + x ^ 2 + y ^ 2 + z ^ 2) := by
  clifford [gConf]

private theorem cga3PointDiag_mul_self (x y z : Rat) :
    cga3PointDiag x y z * cga3PointDiag x y z = 0 := by
  rw [cga3_vec_sq]
  have hzero : ((x ^ 2 + y ^ 2 + z ^ 2 - 1) / 2) ^ 2 - ((x ^ 2 + y ^ 2 + z ^ 2 + 1) / 2) ^ 2
      + x ^ 2 + y ^ 2 + z ^ 2 = 0 := by grind
  rw [hzero]
  ext c
  show (if c = 0 then (0 : Rat) else 0) = 0
  split <;> rfl

private theorem fromDiag_zero {n : Nat} {g : Fin n → Rat} :
    fromDiag (0 : Cl g) = 0 := by
  ext c
  show (bsum n fun a => (0 : Rat) * sfun (fromDiagBlade a) c) = 0
  rw [bsum_congr (f' := fun _ => (0 : Rat)) (fun _ => by grind), bsum_const_zero]

/-- **Conformal null-point theorem in `CGA3`**: for EVERY rational 3D point `(x, y, z)`,
its conformal embedding `P = ½|x|²∞ + ∅ + x` is strictly null (`P * P = 0` under `implMul CGA3`). -/
theorem cga3_point_mul_self (x y z : Rat) :
    implMul CGA3 (cga3Point x y z) (cga3Point x y z) = 0 := by
  rw [← fromDiag_toDiag conf_inverse_5 (implMul CGA3 (cga3Point x y z) (cga3Point x y z)),
      CGA3_toDiag_mul, toDiag_cga3Point, cga3PointDiag_mul_self, fromDiag_zero]

/-- **Conformal null-point inner product `P · P = 0` in `CGA3`** (scalar part of `P * P`). -/
theorem cga3_point_dot_self (x y z : Rat) :
    (implMul CGA3 (cga3Point x y z) (cga3Point x y z)).coeff (0 : BitVec 5) = 0 := by
  rw [cga3_point_mul_self]; rfl

private theorem cga3_vec_anticomm (a₁ b₁ x₁ y₁ z₁ a₂ b₂ x₂ y₂ z₂ : Rat) :
    let v₁ : Cl (gConf 5) := a₁ • Cl.gen 0 + b₁ • Cl.gen 1 + x₁ • Cl.gen 2 + y₁ • Cl.gen 3 + z₁ • Cl.gen 4
    let v₂ : Cl (gConf 5) := a₂ • Cl.gen 0 + b₂ • Cl.gen 1 + x₂ • Cl.gen 2 + y₂ • Cl.gen 3 + z₂ • Cl.gen 4
    v₁ * v₂ + v₂ * v₁ = Cl.scalar (2 * (a₁ * a₂ - b₁ * b₂ + x₁ * x₂ + y₁ * y₂ + z₁ * z₂)) := by
  clifford [gConf]

private theorem cga3PointDiag_anticomm (x₁ y₁ z₁ x₂ y₂ z₂ : Rat) :
    cga3PointDiag x₁ y₁ z₁ * cga3PointDiag x₂ y₂ z₂ +
      cga3PointDiag x₂ y₂ z₂ * cga3PointDiag x₁ y₁ z₁ =
      Cl.scalar (-((x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2 + (z₁ - z₂) ^ 2)) := by
  rw [cga3_vec_anticomm]
  congr 1
  grind

private theorem fromDiag_scalar {n : Nat} {g : Fin n → Rat} (s : Rat) :
    fromDiag (Cl.scalar s : Cl g) = Cl.scalar s := by
  ext c
  show (bsum n fun a => (if a = 0 then s else 0) * sfun (fromDiagBlade a) c) =
    if c = 0 then s else 0
  have h : ∀ a : BitVec n, (if a = 0 then s else 0) * sfun (fromDiagBlade a) c
      = if a = 0 then s * sfun (fromDiagBlade 0) c else 0 := by
    intro a
    by_cases ha : a = 0
    · subst ha; rw [ite_eq_left rfl, ite_eq_left rfl]
    · rw [ite_eq_right ha, ite_eq_right ha]; grind
  rw [bsum_congr h, bsum_ite_eq]
  have h0 : fromDiagBlade (0 : BitVec n) = [(0, 1)] := by
    unfold fromDiagBlade
    have : (0 : BitVec n).toNat % 4 = 0 := by simp
    rw [this]; rfl
  rw [h0]; simp only [sfun, delta]
  by_cases hc : c = 0
  · subst hc; rw [ite_eq_left rfl, ite_eq_left rfl]; grind
  · rw [ite_eq_right hc, ite_eq_right hc]; grind

/-- **Exact `CGA3` Euclidean distance identity**: for ALL rational 3D points `p₁, p₂`,
`P₁ * P₂ + P₂ * P₁ = -‖p₁ - p₂‖²` (so `P₁ · P₂ = -½‖p₁ - p₂‖²`). -/
theorem cga3_point_distance_sq (x₁ y₁ z₁ x₂ y₂ z₂ : Rat) :
    implMul CGA3 (cga3Point x₁ y₁ z₁) (cga3Point x₂ y₂ z₂) +
      implMul CGA3 (cga3Point x₂ y₂ z₂) (cga3Point x₁ y₁ z₁) =
      Cl.scalar (-((x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2 + (z₁ - z₂) ^ 2)) := by
  rw [← fromDiag_toDiag conf_inverse_5 (implMul CGA3 _ _ + implMul CGA3 _ _),
      toDiag_add, CGA3_toDiag_mul, CGA3_toDiag_mul,
      toDiag_cga3Point, toDiag_cga3Point, cga3PointDiag_anticomm, fromDiag_scalar]

/-- Exact conformal embedding `P(x, y) = ½(x²+y²)∞ + ∅ + x e₁ + y e₂` in `CGA2 = S!"∞∅++"`. -/
abbrev cga2Point (x y : Rat) : Cl (gConf 4) :=
  ((x ^ 2 + y ^ 2) / 2) • Cl.gen 0
    + Cl.gen 1
    + x • Cl.gen 2
    + y • Cl.gen 3

/-- Exact diagonal-basis image `T(P(x, y))` in `Cl(3, 1)`. -/
abbrev cga2PointDiag (x y : Rat) : Cl (gConf 4) :=
  ((x ^ 2 + y ^ 2 - 1) / 2) • Cl.gen 0
    + ((x ^ 2 + y ^ 2 + 1) / 2) • Cl.gen 1
    + x • Cl.gen 2
    + y • Cl.gen 3

private theorem toDiag_cga2_gen0 : toDiag (Cl.gen 0 : Cl (gConf 4)) = Cl.gen 0 + Cl.gen 1 := by
  ext c
  have h : (toDiag (Cl.blade (1 : BitVec 4) : Cl (gConf 4))).coeff c = sfun (toDiagBlade (1 : BitVec 4)) c :=
    congrFun (toDiag_blade (1 : BitVec 4)) c
  have hb : toDiagBlade (1 : BitVec 4) = [(1, 1), (2, 1)] := by decide +kernel
  change (toDiag (Cl.blade (1 : BitVec 4) : Cl (gConf 4))).coeff c =
    (Cl.blade (1 : BitVec 4) : Cl (gConf 4)).coeff c + (Cl.blade (2 : BitVec 4) : Cl (gConf 4)).coeff c
  rw [h, hb]
  show 1 * delta 1 c + (1 * delta 2 c + 0) = delta 1 c + delta 2 c
  grind

private theorem toDiag_cga2_gen1 :
    toDiag (Cl.gen 1 : Cl (gConf 4)) = (-1 / 2 : Rat) • Cl.gen 0 + (1 / 2 : Rat) • Cl.gen 1 := by
  ext c
  have h : (toDiag (Cl.blade (2 : BitVec 4) : Cl (gConf 4))).coeff c = sfun (toDiagBlade (2 : BitVec 4)) c :=
    congrFun (toDiag_blade (2 : BitVec 4)) c
  have hb : toDiagBlade (2 : BitVec 4) = [(1, -1/2), (2, 1/2)] := by decide +kernel
  change (toDiag (Cl.blade (2 : BitVec 4) : Cl (gConf 4))).coeff c =
    (-1 / 2 : Rat) * (Cl.blade (1 : BitVec 4) : Cl (gConf 4)).coeff c +
    (1 / 2 : Rat) * (Cl.blade (2 : BitVec 4) : Cl (gConf 4)).coeff c
  rw [h, hb]
  show (-1 / 2) * delta 1 c + ((1 / 2) * delta 2 c + 0) = (-1 / 2) * delta 1 c + (1 / 2) * delta 2 c
  grind

private theorem toDiag_cga2_gen2 : toDiag (Cl.gen 2 : Cl (gConf 4)) = Cl.gen 2 := by
  ext c
  have h : (toDiag (Cl.blade (4 : BitVec 4) : Cl (gConf 4))).coeff c = sfun (toDiagBlade (4 : BitVec 4)) c :=
    congrFun (toDiag_blade (4 : BitVec 4)) c
  have hb : toDiagBlade (4 : BitVec 4) = [(4, 1)] := by decide +kernel
  change (toDiag (Cl.blade (4 : BitVec 4) : Cl (gConf 4))).coeff c =
    (Cl.blade (4 : BitVec 4) : Cl (gConf 4)).coeff c
  rw [h, hb]
  show 1 * delta 4 c + 0 = delta 4 c
  grind

private theorem toDiag_cga2_gen3 : toDiag (Cl.gen 3 : Cl (gConf 4)) = Cl.gen 3 := by
  ext c
  have h : (toDiag (Cl.blade (8 : BitVec 4) : Cl (gConf 4))).coeff c = sfun (toDiagBlade (8 : BitVec 4)) c :=
    congrFun (toDiag_blade (8 : BitVec 4)) c
  have hb : toDiagBlade (8 : BitVec 4) = [(8, 1)] := by decide +kernel
  change (toDiag (Cl.blade (8 : BitVec 4) : Cl (gConf 4))).coeff c =
    (Cl.blade (8 : BitVec 4) : Cl (gConf 4)).coeff c
  rw [h, hb]
  show 1 * delta 8 c + 0 = delta 8 c
  grind

private theorem toDiag_cga2Point (x y : Rat) :
    toDiag (cga2Point x y) = cga2PointDiag x y := by
  simp only [cga2Point, toDiag_add, toDiag_smul,
    toDiag_cga2_gen0, toDiag_cga2_gen1, toDiag_cga2_gen2, toDiag_cga2_gen3]
  ext c
  show ((x ^ 2 + y ^ 2) / 2 * ((Cl.gen 0 : Cl (gConf 4)).coeff c + (Cl.gen 1 : Cl (gConf 4)).coeff c)
        + ((-1 / 2 : Rat) * (Cl.gen 0 : Cl (gConf 4)).coeff c + (1 / 2 : Rat) * (Cl.gen 1 : Cl (gConf 4)).coeff c))
        + x * (Cl.gen 2 : Cl (gConf 4)).coeff c
        + y * (Cl.gen 3 : Cl (gConf 4)).coeff c
      = ((x ^ 2 + y ^ 2 - 1) / 2 * (Cl.gen 0 : Cl (gConf 4)).coeff c
        + (x ^ 2 + y ^ 2 + 1) / 2 * (Cl.gen 1 : Cl (gConf 4)).coeff c)
        + x * (Cl.gen 2 : Cl (gConf 4)).coeff c
        + y * (Cl.gen 3 : Cl (gConf 4)).coeff c
  grind

private theorem cga2_vec_sq (a b x y : Rat) :
    let v : Cl (gConf 4) := a • Cl.gen 0 + b • Cl.gen 1 + x • Cl.gen 2 + y • Cl.gen 3
    v * v = Cl.scalar (a ^ 2 - b ^ 2 + x ^ 2 + y ^ 2) := by
  clifford [gConf]

private theorem cga2PointDiag_mul_self (x y : Rat) :
    cga2PointDiag x y * cga2PointDiag x y = 0 := by
  rw [cga2_vec_sq]
  have hzero : ((x ^ 2 + y ^ 2 - 1) / 2) ^ 2 - ((x ^ 2 + y ^ 2 + 1) / 2) ^ 2
      + x ^ 2 + y ^ 2 = 0 := by grind
  rw [hzero]
  ext c
  show (if c = 0 then (0 : Rat) else 0) = 0
  split <;> rfl

/-- **Conformal null-point theorem in `CGA2`**: `P(x, y) * P(x, y) = 0` for all `(x, y) : Rat²`. -/
theorem cga2_point_mul_self (x y : Rat) :
    implMul CGA2 (cga2Point x y) (cga2Point x y) = 0 := by
  rw [← fromDiag_toDiag conf_inverse_4 (implMul CGA2 (cga2Point x y) (cga2Point x y)),
      CGA2_toDiag_mul, toDiag_cga2Point, cga2PointDiag_mul_self, fromDiag_zero]

/-- **Conformal null-point inner product `P · P = 0` in `CGA2`**. -/
theorem cga2_point_dot_self (x y : Rat) :
    (implMul CGA2 (cga2Point x y) (cga2Point x y)).coeff (0 : BitVec 4) = 0 := by
  rw [cga2_point_mul_self]; rfl

/-! ## 4. `ℝ3` Exact Rational Rotor Unit Norm & Euclidean Isometry -/

/-- General rational even spinor / rotor `R = s + b12·e12 + b13·e13 + b23·e23` in `ℝ3`. -/
abbrev r3Rotor (s b12 b13 b23 : Rat) : Cl (gEuclid 3) :=
  Cl.scalar s
    + b12 • (Cl.gen 0 * Cl.gen 1)
    + b13 • (Cl.gen 0 * Cl.gen 2)
    + b23 • (Cl.gen 1 * Cl.gen 2)

/-- General rational 3D vector `v = x·e1 + y·e2 + z·e3` in `ℝ3`. -/
abbrev r3Vec (x y z : Rat) : Cl (gEuclid 3) :=
  x • Cl.gen 0 + y • Cl.gen 1 + z • Cl.gen 2

/-- **`ℝ3` rational rotor norm identity**: for EVERY rational spinor `R`,
`R * ~R = (s² + b12² + b13² + b23²) · 1`. -/
theorem r3_rotor_mul_reverse (s b12 b13 b23 : Rat) :
    let R := r3Rotor s b12 b13 b23
    R * Cl.reverse R = Cl.scalar (s ^ 2 + b12 ^ 2 + b13 ^ 2 + b23 ^ 2) := by
  clifford

/-- **`ℝ3` rational rotor reverse commutativity**: `(~R) * R = R * (~R)`. -/
theorem r3_rotor_reverse_mul (s b12 b13 b23 : Rat) :
    let R := r3Rotor s b12 b13 b23
    Cl.reverse R * R = Cl.scalar (s ^ 2 + b12 ^ 2 + b13 ^ 2 + b23 ^ 2) := by
  clifford

/-- **Unit rational rotor identity**: whenever `s² + b12² + b13² + b23² = 1`,
`R * ~R = 1` and `~R * R = 1` in `Cl(3, 0, 0)`. -/
theorem r3_unit_rotor_norm_one {s b12 b13 b23 : Rat}
    (hunit : s ^ 2 + b12 ^ 2 + b13 ^ 2 + b23 ^ 2 = 1) :
    let R := r3Rotor s b12 b13 b23
    R * Cl.reverse R = 1 ∧ Cl.reverse R * R = 1 := by
  dsimp only
  rw [r3_rotor_mul_reverse, r3_rotor_reverse_mul, hunit]
  exact ⟨by clifford, by clifford⟩

/-- **Exact Euclidean isometry of any unit rational `ℝ3` rotor**:
for ALL `(s, b12, b13, b23)` with `s² + b12² + b13² + b23² = 1` and ALL `v = (x, y, z) ∈ ℚ³`,
the sandwich `v' = R * v * ~R` preserves squared norm `v' * v' = v * v`. -/
theorem r3_unit_rotor_preserves_norm_sq {s b12 b13 b23 : Rat}
    (hunit : s ^ 2 + b12 ^ 2 + b13 ^ 2 + b23 ^ 2 = 1) (x y z : Rat) :
    let R := r3Rotor s b12 b13 b23
    let v := r3Vec x y z
    (R * v * Cl.reverse R) * (R * v * Cl.reverse R) = v * v := by
  dsimp only
  have ⟨hRR, hRtR⟩ := r3_unit_rotor_norm_one hunit
  have hv2 : r3Vec x y z * r3Vec x y z = Cl.scalar (x ^ 2 + y ^ 2 + z ^ 2) := by clifford
  have hcomm : ∀ (a : Cl (gEuclid 3)) (c : Rat), a * Cl.scalar c = Cl.scalar c * a := by
    intro a c; rw [Cl.mul_scalar, Cl.scalar_mul]
  calc
    (r3Rotor s b12 b13 b23 * r3Vec x y z * Cl.reverse (r3Rotor s b12 b13 b23)) *
        (r3Rotor s b12 b13 b23 * r3Vec x y z * Cl.reverse (r3Rotor s b12 b13 b23))
      = r3Rotor s b12 b13 b23 * (r3Vec x y z *
          ((Cl.reverse (r3Rotor s b12 b13 b23) * r3Rotor s b12 b13 b23) *
            (r3Vec x y z * Cl.reverse (r3Rotor s b12 b13 b23)))) := by
        simp only [Cl.mul_assoc]
    _ = r3Rotor s b12 b13 b23 * ((r3Vec x y z * r3Vec x y z) * Cl.reverse (r3Rotor s b12 b13 b23)) := by
        rw [hRtR, Cl.one_mul, Cl.mul_assoc]
    _ = (r3Vec x y z * r3Vec x y z) * (r3Rotor s b12 b13 b23 * Cl.reverse (r3Rotor s b12 b13 b23)) := by
        rw [hv2, ← Cl.mul_assoc, hcomm, Cl.mul_assoc]
    _ = r3Vec x y z * r3Vec x y z := by
        rw [hRR, Cl.mul_one]

/-- **Concrete executable rational rotor certificate**: `Grassmann.Kernel.R3Rotor.rotor`
(`3/5 + 4/5·e12`) has exact unit norm `R * ~R = 1` both in the specification `Cl(3,0,0)`
and in the executable generated `Spinor ℝ3 Rat` kernel. -/
theorem r3_concrete_rational_rotor_unit :
    r3Rotor (3 / 5) (4 / 5) 0 0 * Cl.reverse (r3Rotor (3 / 5) (4 / 5) 0 0) = 1 ∧
    ((Grassmann.Kernel.R3Rotor.rotor * Grassmann.Kernel.R3Rotor.rotor.reverse : Spinor ℝ3 Rat).v
      = Values.ofFn fun i => if i.1 == 0 then (1 : Rat) else 0) := by
  constructor
  · exact (r3_unit_rotor_norm_one (s := 3 / 5) (b12 := 4 / 5) (b13 := 0) (b23 := 0) (by grind)).1
  · apply Values.ext
    intro ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
      have hlt : i < 4 := hi
      omega
    rcases h with rfl | rfl | rfl | rfl
    · change (Grassmann.Kernel.R3Rotor.rotor * Grassmann.Kernel.R3Rotor.rotor.reverse : Spinor ℝ3 Rat).v.get ⟨0, by decide⟩ = 1
      decide +kernel
    · change (Grassmann.Kernel.R3Rotor.rotor * Grassmann.Kernel.R3Rotor.rotor.reverse : Spinor ℝ3 Rat).v.get ⟨1, by decide⟩ = 0
      decide +kernel
    · change (Grassmann.Kernel.R3Rotor.rotor * Grassmann.Kernel.R3Rotor.rotor.reverse : Spinor ℝ3 Rat).v.get ⟨2, by decide⟩ = 0
      decide +kernel
    · change (Grassmann.Kernel.R3Rotor.rotor * Grassmann.Kernel.R3Rotor.rotor.reverse : Spinor ℝ3 Rat).v.get ⟨3, by decide⟩ = 0
      decide +kernel

end Grassmann.Proofs.ProjectiveConformal
