/-
Formal kernel-verified proofs for:
1. `ALOK-950` Spacetime Algebra `STA = Cl(3, 1)` (`S!"-+++"`, mostly-plus metric `(-, +, +, +)`):
   Lorentz boost rotors `B(c, s) = c + s · e_t e_x`, hyperbolic rapidity composition, exact Lorentz
   boost matrix action, Minkowski quadratic form invariance, spatial rotation invariance, and
   transport to DirectSum's executable `implMul STA`.
2. `PGA2` & `PGA3` Wedge projective incidence laws:
   - `PGA2`: point-on-line incidence (`P ∧ L = (ax+by+c) I`), antisymmetry & incidence of point
     join `A ∨ B`, line meet `L₁ ∧ L₂` incidence with both lines, midpoint `A + B` (and unit
     midpoint `½(A + B)`) incidence on `A ∨ B`.
   - `PGA3`: point-on-plane incidence (`Π ∧ P = (ax+by+cz+d) I`), two-plane meet `P₁ ∧ P₂` lying
     in both planes, three-plane meet `P₁ ∧ P₂ ∧ P₃` lying in all three planes, point-join
     Plücker line antisymmetry & incidence (including midpoint `A + B`), and three-point plane
     `A ∨ B ∨ C` incidence.
   - Transport to DirectSum's executable `implWedge` and `implVee` on `PGA2` and `PGA3`.

Credits:
- Michael Reed (`chakravala` / `Grassmann.jl`): core Clifford/Grassmann algebra architecture.
- Steven De Keninck (`enkimute` / `ganja.js`): PGA dual point/line/plane conventions & Wedge game.

Every theorem in this module has ZERO `sorry`, ZERO custom `axiom`, and ZERO `native_decide`,
and is audited by `#print axioms` in `Tests/Proofs/Axioms.lean`.
-/
import Grassmann.Proofs.Regressive
import Grassmann.Tactic

namespace Grassmann.Proofs.SpacetimeWedge

open DirectSum DirectSum.Proofs Grassmann.Spec Grassmann.Proofs Lean.Grind

/-! ## 1. `ALOK-950` Spacetime Algebra `STA = Cl(3, 1)` (`S!"-+++"`) -/

/-- Timelike basis vector `e_t` (`e_t² = -1`) in `STA = S!"-+++"`. -/
abbrev staT : Cl gSTA := Cl.gen 0
/-- Spacelike basis vector `e_x` (`e_x² = +1`) in `STA = S!"-+++"`. -/
abbrev staX : Cl gSTA := Cl.gen 1
/-- Spacelike basis vector `e_y` (`e_y² = +1`) in `STA = S!"-+++"`. -/
abbrev staY : Cl gSTA := Cl.gen 2
/-- Spacelike basis vector `e_z` (`e_z² = +1`) in `STA = S!"-+++"`. -/
abbrev staZ : Cl gSTA := Cl.gen 3

/-- Spacetime 4-vector `v = v_t e_t + v_x e_x + v_y e_y + v_z e_z` in `STA`. -/
abbrev staVec (vt vx vy vz : Rat) : Cl gSTA :=
  vt • staT + vx • staX + vy • staY + vz • staZ

/-- Lorentz boost rotor `B(c, s) = c + s · (e_t e_x)` along the `x`-axis
(`c = cosh(φ/2)`, `s = sinh(φ/2)` with `c² - s² = 1`). -/
abbrev staBoostX (c s : Rat) : Cl gSTA :=
  Cl.scalar c + s • (staT * staX)

/-- Spatial rotation rotor `R(c, s) = c + s · (e_x e_y)` in the `xy`-plane
(`c = cos(θ/2)`, `s = sin(θ/2)` with `c² + s² = 1`). -/
abbrev staRotXY (c s : Rat) : Cl gSTA :=
  Cl.scalar c + s • (staX * staY)

/-- **Timelike generator square**: `e_t² = -1` in `STA = S!"-+++"`. -/
theorem sta_timelike_sq : staT * staT = (-1 : Cl gSTA) := by
  clifford [gSTA]

/-- **Spacelike generator squares**: `e_x² = e_y² = e_z² = +1` in `STA = S!"-+++"`. -/
theorem sta_spacelike_sq :
    staX * staX = (1 : Cl gSTA) ∧
    staY * staY = (1 : Cl gSTA) ∧
    staZ * staZ = (1 : Cl gSTA) :=
  ⟨by clifford [gSTA], by clifford [gSTA], by clifford [gSTA]⟩

/-- **Generator anticommutativity in `STA`**: distinct basis vectors anticommute. -/
theorem sta_generators_anticomm :
    staX * staY = -(staY * staX) ∧
    staT * staX = -(staX * staT) ∧
    staY * staZ = -(staZ * staY) ∧
    staZ * staX = -(staX * staZ) :=
  ⟨by clifford [gSTA], by clifford [gSTA], by clifford [gSTA], by clifford [gSTA]⟩

/-- **Hyperbolic vs elliptic bivector squares**: boost plane `(e_t e_x)² = +1`,
spatial plane `(e_x e_y)² = -1`. -/
theorem sta_bivector_squares :
    (staT * staX) * (staT * staX) = (1 : Cl gSTA) ∧
    (staX * staY) * (staX * staY) = (-1 : Cl gSTA) :=
  ⟨by clifford [gSTA], by clifford [gSTA]⟩

/-- **Minkowski quadratic form (`-+++`)**: for every spacetime 4-vector `v`,
`v² = -v_t² + v_x² + v_y² + v_z²`. -/
theorem sta_minkowski_quadratic_form (vt vx vy vz : Rat) :
    staVec vt vx vy vz * staVec vt vx vy vz =
      Cl.scalar (-vt ^ 2 + vx ^ 2 + vy ^ 2 + vz ^ 2) := by
  clifford [gSTA]

/-- **Boost rotor hyperbolic norm**: `B(c, s) * ~B(c, s) = (c² - s²) · 1`. -/
theorem sta_boost_mul_reverse (c s : Rat) :
    staBoostX c s * Cl.reverse (staBoostX c s) = Cl.scalar (c ^ 2 - s ^ 2) := by
  clifford [gSTA]

/-- **Boost rotor reverse norm**: `~B(c, s) * B(c, s) = (c² - s²) · 1`. -/
theorem sta_boost_reverse_mul (c s : Rat) :
    Cl.reverse (staBoostX c s) * staBoostX c s = Cl.scalar (c ^ 2 - s ^ 2) := by
  clifford [gSTA]

/-- **Unit Lorentz boost rotor**: whenever `c² - s² = 1`, `B * ~B = 1` and `~B * B = 1`. -/
theorem sta_boost_unit {c s : Rat} (h : c ^ 2 - s ^ 2 = 1) :
    staBoostX c s * Cl.reverse (staBoostX c s) = 1 ∧
    Cl.reverse (staBoostX c s) * staBoostX c s = 1 := by
  rw [sta_boost_mul_reverse, sta_boost_reverse_mul, h]
  exact ⟨by clifford [gSTA], by clifford [gSTA]⟩

/-- **Hyperbolic rapidity composition law**: `B(c₁, s₁) * B(c₂, s₂) = B(c₁c₂ + s₁s₂, c₁s₂ + s₁c₂)`. -/
theorem sta_boost_composition (c₁ s₁ c₂ s₂ : Rat) :
    staBoostX c₁ s₁ * staBoostX c₂ s₂ =
      staBoostX (c₁ * c₂ + s₁ * s₂) (c₁ * s₂ + s₁ * c₂) := by
  clifford [gSTA]

/-- **Exact Lorentz boost sandwich action**: for any `(c, s)` with `c² - s² = 1`,
`B * v * ~B` boosts `(v_t, v_x)` by `(γ = c² + s², βγ = 2cs)` and fixes `(v_y, v_z)`. -/
theorem sta_boost_sandwich_formula {c s : Rat} (h : c ^ 2 - s ^ 2 = 1) (vt vx vy vz : Rat) :
    staBoostX c s * staVec vt vx vy vz * Cl.reverse (staBoostX c s) =
      staVec ((c ^ 2 + s ^ 2) * vt + (2 * c * s) * vx)
             ((2 * c * s) * vt + (c ^ 2 + s ^ 2) * vx)
             vy vz := by
  clifford [gSTA]

/-- **Lorentz boost invariance of the Minkowski quadratic form (`ALOK-950`)**:
for every boost rotor `B(c, s)` with `c² - s² = 1` and every 4-vector `v`,
`(B * v * ~B)² = v² = (-v_t² + v_x² + v_y² + v_z²) · 1`. -/
theorem sta_boost_preserves_minkowski {c s : Rat} (h : c ^ 2 - s ^ 2 = 1) (vt vx vy vz : Rat) :
    let B := staBoostX c s
    let v := staVec vt vx vy vz
    (B * v * Cl.reverse B) * (B * v * Cl.reverse B) = v * v := by
  dsimp only
  rw [sta_boost_sandwich_formula h, sta_minkowski_quadratic_form, sta_minkowski_quadratic_form]
  congr 1
  grind

/-- Explicit scalar Minkowski form version of `sta_boost_preserves_minkowski`. -/
theorem sta_boost_preserves_minkowski_form {c s : Rat} (h : c ^ 2 - s ^ 2 = 1) (vt vx vy vz : Rat) :
    let B := staBoostX c s
    let v := staVec vt vx vy vz
    (B * v * Cl.reverse B) * (B * v * Cl.reverse B) =
      Cl.scalar (-vt ^ 2 + vx ^ 2 + vy ^ 2 + vz ^ 2) := by
  dsimp only
  rw [sta_boost_preserves_minkowski h, sta_minkowski_quadratic_form]

/-- **Implementation transport for `STA` Lorentz boost invariance**:
DirectSum's executable `implMul STA` satisfies exact Minkowski interval preservation. -/
theorem sta_impl_boost_preserves_minkowski {c s : Rat} (h : c ^ 2 - s ^ 2 = 1) (vt vx vy vz : Rat) :
    let B := staBoostX c s
    let v := staVec vt vx vy vz
    let v' := implMul STA (implMul STA B v) (Cl.reverse B)
    implMul STA v' v' = Cl.scalar (-vt ^ 2 + vx ^ 2 + vy ^ 2 + vz ^ 2) := by
  dsimp only
  simp only [STA_mul]
  exact sta_boost_preserves_minkowski_form h vt vx vy vz

/-- **Spatial rotation invariance in `STA`**: every unit spatial rotor `R = c + s·e_x e_y`
with `c² + s² = 1` satisfies `R * ~R = 1` and preserves the Minkowski quadratic form. -/
theorem sta_spatial_rot_preserves_minkowski {c s : Rat} (h : c ^ 2 + s ^ 2 = 1) (vt vx vy vz : Rat) :
    let R := staRotXY c s
    let v := staVec vt vx vy vz
    R * Cl.reverse R = 1 ∧
    (R * v * Cl.reverse R) * (R * v * Cl.reverse R) = v * v := by
  dsimp only
  constructor
  · clifford [gSTA]
  · have hrot : staRotXY c s * staVec vt vx vy vz * Cl.reverse (staRotXY c s) =
        staVec vt ((c ^ 2 - s ^ 2) * vx + (2 * c * s) * vy)
                  (-(2 * c * s) * vx + (c ^ 2 - s ^ 2) * vy) vz := by
      clifford [gSTA]
    rw [hrot, sta_minkowski_quadratic_form, sta_minkowski_quadratic_form]
    congr 1
    grind

/-- **Concrete exact rational Lorentz boost**: `(c, s) = (5/4, 3/4)` (`c² - s² = 1`, `γ = 17/8`,
`β = 15/17`) is a unit boost rotor preserving the Minkowski quadratic form on all 4-vectors. -/
theorem sta_concrete_rational_boost (vt vx vy vz : Rat) :
    let B := staBoostX (5 / 4) (3 / 4)
    let v := staVec vt vx vy vz
    B * Cl.reverse B = 1 ∧
    (B * v * Cl.reverse B) * (B * v * Cl.reverse B) = v * v :=
  ⟨(sta_boost_unit (c := 5 / 4) (s := 3 / 4) (by grind)).1,
   sta_boost_preserves_minkowski (c := 5 / 4) (s := 3 / 4) (by grind) vt vx vy vz⟩

/-! ## 2. Implementation Transport for `implWedge` and `implVee` on `PGA2` and `PGA3` -/

/-- The implementation's regressive product `∨` (bilinear extension of `TensorBundle.terms₂ .vee`). -/
def implVee {n : Nat} (V : TensorBundle) {g : Fin n → Rat} (x y : Cl g) : Cl g :=
  bilin (fun a b => ofTerms g (V.terms₂ .vee (mask a) (mask b))) x y

/-- Every multivector expands in the basis of `Cl.blade a` under `Cl.vee`. -/
private theorem bilin_vee_eq_vee {n : Nat} {g : Fin n → Rat} (x y : Cl g) :
    bilin (fun a b => Cl.vee (Cl.blade a) (Cl.blade b : Cl g)) x y = Cl.vee x y := by
  ext c
  show (bsum n fun a => bsum n fun b => x.coeff a * y.coeff b *
        (Cl.vee (Cl.blade a) (Cl.blade b : Cl g)).coeff c) = (Cl.vee x y).coeff c
  have hterm : ∀ a b : BitVec n, (Cl.vee (Cl.blade a) (Cl.blade b : Cl g)).coeff c =
      signOf (sign c (~~~c)) * (signOf (sign a (~~~a)) * signOf (sign b (~~~b)) *
        wcoef (~~~a) (~~~b) * delta (a ^^^ b) (~~~c)) := by
    intro a b
    have hw : Cl.wedge (Cl.compl (Cl.blade a)) (Cl.compl (Cl.blade b) : Cl g)
        = ((signOf (sign a (~~~a)) : Rat) * signOf (sign b (~~~b)) * wcoef (~~~a) (~~~b))
            • Cl.blade (a ^^^ b) := by
      rw [Cl.compl_blade, Cl.compl_blade, Cl.smul_wedge, Cl.wedge_smul, Cl.blade_wedge_blade,
          Cl.not_xor_not]
      ext d; simp only [Cl.coeff_smul]; grind
    show signOf (sign c (~~~c)) *
        (Cl.wedge (Cl.compl (Cl.blade a)) (Cl.compl (Cl.blade b) : Cl g)).coeff (~~~c) = _
    rw [hw]
    simp only [Cl.coeff_smul, Cl.coeff_blade, delta]
  have hrhs : (Cl.vee x y).coeff c =
      signOf (sign c (~~~c)) *
        (bsum n fun a' => (signOf (sign (~~~a') a') * x.coeff (~~~a')) *
          (signOf (sign (~~~(a' ^^^ ~~~c)) (a' ^^^ ~~~c)) * y.coeff (~~~(a' ^^^ ~~~c))) *
            wcoef a' (a' ^^^ ~~~c)) := by
    show signOf (sign c (~~~c)) *
      (bsum n fun a' => (Cl.compl x).coeff a' *
        (Cl.compl y).coeff (a' ^^^ ~~~c) * wcoef a' (a' ^^^ ~~~c)) = _
    rfl
  rw [hrhs, mul_bsum]
  have hlhs : (bsum n fun a => bsum n fun b => x.coeff a * y.coeff b *
      (Cl.vee (Cl.blade a) (Cl.blade b : Cl g)).coeff c) =
      bsum n fun a => signOf (sign c (~~~c)) *
        ((signOf (sign a (~~~a)) * x.coeff a) *
          (signOf (sign (a ^^^ ~~~c) (~~~(a ^^^ ~~~c))) * y.coeff (a ^^^ ~~~c)) *
            wcoef (~~~a) (~~~(a ^^^ ~~~c))) := by
    apply bsum_congr; intro a
    have hinner : (bsum n fun b => x.coeff a * y.coeff b *
        (Cl.vee (Cl.blade a) (Cl.blade b : Cl g)).coeff c) =
        bsum n fun b => if b = a ^^^ ~~~c then
          x.coeff a * y.coeff (a ^^^ ~~~c) * (signOf (sign c (~~~c)) *
            (signOf (sign a (~~~a)) * signOf (sign (a ^^^ ~~~c) (~~~(a ^^^ ~~~c))) *
              wcoef (~~~a) (~~~(a ^^^ ~~~c))))
        else 0 := by
      apply bsum_congr; intro b
      rw [hterm a b]
      unfold delta
      by_cases hb : b = a ^^^ ~~~c
      · subst hb
        rw [ite_eq_left (xor_xor_cancel_left a (~~~c)).symm, ite_eq_left rfl]; grind
      · have hne : ¬ ~~~c = a ^^^ b := fun e => hb (by rw [e, xor_xor_cancel_left])
        rw [ite_eq_right hne, ite_eq_right hb]; grind
    rw [hinner, bsum_ite_eq]
    grind
  rw [hlhs]
  have hbij : ∀ (f : BitVec n → Rat), (bsum n fun a => f a) = bsum n fun a => f (~~~a) := by
    intro f
    exact (bsum_xor (BitVec.allOnes n) f).symm.trans
      (bsum_congr fun a => congrArg f (not_eq_xor_allOnes a).symm)
  rw [hbij]
  apply bsum_congr; intro a'
  have h1 : ~~~(~~~a') = a' := BitVec.not_not
  have h2 : ~~~a' ^^^ ~~~c = ~~~(a' ^^^ ~~~c) := by
    rw [Cl.not_xor_not a' c]
    rw [not_eq_xor_allOnes, not_eq_xor_allOnes]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_xor]
    apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_xor]
    cases a'.toNat.testBit i <;> cases c.toNat.testBit i <;> cases (BitVec.allOnes n).toNat.testBit i <;> rfl
  rw [h1, h2, BitVec.not_not]

/-- A matching regressive-product table lifts `implVee` to `Cl.vee` on **all** multivectors. -/
theorem implVee_eq_vee {n : Nat} (hn : n ≤ 64) {V : TensorBundle} {g : Fin n → Rat}
    (h : VeeAgrees V g) (x y : Cl g) : implVee V x y = Cl.vee x y := by
  unfold implVee
  have hbl : ∀ a b : BitVec n, ofTerms g (V.terms₂ .vee (mask a) (mask b)) = Cl.vee (Cl.blade a) (Cl.blade b) :=
    implVee_blade hn h
  have : bilin (fun a b => ofTerms g (V.terms₂ .vee (mask a) (mask b))) x y =
      bilin (fun a b => Cl.vee (Cl.blade a) (Cl.blade b : Cl g)) x y := by
    ext c
    show (bsum n fun a => bsum n fun b => x.coeff a * y.coeff b * (ofTerms g _).coeff c) = _
    apply bsum_congr; intro a
    apply bsum_congr; intro b; rw [hbl a b]
  rw [this, bilin_vee_eq_vee]

/-- `PGA2`: the exterior-product table is the spec's. -/
theorem PGA2_wedge_table : TableAgrees PGA2 .wedge (wcoef (R := Rat) (n := 3)) := by
  unfold TableAgrees; decide +kernel

/-- `PGA2`: the regressive-product table is the spec's. -/
theorem PGA2_vee_table : VeeAgrees PGA2 (gPGA 3) := by
  unfold VeeAgrees; decide +kernel

/-- `PGA2`: `implWedge` equals `Cl.wedge` on all multivectors. -/
theorem PGA2_wedge (x y : Cl (gPGA 3)) : implWedge PGA2 x y = Cl.wedge x y :=
  implWedge_eq_wedge (by decide) PGA2_wedge_table x y

/-- `PGA2`: `implVee` equals `Cl.vee` on all multivectors. -/
theorem PGA2_vee (x y : Cl (gPGA 3)) : implVee PGA2 x y = Cl.vee x y :=
  implVee_eq_vee (by decide) PGA2_vee_table x y

/-- `PGA3`: `implWedge` equals `Cl.wedge` on all multivectors. -/
theorem PGA3_wedge (x y : Cl (gPGA 4)) : implWedge PGA3 x y = Cl.wedge x y :=
  implWedge_eq_wedge (by decide) PGA3_wedge_table x y

/-- `PGA3`: `implVee` equals `Cl.vee` on all multivectors. -/
theorem PGA3_vee (x y : Cl (gPGA 4)) : implVee PGA3 x y = Cl.vee x y :=
  implVee_eq_vee (by decide) PGA3_vee_table x y

/-! ## 3. `PGA2` Wedge Projective Incidence Laws -/

/-- Dual-model `PGA2` line `a·x + b·y + c = 0` as a grade-1 vector `c e₀ + a e₁ + b e₂`. -/
abbrev pga2Line (a b c : Rat) : Cl (gPGA 3) :=
  c • Cl.gen 0 + a • Cl.gen 1 + b • Cl.gen 2

/-- Dual-model `PGA2` homogeneous point `(x, y; w)` as a grade-2 bivector
`w e₁₂ + x e₂₀ + y e₀₁` (unit Euclidean point when `w = 1`, ideal point when `w = 0`). -/
abbrev pga2Point (x y w : Rat) : Cl (gPGA 3) :=
  w • (Cl.gen 1 * Cl.gen 2) + x • (Cl.gen 2 * Cl.gen 0) + y • (Cl.gen 0 * Cl.gen 1)

/-- **`PGA2` point-on-line incidence equation**:
`P(x, y; 1) ∧ L(a, b, c) = (a·x + b·y + c) · e₀₁₂`. -/
theorem pga2_point_on_line_eq (x y a b c : Rat) :
    Cl.wedge (pga2Point x y 1) (pga2Line a b c) = (a * x + b * y + c) • Cl.pseudoscalar := by
  clifford [gPGA]

/-- **`PGA2` join antisymmetry**: `A ∨ B = -(B ∨ A)` for every pair of homogeneous points. -/
theorem pga2_join_antisymm (x₁ y₁ w₁ x₂ y₂ w₂ : Rat) :
    Cl.vee (pga2Point x₁ y₁ w₁) (pga2Point x₂ y₂ w₂) =
      -(Cl.vee (pga2Point x₂ y₂ w₂) (pga2Point x₁ y₁ w₁)) := by
  clifford [gPGA]

/-- **`PGA2` self-join vanishes**: `A ∨ A = 0` for every homogeneous point `A`. -/
theorem pga2_join_self_zero (x y w : Rat) :
    Cl.vee (pga2Point x y w) (pga2Point x y w) = 0 := by
  clifford [gPGA]

/-- **`PGA2` join incidence**: the line `A ∨ B` is incident with BOTH `A` and `B`
(`A ∧ (A ∨ B) = 0` and `B ∧ (A ∨ B) = 0`). -/
theorem pga2_join_incident (x₁ y₁ w₁ x₂ y₂ w₂ : Rat) :
    let A := pga2Point x₁ y₁ w₁
    let B := pga2Point x₂ y₂ w₂
    Cl.wedge A (Cl.vee A B) = 0 ∧ Cl.wedge B (Cl.vee A B) = 0 :=
  ⟨by clifford [gPGA], by clifford [gPGA]⟩

/-- **`PGA2` line meet antisymmetry & incidence**: the intersection point `L₁ ∧ L₂`
satisfies `L₁ ∧ L₂ = -(L₂ ∧ L₁)` and is incident with BOTH `L₁` and `L₂`. -/
theorem pga2_meet_lines_laws (a₁ b₁ c₁ a₂ b₂ c₂ : Rat) :
    let L₁ := pga2Line a₁ b₁ c₁
    let L₂ := pga2Line a₂ b₂ c₂
    Cl.wedge L₁ L₂ = -(Cl.wedge L₂ L₁) ∧
    Cl.wedge L₁ (Cl.wedge L₁ L₂) = 0 ∧
    Cl.wedge L₂ (Cl.wedge L₁ L₂) = 0 :=
  ⟨by clifford [gPGA], by clifford [gPGA], by clifford [gPGA]⟩

/-- **`PGA2` midpoint lies on the join line**: for every pair of unit Euclidean points `A, B`,
both the unnormalized midpoint `A + B` and the unit midpoint `M = ½(A + B)` lie on `A ∨ B`. -/
theorem pga2_midpoint_on_join (x₁ y₁ x₂ y₂ : Rat) :
    let A := pga2Point x₁ y₁ 1
    let B := pga2Point x₂ y₂ 1
    Cl.wedge (A + B) (Cl.vee A B) = 0 ∧
    Cl.wedge (pga2Point ((x₁ + x₂) / 2) ((y₁ + y₂) / 2) 1) (Cl.vee A B) = 0 := by
  constructor
  · clifford [gPGA]
  · have hscale : pga2Point ((x₁ + x₂) / 2) ((y₁ + y₂) / 2) 1 =
        (1 / 2 : Rat) • (pga2Point x₁ y₁ 1 + pga2Point x₂ y₂ 1) := by
      ext c
      show ((1 : Rat) * (Cl.gen 1 * Cl.gen 2 : Cl (gPGA 3)).coeff c +
              (x₁ + x₂) / 2 * (Cl.gen 2 * Cl.gen 0 : Cl (gPGA 3)).coeff c +
              (y₁ + y₂) / 2 * (Cl.gen 0 * Cl.gen 1 : Cl (gPGA 3)).coeff c) =
            (1 / 2 : Rat) * (((1 : Rat) * (Cl.gen 1 * Cl.gen 2 : Cl (gPGA 3)).coeff c +
              x₁ * (Cl.gen 2 * Cl.gen 0 : Cl (gPGA 3)).coeff c +
              y₁ * (Cl.gen 0 * Cl.gen 1 : Cl (gPGA 3)).coeff c) +
             ((1 : Rat) * (Cl.gen 1 * Cl.gen 2 : Cl (gPGA 3)).coeff c +
              x₂ * (Cl.gen 2 * Cl.gen 0 : Cl (gPGA 3)).coeff c +
              y₂ * (Cl.gen 0 * Cl.gen 1 : Cl (gPGA 3)).coeff c))
      grind
    rw [hscale, Cl.smul_wedge]
    have h0 : Cl.wedge (pga2Point x₁ y₁ 1 + pga2Point x₂ y₂ 1)
        (Cl.vee (pga2Point x₁ y₁ 1) (pga2Point x₂ y₂ 1)) = 0 := by clifford [gPGA]
    rw [h0]
    ext c; show (1 / 2 : Rat) * 0 = 0; grind

/-- **Implementation transport for `PGA2` Wedge laws**: DirectSum's `implWedge PGA2` and
`implVee PGA2` satisfy join antisymmetry, join incidence, meet incidence, and midpoint incidence. -/
theorem pga2_impl_wedge_laws (x₁ y₁ x₂ y₂ a₁ b₁ c₁ a₂ b₂ c₂ : Rat) :
    let A := pga2Point x₁ y₁ 1
    let B := pga2Point x₂ y₂ 1
    let L₁ := pga2Line a₁ b₁ c₁
    let L₂ := pga2Line a₂ b₂ c₂
    implVee PGA2 A B = -(implVee PGA2 B A) ∧
    implWedge PGA2 A (implVee PGA2 A B) = 0 ∧
    implWedge PGA2 (A + B) (implVee PGA2 A B) = 0 ∧
    implWedge PGA2 L₁ (implWedge PGA2 L₁ L₂) = 0 := by
  dsimp only
  simp only [PGA2_wedge, PGA2_vee]
  exact ⟨pga2_join_antisymm x₁ y₁ 1 x₂ y₂ 1,
    (pga2_join_incident x₁ y₁ 1 x₂ y₂ 1).1,
    (pga2_midpoint_on_join x₁ y₁ x₂ y₂).1,
    (pga2_meet_lines_laws a₁ b₁ c₁ a₂ b₂ c₂).2.1⟩

/-! ## 4. `PGA3` Wedge Projective Incidence Laws -/

/-- Dual-model `PGA3` plane `a·x + b·y + c·z + d = 0` as a grade-1 vector
`d e₀ + a e₁ + b e₂ + c e₃`. -/
abbrev pga3Plane (a b c d : Rat) : Cl (gPGA 4) :=
  d • Cl.gen 0 + a • Cl.gen 1 + b • Cl.gen 2 + c • Cl.gen 3

/-- Dual-model `PGA3` homogeneous point `(x, y, z; w)` as a grade-3 trivector
`w e₁₂₃ + x e₀₃₂ + y e₀₁₃ + z e₀₂₁` (exact `ganja.js` / `Grassmann.Projective` dual point). -/
abbrev pga3Point (x y z w : Rat) : Cl (gPGA 4) :=
  w • (Cl.gen 1 * Cl.gen 2 * Cl.gen 3)
    + x • (Cl.gen 0 * Cl.gen 3 * Cl.gen 2)
    + y • (Cl.gen 0 * Cl.gen 1 * Cl.gen 3)
    + z • (Cl.gen 0 * Cl.gen 2 * Cl.gen 1)

/-- **`PGA3` point-on-plane incidence equation**:
`Π(a, b, c, d) ∧ P(x, y, z; 1) = (a·x + b·y + c·z + d) · e₀₁₂₃`. -/
theorem pga3_point_on_plane_eq (x y z a b c d : Rat) :
    Cl.wedge (pga3Plane a b c d) (pga3Point x y z 1) =
      (a * x + b * y + c * z + d) • Cl.pseudoscalar := by
  clifford [gPGA]

/-- **`PGA3` two-plane meet incidence**: the intersection line `L = P₁ ∧ P₂` lies in
BOTH planes (`P₁ ∧ (P₁ ∧ P₂) = 0` and `P₂ ∧ (P₁ ∧ P₂) = 0`). -/
theorem pga3_meet_planes_incident (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : Rat) :
    let P₁ := pga3Plane a₁ b₁ c₁ d₁
    let P₂ := pga3Plane a₂ b₂ c₂ d₂
    Cl.wedge P₁ (Cl.wedge P₁ P₂) = 0 ∧ Cl.wedge P₂ (Cl.wedge P₁ P₂) = 0 :=
  ⟨by clifford [gPGA], by clifford [gPGA]⟩

/-- **`PGA3` three-plane meet incidence**: the intersection point `Q = P₁ ∧ P₂ ∧ P₃` lies
in all three planes (`Pᵢ ∧ Q = 0`). -/
theorem pga3_meet_three_planes_incident
    (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ a₃ b₃ c₃ d₃ : Rat) :
    let P₁ := pga3Plane a₁ b₁ c₁ d₁
    let P₂ := pga3Plane a₂ b₂ c₂ d₂
    let P₃ := pga3Plane a₃ b₃ c₃ d₃
    let Q := Cl.wedge (Cl.wedge P₁ P₂) P₃
    Cl.wedge P₁ Q = 0 ∧ Cl.wedge P₂ Q = 0 ∧ Cl.wedge P₃ Q = 0 :=
  ⟨by clifford [gPGA], by clifford [gPGA], by clifford [gPGA]⟩

/-- **`PGA3` point-join Plücker line antisymmetry & incidence**:
`A ∨ B = -(B ∨ A)`, and `A`, `B`, and their midpoint `A + B` all lie on `A ∨ B`. -/
theorem pga3_join_points_laws (x₁ y₁ z₁ w₁ x₂ y₂ z₂ w₂ : Rat) :
    let A := pga3Point x₁ y₁ z₁ w₁
    let B := pga3Point x₂ y₂ z₂ w₂
    Cl.vee A B = -(Cl.vee B A) ∧
    Cl.vee A (Cl.vee A B) = 0 ∧
    Cl.vee B (Cl.vee A B) = 0 ∧
    Cl.vee (A + B) (Cl.vee A B) = 0 :=
  ⟨by clifford [gPGA], by clifford [gPGA], by clifford [gPGA], by clifford [gPGA]⟩

/-- **`PGA3` three-point spanning plane incidence**: the plane `pl = (A ∨ B) ∨ C`
contains all three points `A`, `B`, and `C` (`pl ∧ A = pl ∧ B = pl ∧ C = 0`). -/
theorem pga3_join_three_points_plane_incident
    (x₁ y₁ z₁ w₁ x₂ y₂ z₂ w₂ x₃ y₃ z₃ w₃ : Rat) :
    let A := pga3Point x₁ y₁ z₁ w₁
    let B := pga3Point x₂ y₂ z₂ w₂
    let C := pga3Point x₃ y₃ z₃ w₃
    let pl := Cl.vee (Cl.vee A B) C
    Cl.wedge pl A = 0 ∧ Cl.wedge pl B = 0 ∧ Cl.wedge pl C = 0 :=
  ⟨by clifford [gPGA], by clifford [gPGA], by clifford [gPGA]⟩

/-- **Implementation transport for `PGA3` Wedge laws**: DirectSum's `implWedge PGA3` and
`implVee PGA3` satisfy two-plane meet incidence, point-join antisymmetry, and midpoint incidence. -/
theorem pga3_impl_wedge_laws (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ x₁ y₁ z₁ x₂ y₂ z₂ : Rat) :
    let P₁ := pga3Plane a₁ b₁ c₁ d₁
    let P₂ := pga3Plane a₂ b₂ c₂ d₂
    let A := pga3Point x₁ y₁ z₁ 1
    let B := pga3Point x₂ y₂ z₂ 1
    implWedge PGA3 P₁ (implWedge PGA3 P₁ P₂) = 0 ∧
    implWedge PGA3 P₂ (implWedge PGA3 P₁ P₂) = 0 ∧
    implVee PGA3 A B = -(implVee PGA3 B A) ∧
    implVee PGA3 (A + B) (implVee PGA3 A B) = 0 := by
  dsimp only
  simp only [PGA3_wedge, PGA3_vee]
  exact ⟨(pga3_meet_planes_incident a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂).1,
    (pga3_meet_planes_incident a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂).2,
    (pga3_join_points_laws x₁ y₁ z₁ 1 x₂ y₂ z₂ 1).1,
    (pga3_join_points_laws x₁ y₁ z₁ 1 x₂ y₂ z₂ 1).2.2.2⟩

end Grassmann.Proofs.SpacetimeWedge
