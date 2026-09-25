/-
The implementation's blade tables equal the specification, space by space.

For the Euclidean spaces `ℝ2`, `ℝ3`, the spacetime algebra `STA = S!"-+++"`,
the degenerate projective spaces `PGA2 = D!"0,1,1"`, `PGA3 = D!"0,1,1,1"` and
the general diagonal form `D!"1,2,-3"`, kernel evaluation (`decide +kernel`,
exact `Rat` arithmetic, no `native_decide`) checks on **every** basis blade
(pair) that DirectSum's blade rules produce exactly the spec's term:

* geometric product `terms₂ .mul` = `coef g a b · e_{a⊕b}` (`*_mul_table`);
* exterior product `terms₂ .wedge` = `wcoef a b · e_{a⊕b}` (`*_wedge_table`);
* reversion, grade involution, right complement and Hodge star
  (`terms₁ .reverse/.involute/.complementright/.complementrighthodge`, and the
  container-level `Grassmann.Kernel.unTermsC` the reference kernels use);
* the reference kernel's multiply-accumulate plan for
  `Multivector × Multivector` (`Grassmann.Kernel.build`) is the spec table in
  Julia's storage order (`*_mul_plan`).

With `Grassmann.Proofs.Link` the tables lift to all multivectors:
`implMul V x y = x * y` (`R3_mul`, `STA_mul`, `PGA3_mul`, …).
-/
import Grassmann.Proofs.Link

namespace Grassmann.Proofs

open DirectSum DirectSum.Proofs Grassmann.Spec Lean.Grind

variable {n : Nat}

/-! ## Metrics of the checked spaces -/

/-- The Euclidean metric `(1, …, 1)` (`ℝⁿ`, Julia `V"n"`). -/
def gEuclid (n : Nat) : Fin n → Rat := fun _ => 1

/-- The spacetime metric `(-1, 1, 1, 1)` (`STA = S!"-+++"`). -/
def gSTA : Fin 4 → Rat := fun i => if i.1 = 0 then -1 else 1

/-- The projective metric `(0, 1, …, 1)` (`PGA2`, `PGA3`: degenerate). -/
def gPGA (n : Nat) : Fin n → Rat := fun i => if i.1 = 0 then 0 else 1

/-- The general diagonal metric `(1, 2, -3)` (`D!"1,2,-3"`). -/
def gD123 : Fin 3 → Rat := fun i => if i.1 = 0 then 1 else if i.1 = 1 then 2 else -3

/-! ## Unary tables -/

/-- The implementation's image of every blade under the unary operation `op` is
the spec term `k a · e_{f a}`. -/
def UnaryAgrees (V : TensorBundle) (op : UnOp) (f : BitVec n → BitVec n) (k : BitVec n → Rat) : Prop :=
  ∀ a : BitVec n, Matches (V.terms₁ op (mask a)) (f a) (k a) = true

/-- The same for the container-level unary rules of the reference kernels
(`Grassmann.Kernel.unTermsC`, which differ from the blade rules only in
conformal spaces). -/
def UnaryAgreesC (V : TensorBundle) (op : UnOp) (f : BitVec n → BitVec n) (k : BitVec n → Rat) : Prop :=
  ∀ a : BitVec n, Matches (Grassmann.Kernel.unTermsC V op (mask a)) (f a) (k a) = true

/-- The complement-sign-and-metric coefficient of the Hodge star on blade `a`. -/
def hodgeCoef (g : Fin n → Rat) (a : BitVec n) : Rat := signOf (sign a (~~~a)) * mf g a

/-- All unary checks of one space: reversion, grade involution, right
complement and Hodge star, at blade and container level. -/
def UnaryTables (V : TensorBundle) (g : Fin n → Rat) : Prop :=
  UnaryAgrees V .reverse id (revSign (R := Rat) (n := n)) ∧
  UnaryAgrees V .involute id (invSign (R := Rat) (n := n)) ∧
  UnaryAgrees V .complementright (fun a : BitVec n => ~~~a) (fun a => signOf (sign a (~~~a))) ∧
  UnaryAgrees V .complementrighthodge (fun a : BitVec n => ~~~a) (hodgeCoef g) ∧
  UnaryAgreesC V .complementright (fun a : BitVec n => ~~~a) (fun a => signOf (sign a (~~~a))) ∧
  UnaryAgreesC V .complementrighthodge (fun a : BitVec n => ~~~a) (hodgeCoef g)

/-! ## Plans -/

/-- The entries `(ia, ib, ic, coef)` of the reference kernel's plan for `op`
between two full multivectors (storage positions, Julia's `indexbasis` order). -/
def planEntries (V : TensorBundle) (op : BinOp) : List (Nat × Nat × Nat × Rat) :=
  match Grassmann.Kernel.build { V, op := .bin op, la := .full, lb := .full, lc := .full } with
  | .ok p => p.entries.toList
  | .error _ => []

/-- The spec's product table `e_a ⋆ e_b = k(a,b) e_{a⊕b}` as a gather-form plan in
the storage order of full multivectors: for every output position `ic`, every
operand pair `(ia, ib)` landing there with a nonzero coefficient, in operand
order. -/
def specPlan (n : Nat) (k : BitVec n → BitVec n → Rat) : List (Nat × Nat × Nat × Rat) :=
  let bl := Leibniz.indexBasisAll n
  let blade := fun (i : Nat) => BitVec.ofNat n (bl[i]!).toNat
  let N := 2 ^ n
  (List.range N).flatMap fun ic => (List.range N).flatMap fun ia => (List.range N).filterMap fun ib =>
    if blade ia ^^^ blade ib = blade ic ∧ k (blade ia) (blade ib) ≠ 0 then
      some (ia, ib, ic, k (blade ia) (blade ib))
    else none

/-! ## ℝ2 -/

theorem R2_mul_table : TableAgrees ℝ2 .mul (coef (gEuclid 2)) := by unfold TableAgrees; decide +kernel
/-- `ℝ2`: the exterior-product table is the spec's. -/
theorem R2_wedge_table : TableAgrees ℝ2 .wedge (wcoef (R := Rat) (n := 2)) := by
  unfold TableAgrees; decide +kernel
/-- `ℝ2`: reversion, involution, complement and Hodge tables are the spec's. -/
theorem R2_unary : UnaryTables ℝ2 (gEuclid 2) := by
  unfold UnaryTables UnaryAgrees UnaryAgreesC; decide +kernel
/-- `ℝ2`: the reference `Multivector × Multivector` plan is the spec table. -/
theorem R2_mul_plan : planEntries ℝ2 .mul = specPlan 2 (coef (gEuclid 2)) := by decide +kernel

/-- `ℝ2`: the implementation's geometric product is the spec product on all multivectors. -/
theorem R2_mul (x y : Cl (gEuclid 2)) : implMul ℝ2 x y = x * y := implMul_eq_mul (by decide) R2_mul_table x y

/-! ## ℝ3 -/

theorem R3_mul_table : TableAgrees ℝ3 .mul (coef (gEuclid 3)) := by unfold TableAgrees; decide +kernel
/-- `ℝ3`: the exterior-product table is the spec's. -/
theorem R3_wedge_table : TableAgrees ℝ3 .wedge (wcoef (R := Rat) (n := 3)) := by
  unfold TableAgrees; decide +kernel
/-- `ℝ3`: reversion, involution, complement and Hodge tables are the spec's. -/
theorem R3_unary : UnaryTables ℝ3 (gEuclid 3) := by
  unfold UnaryTables UnaryAgrees UnaryAgreesC; decide +kernel
/-- `ℝ3`: the reference `Multivector × Multivector` plan is the spec table. -/
theorem R3_mul_plan : planEntries ℝ3 .mul = specPlan 3 (coef (gEuclid 3)) := by decide +kernel
/-- `ℝ3`: the reference exterior-product plan is the spec table. -/
theorem R3_wedge_plan : planEntries ℝ3 .wedge = specPlan 3 (wcoef (R := Rat)) := by decide +kernel

/-- `ℝ3`: the implementation's geometric product is the spec product on all multivectors. -/
theorem R3_mul (x y : Cl (gEuclid 3)) : implMul ℝ3 x y = x * y := implMul_eq_mul (by decide) R3_mul_table x y

/-- `ℝ3`: the implementation's exterior product is the spec exterior product. -/
theorem R3_wedge (x y : Cl (gEuclid 3)) : implWedge ℝ3 x y = Cl.wedge x y :=
  implWedge_eq_wedge (by decide) R3_wedge_table x y

/-! ## STA -/

theorem STA_mul_table : TableAgrees STA .mul (coef gSTA) := by unfold TableAgrees; decide +kernel
/-- `STA`: the exterior-product table is the spec's. -/
theorem STA_wedge_table : TableAgrees STA .wedge (wcoef (R := Rat) (n := 4)) := by
  unfold TableAgrees; decide +kernel
/-- `STA`: reversion, involution, complement and Hodge tables are the spec's. -/
theorem STA_unary : UnaryTables STA gSTA := by
  unfold UnaryTables UnaryAgrees UnaryAgreesC; decide +kernel
/-- `STA`: the reference `Multivector × Multivector` plan is the spec table. -/
theorem STA_mul_plan : planEntries STA .mul = specPlan 4 (coef gSTA) := by decide +kernel

/-- `STA`: the implementation's geometric product is the spec product on all multivectors. -/
theorem STA_mul (x y : Cl gSTA) : implMul STA x y = x * y := implMul_eq_mul (by decide) STA_mul_table x y

/-- `STA`: the implementation's exterior product is the spec exterior product. -/
theorem STA_wedge (x y : Cl gSTA) : implWedge STA x y = Cl.wedge x y :=
  implWedge_eq_wedge (by decide) STA_wedge_table x y

/-! ## PGA2 and PGA3 (degenerate metrics) -/

theorem PGA2_mul_table : TableAgrees PGA2 .mul (coef (gPGA 3)) := by unfold TableAgrees; decide +kernel
/-- `PGA2`: reversion, involution, complement and Hodge tables are the spec's. -/
theorem PGA2_unary : UnaryTables PGA2 (gPGA 3) := by
  unfold UnaryTables UnaryAgrees UnaryAgreesC; decide +kernel

/-- `PGA3`: the geometric-product table is the spec's (degenerate `e₁² = 0`). -/
theorem PGA3_mul_table : TableAgrees PGA3 .mul (coef (gPGA 4)) := by unfold TableAgrees; decide +kernel
/-- `PGA3`: the exterior-product table is the spec's. -/
theorem PGA3_wedge_table : TableAgrees PGA3 .wedge (wcoef (R := Rat) (n := 4)) := by
  unfold TableAgrees; decide +kernel
/-- `PGA3`: reversion, involution, complement and Hodge tables are the spec's. -/
theorem PGA3_unary : UnaryTables PGA3 (gPGA 4) := by
  unfold UnaryTables UnaryAgrees UnaryAgreesC; decide +kernel
/-- `PGA3`: the reference `Multivector × Multivector` plan is the spec table. -/
theorem PGA3_mul_plan : planEntries PGA3 .mul = specPlan 4 (coef (gPGA 4)) := by decide +kernel

/-- `PGA3`: the implementation's geometric product is the spec product (with the
degenerate `e₀² = 0`) on all multivectors. -/
theorem PGA3_mul (x y : Cl (gPGA 4)) : implMul PGA3 x y = x * y := implMul_eq_mul (by decide) PGA3_mul_table x y

/-! ## A general diagonal form -/

theorem D123_mul_table : TableAgrees D!"1,2,-3" .mul (coef gD123) := by unfold TableAgrees; decide +kernel
/-- `D!"1,2,-3"`: reversion, involution, complement and Hodge tables are the spec's. -/
theorem D123_unary : UnaryTables D!"1,2,-3" gD123 := by
  unfold UnaryTables UnaryAgrees UnaryAgreesC; decide +kernel
/-- `D!"1,2,-3"`: the reference `Multivector × Multivector` plan is the spec table. -/
theorem D123_mul_plan : planEntries D!"1,2,-3" .mul = specPlan 3 (coef gD123) := by decide +kernel

/-- `D!"1,2,-3"`: the implementation's geometric product is the spec product. -/
theorem D123_mul (x y : Cl gD123) : implMul D!"1,2,-3" x y = x * y :=
  implMul_eq_mul (by decide) D123_mul_table x y

/-! ## Contraction and regressive product -/

theorem R2_contraction_table : TableAgrees ℝ2 .contraction (ccoef (gEuclid 2)) := by
  unfold TableAgrees; decide +kernel
/-- `ℝ3`: the contraction table is the spec's. -/
theorem R3_contraction_table : TableAgrees ℝ3 .contraction (ccoef (gEuclid 3)) := by
  unfold TableAgrees; decide +kernel
/-- `STA`: the contraction table is the spec's. -/
theorem STA_contraction_table : TableAgrees STA .contraction (ccoef gSTA) := by
  unfold TableAgrees; decide +kernel
/-- `PGA2`: the contraction table is the spec's. -/
theorem PGA2_contraction_table : TableAgrees PGA2 .contraction (ccoef (gPGA 3)) := by
  unfold TableAgrees; decide +kernel
/-- `PGA3`: the contraction table is the spec's. -/
theorem PGA3_contraction_table : TableAgrees PGA3 .contraction (ccoef (gPGA 4)) := by
  unfold TableAgrees; decide +kernel
/-- `D!"1,2,-3"`: the contraction table is the spec's. -/
theorem D123_contraction_table : TableAgrees D!"1,2,-3" .contraction (ccoef gD123) := by
  unfold TableAgrees; decide +kernel

/-- `ℝ3`: the implementation's contraction `⋅` is the spec contraction `⟨~y x⟩`
on all multivectors. -/
theorem R3_contract (x y : Cl (gEuclid 3)) : implContract ℝ3 x y = Cl.contract x y :=
  implContract_eq_contract (by decide) R3_contraction_table x y

/-- `STA`: the implementation's contraction is the spec contraction. -/
theorem STA_contract (x y : Cl gSTA) : implContract STA x y = Cl.contract x y :=
  implContract_eq_contract (by decide) STA_contraction_table x y

/-- `PGA3`: the implementation's contraction is the spec contraction (degenerate
factors included). -/
theorem PGA3_contract (x y : Cl (gPGA 4)) : implContract PGA3 x y = Cl.contract x y :=
  implContract_eq_contract (by decide) PGA3_contraction_table x y

end Grassmann.Proofs
