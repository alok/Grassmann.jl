/-
Correctness of the dynamic layer's arithmetic (DESIGN.md §4.3, §8 target 2):
the dense value commutes with `+`, `-`, negation and the scalar actions,

  `toDense (a + b) = toDense a + toDense b`,  `toDense (-a) = -toDense a`,
  `toDense (a - b) = toDense a - toDense b`,  `toDense (s • a) = s • toDense a`,

for well-formed linear elements (`TA.WF`: not `∞`, not a `Phasor`, blades of `V`)
over any coefficient type whose `Coeff` operations satisfy the commutative-ring laws
used (`LawfulCoeff`; instances for `Int` and `Rat`, and from any
`Lean.Grind.CommRing` whose operations are `Coeff`'s). One proof covers every branch
of Julia's representation lattice: whichever constructor a sum lands in, it holds
the right element. The index-table facts the proofs need are `LayoutInv V.n`,
kernel-checked for `n ≤ 8` (`Grassmann.Dynamic.Layout`).
-/
import Grassmann.Dynamic.Arith
import Grassmann.Dynamic.Layout

namespace Grassmann

open DirectSum DirectSum.Bits StaticVectors AbstractTensors

/-! ## Coefficient laws -/

/-- The laws of a commutative ring that the dense-value theorems use, stated for the
operations of `Coeff α`. -/
class LawfulCoeff (α : Type) [Coeff α] : Prop where
  /-- `x + 0 = x`. -/
  add_zero : ∀ x : α, x + Coeff.zero = x
  /-- `0 + x = x`. -/
  zero_add : ∀ x : α, Coeff.zero + x = x
  /-- `x + y = y + x`. -/
  add_comm : ∀ x y : α, x + y = y + x
  /-- `(x + y) + z = x + (y + z)`. -/
  add_assoc : ∀ x y z : α, x + y + z = x + (y + z)
  /-- `-0 = 0`. -/
  neg_zero : -(Coeff.zero : α) = Coeff.zero
  /-- `-(x + y) = -x + -y`. -/
  neg_add : ∀ x y : α, -(x + y) = -x + -y
  /-- `x - y = x + -y`. -/
  sub_eq_add_neg : ∀ x y : α, x - y = x + -y
  /-- `s·0 = 0`. -/
  mul_zero : ∀ s : α, s * Coeff.zero = Coeff.zero
  /-- `0·s = 0`. -/
  zero_mul : ∀ s : α, Coeff.zero * s = Coeff.zero
  /-- `s·(x + y) = s·x + s·y`. -/
  mul_add : ∀ s x y : α, s * (x + y) = s * x + s * y
  /-- `(x + y)·s = x·s + y·s`. -/
  add_mul : ∀ x y s : α, (x + y) * s = x * s + y * s
  /-- `s·1 = s`. -/
  mul_one : ∀ s : α, s * Coeff.one = s
  /-- `1·s = s`. -/
  one_mul : ∀ s : α, Coeff.one * s = s

attribute [simp] LawfulCoeff.add_zero LawfulCoeff.zero_add LawfulCoeff.neg_zero
  LawfulCoeff.mul_zero LawfulCoeff.zero_mul LawfulCoeff.mul_one LawfulCoeff.one_mul

/-- `+` of a lawful coefficient type is associative (for `ac_rfl`). -/
instance LawfulCoeff.instAssoc {α : Type} [Coeff α] [LawfulCoeff α] :
    Std.Associative (fun x y : α => x + y) := ⟨LawfulCoeff.add_assoc⟩

/-- `+` of a lawful coefficient type is commutative (for `ac_rfl`). -/
instance LawfulCoeff.instComm {α : Type} [Coeff α] [LawfulCoeff α] :
    Std.Commutative (fun x y : α => x + y) := ⟨LawfulCoeff.add_comm⟩

section CommRing

variable {α : Type} [Lean.Grind.CommRing α]

/-- The commutative-ring facts behind `LawfulCoeff.ofCommRing` (by `grind`). -/
private theorem commRing_laws :
    (∀ x : α, x + 0 = x) ∧ (∀ x : α, 0 + x = x) ∧ (∀ x y : α, x + y = y + x) ∧
    (∀ x y z : α, x + y + z = x + (y + z)) ∧ (-(0 : α) = 0) ∧ (∀ x y : α, -(x + y) = -x + -y) ∧
    (∀ x y : α, x - y = x + -y) ∧ (∀ s : α, s * 0 = 0) ∧ (∀ s : α, 0 * s = 0) ∧
    (∀ s x y : α, s * (x + y) = s * x + s * y) ∧ (∀ x y s : α, (x + y) * s = x * s + y * s) ∧
    (∀ s : α, s * 1 = s) ∧ (∀ s : α, 1 * s = s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> grind

end CommRing

/-- A `Coeff` structure whose operations are those of a `Lean.Grind.CommRing` is
lawful (the ring laws come from `grind`). -/
theorem LawfulCoeff.ofCommRing {α : Type} [c : Coeff α] [r : Lean.Grind.CommRing α]
    (zero : c.zero = 0) (one : c.one = 1)
    (add : ∀ x y : α, @HAdd.hAdd α α α (@instHAdd α c.toAdd) x y = @HAdd.hAdd α α α (@instHAdd α r.toAdd) x y)
    (neg : ∀ x : α, @Neg.neg α c.toNeg x = @Neg.neg α r.toNeg x)
    (sub : ∀ x y : α, @HSub.hSub α α α (@instHSub α c.toSub) x y = @HSub.hSub α α α (@instHSub α r.toSub) x y)
    (mul : ∀ x y : α, @HMul.hMul α α α (@instHMul α c.toMul) x y = @HMul.hMul α α α (@instHMul α r.toMul) x y) :
    LawfulCoeff α := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := commRing_laws (α := α)
  exact {
    add_zero := fun x => by simp only [add, zero]; exact h1 x
    zero_add := fun x => by simp only [add, zero]; exact h2 x
    add_comm := fun x y => by simp only [add]; exact h3 x y
    add_assoc := fun x y z => by simp only [add]; exact h4 x y z
    neg_zero := by simp only [neg, zero]; exact h5
    neg_add := fun x y => by simp only [add, neg]; exact h6 x y
    sub_eq_add_neg := fun x y => by simp only [add, neg, sub]; exact h7 x y
    mul_zero := fun s => by simp only [mul, zero]; exact h8 s
    zero_mul := fun s => by simp only [mul, zero]; exact h9 s
    mul_add := fun s x y => by simp only [add, mul]; exact h10 s x y
    add_mul := fun x y s => by simp only [add, mul]; exact h11 x y s
    mul_one := fun s => by simp only [mul, one]; exact h12 s
    one_mul := fun s => by simp only [mul, one]; exact h13 s }

instance : LawfulCoeff Int :=
  LawfulCoeff.ofCommRing rfl rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance : LawfulCoeff Rat :=
  LawfulCoeff.ofCommRing rfl rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

namespace TA

variable {V : TensorBundle} {α : Type} [Coeff α]

/-! ## Well-formed elements and the dense entries -/

/-- A well-formed linear element: not `∞` or a `Phasor` (no dense value), and every
stored blade is a blade of `V`. -/
def WF : TA V α → Prop
  | zero | one => True
  | infinity | phasor .. => False
  | blade b | single b _ | couple b .. | pseudo b .. => valid V b = true
  | chain .. | spinor _ | cospinor _ | multi _ => True

/-- Entry `i` of the dense value. -/
def dget (x : TA V α) (i : Fin (2 ^ V.n)) : α := x.toDense.v.get i

/-- The dense value is determined by its entries. -/
theorem toDense_ext {x y : TA V α} (h : ∀ i, x.dget i = y.dget i) : x.toDense = y.toDense := by
  have : x.toDense.v = y.toDense.v := Values.ext h
  cases hx : x.toDense; cases hy : y.toDense; simp_all

/-- The entries of a multivector. -/
@[simp] theorem dget_multi (m : Multivector V α) (i : Fin (2 ^ V.n)) : (multi m).dget i = m.v.get i := rfl

/-- The entries of any other kind are its coefficients on the blades of the layout. -/
theorem dget_eq_coeff (x : TA V α) (hx : ∀ m, x ≠ multi m) (i : Fin (2 ^ V.n)) :
    x.dget i = x.coeff (fullBlade V.n i.1) := by
  cases x <;> first | exact absurd rfl (hx _) | simp [dget, toDense, Multivector.ofFn]

/-! ## Layout facts -/

/-- Membership in a chain layout: a blade of `V` of grade `g`. -/
theorem contains_chain (n g : Nat) (β : UInt64) :
    (Layout.chain g).contains n β = (Layout.full.contains n β && popcount β == g) := by
  simp [Layout.contains]

/-- Membership in a half layout: a blade of `V` of parity `p`. -/
theorem contains_half (n : Nat) (p : Bool) (β : UInt64) :
    (halfLayout p).contains n β = (Layout.full.contains n β && (popcount β % 2 == 1) == p) := by
  rcases Nat.mod_two_eq_zero_or_one (popcount β) with h | h <;> cases p <;> simp [halfLayout, Layout.contains, h]

/-- A blade of a chain layout round-trips. -/
theorem roundTrip_chain (hL : LayoutInv V.n) {g : Nat} {β : UInt64}
    (h : (Layout.chain g).contains V.n β = true) : RoundTrip V.n (.chain g) β := by
  rw [contains_chain, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2 ▸ (hL.2 β h.1).1

/-- A blade of a half layout round-trips. -/
theorem roundTrip_half (hL : LayoutInv V.n) {p : Bool} {β : UInt64}
    (h : (halfLayout p).contains V.n β = true) : RoundTrip V.n (halfLayout p) β := by
  rw [contains_half, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2 ▸ (hL.2 β h.1).2.1

/-- Reading back a vector built from the layout's blades at a round-tripping blade. -/
theorem getD_ofFn_blades {L : Layout} {β : UInt64} (h : RoundTrip V.n L β) (f : UInt64 → α) :
    getD (Values.ofFn (n := L.size V.n) fun j => f ((L.blades V.n)[j.1]!)) (L.rank V.n β) = f β := by
  unfold getD; simp [h.1, h.2]

/-- The coefficients of `chainOf`. -/
theorem coeff_chainOf (hL : LayoutInv V.n) (g : Nat) (f : UInt64 → α) (β : UInt64) :
    (chainOf V g f).coeff β = if (Layout.chain g).contains V.n β then f β else Coeff.zero := by
  unfold chainOf Chain.coeff Chain.ofFn
  split
  · rename_i h; exact getD_ofFn_blades (L := .chain g) (roundTrip_chain hL h) f
  · rfl

/-- The coefficients of `halfOf`. -/
theorem coeff_halfOf (hL : LayoutInv V.n) (p : Bool) (f : UInt64 → α) (β : UInt64) :
    (halfOf V p f).coeff β = if (halfLayout p).contains V.n β then f β else Coeff.zero := by
  unfold halfOf Half.coeff Half.ofFn
  split
  · rename_i h; exact getD_ofFn_blades (L := halfLayout p) (roundTrip_half hL h) f
  · rfl

/-- The entries of `multiOf`. -/
@[simp] theorem dget_multiOf (f : UInt64 → α) (i : Fin (2 ^ V.n)) :
    (multi (multiOf V f)).dget i = f (fullBlade V.n i.1) := by
  simp [multiOf, Multivector.ofFn]

/-- Reading a converted vector at a round-tripping blade of the target layout. -/
theorem getD_convertLayout {la lc : Layout} {β : UInt64} (h : RoundTrip V.n lc β)
    (x : Values α (la.size V.n)) :
    getD (convertLayout V.n la lc x) (lc.rank V.n β) =
      if la.contains V.n β then getD x (la.rank V.n β) else Coeff.zero :=
  getD_ofFn_blades h (fun b => if la.contains V.n b then getD x (la.rank V.n b) else Coeff.zero)

/-! ## Coefficients of the static containers -/

/-- A chain's coefficient is `0` off its layout. -/
theorem Chain_coeff_of_not {g : Nat} (c : Chain V g α) {β : UInt64}
    (h : (Layout.chain g).contains V.n β = false) : c.coeff β = Coeff.zero := by
  simp [Chain.coeff, h]

/-- A half's coefficient is `0` off its layout. -/
theorem Half_coeff_of_not {p : Bool} (c : Half V p α) {β : UInt64}
    (h : (halfLayout p).contains V.n β = false) : c.coeff β = Coeff.zero := by
  simp [Half.coeff, h]

/-- Entries of `multiAddAt`: `x` is added at `X`. -/
@[simp] theorem dget_multiAddAt (m : Multivector V α) (X : UInt64) (x : α) (i : Fin (2 ^ V.n)) :
    (multi (multiAddAt m X x)).dget i =
      if fullBlade V.n i.1 == X then m.v.get i + x else m.v.get i := by
  simp [multiAddAt, Multivector.ofFn]

/-! ## Blade facts -/

/-- `0` is a blade of every space. -/
@[simp] theorem valid_zero : valid V 0 = true := by simp [valid, Layout.contains]

/-- The pseudoscalar is a blade of every space. -/
@[simp] theorem valid_pseudoBits : valid V (pseudoBits V) = true := by
  simp [valid, pseudoBits, Layout.contains]

/-- `popcount 0 = 0`. -/
@[simp] theorem popcount_zero : popcount 0 = 0 := by decide

/-- The only grade-0 blade is `0`. -/
theorem eq_zero_of_popcount (hL : LayoutInv V.n) {A : UInt64} (hA : valid V A = true)
    (h : popcount A = 0) : A = 0 := (hL.2 A hA).2.2.1 h

/-- The only grade-`n` blade is the pseudoscalar. -/
theorem eq_top_of_popcount (hL : LayoutInv V.n) {A : UInt64} (hA : valid V A = true)
    (h : popcount A = V.n) : A = pseudoBits V := ((hL.2 A hA).2.2.2 h).1

/-- The pseudoscalar has grade `n`. -/
theorem popcount_pseudoBits (hL : LayoutInv V.n) : popcount (pseudoBits V) = V.n := hL.1

/-- The pseudoscalar is at rank `0` of its chain. -/
theorem bladeRank_pseudoBits (hL : LayoutInv V.n) : Leibniz.bladeRank V.n (pseudoBits V) = 0 :=
  ((hL.2 _ valid_pseudoBits).2.2.2 hL.1).2

/-- Without tangent generators the pseudoscalar grade is `n`. -/
theorem grade_of_coupleOK (h : coupleOK V = true) : V.grade = V.n := by
  simp only [coupleOK, Bool.and_eq_true, Bool.not_eq_true'] at h
  simp only [TensorBundle.istangent, bne_eq_false_iff_eq] at h
  simp [TensorBundle.grade, TensorBundle.tangentSlots, h.1]

/-- A blade of `V` whose chain layout contains `β` has its grade. -/
theorem popcount_of_contains_chain {g : Nat} {β : UInt64}
    (h : (Layout.chain g).contains V.n β = true) : popcount β = g := by
  rw [contains_chain, Bool.and_eq_true, beq_iff_eq] at h; exact h.2

/-! ## Entries of every kind -/

@[simp] theorem dget_zero (i : Fin (2 ^ V.n)) : (zero : TA V α).dget i = Coeff.zero :=
  dget_eq_coeff _ (by simp) i

@[simp] theorem dget_one (i : Fin (2 ^ V.n)) :
    (one : TA V α).dget i = if fullBlade V.n i.1 == 0 then Coeff.one else Coeff.zero :=
  dget_eq_coeff _ (by simp) i

@[simp] theorem dget_blade (b : UInt64) (i : Fin (2 ^ V.n)) :
    (blade b : TA V α).dget i = if fullBlade V.n i.1 == b && valid V b then Coeff.one else Coeff.zero :=
  dget_eq_coeff _ (by simp) i

@[simp] theorem dget_single (b : UInt64) (x : α) (i : Fin (2 ^ V.n)) :
    (single b x : TA V α).dget i = if fullBlade V.n i.1 == b && valid V b then x else Coeff.zero :=
  dget_eq_coeff _ (by simp) i

@[simp] theorem dget_chain {g : Nat} (c : Chain V g α) (i : Fin (2 ^ V.n)) :
    (chain g c).dget i = c.coeff (fullBlade V.n i.1) :=
  dget_eq_coeff _ (by simp) i

@[simp] theorem dget_spinor (h : Spinor V α) (i : Fin (2 ^ V.n)) :
    (spinor h).dget i = h.coeff (fullBlade V.n i.1) :=
  dget_eq_coeff _ (by simp) i

@[simp] theorem dget_cospinor (h : CoSpinor V α) (i : Fin (2 ^ V.n)) :
    (cospinor h).dget i = h.coeff (fullBlade V.n i.1) :=
  dget_eq_coeff _ (by simp) i

@[simp] theorem dget_couple (b : UInt64) (re im : α) (i : Fin (2 ^ V.n)) :
    (couple b re im : TA V α).dget i =
      if fullBlade V.n i.1 == 0 then (if b == 0 then re + im else re)
      else if fullBlade V.n i.1 == b && valid V b then im else Coeff.zero :=
  dget_eq_coeff _ (by simp) i

@[simp] theorem dget_pseudo (b : UInt64) (re im : α) (i : Fin (2 ^ V.n)) :
    (pseudo b re im : TA V α).dget i =
      if fullBlade V.n i.1 == b && valid V b then (if b == pseudoBits V then re + im else re)
      else if fullBlade V.n i.1 == pseudoBits V then im else Coeff.zero :=
  dget_eq_coeff _ (by simp) i

/-- Entries of a static chain embedded as a multivector. -/
@[simp] theorem dget_toMultivector_chain {g : Nat} (c : Chain V g α) (i : Fin (2 ^ V.n)) :
    (multi (toMultivector c)).dget i = c.coeff (fullBlade V.n i.1) := by
  simp only [dget_multi, toMultivector, convertLayout, layoutOf, DenseLayout.layout,
    DenseLayout.values, Chain.coeff, fullBlade, Layout.blades, Layout.rank]
  exact Values.get_ofFn _ _

/-- Entries of a static half embedded as a multivector. -/
@[simp] theorem dget_toMultivector_half {p : Bool} (c : Half V p α) (i : Fin (2 ^ V.n)) :
    (multi (toMultivector c)).dget i = c.coeff (fullBlade V.n i.1) := by
  simp only [dget_multi, toMultivector, convertLayout, layoutOf, DenseLayout.layout,
    DenseLayout.values, Half.coeff, fullBlade, Layout.blades]
  exact Values.get_ofFn _ _

/-- A chain as the half of its parity keeps its coefficients. -/
theorem coeff_halfOfChain (hL : LayoutInv V.n) {g : Nat} (c : Chain V g α) (β : UInt64) :
    (Half.ofChain c).coeff β = c.coeff β := by
  by_cases h : (halfLayout (g % 2 == 1)).contains V.n β
  · have rt := roundTrip_half hL h
    simp only [Half.ofChain, Half.coeff, h, ite_true]
    exact (getD_convertLayout (la := .chain g) rt c.v).trans rfl
  · simp only [Bool.not_eq_true] at h
    rw [Half_coeff_of_not _ h]
    by_cases hc : (Layout.chain g).contains V.n β
    · rw [contains_chain] at hc; rw [contains_half] at h
      simp_all
    · simp only [Bool.not_eq_true] at hc; rw [Chain_coeff_of_not _ hc]

variable [LawfulCoeff α]

/-- Coefficients of a sum of chains. -/
theorem Chain_coeff_add {g : Nat} (c d : Chain V g α) (β : UInt64) :
    (c + d).coeff β = c.coeff β + d.coeff β := by
  show (⟨c.v + d.v⟩ : Chain V g α).coeff β = _
  unfold Chain.coeff getD
  split
  · split <;> simp_all
  · simp

/-- Coefficients of a sum of halves. -/
theorem Half_coeff_add {p : Bool} (c d : Half V p α) (β : UInt64) :
    (c + d).coeff β = c.coeff β + d.coeff β := by
  show (⟨c.v + d.v⟩ : Half V p α).coeff β = _
  unfold Half.coeff getD
  split
  · split <;> simp_all
  · simp

/-- Coefficients of a negated chain. -/
theorem Chain_coeff_neg {g : Nat} (c : Chain V g α) (β : UInt64) : (-c).coeff β = -c.coeff β := by
  show (⟨-c.v⟩ : Chain V g α).coeff β = _
  unfold Chain.coeff getD
  split
  · split <;> simp_all
  · simp

/-- Coefficients of a negated half. -/
theorem Half_coeff_neg {p : Bool} (c : Half V p α) (β : UInt64) : (-c).coeff β = -c.coeff β := by
  show (⟨-c.v⟩ : Half V p α).coeff β = _
  unfold Half.coeff getD
  split
  · split <;> simp_all
  · simp

/-- Coefficients of a chain scaled on the left. -/
theorem Chain_coeff_smul {g : Nat} (s : α) (c : Chain V g α) (β : UInt64) :
    (⟨c.v.map (s * ·)⟩ : Chain V g α).coeff β = s * c.coeff β := by
  unfold Chain.coeff getD
  split
  · split <;> simp_all
  · simp

/-- Coefficients of a half scaled on the left. -/
theorem Half_coeff_smul {p : Bool} (s : α) (c : Half V p α) (β : UInt64) :
    (⟨c.v.map (s * ·)⟩ : Half V p α).coeff β = s * c.coeff β := by
  unfold Half.coeff getD
  split
  · split <;> simp_all
  · simp

/-- Coefficients of a chain scaled on the right. -/
theorem Chain_coeff_mulr {g : Nat} (s : α) (c : Chain V g α) (β : UInt64) :
    (⟨c.v.map (· * s)⟩ : Chain V g α).coeff β = c.coeff β * s := by
  unfold Chain.coeff getD
  split
  · split <;> simp_all
  · simp

/-- Coefficients of a half scaled on the right. -/
theorem Half_coeff_mulr {p : Bool} (s : α) (c : Half V p α) (β : UInt64) :
    (⟨c.v.map (· * s)⟩ : Half V p α).coeff β = c.coeff β * s := by
  unfold Half.coeff getD
  split
  · split <;> simp_all
  · simp

omit [LawfulCoeff α] in
/-- Coefficients of `chainAddAt`: `x` is added at `X`. -/
theorem coeff_chainAddAt (hL : LayoutInv V.n) {g : Nat} (c : Chain V g α) (X : UInt64) (x : α)
    (β : UInt64) :
    (chainAddAt c X x).coeff β =
      if β == X && (Layout.chain g).contains V.n β then c.coeff β + x else c.coeff β := by
  by_cases h : (Layout.chain g).contains V.n β
  · have rt := roundTrip_chain hL h
    have h1 : Leibniz.bladeRank V.n β < Leibniz.binomial V.n g := rt.1
    have h2 : (Leibniz.indexBasis V.n g)[Leibniz.bladeRank V.n β]! = β := rt.2
    simp only [chainAddAt, Chain.coeff, Chain.ofFn, h, Bool.and_true, ite_true, getD]
    simp [h1, h2]
  · simp only [Bool.not_eq_true] at h
    simp [Chain.coeff, h]

omit [LawfulCoeff α] in
/-- Coefficients of `halfAddAt`: `x` is added at `X`. -/
theorem coeff_halfAddAt (hL : LayoutInv V.n) {p : Bool} (c : Half V p α) (X : UInt64) (x : α)
    (β : UInt64) :
    (halfAddAt c X x).coeff β =
      if β == X && (halfLayout p).contains V.n β then c.coeff β + x else c.coeff β := by
  by_cases h : (halfLayout p).contains V.n β
  · have rt := roundTrip_half hL h
    have h1 : Layout.rank V.n (halfLayout p) β < halfDim V.n p := rt.1
    simp only [halfAddAt, Half.coeff, Half.ofFn, h, Bool.and_true, ite_true, getD]
    simp [h1, rt.2]
  · simp only [Bool.not_eq_true] at h
    simp [Half.coeff, h]

/-! ## Sums of terms -/

/-- `twoTerms` at a blade. -/
theorem twoTerms_eq (A : UInt64) (x : α) (B : UInt64) (y : α) (β : UInt64) (hAB : A ≠ B) :
    twoTerms A x B y β = (if β == A then x else Coeff.zero) + (if β == B then y else Coeff.zero) := by
  unfold twoTerms
  by_cases h1 : β = A <;> by_cases h2 : β = B <;> simp_all

/-- The sum of two terms (Julia `adder`) has the dense value of the sum. -/
theorem dget_addTermTerm (hL : LayoutInv V.n) {A B : UInt64} (hA : valid V A = true)
    (hB : valid V B = true) (x y : α) (i : Fin (2 ^ V.n)) :
    (addTermTerm A x B y : TA V α).dget i = (single A x : TA V α).dget i + (single B y).dget i := by
  have hA' : Layout.full.contains V.n A = true := hA
  have hB' : Layout.full.contains V.n B = true := hB
  generalize hR : (single A x : TA V α).dget i + (single B y).dget i = R
  unfold addTermTerm; dsimp only
  split
  · rename_i h; simp only [beq_iff_eq] at h; subst h; subst hR
    simp only [dget_single, hA, Bool.and_true]
    split <;> simp
  rename_i hAB; simp only [beq_iff_eq] at hAB
  subst hR
  simp only [dget_single, hA, hB, Bool.and_true]
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    have hA0 : A = 0 := eq_zero_of_popcount hL hA h.2
    subst hA0
    have hB0 : B ≠ 0 := fun e => hAB e.symm
    simp only [dget_couple, hB, Bool.and_true]
    generalize fullBlade V.n i.1 = β
    by_cases h1 : β = 0 <;> by_cases h2 : β = B <;> simp_all
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    have hB0 : B = 0 := eq_zero_of_popcount hL hB h.2
    subst hB0
    simp only [dget_couple, hA, Bool.and_true]
    generalize fullBlade V.n i.1 = β
    by_cases h1 : β = 0 <;> by_cases h2 : β = A <;> simp_all
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    have hAI : A = pseudoBits V := eq_top_of_popcount hL hA (h.2.trans (grade_of_coupleOK h.1))
    subst hAI
    have hBI : B ≠ pseudoBits V := fun e => hAB e.symm
    simp only [dget_pseudo, hB, Bool.and_true]
    generalize fullBlade V.n i.1 = β
    by_cases h1 : β = B <;> by_cases h2 : β = pseudoBits V <;> simp_all
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    have hBI : B = pseudoBits V := eq_top_of_popcount hL hB (h.2.trans (grade_of_coupleOK h.1))
    subst hBI
    simp only [dget_pseudo, hA, Bool.and_true]
    generalize fullBlade V.n i.1 = β
    by_cases h1 : β = A <;> by_cases h2 : β = pseudoBits V <;> simp_all
  split
  · rename_i h
    simp only [beq_iff_eq] at h
    simp only [dget_chain, coeff_chainOf hL, contains_chain, twoTerms_eq A x B y _ hAB]
    generalize fullBlade V.n i.1 = β
    by_cases h1 : β = A <;> by_cases h2 : β = B <;> simp_all
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    simp only [dget_spinor, coeff_halfOf hL, contains_half, twoTerms_eq A x B y _ hAB]
    generalize fullBlade V.n i.1 = β
    by_cases h1 : β = A <;> by_cases h2 : β = B <;> simp_all
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    simp only [dget_cospinor, coeff_halfOf hL, contains_half, twoTerms_eq A x B y _ hAB]
    generalize fullBlade V.n i.1 = β
    by_cases h1 : β = A <;> by_cases h2 : β = B <;> simp_all
  · simp only [dget_multiOf, twoTerms_eq A x B y _ hAB]

/-! ## Sums with chains -/

omit [LawfulCoeff α] in
/-- A chain has no coefficient off its grade. -/
theorem Chain_coeff_of_popcount_ne {g : Nat} (c : Chain V g α) {β : UInt64} (h : popcount β ≠ g) :
    c.coeff β = Coeff.zero := by
  apply Chain_coeff_of_not
  rw [contains_chain]; simp [h]

omit [LawfulCoeff α] in
/-- A scalar chain lives on the scalar blade. -/
theorem Chain_coeff_zero_grade (hL : LayoutInv V.n) (c : Chain V 0 α) (β : UInt64) :
    c.coeff β = if β == 0 then getD c.v 0 else Coeff.zero := by
  by_cases h : (Layout.chain 0).contains V.n β
  · have rt := roundTrip_chain hL h
    have hv : Layout.full.contains V.n β = true := by rw [contains_chain] at h; simp_all
    have h0 : β = 0 := eq_zero_of_popcount hL hv (popcount_of_contains_chain h)
    subst h0
    have hr : Leibniz.bladeRank V.n 0 = 0 := by
      have := rt.1; simp only [Layout.size, Layout.rank] at this
      have h1 : Leibniz.choose V.n 0 = 1 := rfl
      omega
    simp [Chain.coeff, h, hr]
  · simp only [Bool.not_eq_true] at h
    rw [Chain_coeff_of_not _ h]
    have : β ≠ 0 := by
      rintro rfl; rw [contains_chain] at h
      simp [show Layout.full.contains V.n 0 = true from valid_zero] at h
    simp [this]

omit [LawfulCoeff α] in
/-- A top-grade chain lives on the pseudoscalar. -/
theorem Chain_coeff_top_grade (hL : LayoutInv V.n) {g : Nat} (hg : g = V.n) (c : Chain V g α)
    (β : UInt64) : c.coeff β = if β == pseudoBits V then getD c.v 0 else Coeff.zero := by
  subst hg
  by_cases h : (Layout.chain V.n).contains V.n β
  · have hv : Layout.full.contains V.n β = true := by rw [contains_chain] at h; simp_all
    have hI : β = pseudoBits V := eq_top_of_popcount hL hv (popcount_of_contains_chain h)
    subst hI
    simp [Chain.coeff, h, bladeRank_pseudoBits hL]
  · simp only [Bool.not_eq_true] at h
    rw [Chain_coeff_of_not _ h]
    have : β ≠ pseudoBits V := by
      rintro rfl; rw [contains_chain] at h
      simp [popcount_pseudoBits hL, show Layout.full.contains V.n (pseudoBits V) = true from
        valid_pseudoBits] at h
    simp [this]

/-- A term plus a chain (Julia `adder`) has the dense value of the sum. -/
theorem dget_addTermChain (hL : LayoutInv V.n) {A : UInt64} (hA : valid V A = true) (x : α) {G : Nat}
    (c : Chain V G α) (i : Fin (2 ^ V.n)) :
    (addTermChain A x c : TA V α).dget i = (single A x : TA V α).dget i + (chain G c).dget i := by
  have hA' : Layout.full.contains V.n A = true := hA
  generalize hR : (single A x : TA V α).dget i + (chain G c).dget i = R
  unfold addTermChain; dsimp only
  subst hR
  simp only [dget_single, dget_chain, hA, Bool.and_true]
  split
  · rename_i h; simp only [beq_iff_eq] at h; subst h
    simp only [dget_chain, coeff_chainAddAt hL, contains_chain]
    generalize fullBlade V.n i.1 = β
    by_cases h1 : β = A <;> simp_all [LawfulCoeff.add_comm]
  rename_i hLG; simp only [beq_iff_eq] at hLG
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    have hA0 : A = 0 := eq_zero_of_popcount hL hA h.1.2
    subst hA0
    have hI0 : pseudoBits V ≠ 0 := by
      intro e; have := popcount_pseudoBits hL; rw [e] at this; simp at this; omega
    simp only [dget_couple, Chain_coeff_top_grade hL h.2 c, valid_pseudoBits, Bool.and_true]
    generalize fullBlade V.n i.1 = β
    by_cases h1 : β = 0 <;> by_cases h2 : β = pseudoBits V <;> simp_all
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨_, hG⟩ := h
    subst hG
    have hA0 : A ≠ 0 := by rintro rfl; simp at hLG
    simp only [dget_couple, Chain_coeff_zero_grade hL c, hA, Bool.and_true]
    generalize fullBlade V.n i.1 = β
    by_cases h1 : β = 0 <;> by_cases h2 : β = A <;> simp_all
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    have hG : G = V.n := h.2.trans (grade_of_coupleOK h.1)
    have hAI : A ≠ pseudoBits V := by
      rintro rfl; exact hLG (popcount_pseudoBits hL |>.trans hG.symm)
    simp only [dget_pseudo, Chain_coeff_top_grade hL hG c, hA, Bool.and_true]
    generalize fullBlade V.n i.1 = β
    by_cases h1 : β = A <;> by_cases h2 : β = pseudoBits V <;> simp_all
  have hcA : c.coeff A = Coeff.zero := Chain_coeff_of_popcount_ne c hLG
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    simp only [dget_spinor, coeff_halfOf hL, contains_half]
    generalize fullBlade V.n i.1 = β
    by_cases h1 : β = A
    · simp_all
    · by_cases hc : (Layout.chain G).contains V.n β
      · have := popcount_of_contains_chain hc
        rw [contains_chain] at hc; simp_all
      · simp only [Bool.not_eq_true] at hc; simp [h1, Chain_coeff_of_not c hc]
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    simp only [dget_cospinor, coeff_halfOf hL, contains_half]
    generalize fullBlade V.n i.1 = β
    by_cases h1 : β = A
    · simp_all
    · by_cases hc : (Layout.chain G).contains V.n β
      · have := popcount_of_contains_chain hc
        rw [contains_chain] at hc; simp_all
      · simp only [Bool.not_eq_true] at hc; simp [h1, Chain_coeff_of_not c hc]
  · simp only [dget_multiOf]
    generalize fullBlade V.n i.1 = β
    by_cases h1 : β = A <;> simp_all

/-! ## Sums of containers -/

omit [LawfulCoeff α] in
/-- The entries of a sum of multivectors. -/
@[simp] theorem dget_multi_add (m w : Multivector V α) (i : Fin (2 ^ V.n)) :
    (multi (m + w)).dget i = m.v.get i + w.v.get i :=
  Values.get_add m.v w.v i

omit [LawfulCoeff α] in
/-- The entries of a half as a dynamic element. -/
@[simp] theorem dget_ofHalf {p : Bool} (h : Half V p α) (i : Fin (2 ^ V.n)) :
    (ofHalf h).dget i = h.coeff (fullBlade V.n i.1) := by
  cases p <;> simp [ofHalf]

omit [LawfulCoeff α] in
/-- Casting a half keeps its coefficients. -/
@[simp] theorem Half_coeff_cast {p q : Bool} (e : p = q) (h : Half V p α) (β : UInt64) :
    (h.cast e).coeff β = h.coeff β := by
  subst e; rfl

omit [LawfulCoeff α] in
/-- Casting a chain keeps its coefficients. -/
@[simp] theorem Chain_coeff_cast {g h : Nat} (e : g = h) (c : Chain V g α) (β : UInt64) :
    (c.cast e).coeff β = c.coeff β := by
  subst e; rfl

/-- The sum of two halves. -/
theorem dget_addHalves {p q : Bool} (a : Half V p α) (b : Half V q α) (i : Fin (2 ^ V.n)) :
    (addHalves a b).dget i = a.coeff (fullBlade V.n i.1) + b.coeff (fullBlade V.n i.1) := by
  unfold addHalves
  split
  · rename_i e; simp [Half_coeff_add]
  · rw [dget_multi_add, ← dget_multi, ← dget_multi, dget_toMultivector_half, dget_toMultivector_half]

omit [LawfulCoeff α] in
/-- `Single(c)` of a scalar chain. -/
theorem singleOfChain_zero (c : Chain V 0 α) : singleOfChain c = single 0 (getD c.v 0) := by
  simp [singleOfChain]

omit [LawfulCoeff α] in
/-- `Single(c)` of a top-grade chain. -/
theorem singleOfChain_top {G : Nat} (c : Chain V G α) (hG : G ≠ 0) :
    singleOfChain c = single (pseudoBits V) (getD c.v 0) := by
  simp [singleOfChain, hG]

omit [LawfulCoeff α] in
/-- `Single(c)` keeps the dense value of a scalar or top-grade chain. -/
theorem dget_singleOfChain (hL : LayoutInv V.n) {G : Nat} (c : Chain V G α) (hG : G = 0 ∨ G = V.n)
    (i : Fin (2 ^ V.n)) : (singleOfChain c).dget i = (chain G c).dget i := by
  by_cases h0 : G = 0
  · subst h0
    rw [singleOfChain_zero, dget_single, dget_chain, Chain_coeff_zero_grade hL]
    simp
  · have hn : G = V.n := hG.resolve_left h0
    rw [singleOfChain_top c h0, dget_single, dget_chain, Chain_coeff_top_grade hL hn]
    simp

/-- The sum of two chains (Julia `plus(::Chain, ::Chain)`). -/
theorem dget_addChains (hL : LayoutInv V.n) {G L : Nat} (a : Chain V G α) (b : Chain V L α)
    (i : Fin (2 ^ V.n)) : (addChains a b).dget i = (chain G a).dget i + (chain L b).dget i := by
  unfold addChains
  split
  · rename_i e; subst e; simp [Chain_coeff_add]
  rename_i hGL
  split
  · rename_i h
    have hG : G = 0 ∨ G = V.n := by simpa [Bool.or_eq_true, beq_iff_eq] using h
    by_cases h0 : G = 0
    · subst h0
      rw [singleOfChain_zero]; dsimp only
      rw [dget_addTermChain hL valid_zero, ← singleOfChain_zero, dget_singleOfChain hL a hG]
    · rw [singleOfChain_top a h0]; dsimp only
      rw [dget_addTermChain hL valid_pseudoBits, ← singleOfChain_top a h0,
        dget_singleOfChain hL a hG]
  split
  · rename_i h
    have hL' : L = 0 ∨ L = V.n := by simpa [Bool.or_eq_true, beq_iff_eq] using h
    rw [LawfulCoeff.add_comm]
    by_cases h0 : L = 0
    · subst h0
      rw [singleOfChain_zero]; dsimp only
      rw [dget_addTermChain hL valid_zero, ← singleOfChain_zero, dget_singleOfChain hL b hL']
    · rw [singleOfChain_top b h0]; dsimp only
      rw [dget_addTermChain hL valid_pseudoBits, ← singleOfChain_top b h0,
        dget_singleOfChain hL b hL']
  split
  · rw [dget_addHalves, coeff_halfOfChain hL, coeff_halfOfChain hL, dget_chain, dget_chain]
  · rw [dget_multi_add, ← dget_multi, ← dget_multi, dget_toMultivector_chain,
      dget_toMultivector_chain, dget_chain, dget_chain]

/-- The sum of two containers (chains, halves, multivectors). -/
theorem dget_addXX (hL : LayoutInv V.n) (a b : TA V α) (i : Fin (2 ^ V.n)) :
    (addXX a b).dget i = a.dget i + b.dget i := by
  unfold addXX
  split
  · exact dget_addChains hL _ _ i
  · split
    · rw [dget_addHalves, coeff_halfOfChain hL, dget_chain, dget_spinor]
    · rw [dget_multi_add, ← dget_multi, ← dget_multi, dget_toMultivector_chain,
        dget_toMultivector_half, dget_chain, dget_spinor]
  · split
    · rw [dget_addHalves, coeff_halfOfChain hL, dget_chain, dget_spinor]
    · rw [dget_multi_add, ← dget_multi, ← dget_multi, dget_toMultivector_chain,
        dget_toMultivector_half, dget_chain, dget_spinor]
  · split
    · rw [dget_addHalves, coeff_halfOfChain hL, dget_chain, dget_cospinor]
    · rw [dget_multi_add, ← dget_multi, ← dget_multi, dget_toMultivector_chain,
        dget_toMultivector_half, dget_chain, dget_cospinor]
  · split
    · rw [dget_addHalves, coeff_halfOfChain hL, dget_chain, dget_cospinor]
    · rw [dget_multi_add, ← dget_multi, ← dget_multi, dget_toMultivector_chain,
        dget_toMultivector_half, dget_chain, dget_cospinor]
  · simp [Half_coeff_add]
  · simp [Half_coeff_add]
  · exact dget_multi_add _ _ i
  · exact dget_multi_add _ _ i

/-! ## Terms -/

omit [LawfulCoeff α] in
/-- A term's dense value is that of its `Single`. -/
theorem dget_of_term {x : TA V α} {A : UInt64} {v : α} (h : x.term? = some (A, v)) (i : Fin (2 ^ V.n)) :
    x.dget i = (single A v : TA V α).dget i := by
  cases x <;> simp [term?] at h <;> obtain ⟨rfl, rfl⟩ := h <;> simp

omit [LawfulCoeff α] in
/-- A well-formed term's blade is a blade of `V`. -/
theorem valid_of_term {x : TA V α} {A : UInt64} {v : α} (h : x.term? = some (A, v)) (hx : x.WF) :
    valid V A = true := by
  cases x <;> simp [term?] at h <;> obtain ⟨rfl, rfl⟩ := h <;> simp_all [WF]

/-- A term plus a container (Julia `plus(::TensorTerm, b)`). -/
theorem dget_addTermX (hL : LayoutInv V.n) {A : UInt64} (hA : valid V A = true) (x : α) (b : TA V α)
    (i : Fin (2 ^ V.n)) : (addTermX A x b).dget i = (single A x : TA V α).dget i + b.dget i := by
  have hA' : Layout.full.contains V.n A = true := hA
  unfold addTermX
  split
  · exact dget_addTermChain hL hA x _ i
  · rw [dget_multiAddAt]
    simp only [dget_single, dget_multi, hA, Bool.and_true]
    split <;> simp [LawfulCoeff.add_comm]
  · split
    · rename_i h
      simp only [dget_spinor, coeff_halfAddAt hL, dget_single, hA, Bool.and_true, contains_half]
      generalize fullBlade V.n i.1 = β
      by_cases h1 : β = A <;> simp_all [LawfulCoeff.add_comm]
    · rw [dget_multiAddAt]
      simp only [dget_single, hA, Bool.and_true]
      rw [← dget_multi, dget_toMultivector_half, dget_spinor]
      split <;> simp [LawfulCoeff.add_comm]
  · split
    · rename_i h
      simp only [dget_cospinor, coeff_halfAddAt hL, dget_single, hA, Bool.and_true, contains_half]
      generalize fullBlade V.n i.1 = β
      by_cases h1 : β = A <;> simp_all [LawfulCoeff.add_comm]
    · rw [dget_multiAddAt]
      simp only [dget_single, hA, Bool.and_true]
      rw [← dget_multi, dget_toMultivector_half, dget_cospinor]
      split <;> simp [LawfulCoeff.add_comm]
  · rw [dget_multiAddAt]
    simp only [dget_single, hA, Bool.and_true]
    split <;> simp [dget, LawfulCoeff.add_comm]

/-- The lattice on terms and containers has the dense value of the sum. -/
theorem dget_addB (hL : LayoutInv V.n) (a b : TA V α) (ha : a.WF) (hb : b.WF) (i : Fin (2 ^ V.n)) :
    (addB a b).dget i = a.dget i + b.dget i := by
  unfold addB
  split
  · rename_i hta htb
    rw [dget_addTermTerm hL (valid_of_term hta ha) (valid_of_term htb hb), dget_of_term hta,
      dget_of_term htb]
  · rename_i hta _
    rw [dget_addTermX hL (valid_of_term hta ha), dget_of_term hta]
  · rename_i _ htb
    rw [dget_addTermX hL (valid_of_term htb hb), dget_of_term htb, LawfulCoeff.add_comm]
  · exact dget_addXX hL a b i

/-! ## Well-formedness is preserved -/

omit [LawfulCoeff α] in
/-- Sums of well-formed terms are well formed. -/
theorem wf_addTermTerm {A B : UInt64} (hA : valid V A = true) (hB : valid V B = true) (x y : α) :
    (addTermTerm A x B y : TA V α).WF := by
  unfold addTermTerm; dsimp only
  repeat' split
  all_goals simp_all [WF]

omit [LawfulCoeff α] in
/-- A well-formed term plus a chain is well formed. -/
theorem wf_addTermChain {A : UInt64} (hA : valid V A = true) (x : α) {G : Nat} (c : Chain V G α) :
    (addTermChain A x c : TA V α).WF := by
  unfold addTermChain; dsimp only
  repeat' split
  all_goals simp_all [WF]

omit [LawfulCoeff α] in
/-- A well-formed term plus a container is well formed. -/
theorem wf_addTermX {A : UInt64} (hA : valid V A = true) (x : α) (b : TA V α) :
    (addTermX A x b : TA V α).WF := by
  unfold addTermX
  split
  · exact wf_addTermChain hA x _
  all_goals first | trivial | (split <;> trivial)

omit [LawfulCoeff α] in
/-- A half as a dynamic element is well formed. -/
theorem wf_ofHalf {p : Bool} (h : Half V p α) : (ofHalf h).WF := by cases p <;> trivial

omit [LawfulCoeff α] in
/-- `Single(c)` is on a blade of `V`. -/
theorem valid_singleOfChain {G : Nat} {c : Chain V G α} {A : UInt64} {x : α}
    (h : singleOfChain c = single A x) : valid V A = true := by
  unfold singleOfChain at h; split at h <;> cases h <;> simp

omit [LawfulCoeff α] in
/-- A sum of halves is well formed. -/
theorem wf_addHalves {p q : Bool} (a : Half V p α) (b : Half V q α) : (addHalves a b).WF := by
  unfold addHalves; split
  · exact wf_ofHalf _
  · trivial

omit [LawfulCoeff α] in
/-- A sum of chains is well formed. -/
theorem wf_addChains {G L : Nat} (a : Chain V G α) (b : Chain V L α) : (addChains a b).WF := by
  unfold addChains
  split
  · trivial
  split
  · split
    · rename_i h; exact wf_addTermChain (valid_singleOfChain h) _ _
    · trivial
  split
  · split
    · rename_i h; exact wf_addTermChain (valid_singleOfChain h) _ _
    · trivial
  split
  · exact wf_addHalves _ _
  · trivial

omit [LawfulCoeff α] in
/-- A sum of containers is well formed. -/
theorem wf_addXX (a b : TA V α) : (addXX a b).WF := by
  unfold addXX
  split
  · exact wf_addChains _ _
  all_goals first | trivial | (split <;> first | exact wf_addHalves _ _ | trivial)

omit [LawfulCoeff α] in
/-- The base lattice preserves well-formedness. -/
theorem wf_addB (a b : TA V α) (ha : a.WF) (hb : b.WF) : (addB a b).WF := by
  unfold addB
  split
  · rename_i hta htb; exact wf_addTermTerm (valid_of_term hta ha) (valid_of_term htb hb) _ _
  · rename_i hta _; exact wf_addTermX (valid_of_term hta ha) _ _
  · rename_i _ htb; exact wf_addTermX (valid_of_term htb hb) _ _
  · exact wf_addXX a b

/-! ## `multispin` keeps the value -/

omit [LawfulCoeff α] in
/-- Re-storing an element supported on one parity as a half keeps its dense value. -/
theorem dget_toHalfTA (hL : LayoutInv V.n) (p : Bool) (x : TA V α) (hx : ∀ m, x ≠ multi m)
    (hsupp : ∀ β, (halfLayout p).contains V.n β = false → x.coeff β = Coeff.zero)
    (i : Fin (2 ^ V.n)) : (toHalfTA p x).dget i = x.dget i := by
  rw [toHalfTA, dget_ofHalf, coeff_halfOf hL, dget_eq_coeff x hx]
  split
  · rfl
  · rename_i h; simp only [Bool.not_eq_true] at h; exact (hsupp _ h).symm

omit [LawfulCoeff α] in
/-- `multispin` keeps the dense value of a well-formed element. -/
theorem dget_multispin (hL : LayoutInv V.n) (x : TA V α) (hx : x.WF) (i : Fin (2 ^ V.n)) :
    (multispin x).dget i = x.dget i := by
  have hv0 : Layout.full.contains V.n 0 = true := valid_zero
  have hvI : Layout.full.contains V.n (pseudoBits V) = true := valid_pseudoBits
  have hpI := popcount_pseudoBits hL
  cases x with
  | zero => rfl
  | infinity => rfl
  | phasor => rfl
  | spinor => rfl
  | cospinor => rfl
  | multi => rfl
  | one =>
    simp only [multispin, grade?]
    refine dget_toHalfTA hL _ _ (by simp) (fun β hβ => ?_) i
    rw [contains_half] at hβ
    by_cases h1 : β = 0 <;> simp_all [coeff]
  | blade b =>
    have hb : Layout.full.contains V.n b = true := hx
    simp only [multispin, grade?]
    refine dget_toHalfTA hL _ _ (by simp) (fun β hβ => ?_) i
    rw [contains_half] at hβ
    by_cases h1 : β = b <;> simp_all [coeff]
  | single b v =>
    have hb : Layout.full.contains V.n b = true := hx
    simp only [multispin, grade?]
    refine dget_toHalfTA hL _ _ (by simp) (fun β hβ => ?_) i
    rw [contains_half] at hβ
    by_cases h1 : β = b <;> simp_all [coeff]
  | chain g c =>
    simp only [multispin]
    refine dget_toHalfTA hL _ _ (by simp) (fun β hβ => ?_) i
    simp only [coeff]
    apply Chain_coeff_of_not
    rw [contains_half] at hβ; rw [contains_chain]
    by_cases hc : popcount β = g <;> simp_all
  | couple b re im =>
    have hb : Layout.full.contains V.n b = true := hx
    simp only [multispin]
    split
    · refine dget_toHalfTA hL false _ (by simp) (fun β hβ => ?_) i
      rw [contains_half] at hβ
      simp only [coeff]
      by_cases h1 : β = 0 <;> by_cases h2 : β = b <;> simp_all
    · rfl
  | pseudo b re im =>
    have hb : Layout.full.contains V.n b = true := hx
    simp only [multispin]
    split
    · rename_i h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      refine dget_toHalfTA hL false _ (by simp) (fun β hβ => ?_) i
      rw [contains_half] at hβ
      simp only [coeff]
      by_cases h1 : β = b <;> by_cases h2 : β = pseudoBits V <;> simp_all
    split
    · rename_i h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      refine dget_toHalfTA hL true _ (by simp) (fun β hβ => ?_) i
      rw [contains_half] at hβ
      simp only [coeff]
      by_cases h1 : β = b <;> by_cases h2 : β = pseudoBits V <;> simp_all
    · rfl

omit [LawfulCoeff α] in
/-- `multispin` keeps well-formedness. -/
theorem wf_multispin (x : TA V α) (hx : x.WF) : (multispin x).WF := by
  unfold multispin toHalfTA toMultiTA
  split <;> (try split) <;> (try split) <;> first | exact hx | exact wf_ofHalf _ | trivial

/-! ## Couples meeting terms -/

/-- A couple is its scalar part plus its imaginary term. -/
theorem dget_couple_split {B : UInt64} (hB : valid V B = true) (re im : α) (i : Fin (2 ^ V.n)) :
    (couple B re im : TA V α).dget i = (single 0 re : TA V α).dget i + (single B im).dget i := by
  simp only [dget_couple, dget_single, hB, valid_zero, Bool.and_true]
  generalize fullBlade V.n i.1 = β
  by_cases h1 : β = 0 <;> by_cases h2 : β = B <;> by_cases h3 : B = 0 <;> simp_all

/-- A pseudo-couple is its imaginary term plus its pseudoscalar term. -/
theorem dget_pseudo_split {B : UInt64} (hB : valid V B = true) (re im : α) (i : Fin (2 ^ V.n)) :
    (pseudo B re im : TA V α).dget i =
      (single B re : TA V α).dget i + (single (pseudoBits V) im).dget i := by
  simp only [dget_pseudo, dget_single, hB, valid_pseudoBits, Bool.and_true]
  generalize fullBlade V.n i.1 = β
  by_cases h1 : β = B <;> by_cases h2 : β = pseudoBits V <;> simp_all

/-- A couple plus a term (Julia `plus(::Couple, ::TensorTerm)`). -/
theorem dget_addCoupleTerm (hL : LayoutInv V.n) {B C : UInt64} (hB : valid V B = true)
    (hC : valid V C = true) (re im y : α) (i : Fin (2 ^ V.n)) :
    (addCoupleTerm B re im C y : TA V α).dget i = (couple B re im : TA V α).dget i + (single C y).dget i := by
  unfold addCoupleTerm
  split
  · rename_i h; simp only [beq_iff_eq] at h; subst h
    rw [dget_couple_split hB, dget_couple_split hB]
    simp only [dget_single, hB, valid_zero, Bool.and_true]
    generalize fullBlade V.n i.1 = β
    by_cases h1 : β = 0 <;> by_cases h2 : β = B <;> simp_all <;> ac_rfl
  split
  · rename_i h0 h; simp only [beq_iff_eq] at h h0; subst h
    rw [dget_couple_split hB, dget_couple_split hB]
    simp only [dget_single, hB, valid_zero, Bool.and_true]
    generalize fullBlade V.n i.1 = β
    by_cases h1 : β = 0 <;> by_cases h2 : β = C <;> simp_all <;> ac_rfl
  · rw [dget_addB hL (multispin (couple B re im)) (single C y) (wf_multispin (couple B re im) hB) hC,
      dget_multispin hL (couple B re im) hB]

/-- A term plus a couple (Julia `plus(::TensorTerm, ::Couple)`). -/
theorem dget_addTermCouple (hL : LayoutInv V.n) {B C : UInt64} (hB : valid V B = true)
    (hC : valid V C = true) (re im y : α) (i : Fin (2 ^ V.n)) :
    (addTermCouple C y B re im : TA V α).dget i = (single C y : TA V α).dget i + (couple B re im).dget i := by
  unfold addTermCouple
  split
  · rename_i h; simp only [beq_iff_eq] at h; subst h
    rw [dget_couple_split hB, dget_couple_split hB]
    simp only [dget_single, hB, valid_zero, Bool.and_true]
    generalize fullBlade V.n i.1 = β
    by_cases h1 : β = 0 <;> by_cases h2 : β = B <;> simp_all <;> ac_rfl
  split
  · rename_i h0 h; simp only [beq_iff_eq] at h h0; subst h
    rw [dget_couple_split hB, dget_couple_split hB]
    simp only [dget_single, hB, valid_zero, Bool.and_true]
    generalize fullBlade V.n i.1 = β
    by_cases h1 : β = 0 <;> by_cases h2 : β = C <;> simp_all <;> ac_rfl
  · rw [dget_addB hL (single C y) (multispin (couple B re im)) hC (wf_multispin (couple B re im) hB),
      dget_multispin hL (couple B re im) hB]

/-- A pseudo-couple plus a term (Julia `plus(::PseudoCouple, ::TensorTerm)`). -/
theorem dget_addPseudoTerm (hL : LayoutInv V.n) {B C : UInt64} (hB : valid V B = true)
    (hC : valid V C = true) (re im y : α) (i : Fin (2 ^ V.n)) :
    (addPseudoTerm B re im C y : TA V α).dget i = (pseudo B re im : TA V α).dget i + (single C y).dget i := by
  unfold addPseudoTerm
  split
  · rename_i h; simp only [beq_iff_eq] at h; subst h
    rw [dget_pseudo_split hB, dget_pseudo_split hB]
    simp only [dget_single, hB, valid_pseudoBits, Bool.and_true]
    generalize fullBlade V.n i.1 = β
    by_cases h1 : β = C <;> by_cases h2 : β = pseudoBits V <;> simp_all <;> ac_rfl
  split
  · rename_i h0 h; simp only [beq_iff_eq] at h h0; subst h
    rw [dget_pseudo_split hB, dget_pseudo_split hB]
    simp only [dget_single, hB, valid_pseudoBits, Bool.and_true]
    generalize fullBlade V.n i.1 = β
    by_cases h1 : β = B <;> by_cases h2 : β = pseudoBits V <;> simp_all <;> ac_rfl
  · rw [dget_addB hL (multispin (pseudo B re im)) (single C y) (wf_multispin (pseudo B re im) hB) hC,
      dget_multispin hL (pseudo B re im) hB]

/-- A term plus a pseudo-couple (Julia `plus(::TensorTerm, ::PseudoCouple)`). -/
theorem dget_addTermPseudo (hL : LayoutInv V.n) {B C : UInt64} (hB : valid V B = true)
    (hC : valid V C = true) (re im y : α) (i : Fin (2 ^ V.n)) :
    (addTermPseudo C y B re im : TA V α).dget i = (single C y : TA V α).dget i + (pseudo B re im).dget i := by
  unfold addTermPseudo
  split
  · rename_i h; simp only [beq_iff_eq] at h; subst h
    rw [dget_pseudo_split hB, dget_pseudo_split hB]
    simp only [dget_single, hB, valid_pseudoBits, Bool.and_true]
    generalize fullBlade V.n i.1 = β
    by_cases h1 : β = C <;> by_cases h2 : β = pseudoBits V <;> simp_all <;> ac_rfl
  split
  · rename_i h0 h; simp only [beq_iff_eq] at h h0; subst h
    rw [dget_pseudo_split hB, dget_pseudo_split hB]
    simp only [dget_single, hB, valid_pseudoBits, Bool.and_true]
    generalize fullBlade V.n i.1 = β
    by_cases h1 : β = B <;> by_cases h2 : β = pseudoBits V <;> simp_all <;> ac_rfl
  · rw [dget_addB hL (single C y) (multispin (pseudo B re im)) hC (wf_multispin (pseudo B re im) hB),
      dget_multispin hL (pseudo B re im) hB]

omit [LawfulCoeff α] in
/-- Couples meeting terms stay well formed. -/
theorem wf_addCoupleTerm {B C : UInt64} (hB : valid V B = true) (hC : valid V C = true) (re im y : α) :
    (addCoupleTerm B re im C y : TA V α).WF := by
  unfold addCoupleTerm
  split
  · exact hB
  split
  · exact hB
  · exact wf_addB _ _ (wf_multispin (couple B re im) hB) hC

omit [LawfulCoeff α] in
/-- Terms meeting couples stay well formed. -/
theorem wf_addTermCouple {B C : UInt64} (hB : valid V B = true) (hC : valid V C = true) (re im y : α) :
    (addTermCouple C y B re im : TA V α).WF := by
  unfold addTermCouple
  split
  · exact hB
  split
  · exact hB
  · exact wf_addB _ _ hC (wf_multispin (couple B re im) hB)

omit [LawfulCoeff α] in
/-- Pseudo-couples meeting terms stay well formed. -/
theorem wf_addPseudoTerm {B C : UInt64} (hB : valid V B = true) (hC : valid V C = true) (re im y : α) :
    (addPseudoTerm B re im C y : TA V α).WF := by
  unfold addPseudoTerm
  split
  · exact hB
  split
  · exact hB
  · exact wf_addB _ _ (wf_multispin (pseudo B re im) hB) hC

omit [LawfulCoeff α] in
/-- Terms meeting pseudo-couples stay well formed. -/
theorem wf_addTermPseudo {B C : UInt64} (hB : valid V B = true) (hC : valid V C = true) (re im y : α) :
    (addTermPseudo C y B re im : TA V α).WF := by
  unfold addTermPseudo
  split
  · exact hB
  split
  · exact hB
  · exact wf_addB _ _ hC (wf_multispin (pseudo B re im) hB)

omit [LawfulCoeff α] in
/-- The couple layer preserves well-formedness. -/
theorem wf_addL1 (a b : TA V α) (ha : a.WF) (hb : b.WF) : (addL1 a b).WF := by
  unfold addL1
  split
  · split
    · rename_i hbt; exact wf_addCoupleTerm ha (valid_of_term hbt hb) _ _ _
    · exact wf_addB _ _ (wf_multispin _ ha) hb
  · split
    · rename_i hbt; exact wf_addPseudoTerm ha (valid_of_term hbt hb) _ _ _
    · exact wf_addB _ _ (wf_multispin _ ha) hb
  · split
    · rename_i hat; exact wf_addTermCouple hb (valid_of_term hat ha) _ _ _
    · exact wf_addB _ _ ha (wf_multispin _ hb)
  · split
    · rename_i hat; exact wf_addTermPseudo hb (valid_of_term hat ha) _ _ _
    · exact wf_addB _ _ ha (wf_multispin _ hb)
  · exact wf_addB _ _ ha hb

/-- The couple layer has the dense value of the sum. -/
theorem dget_addL1 (hL : LayoutInv V.n) (a b : TA V α) (ha : a.WF) (hb : b.WF) (i : Fin (2 ^ V.n)) :
    (addL1 a b).dget i = a.dget i + b.dget i := by
  unfold addL1
  split
  · split
    · rename_i hbt; rw [dget_addCoupleTerm hL ha (valid_of_term hbt hb), dget_of_term hbt]
    · rw [dget_addB hL _ _ (wf_multispin _ ha) hb, dget_multispin hL _ ha]
  · split
    · rename_i hbt; rw [dget_addPseudoTerm hL ha (valid_of_term hbt hb), dget_of_term hbt]
    · rw [dget_addB hL _ _ (wf_multispin _ ha) hb, dget_multispin hL _ ha]
  · split
    · rename_i hat; rw [dget_addTermCouple hL hb (valid_of_term hat ha), dget_of_term hat]
    · rw [dget_addB hL _ _ ha (wf_multispin _ hb), dget_multispin hL _ hb]
  · split
    · rename_i hat; rw [dget_addTermPseudo hL hb (valid_of_term hat ha), dget_of_term hat]
    · rw [dget_addB hL _ _ ha (wf_multispin _ hb), dget_multispin hL _ hb]
  · exact dget_addB hL a b ha hb i

/-! ## The full lattice -/

omit [LawfulCoeff α] in
theorem wf_coupleScalar (x : α) : (coupleScalar x : TA V α).WF := valid_zero (V := V)

omit [LawfulCoeff α] in
theorem wf_termOf {B : UInt64} (h : valid V B = true) (x : α) : (termOf B x : TA V α).WF := h

omit [LawfulCoeff α] in
theorem wf_pseudoVolume (x : α) : (pseudoVolume x : TA V α).WF := valid_pseudoBits (V := V)

/-- A couple is `coupleScalar re + termOf B im`. -/
theorem dget_couple_parts {B : UInt64} (hB : valid V B = true) (re im : α) (i : Fin (2 ^ V.n)) :
    (couple B re im : TA V α).dget i = (coupleScalar re : TA V α).dget i + (termOf B im).dget i :=
  dget_couple_split hB re im i

/-- A pseudo-couple is `termOf B re + pseudoVolume im`. -/
theorem dget_pseudo_parts {B : UInt64} (hB : valid V B = true) (re im : α) (i : Fin (2 ^ V.n)) :
    (pseudo B re im : TA V α).dget i = (termOf B re : TA V α).dget i + (pseudoVolume im).dget i :=
  dget_pseudo_split hB re im i

/-- Two couples on one blade add componentwise. -/
theorem dget_couple_add {B : UInt64} (hB : valid V B = true) (r i s j : α) (k : Fin (2 ^ V.n)) :
    (couple B (r + s) (i + j) : TA V α).dget k = (couple B r i).dget k + (couple B s j).dget k := by
  simp only [dget_couple_split hB, dget_single, hB, valid_zero, Bool.and_true]
  generalize fullBlade V.n k.1 = β
  by_cases h1 : β = 0 <;> by_cases h2 : β = B <;> by_cases h3 : B = 0 <;> simp_all <;> ac_rfl

/-- Two pseudo-couples on one blade add componentwise. -/
theorem dget_pseudo_add {B : UInt64} (hB : valid V B = true) (r i s j : α) (k : Fin (2 ^ V.n)) :
    (pseudo B (r + s) (i + j) : TA V α).dget k = (pseudo B r i).dget k + (pseudo B s j).dget k := by
  simp only [dget_pseudo_split hB, dget_single, hB, valid_pseudoBits, Bool.and_true]
  generalize fullBlade V.n k.1 = β
  by_cases h1 : β = B <;> by_cases h2 : β = pseudoBits V <;> by_cases h3 : B = pseudoBits V <;>
    simp_all <;> ac_rfl

/-- **The representation lattice is correct**: `a + b` has the dense value of the sum,
whichever of Julia's kinds it lands in. -/
theorem dget_add (hL : LayoutInv V.n) (a b : TA V α) (ha : a.WF) (hb : b.WF) (i : Fin (2 ^ V.n)) :
    (add a b).dget i = a.dget i + b.dget i := by
  -- `(x + t₁) + t₂` of the couple layer, for well-formed `x` and terms `t₁`, `t₂`
  have two : ∀ (x t₁ t₂ : TA V α), x.WF → t₁.WF → t₂.WF →
      ((addB x t₁).addL1 t₂).dget i = x.dget i + t₁.dget i + t₂.dget i := fun x t₁ t₂ hx h₁ h₂ => by
    rw [dget_addL1 hL _ _ (wf_addB _ _ hx h₁) h₂, dget_addB hL _ _ hx h₁]
  have two' : ∀ (x t₁ t₂ : TA V α), x.WF → t₁.WF → t₂.WF →
      ((addL1 x t₁).addL1 t₂).dget i = x.dget i + t₁.dget i + t₂.dget i := fun x t₁ t₂ hx h₁ h₂ => by
    rw [dget_addL1 hL _ _ (wf_addL1 _ _ hx h₁) h₂, dget_addL1 hL _ _ hx h₁]
  unfold add
  split
  · simp
  · simp
  · simp [WF] at ha
  · simp [WF] at hb
  · simp [WF] at ha
  · simp [WF] at hb
  · -- couple + couple
    split
    · rename_i h; simp only [beq_iff_eq] at h; subst h; exact dget_couple_add ha _ _ _ _ i
    · rw [two' _ _ _ ha (wf_coupleScalar _) (wf_termOf hb _), dget_couple_parts hb]; ac_rfl
  · -- pseudo + pseudo
    split
    · rename_i h; simp only [beq_iff_eq] at h; subst h; exact dget_pseudo_add ha _ _ _ _ i
    · rw [two' _ _ _ ha (wf_pseudoVolume _) (wf_termOf hb _), dget_pseudo_parts hb]; ac_rfl
  · rw [two' _ _ _ ha (wf_termOf hb _) (wf_pseudoVolume _), dget_pseudo_parts hb]; ac_rfl
  · rw [two' _ _ _ (wf_termOf ha _) hb (wf_pseudoVolume _), dget_pseudo_parts ha]; ac_rfl
  · split
    · rw [two _ _ _ hb (wf_coupleScalar _) (wf_termOf ha _), dget_couple_parts ha]; ac_rfl
    · rw [two _ _ _ hb (wf_termOf ha _) (wf_coupleScalar _), dget_couple_parts ha]; ac_rfl
  · split
    · rw [two _ _ _ ha (wf_coupleScalar _) (wf_termOf hb _), dget_couple_parts hb]; ac_rfl
    · rw [two _ _ _ ha (wf_termOf hb _) (wf_coupleScalar _), dget_couple_parts hb]; ac_rfl
  · split
    · rw [two _ _ _ hb (wf_pseudoVolume _) (wf_termOf ha _), dget_pseudo_parts ha]; ac_rfl
    · rw [two _ _ _ hb (wf_termOf ha _) (wf_pseudoVolume _), dget_pseudo_parts ha]; ac_rfl
  · split
    · rw [two _ _ _ ha (wf_pseudoVolume _) (wf_termOf hb _), dget_pseudo_parts hb]; ac_rfl
    · rw [two _ _ _ ha (wf_termOf hb _) (wf_pseudoVolume _), dget_pseudo_parts hb]; ac_rfl
  all_goals first
    | (rw [two _ _ _ hb (wf_coupleScalar _) (wf_termOf ha _), dget_couple_parts ha]; ac_rfl)
    | (rw [two _ _ _ ha (wf_coupleScalar _) (wf_termOf hb _), dget_couple_parts hb]; ac_rfl)
    | (rw [two _ _ _ hb (wf_pseudoVolume _) (wf_termOf ha _), dget_pseudo_parts ha]; ac_rfl)
    | (rw [two _ _ _ ha (wf_pseudoVolume _) (wf_termOf hb _), dget_pseudo_parts hb]; ac_rfl)
    | exact dget_addL1 hL a b ha hb i

omit [LawfulCoeff α] in
/-- Sums of well-formed elements are well formed. -/
theorem wf_add (a b : TA V α) (ha : a.WF) (hb : b.WF) : (add a b).WF := by
  unfold add
  split
  · exact hb
  · exact ha
  · simp [WF] at ha
  · simp [WF] at hb
  · simp [WF] at ha
  · simp [WF] at hb
  · split
    · exact ha
    · exact wf_addL1 _ _ (wf_addL1 _ _ ha (wf_coupleScalar _)) (wf_termOf hb _)
  · split
    · exact ha
    · exact wf_addL1 _ _ (wf_addL1 _ _ ha (wf_pseudoVolume _)) (wf_termOf hb _)
  · exact wf_addL1 _ _ (wf_addL1 _ _ ha (wf_termOf hb _)) (wf_pseudoVolume _)
  · exact wf_addL1 _ _ (wf_addL1 _ _ (wf_termOf ha _) hb) (wf_pseudoVolume _)
  all_goals first
    | (split <;> first
        | exact wf_addL1 _ _ (wf_addB _ _ hb (wf_coupleScalar _)) (wf_termOf ha _)
        | exact wf_addL1 _ _ (wf_addB _ _ hb (wf_termOf ha _)) (wf_coupleScalar _)
        | exact wf_addL1 _ _ (wf_addB _ _ ha (wf_coupleScalar _)) (wf_termOf hb _)
        | exact wf_addL1 _ _ (wf_addB _ _ ha (wf_termOf hb _)) (wf_coupleScalar _)
        | exact wf_addL1 _ _ (wf_addB _ _ hb (wf_pseudoVolume _)) (wf_termOf ha _)
        | exact wf_addL1 _ _ (wf_addB _ _ hb (wf_termOf ha _)) (wf_pseudoVolume _)
        | exact wf_addL1 _ _ (wf_addB _ _ ha (wf_pseudoVolume _)) (wf_termOf hb _)
        | exact wf_addL1 _ _ (wf_addB _ _ ha (wf_termOf hb _)) (wf_pseudoVolume _))
    | exact wf_addL1 _ _ (wf_addB _ _ hb (wf_coupleScalar _)) (wf_termOf ha _)
    | exact wf_addL1 _ _ (wf_addB _ _ ha (wf_coupleScalar _)) (wf_termOf hb _)
    | exact wf_addL1 _ _ (wf_addB _ _ hb (wf_pseudoVolume _)) (wf_termOf ha _)
    | exact wf_addL1 _ _ (wf_addB _ _ ha (wf_pseudoVolume _)) (wf_termOf hb _)
    | exact wf_addL1 a b ha hb

omit [LawfulCoeff α] in
/-- Negation keeps well-formedness. -/
theorem wf_neg (a : TA V α) (ha : a.WF) : (neg a).WF := by
  cases a <;> simp_all [neg, WF]

omit [LawfulCoeff α] in
/-- Scaling keeps well-formedness. -/
theorem wf_smul (s : α) (a : TA V α) (ha : a.WF) : (smul s a).WF := by
  cases a <;> simp_all [smul, WF]

/-- The entries of a negation. -/
theorem dget_neg (a : TA V α) (ha : a.WF) (i : Fin (2 ^ V.n)) : (neg a).dget i = -a.dget i := by
  cases a with
  | infinity => simp [WF] at ha
  | phasor => simp [WF] at ha
  | multi m => exact Values.get_neg m.v i
  | chain g c => simp [neg, Chain_coeff_neg]
  | spinor h => simp [neg, Half_coeff_neg]
  | cospinor h => simp [neg, Half_coeff_neg]
  | couple b re im =>
    simp only [neg, dget_couple]
    split <;> (try split) <;> simp [LawfulCoeff.neg_add]
  | pseudo b re im =>
    simp only [neg, dget_pseudo]
    split <;> (try split) <;> simp [LawfulCoeff.neg_add]
  | zero => simp [neg]
  | one => simp only [neg, dget_single, dget_one, valid_zero, Bool.and_true]; split <;> simp
  | blade b => simp only [neg, dget_single, dget_blade]; split <;> simp
  | single b x => simp only [neg, dget_single]; split <;> simp

/-- The entries of a left scalar multiple. -/
theorem dget_smul (s : α) (a : TA V α) (ha : a.WF) (i : Fin (2 ^ V.n)) :
    (smul s a).dget i = s * a.dget i := by
  cases a with
  | infinity => simp [WF] at ha
  | phasor => simp [WF] at ha
  | multi m => exact Values.get_map _ m.v i
  | chain g c => simp [smul, Chain_coeff_smul]
  | spinor h => simp [smul, Half_coeff_smul]
  | cospinor h => simp [smul, Half_coeff_smul]
  | couple b re im =>
    simp only [smul, dget_couple]
    split <;> (try split) <;> simp [LawfulCoeff.mul_add]
  | pseudo b re im =>
    simp only [smul, dget_pseudo]
    split <;> (try split) <;> simp [LawfulCoeff.mul_add]
  | zero => simp [smul]
  | one => simp only [smul, dget_single, dget_one, valid_zero, Bool.and_true]; split <;> simp
  | blade b => simp only [smul, dget_single, dget_blade]; split <;> simp
  | single b x => simp only [smul, dget_single]; split <;> simp

/-- The entries of a right scalar multiple. -/
theorem dget_mulScalar (a : TA V α) (s : α) (ha : a.WF) (i : Fin (2 ^ V.n)) :
    (mulScalar a s).dget i = a.dget i * s := by
  cases a with
  | infinity => simp [WF] at ha
  | phasor => simp [WF] at ha
  | multi m => exact Values.get_map _ m.v i
  | chain g c => simp [mulScalar, Chain_coeff_mulr]
  | spinor h => simp [mulScalar, Half_coeff_mulr]
  | cospinor h => simp [mulScalar, Half_coeff_mulr]
  | couple b re im =>
    simp only [mulScalar, dget_couple]
    split <;> (try split) <;> simp [LawfulCoeff.add_mul]
  | pseudo b re im =>
    simp only [mulScalar, dget_pseudo]
    split <;> (try split) <;> simp [LawfulCoeff.add_mul]
  | zero => simp [mulScalar]
  | one => simp only [mulScalar, dget_single, dget_one, valid_zero, Bool.and_true]; split <;> simp
  | blade b => simp only [mulScalar, dget_single, dget_blade]; split <;> simp
  | single b x => simp only [mulScalar, dget_single]; split <;> simp

/-! ## The dense-value theorems -/

omit [LawfulCoeff α] in
/-- Multivectors are equal when their entries are. -/
theorem Multivector_ext {m w : Multivector V α} (h : ∀ i, m.v.get i = w.v.get i) : m = w := by
  cases m; cases w; congr; exact Values.ext h

/-- **`toDense` is additive** on well-formed elements: every branch of Julia's `+`
lattice (DESIGN.md §4.3) computes the sum. -/
theorem toDense_add (hL : LayoutInv V.n) {a b : TA V α} (ha : a.WF) (hb : b.WF) :
    (a + b).toDense = a.toDense + b.toDense :=
  Multivector_ext fun i => (dget_add hL a b ha hb i).trans (Values.get_add _ _ i).symm

/-- **`toDense` commutes with negation.** -/
theorem toDense_neg {a : TA V α} (ha : a.WF) : (-a).toDense = -a.toDense :=
  Multivector_ext fun i => (dget_neg a ha i).trans (Values.get_neg _ i).symm

/-- **`toDense` commutes with subtraction** (`a - b = a + (-b)`). -/
theorem toDense_sub (hL : LayoutInv V.n) {a b : TA V α} (ha : a.WF) (hb : b.WF) :
    (a - b).toDense = a.toDense - b.toDense :=
  Multivector_ext fun i => by
    show (add a (neg b)).dget i = _
    rw [dget_add hL a (neg b) ha (wf_neg b hb) i, dget_neg b hb i, ← LawfulCoeff.sub_eq_add_neg]
    exact (Values.get_sub _ _ i).symm

/-- **`toDense` commutes with scalar multiplication** (Julia `s * x`). -/
theorem toDense_smul (s : α) {a : TA V α} (ha : a.WF) : (s • a).toDense = s • a.toDense :=
  Multivector_ext fun i => (dget_smul s a ha i).trans (Values.get_map _ _ i).symm

/-- `toDense` commutes with scalar multiplication on the right (Julia `x * s`). -/
theorem toDense_mulScalar (s : α) {a : TA V α} (ha : a.WF) : (a * s).toDense = a.toDense * s :=
  Multivector_ext fun i => (dget_mulScalar a s ha i).trans (Values.get_map (· * s) a.toDense.v i).symm

omit [LawfulCoeff α] in
/-- Sums, differences, negations and scalar multiples of well-formed elements are
well formed, so the theorems compose. -/
theorem wf_sub (a b : TA V α) (ha : a.WF) (hb : b.WF) : (a - b).WF := wf_add a (neg b) ha (wf_neg b hb)

/-- `toDense_add` for every space of at most 8 generators (the kernel-checked
`LayoutInv`). -/
theorem toDense_add_le8 (h : V.n ≤ 8) {a b : TA V α} (ha : a.WF) (hb : b.WF) :
    (a + b).toDense = a.toDense + b.toDense := toDense_add (layoutInv_le8 V.n h) ha hb

/-- `toDense_sub` for every space of at most 8 generators. -/
theorem toDense_sub_le8 (h : V.n ≤ 8) {a b : TA V α} (ha : a.WF) (hb : b.WF) :
    (a - b).toDense = a.toDense - b.toDense := toDense_sub (layoutInv_le8 V.n h) ha hb

end TA

end Grassmann
