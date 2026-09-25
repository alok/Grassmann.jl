/-
Reflection for the `clifford` tactic: multivector expressions of a concrete
space and their coordinates as polynomials.

A goal `x = y` between multivectors of `Cl g` (`g : Fin n → R`, `n` a numeral,
`R` any `Lean.Grind.CommRing`) is reified into two `MExpr`s. `MExpr.eval`
computes their `2ⁿ` coordinates as coefficient polynomials (`Poly`: integer
constants, scalar atoms, coordinates of opaque multivectors and metric
entries, with sums, products and negations), from the spec's blade tables:
the product of two blades is looked up with the same sign and metric
functions as `Grassmann.Spec.coef`, so nothing is re-derived. Zero terms are
pruned as they arise (`addS`, `mulS`), so products of explicit blades fold to
constants.

`eq_of_coords` is the soundness theorem: if the coordinate polynomials agree
under `Poly.denote`, the multivectors are equal. The tactic
(`Grassmann.Tactic.Clifford`) evaluates `MExpr.eval` natively, states the
`2ⁿ` coordinate equations directly (the kernel re-checks them by evaluation),
and closes each with `grind`, which does the commutative ring normalization
(and uses hypotheses such as `c² + s² = 1`).
-/
import Grassmann.Spec

namespace Grassmann.Tactic

open Lean.Grind DirectSum.Proofs Grassmann.Spec

universe u

/-! ## Integer numerals -/

section IntLit

variable {R : Type u} [CommRing R]

attribute [local instance] Semiring.natCast Ring.intCast

/-- The integer `k` as a numeral of `R`: `OfNat.ofNat k`, or `-OfNat.ofNat |k|`. -/
def intLit : Int → R
  | .ofNat k => OfNat.ofNat k
  | .negSucc k => -OfNat.ofNat (k + 1)

/-- `intLit` is the canonical map from the integers. -/
theorem intLit_eq (k : Int) : (intLit k : R) = (Int.cast k : R) := by
  cases k with
  | ofNat k => exact (Ring.intCast_ofNat k).symm
  | negSucc k =>
    show -(OfNat.ofNat (k + 1) : R) = (Int.cast (-((k + 1 : Nat) : Int)) : R)
    rw [Ring.intCast_neg, Ring.intCast_natCast, Semiring.ofNat_eq_natCast]

theorem intLit_add (a b : Int) : (intLit (a + b) : R) = intLit a + intLit b := by
  simp only [intLit_eq, Ring.intCast_add]

theorem intLit_mul (a b : Int) : (intLit (a * b) : R) = intLit a * intLit b := by
  simp only [intLit_eq, Ring.intCast_mul]

theorem intLit_neg (a : Int) : (intLit (-a) : R) = -intLit a := by
  simp only [intLit_eq, Ring.intCast_neg]

theorem intLit_zero : (intLit 0 : R) = 0 := rfl
theorem intLit_one : (intLit 1 : R) = 1 := rfl
theorem intLit_neg_one : (intLit (-1) : R) = -1 := rfl

end IntLit

/-! ## Finite sums over `Nat` indices -/

section SumTo

variable {R : Type u} [CommRing R]

/-- `sumTo m f = f 0 + ⋯ + f (m-1)`. -/
def sumTo : Nat → (Nat → R) → R
  | 0, _ => 0
  | m + 1, f => sumTo m f + f m

theorem sumTo_congr {m : Nat} {f f' : Nat → R} (h : ∀ k < m, f k = f' k) : sumTo m f = sumTo m f' := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show sumTo m f + f m = sumTo m f' + f' m
    rw [ih (fun k hk => h k (by omega)), h m (by omega)]

theorem sumTo_add (a b : Nat) (f : Nat → R) :
    sumTo (a + b) f = sumTo a f + sumTo b (fun k => f (a + k)) := by
  induction b with
  | zero => show sumTo a f = sumTo a f + 0; grind
  | succ b ih =>
    show sumTo (a + b) f + f (a + b) = sumTo a f + (sumTo b (fun k => f (a + k)) + f (a + b))
    rw [ih]; grind

private theorem cons_ofNat {n k : Nat} (b : Bool) (hk : k < 2 ^ n) :
    BitVec.cons b (BitVec.ofNat n k) = BitVec.ofNat (n + 1) (if b then 2 ^ n + k else k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_cons, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
  have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; omega
  cases b
  · simp only [Bool.toNat_false, Nat.zero_shiftLeft, Nat.zero_or, Bool.false_eq_true, ite_false]
    rw [Nat.mod_eq_of_lt (by omega)]
  · simp only [Bool.toNat_true, ite_true]
    rw [Nat.mod_eq_of_lt (by omega), Nat.shiftLeft_eq, Nat.one_mul]
    have := Nat.two_pow_add_eq_or_of_lt hk 1
    rw [Nat.mul_one] at this
    rw [this]

/-- **Sums over blades are sums over masks**: `Σ_{a : BitVec n} f a = Σ_{k < 2ⁿ} f (ofNat k)`. -/
theorem bsum_eq_sumTo (n : Nat) (f : BitVec n → R) :
    bsum n f = sumTo (2 ^ n) (fun k => f (BitVec.ofNat n k)) := by
  induction n with
  | zero => show f 0#0 = 0 + f (BitVec.ofNat 0 0); grind
  | succ n ih =>
    rw [bsum_succ, ih, ih, show 2 ^ (n + 1) = 2 ^ n + 2 ^ n by rw [Nat.pow_succ]; omega, sumTo_add]
    congr 1
    · exact sumTo_congr fun k hk => by rw [cons_ofNat false hk]; rfl
    · exact sumTo_congr fun k hk => by rw [cons_ofNat true hk]; rfl

end SumTo

/-! ## Coefficient polynomials -/

/-- A coefficient polynomial: what `denote` makes of it is an `R`-expression
over the scalar atoms `ρ`, the coordinates of the opaque multivectors `vs`
and the metric `g`. -/
inductive Poly where
  /-- An integer constant. -/
  | int (k : Int)
  /-- The scalar atom `ρ[i]`. -/
  | atom (i : Nat)
  /-- The coordinate on blade `k` of the opaque multivector `vs[v]`. -/
  | coeff (v k : Nat)
  /-- The metric entry `g i` (as `extendMetric g i`). -/
  | met (i : Nat)
  /-- A sum. -/
  | add (p q : Poly)
  /-- A product. -/
  | mul (p q : Poly)
  /-- A negation. -/
  | neg (p : Poly)
  /-- A difference (kept apart from `add`/`neg`: in an abstract ring `a - b`
  is not definitionally `a + -b`, and reified terms must denote the goal's
  own terms up to definitional unfolding). -/
  | sub (p q : Poly)
  /-- A power with a literal exponent (likewise not definitionally a product). -/
  | pow (p : Poly) (k : Nat)
  deriving Inhabited, Repr, BEq

namespace Poly

variable {R : Type u} [CommRing R] {n : Nat}

/-- The value of a coefficient polynomial. -/
def denote (g : Fin n → R) (ρ : List R) (vs : List (Cl g)) : Poly → R
  | int k => intLit k
  | atom i => ρ.getD i 0
  | coeff v k => (vs.getD v 0).coeff (BitVec.ofNat n k)
  | met i => extendMetric g i
  | add p q => denote g ρ vs p + denote g ρ vs q
  | mul p q => denote g ρ vs p * denote g ρ vs q
  | neg p => -denote g ρ vs p
  | sub p q => denote g ρ vs p - denote g ρ vs q
  | pow p k => denote g ρ vs p ^ k

/-- Negation, folding constants and double negations. -/
def negS : Poly → Poly
  | int k => int (-k)
  | neg p => p
  | p => neg p

/-- Addition, dropping zeros and folding constants. -/
def addS : Poly → Poly → Poly
  | int 0, q => q
  | p, int 0 => p
  | int a, int b => int (a + b)
  | p, q => add p q

/-- Multiplication, absorbing zeros, dropping units and folding constants. -/
def mulS : Poly → Poly → Poly
  | int 0, _ => int 0
  | _, int 0 => int 0
  | int 1, q => q
  | p, int 1 => p
  | int a, int b => int (a * b)
  | int (-1), q => negS q
  | p, int (-1) => negS p
  | p, q => mul p q

/-- `Σ_{k < m} f k`. -/
def psum : Nat → (Nat → Poly) → Poly
  | 0, _ => int 0
  | m + 1, f => addS (psum m f) (f m)

/-- The sign `(-1)^s`. -/
def signP (s : Bool) : Poly := if s then int (-1) else int 1

variable {g : Fin n → R} {ρ : List R} {vs : List (Cl g)}

@[simp] theorem denote_int (k : Int) : (int k).denote g ρ vs = intLit k := rfl
@[simp] theorem denote_add (p q : Poly) : (add p q).denote g ρ vs = p.denote g ρ vs + q.denote g ρ vs := rfl
@[simp] theorem denote_mul (p q : Poly) : (mul p q).denote g ρ vs = p.denote g ρ vs * q.denote g ρ vs := rfl
@[simp] theorem denote_neg (p : Poly) : (neg p).denote g ρ vs = -p.denote g ρ vs := rfl

theorem denote_negS (p : Poly) : (negS p).denote g ρ vs = -p.denote g ρ vs := by
  unfold negS
  split
  · simp only [denote_int, intLit_neg]
  · simp only [denote_neg]; grind
  · rfl

theorem denote_addS (p q : Poly) : (addS p q).denote g ρ vs = p.denote g ρ vs + q.denote g ρ vs := by
  unfold addS
  split
  · simp only [denote_int, intLit_zero]; grind
  · simp only [denote_int, intLit_zero]; grind
  · simp only [denote_int, intLit_add]
  · rfl

theorem denote_mulS (p q : Poly) : (mulS p q).denote g ρ vs = p.denote g ρ vs * q.denote g ρ vs := by
  unfold mulS
  split
  · simp only [denote_int, intLit_zero]; grind
  · simp only [denote_int, intLit_zero]; grind
  · simp only [denote_int, intLit_one]; grind
  · simp only [denote_int, intLit_one]; grind
  · simp only [denote_int, intLit_mul]
  · simp only [denote_negS, denote_int, intLit_neg_one]; grind
  · simp only [denote_negS, denote_int, intLit_neg_one]; grind
  · rfl

theorem denote_psum (m : Nat) (f : Nat → Poly) :
    (psum m f).denote g ρ vs = sumTo m (fun k => (f k).denote g ρ vs) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [psum, denote_addS, ih]; rfl

theorem denote_signP (s : Bool) : (signP s).denote g ρ vs = (signOf s : R) := by
  cases s <;> rfl

end Poly

open Poly

/-! ## Blade tables as polynomials -/

section Tables

/-- The metric entry of generator `i` (`i < n`): a known constant or the atom `met i`. -/
def metEntry (ms : List Poly) (i : Nat) : Poly := ms.getD i (met i)

/-- `Π_{i < k, i ∈ m} gᵢ`, mirroring `DirectSum.Proofs.metricFactor`. -/
def metP (ms : List Poly) : Nat → Nat → Poly
  | 0, _ => int 1
  | k + 1, m => if m.testBit k then mulS (metP ms k m) (metEntry ms k) else metP ms k m

/-- The geometric-product coefficient `e_a e_b = coefP a b · e_{a⊕b}`. -/
def coefP (ms : List Poly) (n a b : Nat) : Poly := mulS (signP (sigma n a b)) (metP ms n (a &&& b))

/-- The exterior-product coefficient. -/
def wcoefP (n a b : Nat) : Poly := if a &&& b = 0 then signP (sigma n a b) else int 0

/-- The reversion sign of blade `c`. -/
def revP (n c : Nat) : Poly := signP (Leibniz.parityreverse (bitCount n c))

/-- The grade-involution sign of blade `c`. -/
def invP (n c : Nat) : Poly := signP (Leibniz.parityinvolute (bitCount n c))

/-- The contraction coefficient (`Grassmann.Spec.ccoef`). -/
def ccoefP (ms : List Poly) (n a b : Nat) : Poly :=
  if b &&& a = b then mulS (revP n b) (coefP ms n b a) else int 0

variable {R : Type u} [CommRing R] {n : Nat} {g : Fin n → R} {ρ : List R} {vs : List (Cl g)}

/-- The metric entries are right below `n`. -/
def MetricOK (g : Fin n → R) (ρ : List R) (vs : List (Cl g)) (ms : List Poly) : Prop :=
  ∀ i < n, (metEntry ms i).denote g ρ vs = extendMetric g i

/-- The atoms `met i` are always right. -/
theorem metricOK_nil : MetricOK g ρ vs [] := fun _ _ => rfl

/-- `P 0 ∧ P 1 ∧ ⋯ ∧ P (k-1)`, for building `MetricOK` entry by entry. -/
def AllBelow (P : Nat → Prop) : Nat → Prop
  | 0 => True
  | k + 1 => AllBelow P k ∧ P k

theorem AllBelow.forall {P : Nat → Prop} {k : Nat} (h : AllBelow P k) : ∀ i < k, P i := by
  induction k with
  | zero => intro i hi; omega
  | succ k ih =>
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact ih h.1 i hi
    · exact h.2

theorem metricOK_of_allBelow {ms : List Poly}
    (h : AllBelow (fun i => (metEntry ms i).denote g ρ vs = extendMetric g i) n) : MetricOK g ρ vs ms :=
  h.forall

theorem denote_metP {ms : List Poly} (hms : MetricOK g ρ vs ms) (m : Nat) :
    ∀ k ≤ n, (metP ms k m).denote g ρ vs = metricFactor (extendMetric g) k m := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    rw [metricFactor_succ]
    unfold metP
    by_cases hb : m.testBit k
    · rw [ite_eq_left hb, ite_eq_left hb, denote_mulS, ih (by omega), hms k (by omega)]
    · rw [ite_eq_right hb, ite_eq_right hb, ih (by omega)]; grind

private theorem toNat_ofNat_lt {a : Nat} (ha : a < 2 ^ n) : (BitVec.ofNat n a).toNat = a := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]

theorem denote_coefP {ms : List Poly} (hms : MetricOK g ρ vs ms) {a b : Nat} (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    (coefP ms n a b).denote g ρ vs = coef g (BitVec.ofNat n a) (BitVec.ofNat n b) := by
  rw [coef_eq, coefP, denote_mulS, denote_signP, denote_metP hms _ n (Nat.le_refl n)]
  simp only [sign, mf, BitVec.toNat_and, toNat_ofNat_lt ha, toNat_ofNat_lt hb]

private theorem ofNat_and_eq_zero {a b : Nat} (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    (BitVec.ofNat n a &&& BitVec.ofNat n b = 0) ↔ a &&& b = 0 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [BitVec.toNat_and, toNat_ofNat_lt ha, toNat_ofNat_lt hb] at this
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, toNat_ofNat_lt ha, toNat_ofNat_lt hb, h]; rfl

theorem denote_wcoefP {a b : Nat} (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    (wcoefP n a b).denote g ρ vs = (wcoef (BitVec.ofNat n a) (BitVec.ofNat n b) : R) := by
  unfold wcoefP wcoef
  by_cases h : a &&& b = 0
  · rw [ite_eq_left h, ite_eq_left ((ofNat_and_eq_zero ha hb).mpr h), denote_signP]
    simp only [sign, toNat_ofNat_lt ha, toNat_ofNat_lt hb]
  · rw [ite_eq_right h, ite_eq_right (fun e => h ((ofNat_and_eq_zero ha hb).mp e))]; rfl

theorem denote_revP {c : Nat} (hc : c < 2 ^ n) :
    (revP n c).denote g ρ vs = (revSign (BitVec.ofNat n c) : R) := by
  rw [revP, denote_signP, revSign, grade, toNat_ofNat_lt hc]

theorem denote_invP {c : Nat} (hc : c < 2 ^ n) :
    (invP n c).denote g ρ vs = (invSign (BitVec.ofNat n c) : R) := by
  rw [invP, denote_signP, invSign, grade, toNat_ofNat_lt hc]

private theorem ofNat_and_eq_self {a b : Nat} (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    (BitVec.ofNat n b &&& BitVec.ofNat n a = BitVec.ofNat n b) ↔ b &&& a = b := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [BitVec.toNat_and, toNat_ofNat_lt ha, toNat_ofNat_lt hb] at this
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, toNat_ofNat_lt ha, toNat_ofNat_lt hb, h]

theorem denote_ccoefP {ms : List Poly} (hms : MetricOK g ρ vs ms) {a b : Nat} (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    (ccoefP ms n a b).denote g ρ vs = ccoef g (BitVec.ofNat n a) (BitVec.ofNat n b) := by
  unfold ccoefP ccoef
  by_cases h : b &&& a = b
  · rw [ite_eq_left h, ite_eq_left ((ofNat_and_eq_self ha hb).mpr h), denote_mulS, denote_revP hb, denote_coefP hms hb ha]
  · rw [ite_eq_right h, ite_eq_right (fun e => h ((ofNat_and_eq_self ha hb).mp e))]; rfl

end Tables

/-! ## Multivector expressions -/

/-- A multivector expression of a concrete space, as the `clifford` tactic sees it. -/
inductive MExpr where
  /-- The opaque multivector `vs[i]`. -/
  | var (i : Nat)
  /-- The basis blade with mask `a`. -/
  | blade (a : Nat)
  /-- A scalar. -/
  | scalar (p : Poly)
  /-- `0`. -/
  | zero
  /-- `1`. -/
  | one
  /-- `x + y`. -/
  | add (x y : MExpr)
  /-- `x - y`. -/
  | sub (x y : MExpr)
  /-- `-x`. -/
  | neg (x : MExpr)
  /-- `r • x`. -/
  | smul (p : Poly) (x : MExpr)
  /-- The geometric product. -/
  | mul (x y : MExpr)
  /-- The exterior product. -/
  | wedge (x y : MExpr)
  /-- The contraction `x ⋅ y`. -/
  | contract (x y : MExpr)
  /-- The regressive product. -/
  | vee (x y : MExpr)
  /-- Reversion. -/
  | reverse (x : MExpr)
  /-- Grade involution. -/
  | involute (x : MExpr)
  /-- Clifford conjugation. -/
  | clifford (x : MExpr)
  /-- The grade-`k` part. -/
  | proj (k : Nat) (x : MExpr)
  /-- The right complement. -/
  | compl (x : MExpr)
  /-- The inverse of the right complement. -/
  | complInv (x : MExpr)
  /-- The Hodge star. -/
  | hodge (x : MExpr)
  /-- A power with a literal exponent (`Cl.instRing`). -/
  | pow (x : MExpr) (k : Nat)
  deriving Inhabited, Repr

namespace MExpr

variable {R : Type u} [CommRing R] {n : Nat}

/-- The multivector an expression stands for. -/
def denote (g : Fin n → R) (ρ : List R) (vs : List (Cl g)) : MExpr → Cl g
  | var i => vs.getD i 0
  | blade a => Cl.blade (BitVec.ofNat n a)
  | scalar p => Cl.scalar (p.denote g ρ vs)
  | zero => 0
  | one => 1
  | add x y => denote g ρ vs x + denote g ρ vs y
  | sub x y => denote g ρ vs x - denote g ρ vs y
  | neg x => -denote g ρ vs x
  | smul p x => p.denote g ρ vs • denote g ρ vs x
  | mul x y => denote g ρ vs x * denote g ρ vs y
  | wedge x y => Cl.wedge (denote g ρ vs x) (denote g ρ vs y)
  | contract x y => Cl.contract (denote g ρ vs x) (denote g ρ vs y)
  | vee x y => Cl.vee (denote g ρ vs x) (denote g ρ vs y)
  | reverse x => Cl.reverse (denote g ρ vs x)
  | involute x => Cl.involute (denote g ρ vs x)
  | clifford x => Cl.clifford (denote g ρ vs x)
  | proj k x => Cl.proj k (denote g ρ vs x)
  | compl x => Cl.compl (denote g ρ vs x)
  | complInv x => Cl.complInv (denote g ρ vs x)
  | hodge x => Cl.hodge (denote g ρ vs x)
  | pow x k => denote g ρ vs x ^ k

end MExpr

/-! ## Dense coordinates -/

section Dense

/-- The `2ⁿ` coordinates `f 0, …, f (2ⁿ-1)`. -/
def dense (n : Nat) (f : Nat → Poly) : List Poly := (List.range (2 ^ n)).map f

/-- A coordinate of a dense vector (`0` out of range). -/
def at' (X : List Poly) (c : Nat) : Poly := X.getD c (int 0)

/-- The product of dense vectors under the blade coefficient `k`:
`Z[c] = Σ_a X[a] Y[a ⊕ c] k(a, a ⊕ c)`. -/
def twistD (n : Nat) (k : Nat → Nat → Poly) (X Y : List Poly) : List Poly :=
  dense n fun c => psum (2 ^ n) fun a => mulS (mulS (at' X a) (at' Y (a ^^^ c))) (k a (a ^^^ c))

/-- The mask of the complementary blade. -/
def notMask (n c : Nat) : Nat := c ^^^ (2 ^ n - 1)

/-- Dense right complement. -/
def complD (n : Nat) (X : List Poly) : List Poly :=
  dense n fun c => mulS (signP (sigma n (notMask n c) c)) (at' X (notMask n c))

/-- Dense inverse right complement. -/
def complInvD (n : Nat) (X : List Poly) : List Poly :=
  dense n fun c => mulS (signP (sigma n c (notMask n c))) (at' X (notMask n c))

/-- Dense powers: `X^k` by repeated multiplication on the right. -/
def powD (n : Nat) (ms : List Poly) (X : List Poly) : Nat → List Poly
  | 0 => dense n fun c => if c = 0 then int 1 else int 0
  | k + 1 => twistD n (coefP ms n) (powD n ms X k) X

/-- Dense coordinates of a multivector expression. -/
def MExpr.eval (n : Nat) (ms : List Poly) : MExpr → List Poly
  | .var i => dense n (coeff i)
  | .blade a => dense n fun c => if c = a % 2 ^ n then int 1 else int 0
  | .scalar p => dense n fun c => if c = 0 then p else int 0
  | .zero => dense n fun _ => int 0
  | .one => dense n fun c => if c = 0 then int 1 else int 0
  | .add x y => let X := eval n ms x; let Y := eval n ms y; dense n fun c => addS (at' X c) (at' Y c)
  | .sub x y => let X := eval n ms x; let Y := eval n ms y; dense n fun c => addS (at' X c) (negS (at' Y c))
  | .neg x => let X := eval n ms x; dense n fun c => negS (at' X c)
  | .smul p x => let X := eval n ms x; dense n fun c => mulS p (at' X c)
  | .mul x y => twistD n (coefP ms n) (eval n ms x) (eval n ms y)
  | .wedge x y => twistD n (wcoefP n) (eval n ms x) (eval n ms y)
  | .contract x y => twistD n (ccoefP ms n) (eval n ms x) (eval n ms y)
  | .vee x y => complInvD n (twistD n (wcoefP n) (complD n (eval n ms x)) (complD n (eval n ms y)))
  | .reverse x => let X := eval n ms x; dense n fun c => mulS (revP n c) (at' X c)
  | .involute x => let X := eval n ms x; dense n fun c => mulS (invP n c) (at' X c)
  | .clifford x => let X := eval n ms x; dense n fun c => mulS (invP n c) (mulS (revP n c) (at' X c))
  | .proj k x => let X := eval n ms x; dense n fun c => if bitCount n c = k then at' X c else int 0
  | .compl x => complD n (eval n ms x)
  | .complInv x => complInvD n (eval n ms x)
  | .hodge x => let X := eval n ms x
      dense n fun c => mulS (mulS (signP (sigma n (notMask n c) c)) (metP ms n (notMask n c))) (at' X (notMask n c))
  | .pow x k => powD n ms (eval n ms x) k

variable {R : Type u} [CommRing R] {n : Nat} {g : Fin n → R} {ρ : List R} {vs : List (Cl g)}

theorem at'_dense {f : Nat → Poly} {c : Nat} (hc : c < 2 ^ n) : at' (dense n f) c = f c := by
  unfold at' dense
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hc]
  rfl

theorem length_dense (f : Nat → Poly) : (dense n f).length = 2 ^ n := by
  simp [dense]

/-- A dense vector represents a multivector: coordinate `c` is the coefficient
of blade `c`, for every `c < 2ⁿ`. -/
def Represents (X : List Poly) (x : Cl g) (ρ : List R) (vs : List (Cl g)) : Prop :=
  ∀ c < 2 ^ n, (at' X c).denote g ρ vs = x.coeff (BitVec.ofNat n c)

private theorem toNat_ofNat_lt' {a : Nat} (ha : a < 2 ^ n) : (BitVec.ofNat n a).toNat = a := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]

private theorem ofNat_xor (a b : Nat) : BitVec.ofNat n a ^^^ BitVec.ofNat n b = BitVec.ofNat n (a ^^^ b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_xor, Nat.testBit_mod_two_pow]
  cases decide (i < n) <;> simp

private theorem xor_lt {a b : Nat} (ha : a < 2 ^ n) (hb : b < 2 ^ n) : a ^^^ b < 2 ^ n := Nat.xor_lt_two_pow ha hb

theorem represents_twist {k : Nat → Nat → Poly} {K : BitVec n → BitVec n → R}
    (hk : ∀ a b, a < 2 ^ n → b < 2 ^ n → (k a b).denote g ρ vs = K (BitVec.ofNat n a) (BitVec.ofNat n b))
    {X Y : List Poly} {x y : Cl g} (hX : Represents X x ρ vs) (hY : Represents Y y ρ vs) :
    Represents (twistD n k X Y) (⟨twist K x.coeff y.coeff⟩ : Cl g) ρ vs := by
  intro c hc
  unfold twistD
  rw [at'_dense hc, denote_psum]
  show _ = bsum n fun a => x.coeff a * y.coeff (a ^^^ BitVec.ofNat n c) * K a (a ^^^ BitVec.ofNat n c)
  rw [bsum_eq_sumTo]
  refine sumTo_congr fun a ha => ?_
  rw [denote_mulS, denote_mulS, hX a ha, hY _ (xor_lt ha hc), hk a _ ha (xor_lt ha hc), ofNat_xor]

private theorem not_ofNat {c : Nat} (hc : c < 2 ^ n) : ~~~(BitVec.ofNat n c) = BitVec.ofNat n (notMask n c) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_not_eq, toNat_ofNat_lt' hc, notMask, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hc (by have := Nat.one_le_two_pow (n := n); omega))]

private theorem notMask_lt {c : Nat} (hc : c < 2 ^ n) : notMask n c < 2 ^ n :=
  Nat.xor_lt_two_pow hc (by have := Nat.one_le_two_pow (n := n); omega)

theorem represents_compl {X : List Poly} {x : Cl g} (hX : Represents X x ρ vs) :
    Represents (complD n X) (Cl.compl x) ρ vs := by
  intro c hc
  unfold complD
  rw [at'_dense hc, denote_mulS, denote_signP, hX _ (notMask_lt hc)]
  show _ = signOf (sign (~~~(BitVec.ofNat n c)) (BitVec.ofNat n c)) * x.coeff (~~~(BitVec.ofNat n c))
  rw [not_ofNat hc, sign, toNat_ofNat_lt' (notMask_lt hc), toNat_ofNat_lt' hc]

theorem represents_complInv {X : List Poly} {x : Cl g} (hX : Represents X x ρ vs) :
    Represents (complInvD n X) (Cl.complInv x) ρ vs := by
  intro c hc
  unfold complInvD
  rw [at'_dense hc, denote_mulS, denote_signP, hX _ (notMask_lt hc)]
  show _ = signOf (sign (BitVec.ofNat n c) (~~~(BitVec.ofNat n c))) * x.coeff (~~~(BitVec.ofNat n c))
  rw [not_ofNat hc, sign, toNat_ofNat_lt' (notMask_lt hc), toNat_ofNat_lt' hc]

/-- **Soundness of the dense coordinates.** -/
theorem represents_eval {ms : List Poly} (hms : MetricOK g ρ vs ms) :
    ∀ x : MExpr, Represents (x.eval n ms) (x.denote g ρ vs) ρ vs := by
  intro x
  induction x with
  | var i =>
    intro c hc; rw [MExpr.eval, at'_dense hc]; rfl
  | blade a =>
    intro c hc
    rw [MExpr.eval, at'_dense hc]
    show _ = if BitVec.ofNat n c = BitVec.ofNat n a then 1 else 0
    have hiff : BitVec.ofNat n c = BitVec.ofNat n a ↔ c = a % 2 ^ n := by
      constructor
      · intro h; have := congrArg BitVec.toNat h
        rwa [toNat_ofNat_lt' hc, BitVec.toNat_ofNat] at this
      · intro h; apply BitVec.eq_of_toNat_eq; rw [toNat_ofNat_lt' hc, BitVec.toNat_ofNat, h]
    by_cases h : c = a % 2 ^ n
    · rw [ite_eq_left h, ite_eq_left (hiff.mpr h)]; rfl
    · rw [ite_eq_right h, ite_eq_right (fun e => h (hiff.mp e))]; rfl
  | scalar p =>
    intro c hc
    rw [MExpr.eval, at'_dense hc]
    show _ = if BitVec.ofNat n c = 0 then p.denote g ρ vs else 0
    have hiff : BitVec.ofNat n c = 0 ↔ c = 0 := by
      constructor
      · intro h; have := congrArg BitVec.toNat h; rwa [toNat_ofNat_lt' hc] at this
      · intro h; subst h; rfl
    by_cases h : c = 0
    · rw [ite_eq_left h, ite_eq_left (hiff.mpr h)]
    · rw [ite_eq_right h, ite_eq_right (fun e => h (hiff.mp e))]; rfl
  | zero => intro c hc; rw [MExpr.eval, at'_dense hc]; rfl
  | one =>
    intro c hc
    rw [MExpr.eval, at'_dense hc]
    show _ = if BitVec.ofNat n c = 0 then 1 else 0
    have hiff : BitVec.ofNat n c = 0 ↔ c = 0 := by
      constructor
      · intro h; have := congrArg BitVec.toNat h; rwa [toNat_ofNat_lt' hc] at this
      · intro h; subst h; rfl
    by_cases h : c = 0
    · rw [ite_eq_left h, ite_eq_left (hiff.mpr h)]; rfl
    · rw [ite_eq_right h, ite_eq_right (fun e => h (hiff.mp e))]; rfl
  | add x y ihx ihy =>
    intro c hc
    simp only [MExpr.eval]
    rw [at'_dense hc, denote_addS, ihx c hc, ihy c hc]; rfl
  | sub x y ihx ihy =>
    intro c hc
    simp only [MExpr.eval]
    rw [at'_dense hc, denote_addS, denote_negS, ihx c hc, ihy c hc]
    show _ = _ - _
    grind
  | neg x ihx =>
    intro c hc
    simp only [MExpr.eval]
    rw [at'_dense hc, denote_negS, ihx c hc]; rfl
  | smul p x ihx =>
    intro c hc
    simp only [MExpr.eval]
    rw [at'_dense hc, denote_mulS, ihx c hc]; rfl
  | mul x y ihx ihy =>
    exact represents_twist (fun a b ha hb => denote_coefP hms ha hb) ihx ihy
  | wedge x y ihx ihy =>
    exact represents_twist (fun a b ha hb => denote_wcoefP ha hb) ihx ihy
  | contract x y ihx ihy =>
    exact represents_twist (fun a b ha hb => denote_ccoefP hms ha hb) ihx ihy
  | vee x y ihx ihy =>
    exact represents_complInv (represents_twist (fun a b ha hb => denote_wcoefP ha hb)
      (represents_compl ihx) (represents_compl ihy))
  | reverse x ihx =>
    intro c hc
    simp only [MExpr.eval]
    rw [at'_dense hc, denote_mulS, denote_revP hc, ihx c hc]; rfl
  | involute x ihx =>
    intro c hc
    simp only [MExpr.eval]
    rw [at'_dense hc, denote_mulS, denote_invP hc, ihx c hc]; rfl
  | clifford x ihx =>
    intro c hc
    simp only [MExpr.eval]
    rw [at'_dense hc, denote_mulS, denote_mulS, denote_invP hc, denote_revP hc, ihx c hc]; rfl
  | proj k x ihx =>
    intro c hc
    simp only [MExpr.eval]
    rw [at'_dense hc]
    show _ = if grade (BitVec.ofNat n c) = k then _ else 0
    rw [grade, toNat_ofNat_lt' hc]
    by_cases h : bitCount n c = k
    · rw [ite_eq_left h, ite_eq_left h, ihx c hc]
    · rw [ite_eq_right h, ite_eq_right h]; rfl
  | compl x ihx => exact represents_compl ihx
  | pow x k ihx =>
    induction k with
    | zero =>
      intro c hc
      simp only [MExpr.eval, powD]
      rw [at'_dense hc]
      show _ = if BitVec.ofNat n c = 0 then 1 else 0
      have hiff : BitVec.ofNat n c = 0 ↔ c = 0 := by
        constructor
        · intro h; have := congrArg BitVec.toNat h; rwa [toNat_ofNat_lt' hc] at this
        · intro h; subst h; rfl
      by_cases h : c = 0
      · rw [ite_eq_left h, ite_eq_left (hiff.mpr h)]; rfl
      · rw [ite_eq_right h, ite_eq_right (fun e => h (hiff.mp e))]; rfl
    | succ k ihk =>
      have := represents_twist (fun a b ha hb => denote_coefP hms ha hb) ihk ihx
      exact this
  | complInv x ihx => exact represents_complInv ihx
  | hodge x ihx =>
    intro c hc
    simp only [MExpr.eval]
    rw [at'_dense hc, denote_mulS, denote_mulS, denote_signP, denote_metP hms _ n (Nat.le_refl n),
      ihx _ (notMask_lt hc)]
    show _ = signOf (sign (~~~(BitVec.ofNat n c)) (BitVec.ofNat n c)) * mf g (~~~(BitVec.ofNat n c))
      * (MExpr.denote g ρ vs x).coeff (~~~(BitVec.ofNat n c))
    rw [not_ofNat hc, sign, mf, toNat_ofNat_lt' (notMask_lt hc), toNat_ofNat_lt' hc]

theorem length_powD (ms X : List Poly) (k : Nat) : (powD n ms X k).length = 2 ^ n := by
  cases k <;> simp [powD, twistD, length_dense]

theorem length_eval (ms : List Poly) (x : MExpr) : (x.eval n ms).length = 2 ^ n := by
  cases x <;> simp [MExpr.eval, twistD, complInvD, complD, length_dense, length_powD]

end Dense

/-! ## The soundness theorem -/

section Sound

variable {R : Type u} [CommRing R] {n : Nat} {g : Fin n → R} {ρ : List R} {vs : List (Cl g)}

/-- Pointwise equality of two coordinate lists. -/
def AllEq (g : Fin n → R) (ρ : List R) (vs : List (Cl g)) : List Poly → List Poly → Prop
  | [], [] => True
  | p :: ps, q :: qs => p.denote g ρ vs = q.denote g ρ vs ∧ AllEq g ρ vs ps qs
  | _, _ => False

theorem AllEq.coord : ∀ {xs ys : List Poly}, AllEq g ρ vs xs ys → ∀ c,
    (at' xs c).denote g ρ vs = (at' ys c).denote g ρ vs
  | [], [], _, _ => rfl
  | p :: ps, q :: qs, h, c => by
    cases c with
    | zero => exact h.1
    | succ c => exact AllEq.coord (xs := ps) (ys := qs) h.2 c
  | [], _ :: _, h, _ => absurd h id
  | _ :: _, [], h, _ => absurd h id

theorem AllEq.of_coord : ∀ {xs ys : List Poly}, xs.length = ys.length →
    (∀ c, (at' xs c).denote g ρ vs = (at' ys c).denote g ρ vs) → AllEq g ρ vs xs ys
  | [], [], _, _ => trivial
  | p :: ps, q :: qs, hl, h => ⟨h 0, AllEq.of_coord (by simpa using hl) fun c => h (c + 1)⟩
  | [], _ :: _, hl, _ => absurd hl (by simp)
  | _ :: _, [], hl, _ => absurd hl (by simp)

/-- **The `clifford` tactic's soundness theorem**: multivector expressions with
equal coordinate polynomials are equal. -/
theorem eq_of_coords {ms : List Poly} (hms : MetricOK g ρ vs ms) (x y : MExpr)
    (h : AllEq g ρ vs (x.eval n ms) (y.eval n ms)) : x.denote g ρ vs = y.denote g ρ vs := by
  ext a
  have ha : a = BitVec.ofNat n a.toNat := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt a.isLt]
  rw [ha, ← represents_eval hms x _ a.isLt, ← represents_eval hms y _ a.isLt]
  exact h.coord _

/-- The converse: equal multivectors have equal coordinate polynomials (used to
turn multivector hypotheses into coordinate hypotheses). -/
theorem coords_of_eq {ms : List Poly} (hms : MetricOK g ρ vs ms) (x y : MExpr)
    (h : x.denote g ρ vs = y.denote g ρ vs) : AllEq g ρ vs (x.eval n ms) (y.eval n ms) := by
  refine AllEq.of_coord (by rw [length_eval, length_eval]) fun c => ?_
  by_cases hc : c < 2 ^ n
  · rw [represents_eval hms x c hc, represents_eval hms y c hc, h]
  · have hx : at' (x.eval n ms) c = int 0 := by
      unfold at'
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [length_eval]; omega)]; rfl
    have hy : at' (y.eval n ms) c = int 0 := by
      unfold at'
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [length_eval]; omega)]; rfl
    rw [hx, hy]

end Sound

end Grassmann.Tactic
