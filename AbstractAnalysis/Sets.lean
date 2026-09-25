import AbstractAnalysis.Sequence

/-!
# Countable sets

The enumerations of src/AbstractAnalysis.jl:327-420: `Integers`, Stern's
diatomic sequence (`SternBrocot`), the Calkin–Wilf `PositiveRationals` and
`Rationals`, Szudzik's "elegant" pairing (`ElegantPairs`), Cantor pairing,
Gaussian integers/rationals and the primes.

What the proofs buy:
* `fusc` runs in `O(log n)` over the binary digits of `n`, yet it provably
  satisfies Julia's (exponential) defining recursion `sternbrocot`
  (`fusc_double`, `fusc_double_add_one`), and consecutive terms are coprime
  (`fusc_coprime`), so `positiveRational` never needs a gcd.
* The elegant pairing is a bijection `ℕ ≃ ℕ × ℕ` (`elegantPair_unpair`,
  `elegantUnpair_pair`): every pair is enumerated exactly once.
* Julia's `cantorinversion` is wrong (quirk #13): it is kept as
  `Julia.cantorInversion`, and `cantorUnpair` is the correct inverse of
  `cantorPair`, checked in the tests.
-/

namespace AbstractAnalysis

open JuliaBase

/-! ## Integers -/

/-- Julia `integer(n) = iseven(n) ? n÷2 : -(n÷2)`: `1 ↦ 0, 2 ↦ 1, 3 ↦ -1, 4 ↦ 2, …`. -/
def integer (n : Nat) : Int := if n % 2 = 0 then ((n / 2 : Nat) : Int) else -((n / 2 : Nat) : Int)

/-! ## Stern's diatomic sequence -/

/-- Worker for `fusc`: consumes the binary digits of `n`, maintaining the
linear form `a·fusc(n) + b·fusc(n+1)`. `fuel ≥ n` suffices. -/
def fuscGo : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, b => b
  | fuel + 1, n, a, b =>
    if n = 0 then b
    else if n % 2 = 1 then fuscGo fuel (n / 2) a (a + b)
    else fuscGo fuel (n / 2) (a + b) b

/-- Stern's diatomic sequence `fusc(n)` (Julia `sternbrocot(n)`,
src/AbstractAnalysis.jl:363-372), computed in `O(log n)`. -/
def fusc (n : Nat) : Nat := fuscGo (n + 1) n 1 0

/-- Any fuel `≥ n` gives the same answer. -/
theorem fuscGo_fuel (f g n a b : Nat) (hf : n ≤ f) (hg : n ≤ g) :
    fuscGo f n a b = fuscGo g n a b := by
  induction f generalizing g n a b with
  | zero =>
    have : n = 0 := by omega
    subst this; cases g <;> simp [fuscGo]
  | succ f ih =>
    cases g with
    | zero => have : n = 0 := by omega
              subst this; simp [fuscGo]
    | succ g =>
      simp only [fuscGo]
      split
      · rfl
      · have h1 : n / 2 ≤ f := by omega
        have h2 : n / 2 ≤ g := by omega
        split <;> exact ih _ _ _ _ h1 h2

/-- The worker is linear in its accumulator `(a, b)`. -/
theorem fuscGo_linear (f n a b : Nat) :
    fuscGo f n a b = a * fuscGo f n 1 0 + b * fuscGo f n 0 1 := by
  induction f generalizing n a b with
  | zero => simp [fuscGo]
  | succ f ih =>
    simp only [fuscGo]
    split
    · simp
    · split
      · rw [ih _ a (a + b), ih _ 1 1]; grind
      · rw [ih _ (a + b) b, ih _ 1 1]; grind

/-- One step on an odd digit. -/
theorem fuscGo_odd (f m a b : Nat) : fuscGo (f + 1) (2 * m + 1) a b = fuscGo f m a (a + b) := by
  simp only [fuscGo, show 2 * m + 1 ≠ 0 by omega, show (2 * m + 1) % 2 = 1 by omega,
    show (2 * m + 1) / 2 = m by omega, ite_false, ite_true]

/-- One step on an even digit. -/
theorem fuscGo_even (f m a b : Nat) (hm : 0 < m) : fuscGo (f + 1) (2 * m) a b = fuscGo f m (a + b) b := by
  simp only [fuscGo, show 2 * m ≠ 0 by omega, show ¬ (2 * m) % 2 = 1 by omega,
    show (2 * m) / 2 = m by omega, ite_false]

/-- The second coordinate of the linear form is `fusc (n + 1)`. -/
theorem fuscGo_zero_one (n : Nat) : fuscGo (n + 1) n 0 1 = fusc (n + 1) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold fusc
    obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 := ⟨n / 2, by omega⟩
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [fuscGo]
      · rw [fuscGo_even _ _ _ _ hm, fuscGo_odd]
        exact fuscGo_fuel _ _ _ _ _ (by omega) (by omega)
    · have e2 : 2 * m + 1 + 1 = 2 * (m + 1) := by omega
      rw [fuscGo_odd, e2, fuscGo_even _ _ _ _ (by omega), Nat.zero_add, Nat.add_zero]
      have ihm := ih m (by omega)
      unfold fusc at ihm
      rw [fuscGo_fuel (2 * m + 1) (m + 1) _ _ _ (by omega) (by omega), ihm,
        fuscGo_fuel (m + 1 + 1) (2 * (m + 1)) _ _ _ (by omega) (by omega)]

/-- Julia's even case: `sternbrocot(2m) = sternbrocot(m)`. -/
theorem fusc_double (m : Nat) : fusc (2 * m) = fusc m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rfl
  · unfold fusc
    rw [fuscGo_even _ _ _ _ hm]
    exact fuscGo_fuel _ _ _ _ _ (by omega) (by omega)

/-- Julia's odd case: `sternbrocot(2m+1) = sternbrocot(m) + sternbrocot(m+1)`. -/
theorem fusc_double_add_one (m : Nat) : fusc (2 * m + 1) = fusc m + fusc (m + 1) := by
  unfold fusc
  rw [fuscGo_odd, fuscGo_linear, fuscGo_fuel (2 * m + 1) (m + 1) m 1 0 (by omega) (by omega),
    fuscGo_fuel (2 * m + 1) (m + 1) m 0 1 (by omega) (by omega), fuscGo_zero_one]
  unfold fusc; simp

/-- Consecutive Stern numbers are coprime, so `fusc n // fusc (n+1)` is already
in lowest terms (the Calkin–Wilf tree). -/
theorem fusc_coprime (n : Nat) : Nat.gcd (fusc n) (fusc (n + 1)) = 1 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 := ⟨n / 2, by omega⟩
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · decide
      · rw [fusc_double, fusc_double_add_one, Nat.gcd_comm, Nat.add_comm,
          Nat.gcd_add_self_left, Nat.gcd_comm]
        exact ih m (by omega)
    · have h2 : 2 * m + 1 + 1 = 2 * (m + 1) := by omega
      rw [h2, fusc_double, fusc_double_add_one, Nat.gcd_add_self_left]
      exact ih m (by omega)

/-- The memo recurrence of Julia `sternbrocot(a, n)`: `a[n÷2]` for even `n`,
`a[k] + a[k+1]` for odd `n = 2k+1` (1-based storage). -/
def sternBrocotStep (a : Array Nat) (n : Nat) : Nat :=
  if n % 2 = 0 then a[n / 2 - 1]! else a[(n - 1) / 2 - 1]! + a[(n - 1) / 2]!

/-- Julia `SternBrocot = SequenceArray([1], sternbrocot)`. -/
def SternBrocot : SequenceVector Nat := ⟨#[1], sternBrocotStep⟩

/-! ## Rationals (Calkin–Wilf) -/

/-- Julia `positiverational(n) = sternbrocot(n) // sternbrocot(n+1)`. -/
def positiveRational (n : Nat) : Rat := ((fusc n : Int) : Rat) / ((fusc (n + 1) : Nat) : Rat)

/-- Julia `rational(z)`: `0` at `z = 1`, then `±positiverational(|integer z|)`. -/
def rational (z : Nat) : Rat :=
  let n := integer z
  if n = 0 then 0 else if n > 0 then positiveRational n.natAbs else -positiveRational n.natAbs

/-- Julia `nonzerorational(n) = rational(n + 1)`. -/
def nonzeroRational (n : Nat) : Rat := rational (n + 1)

/-! ## Pairings -/

/-- Julia `elegantinversion(n)`: Szudzik's unpairing from 0,
`s = ⌊√n⌋, r = n - s²; r < s ? (r, s) : (s, r - s)` (src/AbstractAnalysis.jl:333-341).
Julia takes `⌊√n⌋` in `Float64`, which agrees with `Nat.sqrt` for `n < 2^52`. -/
def elegantUnpair (n : Nat) : Nat × Nat :=
  let s := n.sqrt
  let r := n - s * s
  if r < s then (r, s) else (s, r - s)

/-- Szudzik's pairing, the inverse of `elegantUnpair`. -/
def elegantPair (a b : Nat) : Nat := if a < b then b * b + a else a * a + a + b

/-- `⌊√n⌋` is characterised by its bounds. -/
theorem sqrt_eq_of_bounds {s n : Nat} (h1 : s * s ≤ n) (h2 : n < (s + 1) * (s + 1)) : n.sqrt = s := by
  have ht1 := Nat.sqrt_le n
  have ht2 := Nat.lt_succ_sqrt n
  rcases Nat.lt_trichotomy n.sqrt s with h | h | h
  · have : (n.sqrt + 1) * (n.sqrt + 1) ≤ s * s := Nat.mul_le_mul h h
    simp only [Nat.succ_eq_add_one] at ht2; omega
  · exact h
  · have : (s + 1) * (s + 1) ≤ n.sqrt * n.sqrt := Nat.mul_le_mul h h
    omega

/-- Pairing after unpairing is the identity: `ElegantPairs0` enumerates without gaps. -/
theorem elegantPair_unpair (n : Nat) : elegantPair (elegantUnpair n).1 (elegantUnpair n).2 = n := by
  have h1 := Nat.sqrt_le n
  have h2 := Nat.lt_succ_sqrt n
  simp only [Nat.succ_eq_add_one] at h2
  unfold elegantUnpair
  generalize n.sqrt = s at h1 h2 ⊢
  have h3 : n - s * s ≤ 2 * s := by grind
  by_cases h : n - s * s < s
  · simp only [h, ite_true, elegantPair]; omega
  · simp only [h, ite_false, elegantPair, show ¬ s < n - s * s - s by omega]; omega

/-- Unpairing after pairing is the identity: `ElegantPairs0` enumerates without repeats. -/
theorem elegantUnpair_pair (a b : Nat) : elegantUnpair (elegantPair a b) = (a, b) := by
  unfold elegantPair
  split
  · have hs : (b * b + a).sqrt = b := sqrt_eq_of_bounds (by omega) (by grind)
    simp [elegantUnpair, hs]; omega
  · have hs : (a * a + a + b).sqrt = a := sqrt_eq_of_bounds (by omega) (by grind)
    simp only [elegantUnpair, hs]
    rw [ite_eq_right (by omega)]; simp; omega

/-- Julia `elegantinversion(n, k)`: the pairing offset by `k`
(src/AbstractAnalysis.jl:344-352). -/
def elegantUnpairFrom (k n : Nat) : Nat × Nat :=
  let p := elegantUnpair (n - k)
  (p.1 + k, p.2 + k)

/-- Julia's `cantorinversion(n)` as written (**quirk #13**: `t = (w²+2)÷2` instead
of `(w²+w)÷2`, giving e.g. `(4, -1)` at `n = 9`). -/
def Julia.cantorInversion (n : Nat) : Int × Int :=
  let w : Int := ((Nat.sqrt (8 * n + 1) - 1) / 2 : Nat)
  let t : Int := (w ^ 2 + 2) / 2
  ((n : Int) - t, w - n + t)

/-- Cantor's pairing `(x, y) ↦ (x+y)(x+y+1)/2 + x`. -/
def cantorPair (x y : Nat) : Nat := (x + y) * (x + y + 1) / 2 + x

/-- The correct Cantor unpairing: `w = ⌊(√(8n+1) - 1)/2⌋`, `t = w(w+1)/2`,
`(n - t, w - (n - t))`. -/
def cantorUnpair (n : Nat) : Nat × Nat :=
  let w := (Nat.sqrt (8 * n + 1) - 1) / 2
  let t := w * (w + 1) / 2
  (n - t, w - (n - t))

/-! ## The standard countable sets (src/AbstractAnalysis.jl:396-413) -/

/-- Julia `Integers`. -/
def Integers (len : Nat := 100) : CountableVector Int := ⟨integer, len⟩
/-- Julia `PositiveRationals`. -/
def PositiveRationals (len : Nat := 100) : CountableVector Rat := ⟨positiveRational, len⟩
/-- Julia `Rationals`. -/
def Rationals (len : Nat := 100) : CountableVector Rat := ⟨rational, len⟩
/-- Julia `NonzeroRationals`. -/
def NonzeroRationals (len : Nat := 100) : CountableVector Rat := ⟨nonzeroRational, len⟩
/-- Julia `CantorPairs` (buggy, reproduced). -/
def CantorPairs (len : Nat := 100) : CountableVector (Int × Int) := ⟨Julia.cantorInversion, len⟩
/-- Julia `ElegantPairs0`. -/
def ElegantPairs0 (len : Nat := 100) : CountableVector (Nat × Nat) := ⟨elegantUnpair, len⟩
/-- Julia `ElegantPairs1` (= `ElegantPairs`). -/
def ElegantPairs1 (len : Nat := 100) : CountableVector (Nat × Nat) := ⟨elegantUnpairFrom 1, len⟩

/-- Julia `elegantproduct(a, b, op)`: `n ↦ op(a(i), b(j))` with
`(i, j) = elegantinversion1(n)`, length 100 (src/AbstractAnalysis.jl:355-361). -/
def elegantProduct {α β γ : Type} (a : CountableVector α) (b : CountableVector β) (op : α → β → γ) :
    CountableVector γ :=
  ⟨fun n => let (i, j) := elegantUnpairFrom 1 n; op (a.f i) (b.f j), 100⟩

/-- Julia `GaussianNaturals = map(complextuple, ElegantPairs1)`. -/
def GaussianNaturals (len : Nat := 100) : CountableVector (Complex Int) :=
  (ElegantPairs1 len).map fun (i, j) => ⟨i, j⟩
/-- Julia `GaussianIntegers = map(complextuple, elegantpair(Integers, Integers))`. -/
def GaussianIntegers : CountableVector (Complex Int) := elegantProduct (Integers) (Integers) Complex.mk
/-- Julia `GaussianRationals`. -/
def GaussianRationals : CountableVector (Complex Rat) := elegantProduct (Rationals) (Rationals) Complex.mk

/-! ## Primes (Julia's `PrimesExt` weak dependency) -/

/-- Trial division by the stored primes (all primes `< p` are present). -/
def isPrimeGiven (ps : Array Nat) (p : Nat) : Bool :=
  go 0 ps.size
where
  /-- Scan until `q² > p`. -/
  go (i : Nat) : Nat → Bool
    | 0 => true
    | fuel + 1 =>
      match ps[i]? with
      | none => true
      | some q => if q * q > p then true else if p % q = 0 then false else go (i + 1) fuel

/-- The recurrence of Julia `PrimeCache = SequenceArray([2], prime)`: the next
prime after the last stored one. -/
def nextPrimeStep (ps : Array Nat) (_k : Nat) : Nat :=
  let last := ps.back?.getD 1
  go (last + 1) (last + 2)
where
  /-- Bertrand's postulate bounds the search by `last + 2`… `2·last`. -/
  go (c : Nat) : Nat → Nat
    | 0 => c
    | fuel + 1 => if isPrimeGiven ps c then c else go (c + 1) fuel

/-- Julia `PrimeCache`. -/
def PrimeCache : SequenceVector Nat := ⟨#[2], nextPrimeStep⟩

/-- Julia `prime(i)`: the `i`-th prime (1-based). -/
def prime (i : Nat) : Nat := (PrimeCache.get i).1

/-- Julia `PrimeIntegers = CountableVector{Int}(prime)`. -/
def PrimeIntegers (len : Nat := 100) : CountableVector Nat :=
  let cache := PrimeCache.resize len
  ⟨fun i => (cache.get i).1, len⟩

end AbstractAnalysis
