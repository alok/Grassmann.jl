/-
The SWAR population count is correct on all 64-bit masks.

`Bits.popcount` counts bits in parallel ("SIMD within a register"): it replaces
each 2-bit field by its bit count, adds neighbouring fields into 4-bit and then
8-bit fields, and sums the eight bytes with one multiplication by
`0x0101010101010101`. `popcount_eq_bitCount` proves it equal to the plain bit
count `bitCount 64` for **all** `UInt64`s.

Method: numbers are written as little-endian field sums `fs w m f = Σ_j f j 2^{wj}`.
Every SWAR step is then an identity between field sums (`fs_add`, `fs_sub`,
`fs_and`, `fs_regroup`, `fs_div`), valid because no field ever overflows
(bounds tracked explicitly), and the final multiplication is one polynomial
identity plus a bound on the prefix sums. The bit count is the sum of the
fields at every stage (`fsum_pairs`).
-/
import DirectSum.Proofs.Sign

namespace DirectSum.Proofs

/-! ## Field sums -/

/-- `fs w m f = f 0 + 2^w f 1 + … + 2^{w(m-1)} f (m-1)`: the number with the
`w`-bit fields `f 0, …, f (m-1)` (little-endian). -/
def fs (w : Nat) : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | m + 1, f => f 0 + 2 ^ w * fs w m (fun j => f (j + 1))

/-- `fsum m f = f 0 + … + f (m-1)`. -/
def fsum : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | m + 1, f => f 0 + fsum m (fun j => f (j + 1))

theorem fs_congr {w m : Nat} {f f' : Nat → Nat} (h : ∀ j < m, f j = f' j) : fs w m f = fs w m f' := by
  induction m generalizing f f' with
  | zero => rfl
  | succ m ih => simp only [fs]; rw [h 0 (by omega), ih (fun j hj => h (j + 1) (by omega))]

theorem fsum_congr {m : Nat} {f f' : Nat → Nat} (h : ∀ j < m, f j = f' j) : fsum m f = fsum m f' := by
  induction m generalizing f f' with
  | zero => rfl
  | succ m ih => simp only [fsum]; rw [h 0 (by omega), ih (fun j hj => h (j + 1) (by omega))]

/-- A field sum with fields below `2^w` is below `2^{wm}`. -/
theorem fs_lt {w m : Nat} {f : Nat → Nat} (h : ∀ j < m, f j < 2 ^ w) : fs w m f < 2 ^ (w * m) := by
  induction m generalizing f with
  | zero => simp [fs]
  | succ m ih =>
    simp only [fs]
    have h0 := h 0 (by omega)
    have h1 := ih (f := fun j => f (j + 1)) (fun j hj => h (j + 1) (by omega))
    have hp : 2 ^ (w * (m + 1)) = 2 ^ w * 2 ^ (w * m) := by
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
    rw [hp]
    have : 2 ^ w * fs w m (fun j => f (j + 1)) + 2 ^ w ≤ 2 ^ w * 2 ^ (w * m) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h1
    omega

/-- Field sums add field by field (always: this is linearity, no carries involved). -/
theorem fs_add (w m : Nat) (f g : Nat → Nat) : fs w m f + fs w m g = fs w m (fun j => f j + g j) := by
  induction m generalizing f g with
  | zero => rfl
  | succ m ih =>
    simp only [fs]
    rw [← ih]
    grind

/-- Fieldwise smaller gives smaller. -/
theorem fs_le {w m : Nat} {f g : Nat → Nat} (h : ∀ j < m, g j ≤ f j) : fs w m g ≤ fs w m f := by
  induction m generalizing f g with
  | zero => exact Nat.le_refl 0
  | succ m ih =>
    simp only [fs]
    have := ih (f := fun j => f (j + 1)) (g := fun j => g (j + 1)) (fun j hj => h (j + 1) (by omega))
    have := h 0 (by omega)
    have := Nat.mul_le_mul_left (2 ^ w) ‹fs w m (fun j => g (j + 1)) ≤ fs w m (fun j => f (j + 1))›
    omega

/-- Field sums subtract field by field when every field of the subtrahend is smaller. -/
theorem fs_sub {w m : Nat} {f g : Nat → Nat} (h : ∀ j < m, g j ≤ f j) :
    fs w m f - fs w m g = fs w m (fun j => f j - g j) := by
  have e : fs w m g + fs w m (fun j => f j - g j) = fs w m f := by
    rw [fs_add]; exact fs_congr fun j hj => by have := h j hj; omega
  omega

/-- Dropping the lowest field (division by `2^w`). -/
theorem fs_div {w m : Nat} {f : Nat → Nat} (h0 : f 0 < 2 ^ w) :
    fs w (m + 1) f / 2 ^ w = fs w m (fun j => f (j + 1)) := by
  simp only [fs]
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos w), Nat.div_eq_of_lt h0, Nat.zero_add]

/-- The top-down recursion: one more field on top. -/
theorem fs_succ_top (w m : Nat) (f : Nat → Nat) : fs w (m + 1) f = fs w m f + 2 ^ (w * m) * f m := by
  induction m generalizing f with
  | zero => simp [fs]
  | succ m ih =>
    rw [fs, ih (fun j => f (j + 1)), fs]
    have hp : 2 ^ (w * (m + 1)) = 2 ^ w * 2 ^ (w * m) := by rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
    rw [hp]; grind

/-- The top field of a field sum. -/
theorem fs_div_top {w m : Nat} {f : Nat → Nat} (h : ∀ j < m, f j < 2 ^ w) :
    fs w (m + 1) f / 2 ^ (w * m) = f m := by
  rw [fs_succ_top, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (fs_lt h), Nat.zero_add]

private theorem testBit_field (a b w j : Nat) (ha : a < 2 ^ w) :
    (a + 2 ^ w * b).testBit j = if j < w then a.testBit j else b.testBit (j - w) := by
  rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ ha]

/-- Field sums `and` field by field (fields below `2^w`). -/
theorem fs_and {w m : Nat} {f g : Nat → Nat} (hf : ∀ j < m, f j < 2 ^ w) (hg : ∀ j < m, g j < 2 ^ w) :
    fs w m f &&& fs w m g = fs w m (fun j => f j &&& g j) := by
  induction m generalizing f g with
  | zero => simp [fs]
  | succ m ih =>
    simp only [fs]
    rw [← ih (fun j hj => hf (j + 1) (by omega)) (fun j hj => hg (j + 1) (by omega))]
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and, testBit_field _ _ _ _ (hf 0 (by omega)), testBit_field _ _ _ _ (hg 0 (by omega)),
      testBit_field _ _ _ _ (Nat.and_lt_two_pow _ (hg 0 (by omega))), Nat.testBit_and, Nat.testBit_and]
    split <;> rfl

/-- Two neighbouring `w`-bit fields make one `2w`-bit field. -/
theorem fs_regroup (w m : Nat) (f : Nat → Nat) :
    fs w (2 * m) f = fs (2 * w) m (fun j => f (2 * j) + 2 ^ w * f (2 * j + 1)) := by
  induction m generalizing f with
  | zero => rfl
  | succ m ih =>
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, fs, fs, ih]
    simp only [fs]
    have e : ∀ j, (2 * j + 1 + 1) = 2 * (j + 1) := fun j => by omega
    have e' : ∀ j, (2 * j + 1 + 1 + 1) = 2 * (j + 1) + 1 := fun j => by omega
    simp only [e, Nat.mul_zero, Nat.zero_add]
    have hp : 2 ^ (2 * w) = 2 ^ w * 2 ^ w := by rw [Nat.two_mul, Nat.pow_add]
    rw [hp]; grind

/-- Summing neighbouring fields pairwise keeps the total. -/
theorem fsum_pairs (m : Nat) (f : Nat → Nat) : fsum m (fun j => f (2 * j) + f (2 * j + 1)) = fsum (2 * m) f := by
  induction m generalizing f with
  | zero => rfl
  | succ m ih =>
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, fsum, fsum, fsum]
    have := ih (fun j => f (j + 2))
    simp only [show ∀ j, 2 * j + 2 = 2 * (j + 1) from fun j => by omega,
      show ∀ j, 2 * j + 1 + 2 = 2 * (j + 1) + 1 from fun j => by omega] at this
    simp only [Nat.mul_zero, Nat.zero_add]
    rw [← this]; omega

/-- A sum of `m` fields bounded by `B` is at most `m B`. -/
theorem fsum_le {m B : Nat} {f : Nat → Nat} (h : ∀ j < m, f j ≤ B) : fsum m f ≤ m * B := by
  induction m generalizing f with
  | zero => simp [fsum]
  | succ m ih =>
    simp only [fsum]
    have := ih (f := fun j => f (j + 1)) (fun j hj => h (j + 1) (by omega))
    have := h 0 (by omega)
    rw [Nat.succ_mul]; omega

theorem fsum_succ_top (m : Nat) (f : Nat → Nat) : fsum (m + 1) f = fsum m f + f m := by
  induction m generalizing f with
  | zero => simp [fsum]
  | succ m ih => rw [fsum, ih, fsum]; omega

/-- The bit count is the sum of the bits. -/
theorem bitCount_eq_fsum (m x : Nat) : bitCount m x = fsum m (fun i => (x.testBit i).toNat) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [bitCount_succ, fsum_succ_top, ih]

/-- The binary expansion as a field sum of width 1. -/
theorem fs_bits {m x : Nat} (hx : x < 2 ^ m) : x = fs 1 m (fun i => (x.testBit i).toNat) := by
  induction m generalizing x with
  | zero => simp at hx; simp [hx, fs]
  | succ m ih =>
    simp only [fs]
    have hx2 : x / 2 < 2 ^ m := by rw [Nat.pow_succ] at hx; omega
    have := ih hx2
    have e : (fun j => (x.testBit (j + 1)).toNat) = fun j => ((x / 2).testBit j).toNat := by
      funext j; rw [Nat.testBit_add_one]
    rw [e, ← this, Nat.testBit_zero]
    have := Nat.mod_two_eq_zero_or_one x
    rcases this with h | h <;> simp [h] <;> omega

/-! ## The SWAR steps -/

private theorem and_low (u v w : Nat) (hu : u < 2 ^ w) : (u + 2 ^ w * v) &&& (2 ^ w - 1) = u := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu]

private theorem toNat_le_one (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide

/-- **The SWAR population count is the bit count, for every 64-bit mask.** -/
theorem popcount_eq_bitCount (x : UInt64) : Bits.popcount x = bitCount 64 x.toNat := by
  -- the bits of `x`
  let X := x.toNat
  have hX : X < 2 ^ 64 := x.toNat_lt
  let b : Nat → Nat := fun i => (X.testBit i).toNat
  have hb : ∀ i, b i ≤ 1 := fun i => toNat_le_one _
  have hb64 : ∀ i, 64 ≤ i → b i = 0 := fun i hi => by
    simp [b, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hX (Nat.pow_le_pow_right (by decide) hi))]
  -- step 1: 2-bit fields hold the bit counts `c j = b (2j) + b (2j+1)`
  let c : Nat → Nat := fun j => b (2 * j) + b (2 * j + 1)
  have hc : ∀ j, c j ≤ 2 := fun j => by
    show b (2 * j) + b (2 * j + 1) ≤ 2
    have := hb (2 * j); have := hb (2 * j + 1); omega
  have hX2 : X = fs 2 32 (fun j => b (2 * j) + 2 ^ 1 * b (2 * j + 1)) := by
    conv => lhs; rw [fs_bits hX]
    rw [show (64 : Nat) = 2 * 32 from rfl, fs_regroup]
  have hshr1 : X >>> 1 = fs 2 32 (fun j => b (2 * j + 1) + 2 ^ 1 * b (2 * j + 1 + 1)) := by
    rw [Nat.shiftRight_eq_div_pow]
    conv => lhs; rw [fs_bits hX]
    rw [show (64 : Nat) = 63 + 1 from rfl, fs_div (by have := hb 0; simp only [b] at this ⊢; omega)]
    rw [show fs 1 63 (fun j => (X.testBit (j + 1)).toNat) = fs 1 64 (fun j => (X.testBit (j + 1)).toNat) from by
      rw [fs_succ_top 1 63]; simp [Nat.testBit_lt_two_pow hX]]
    rw [show (64 : Nat) = 2 * 32 from rfl, fs_regroup]
  have hm1 : (0x5555555555555555 : Nat) = fs 2 32 (fun _ => 1) := by decide
  have hE : (X >>> 1) &&& 0x5555555555555555 = fs 2 32 (fun j => b (2 * j + 1)) := by
    rw [hshr1, hm1, fs_and (fun j _ => by have := hb (2 * j + 1); have := hb (2 * j + 1 + 1); omega)
      (fun _ _ => by decide)]
    exact fs_congr fun j _ => by
      have h1 := hb (2 * j + 1); have h2 := hb (2 * j + 1 + 1)
      rcases (by omega : b (2 * j + 1) = 0 ∨ b (2 * j + 1) = 1) with e1 | e1 <;>
        rcases (by omega : b (2 * j + 1 + 1) = 0 ∨ b (2 * j + 1 + 1) = 1) with e2 | e2 <;>
        rw [e1, e2] <;> decide
  have hEle : (X >>> 1) &&& 0x5555555555555555 ≤ X := by
    rw [hE, hX2]; exact fs_le fun j _ => by omega
  have ht1 : X - ((X >>> 1) &&& 0x5555555555555555) = fs 2 32 c := by
    rw [hE, hX2, fs_sub (fun j _ => by omega)]
    exact fs_congr fun j _ => by show _ = b (2 * j) + b (2 * j + 1); omega
  -- step 2: 4-bit fields hold `d i = c (2i) + c (2i+1)`
  let d : Nat → Nat := fun i => c (2 * i) + c (2 * i + 1)
  have hd : ∀ i, d i ≤ 4 := fun i => by
    show c (2 * i) + c (2 * i + 1) ≤ 4
    have := hc (2 * i); have := hc (2 * i + 1); omega
  have hc32 : ∀ j, 32 ≤ j → c j = 0 := fun j hj => by
    show b (2 * j) + b (2 * j + 1) = 0
    rw [hb64 _ (by omega), hb64 _ (by omega)]
  have hm2 : (0x3333333333333333 : Nat) = fs 4 16 (fun _ => 2 ^ 2 - 1) := by decide
  have hlo : fs 2 32 c &&& 0x3333333333333333 = fs 4 16 (fun i => c (2 * i)) := by
    rw [show (32 : Nat) = 2 * 16 from rfl, fs_regroup, hm2,
      fs_and (fun i _ => by
          have := hc (2 * i); have := hc (2 * i + 1)
          show c (2 * i) + 2 ^ 2 * c (2 * i + 1) < 2 ^ (2 * 2); omega)
        (fun _ _ => by decide)]
    exact fs_congr fun i _ => and_low _ _ 2 (by have := hc (2 * i); omega)
  have hhi : (fs 2 32 c >>> 2) &&& 0x3333333333333333 = fs 4 16 (fun i => c (2 * i + 1)) := by
    rw [Nat.shiftRight_eq_div_pow, show (32 : Nat) = 31 + 1 from rfl,
      fs_div (by have := hc 0; omega)]
    rw [show fs 2 31 (fun j => c (j + 1)) = fs 2 32 (fun j => c (j + 1)) from by
      rw [fs_succ_top 2 31, hc32 32 (by omega)]; simp]
    rw [show (32 : Nat) = 2 * 16 from rfl, fs_regroup, hm2,
      fs_and (fun i _ => by
          have := hc (2 * i + 1); have := hc (2 * i + 1 + 1)
          show c (2 * i + 1) + 2 ^ 2 * c (2 * i + 1 + 1) < 2 ^ (2 * 2); omega)
        (fun _ _ => by decide)]
    exact fs_congr fun i _ => and_low _ _ 2 (by have := hc (2 * i + 1); omega)
  have ht2 : (fs 2 32 c &&& 0x3333333333333333) + ((fs 2 32 c >>> 2) &&& 0x3333333333333333) = fs 4 16 d := by
    rw [hlo, hhi, fs_add]
  -- step 3: bytes hold `e k = d (2k) + d (2k+1)`
  let e : Nat → Nat := fun k => d (2 * k) + d (2 * k + 1)
  have he : ∀ k, e k ≤ 8 := fun k => by
    show d (2 * k) + d (2 * k + 1) ≤ 8
    have := hd (2 * k); have := hd (2 * k + 1); omega
  have hd16 : ∀ i, 16 ≤ i → d i = 0 := fun i hi => by
    show c (2 * i) + c (2 * i + 1) = 0
    rw [hc32 _ (by omega), hc32 _ (by omega)]
  have hsh4 : fs 4 16 d >>> 4 = fs 4 16 (fun i => d (i + 1)) := by
    rw [Nat.shiftRight_eq_div_pow, show (16 : Nat) = 15 + 1 from rfl, fs_div (by have := hd 0; omega)]
    rw [fs_succ_top 4 15 (fun i => d (i + 1)), hd16 16 (by omega)]; simp
  have hsum3 : fs 4 16 d + fs 4 16 d >>> 4 = fs 4 16 (fun i => d i + d (i + 1)) := by
    rw [hsh4, fs_add]
  have hsum3lt : fs 4 16 d + fs 4 16 d >>> 4 < 2 ^ 64 := by
    rw [hsum3]
    exact fs_lt (w := 4) (m := 16) fun i _ => by have := hd i; have := hd (i + 1); omega
  have hm4 : (0x0F0F0F0F0F0F0F0F : Nat) = fs 8 8 (fun _ => 2 ^ 4 - 1) := by decide
  have ht3 : (fs 4 16 d + fs 4 16 d >>> 4) &&& 0x0F0F0F0F0F0F0F0F = fs 8 8 e := by
    rw [hsum3, show (16 : Nat) = 2 * 8 from rfl, fs_regroup, hm4,
      fs_and (fun k _ => by
          have := hd (2 * k); have := hd (2 * k + 1); have := hd (2 * k + 1 + 1)
          show d (2 * k) + d (2 * k + 1) + 2 ^ 4 * (d (2 * k + 1) + d (2 * k + 1 + 1)) < 2 ^ (2 * 4)
          omega)
        (fun _ _ => by decide)]
    exact fs_congr fun k _ => and_low _ _ 4 (by have := hd (2 * k); have := hd (2 * k + 1); omega)
  -- step 4: the multiplication sums the bytes into the top byte
  have hmul : (fs 8 8 e * 0x0101010101010101) % 2 ^ 64 / 2 ^ 56 = fsum 8 e := by
    let P : Nat → Nat := fun p => fsum (p + 1) e
    have hP : fs 8 8 e * 0x0101010101010101 = fs 8 8 P + 2 ^ 64 *
        ((e 1 + e 2 + e 3 + e 4 + e 5 + e 6 + e 7) + 2 ^ 8 * (e 2 + e 3 + e 4 + e 5 + e 6 + e 7)
          + 2 ^ 16 * (e 3 + e 4 + e 5 + e 6 + e 7) + 2 ^ 24 * (e 4 + e 5 + e 6 + e 7)
          + 2 ^ 32 * (e 5 + e 6 + e 7) + 2 ^ 40 * (e 6 + e 7) + 2 ^ 48 * e 7) := by
      simp only [fs, fsum, P]
      grind
    have hPb : ∀ p < 8, P p < 2 ^ 8 := fun p hp => by
      have := fsum_le (m := p + 1) (B := 8) (f := e) (fun j _ => he j)
      show fsum (p + 1) e < 2 ^ 8
      have : (p + 1) * 8 ≤ 64 := by omega
      omega
    have hPlt : fs 8 8 P < 2 ^ 64 := fs_lt hPb
    rw [hP, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hPlt,
      show (8 : Nat) = 7 + 1 from rfl, show (56 : Nat) = 8 * 7 from rfl,
      fs_div_top (fun p hp => hPb p (by omega))]
  -- the bit count is the sum of the fields at every stage
  have hcount : fsum 8 e = bitCount 64 X := by
    rw [show fsum 8 e = fsum 16 d from fsum_pairs 8 d, show fsum 16 d = fsum 32 c from fsum_pairs 16 c,
      show fsum 32 c = fsum 64 b from fsum_pairs 32 b, bitCount_eq_fsum]
  -- from `UInt64` to `Nat`
  have l1 : (0x5555555555555555 : UInt64).toNat = 0x5555555555555555 := by decide
  have l2 : (0x3333333333333333 : UInt64).toNat = 0x3333333333333333 := by decide
  have l4 : (0x0F0F0F0F0F0F0F0F : UInt64).toNat = 0x0F0F0F0F0F0F0F0F := by decide
  have lh : (0x0101010101010101 : UInt64).toNat = 0x0101010101010101 := by decide
  have s1 : (1 : UInt64).toNat % 64 = 1 := by decide
  have s2 : (2 : UInt64).toNat % 64 = 2 := by decide
  have s4 : (4 : UInt64).toNat % 64 = 4 := by decide
  have s56 : (56 : UInt64).toNat % 64 = 56 := by decide
  simp only [Bits.popcount]
  have hle : ((x >>> 1) &&& (0x5555555555555555 : UInt64)) ≤ x := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_and, UInt64.toNat_shiftRight, s1, l1]; exact hEle
  have hx1 : (x - ((x >>> 1) &&& (0x5555555555555555 : UInt64))).toNat = fs 2 32 c := by
    rw [UInt64.toNat_sub_of_le _ _ hle, UInt64.toNat_and, UInt64.toNat_shiftRight, s1, l1]; exact ht1
  generalize x - ((x >>> 1) &&& (0x5555555555555555 : UInt64)) = y at hx1 ⊢
  have hx2 : ((y &&& (0x3333333333333333 : UInt64)) + ((y >>> 2) &&& (0x3333333333333333 : UInt64))).toNat = fs 4 16 d := by
    rw [UInt64.toNat_add, UInt64.toNat_and, UInt64.toNat_and, UInt64.toNat_shiftRight, s2, l2, hx1, ht2,
      Nat.mod_eq_of_lt (fs_lt (w := 4) (m := 16) fun i _ => by have := hd i; omega)]
  generalize (y &&& (0x3333333333333333 : UInt64)) + ((y >>> 2) &&& (0x3333333333333333 : UInt64)) = z at hx2 ⊢
  have hx3 : ((z + (z >>> 4)) &&& (0x0F0F0F0F0F0F0F0F : UInt64)).toNat = fs 8 8 e := by
    rw [UInt64.toNat_and, UInt64.toNat_add, UInt64.toNat_shiftRight, s4, l4, hx2, Nat.mod_eq_of_lt hsum3lt]
    exact ht3
  generalize (z + (z >>> 4)) &&& (0x0F0F0F0F0F0F0F0F : UInt64) = u at hx3 ⊢
  rw [UInt64.toNat_shiftRight, s56, UInt64.toNat_mul, lh, hx3, Nat.shiftRight_eq_div_pow, hmul, hcount]

end DirectSum.Proofs
