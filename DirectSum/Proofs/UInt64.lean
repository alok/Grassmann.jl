/-
The fast bit-parallel sign kernels equal the specification on all 64-bit masks.

`Bits.reorderParity a b = parity (a &&& prefixParity b)` computes the reordering
sign with a Hillis-Steele prefix-xor scan and a folded parity: about twenty ALU
operations, no loop. `Bits.reorderParity_eq_spec_4` checked it by `decide` for
4-bit masks; here it is proved for all `2¹²⁸` pairs of `UInt64` masks.

## Method: linearity plus a basis check

Every function involved is `𝔽₂`-linear in its argument (a composite of shifts
and xors), and a linear functional on `𝔽₂⁶⁴` is determined by its values on the
64 unit vectors `1 <<< k`. `linear_eq_xorSum` proves this once, by induction on
the number of low bits; the 64 (resp. 64 × 64) values on unit vectors are then
closed terms, checked by kernel evaluation (`decide +kernel`, no
`native_decide`). The rest is bookkeeping with `Nat.testBit`.

## Results

* `parity_eq_bitParity`: `Bits.parity x` is the parity of the popcount;
* `prefixParity_testBit`: bit `i` of `prefixParity b` is the parity of the bits
  of `b` below `i`;
* `reorderParity_eq_sigma`, `reorderParity_eq_spec`: the fast reordering parity
  is `σ` (and the repository's naive `reorderParitySpec`) on all `UInt64`s;
* `reorderParity_cocycle`: hence the implementation itself satisfies the
  2-cocycle identity;
* `parityjoin_eq`, `signOf_parityjoin`: Julia's `parityjoin` (the geometric
  product sign of a signature space) is the spec blade coefficient.
-/
import DirectSum.Proofs.Metric
import DirectSum.Parity

namespace DirectSum.Proofs

open Bits

/-! ## Linear functionals on `UInt64` -/

/-- `1 <<< k` is `2^k` below 64. -/
theorem toNat_shl_one {k : Nat} (hk : k < 64) : ((1 : UInt64) <<< k.toUInt64).toNat = 2 ^ k := by
  rw [UInt64.toNat_shiftLeft, UInt64.toNat_one, Nat.toUInt64_eq, UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt (Nat.lt_trans hk (by decide)), Nat.mod_eq_of_lt hk, Nat.one_shiftLeft,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hk)]

/-- The low `m` bits of `x`, xor the next one, are the low `m+1` bits. -/
theorem low_succ (x : UInt64) {m : Nat} (hm : m < 64) :
    UInt64.ofNat (x.toNat % 2 ^ (m + 1))
      = UInt64.ofNat (x.toNat % 2 ^ m) ^^^ (if x.toNat.testBit m then (1 : UInt64) <<< m.toUInt64 else 0) := by
  apply UInt64.toNat_inj.mp
  have hlt : ∀ k, k ≤ 64 → x.toNat % 2 ^ k < 2 ^ 64 := fun k hk =>
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos k)) (Nat.pow_le_pow_right (by decide) hk)
  rw [UInt64.toNat_xor, UInt64.toNat_ofNat', UInt64.toNat_ofNat', Nat.mod_eq_of_lt (hlt _ (by omega)),
    Nat.mod_eq_of_lt (hlt _ (by omega))]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  split
  · rw [toNat_shl_one hm, Nat.testBit_two_pow]
    by_cases hi : i < m
    · simp [hi, show i < m + 1 by omega, show m ≠ i by omega]
    · by_cases hi' : i = m
      · subst hi'; simp_all
      · simp [hi, show ¬ i < m + 1 by omega, show m ≠ i by omega]
  · rename_i h
    rw [UInt64.toNat_zero, Nat.zero_testBit]
    by_cases hi : i < m
    · simp [hi, show i < m + 1 by omega]
    · by_cases hi' : i = m
      · subst hi'; simp_all
      · simp [hi, show ¬ i < m + 1 by omega]

/-- An `𝔽₂`-linear functional on `UInt64` is determined by its values on the unit
vectors `1 <<< k`: `F x = ⨁_{k < 64} x_k · F(1 <<< k)`. -/
theorem linear_eq_xorSum (F : UInt64 → Bool) (h0 : F 0 = false)
    (hlin : ∀ x y, F (x ^^^ y) = (F x ^^ F y)) (x : UInt64) :
    F x = xorSum (fun k => x.toNat.testBit k && F ((1 : UInt64) <<< k.toUInt64)) 64 := by
  have key : ∀ m ≤ 64, F (UInt64.ofNat (x.toNat % 2 ^ m))
      = xorSum (fun k => x.toNat.testBit k && F ((1 : UInt64) <<< k.toUInt64)) m := by
    intro m hm
    induction m with
    | zero =>
      show F (UInt64.ofNat (x.toNat % 2 ^ 0)) = false
      rw [Nat.pow_zero, Nat.mod_one]; exact h0
    | succ m ih =>
      rw [low_succ x (by omega), hlin, ih (by omega)]
      simp only [xorSum]
      cases x.toNat.testBit m <;> simp [h0]
  have := key 64 (Nat.le_refl _)
  rwa [Nat.mod_eq_of_lt x.toNat_lt, UInt64.ofNat_toNat] at this

/-! ## `parity` -/

/-- One folding step `x ^^^ (x >>> k)` of `Bits.parity`. -/
private def foldStep (k : UInt64) (x : UInt64) : UInt64 := x ^^^ (x >>> k)

private theorem foldStep_xor (k x y : UInt64) : foldStep k (x ^^^ y) = foldStep k x ^^^ foldStep k y := by
  simp only [foldStep, UInt64.shiftRight_xor]
  ac_rfl

private theorem and_one_eq (x : UInt64) : ((x &&& 1) == 1) = x.toNat.testBit 0 := by
  have h : (x &&& 1).toNat = x.toNat % 2 := by
    rw [UInt64.toNat_and, UInt64.toNat_one, Nat.and_one_is_mod]
  have e : (x &&& 1 = 1) ↔ x.toNat % 2 = 1 := by rw [← UInt64.toNat_inj, h, UInt64.toNat_one]
  rw [Nat.testBit_zero, Bool.eq_iff_iff]
  simp only [beq_iff_eq, decide_eq_true_eq]
  exact e

private theorem parity_eq_fold (x : UInt64) :
    parity x = (foldStep 1 (foldStep 2 (foldStep 4 (foldStep 8 (foldStep 16 (foldStep 32 x)))))).toNat.testBit 0 := by
  rw [← and_one_eq]; rfl

private theorem parity_xor (x y : UInt64) : parity (x ^^^ y) = (parity x ^^ parity y) := by
  simp only [parity_eq_fold, foldStep_xor, UInt64.toNat_xor, Nat.testBit_xor]

private theorem parity_unit : ∀ k : Fin 64, parity ((1 : UInt64) <<< k.1.toUInt64) = true := by
  decide +kernel

/-- `Bits.parity` (six folding xors) is the parity of the popcount. -/
theorem parity_eq_bitParity (x : UInt64) : parity x = bitParity 64 x.toNat := by
  rw [linear_eq_xorSum parity (by decide) parity_xor, bitParity_eq_xorSum]
  exact xorSum_congr fun k hk => by rw [parity_unit ⟨k, hk⟩, Bool.and_true]

/-! ## `prefixParity` -/

/-- One scan step `y ^^^ (y <<< k)` of `Bits.prefixParity`. -/
private def scanStep (k : UInt64) (y : UInt64) : UInt64 := y ^^^ (y <<< k)

private theorem scanStep_xor (k x y : UInt64) : scanStep k (x ^^^ y) = scanStep k x ^^^ scanStep k y := by
  simp only [scanStep, UInt64.shiftLeft_xor]
  ac_rfl

private theorem prefixParity_eq_scan (b : UInt64) :
    prefixParity b = scanStep 32 (scanStep 16 (scanStep 8 (scanStep 4 (scanStep 2 (scanStep 1 (b <<< 1)))))) :=
  rfl

private theorem prefixParity_xor (x y : UInt64) :
    prefixParity (x ^^^ y) = prefixParity x ^^^ prefixParity y := by
  simp only [prefixParity_eq_scan, UInt64.shiftLeft_xor, scanStep_xor]

private theorem prefixParity_unit :
    ∀ i k : Fin 64, (prefixParity ((1 : UInt64) <<< k.1.toUInt64)).toNat.testBit i.1 = decide (k.1 < i.1) := by
  decide +kernel

/-- Bit `i` of `Bits.prefixParity b` (a Hillis-Steele prefix-xor scan) is the
parity of the bits of `b` strictly below `i`. -/
theorem prefixParity_testBit (b : UInt64) {i : Nat} (hi : i < 64) :
    (prefixParity b).toNat.testBit i = bitParity i b.toNat := by
  have := linear_eq_xorSum (fun b => (prefixParity b).toNat.testBit i) (by simp [prefixParity])
    (fun x y => by simp only [prefixParity_xor, UInt64.toNat_xor, Nat.testBit_xor]) b
  rw [this, bitParity_eq_xorSum, ← xorSum_and_lt _ (Nat.le_of_lt hi)]
  exact xorSum_congr fun k hk => by rw [prefixParity_unit ⟨i, hi⟩ ⟨k, hk⟩]

/-! ## The reordering parity -/

/-- **The fast reordering parity is `σ`** on every pair of 64-bit masks. -/
theorem reorderParity_eq_sigma (a b : UInt64) : reorderParity a b = sigma 64 a.toNat b.toNat := by
  rw [reorderParity, parity_eq_bitParity, bitParity_eq_xorSum, sigma_eq_xorSum]
  exact xorSum_congr fun k hk => by
    rw [UInt64.toNat_and, Nat.testBit_and, prefixParity_testBit b hk]

/-- **The fast reordering parity meets its naive specification on all `UInt64`
masks** (`reorderParity_eq_spec_4` checked 4-bit masks by `decide`). -/
theorem reorderParity_eq_spec (a b : UInt64) :
    reorderParity a b = reorderParitySpec 64 a.toNat b.toNat := by
  rw [reorderParity_eq_sigma, reorderParitySpec_eq_sigma]

/-- The implementation's reordering parity satisfies the 2-cocycle identity. -/
theorem reorderParity_cocycle (a b c : UInt64) :
    (reorderParity a b ^^ reorderParity (a ^^^ b) c) = (reorderParity b c ^^ reorderParity a (b ^^^ c)) := by
  simp only [reorderParity_eq_sigma, UInt64.toNat_xor, sigma_cocycle]

/-- Swapping two blades in the implementation: `σ(a,b) + σ(b,a) ≡ |a||b| + |a∧b|`. -/
theorem reorderParity_swap (a b : UInt64) :
    (reorderParity a b ^^ reorderParity b a)
      = ((parity a && parity b) ^^ parity (a &&& b)) := by
  simp only [reorderParity_eq_sigma, parity_eq_bitParity, UInt64.toNat_and, sigma_swap]

/-! ## Signature spaces -/

/-- Julia `parityjoin(S, a, b)` (the sign of `e_a e_b` in the signature `S`) is
the reordering sign plus the parity of the shared negative generators. -/
theorem parityjoin_eq (s a b : UInt64) :
    parityjoin s a b = (sigma 64 a.toNat b.toNat ^^ bitParity 64 (a.toNat &&& b.toNat &&& s.toNat)) := by
  unfold parityjoin
  rw [reorderParity_eq_sigma, parity_eq_bitParity, UInt64.toNat_and, UInt64.toNat_and]

/-- **The geometric-product sign of every signature space is the spec blade
coefficient**, for every pair of 64-bit masks and in every commutative ring:
`(-1)^{parityjoin s a b} = bladeCoef (sigMetric s) 64 a b`. -/
theorem signOf_parityjoin {R : Type _} [Lean.Grind.CommRing R] (s a b : UInt64) :
    (signOf (parityjoin s a b) : R) = bladeCoef (sigMetric s.toNat) 64 a.toNat b.toNat := by
  rw [parityjoin_eq, bladeCoef_sigMetric]

end DirectSum.Proofs
