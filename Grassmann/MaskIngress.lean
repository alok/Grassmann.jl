/- Checked original-Nat mask ingress; existing executable masks remain UInt64.
Attribution: independent Lean port of Michael Reed/chakravala's Grassmann ecosystem. -/
import Grassmann.Proofs.Link
import Grassmann.Types.Single

namespace Grassmann.MaskIngress
open DirectSum DirectSum.Bits

/-- Preserve an original natural mask exactly, or reject values outside the semantic width.
Unlike ordinary BitVec literals, this checks before any modular conversion. -/
def bitVec? (n raw : Nat) : Option (BitVec n) :=
  if h : raw < 2^n then some (BitVec.ofNatLT raw h) else none

/-- Exact ingress succeeds at every in-range original value, including width zero's scalar. -/
theorem bitVec?_of_lt {n raw : Nat} (h : raw < 2^n) :
    bitVec? n raw = some (BitVec.ofNatLT raw h) := by simp [bitVec?, h]

/-- Rejection is exactly semantic-width overflow; arbitrary dimensions remain supported. -/
theorem bitVec?_eq_none_iff (n raw : Nat) : bitVec? n raw = none ↔ 2^n ≤ raw := by
  by_cases h : raw < 2^n <;> simp [bitVec?, h] <;> omega

/-- Successful ingress preserves the original unbounded natural value without truncation. -/
theorem bitVec?_toNat {n raw : Nat} {b : BitVec n} (h : bitVec? n raw = some b) :
    b.toNat = raw := by
  by_cases hr : raw < 2^n
  · have hb : BitVec.ofNatLT raw hr = b := by simpa [bitVec?, hr] using h
    rw [← hb]
    rfl
  · simp [bitVec?, hr] at h

/-- Every already proof-bounded mask round-trips through checked Nat ingress. -/
theorem bitVec?_roundTrip {n : Nat} (b : BitVec n) : bitVec? n b.toNat = some b := by
  rw [bitVec?_of_lt b.isLt]
  rfl

/-- Checked executable-word ingress, reusing the existing BitVec-to-UInt64 proof bridge.
Widths above 64 are incompatible even when the original value is zero. -/
def word? (n raw : Nat) : Option UInt64 :=
  if n ≤ 64 then (bitVec? n raw).map Proofs.mask else none

/-- The exact in-range word is produced only at a compatible semantic width. -/
theorem word?_of_lt {n raw : Nat} (hn : n ≤ 64) (hr : raw < 2^n) :
    word? n raw = some (Proofs.mask (BitVec.ofNatLT raw hr)) := by
  simp [word?, hn, bitVec?_of_lt hr]

/-- Word ingress rejects incompatible widths or original-value overflow, before narrowing. -/
theorem word?_eq_none_iff (n raw : Nat) :
    word? n raw = none ↔ 64 < n ∨ 2^n ≤ raw := by
  by_cases hn : n ≤ 64
  · by_cases hr : raw < 2^n <;> simp [word?, bitVec?, hn, hr] <;> omega
  · simp [word?, hn]
    omega

/-- Accepted words carry compatible width, original bounds, and exact original value. -/
theorem word?_sound {n raw : Nat} {w : UInt64} (h : word? n raw = some w) :
    n ≤ 64 ∧ raw < 2^n ∧ w.toNat = raw := by
  by_cases hn : n ≤ 64
  · by_cases hr : raw < 2^n
    · have hw : Proofs.mask (BitVec.ofNatLT raw hr) = w := by
        simpa [word?, bitVec?, hn, hr] using h
      rw [← hw]
      exact ⟨hn, hr, Proofs.toNat_mask hn (BitVec.ofNatLT raw hr)⟩
    · simp [word?, bitVec?, hn, hr] at h
  · simp [word?, hn] at h

/-- Compatible proof-bounded masks reuse the existing bridge without changing its word. -/
theorem word?_bridge {n : Nat} (hn : n ≤ 64) (b : BitVec n) :
    word? n b.toNat = some (Proofs.mask b) := by simp [word?, hn, bitVec?_roundTrip]

/-- An existing word whose original natural value fits the requested width round-trips. -/
theorem word?_roundTrip {n : Nat} (hn : n ≤ 64) (w : UInt64) (hw : w.toNat < 2^n) :
    word? n w.toNat = some w := by
  rw [word?_of_lt hn hw]
  congr 1
  apply UInt64.toNat_inj.mp
  exact Proofs.toNat_mask hn (BitVec.ofNatLT w.toNat hw)

/-- Original-Nat typed blade ingress composes exact word admission with the existing grade check.
This does not certify the descriptor's metric, a mesh, or tangent multiplicities. -/
def blade? {V : TensorBundle} {G : Nat} (raw : Nat) : Option (Submanifold V G) :=
  (word? V.n raw).bind Submanifold.ofBits?

private theorem guard_some {α : Type} (ok : Bool) (a b : α)
    (h : (if ok then some a else none) = some b) : a = b ∧ ok = true := by
  cases ok <;> simp_all

/-- An admitted typed blade preserves the original mask, semantic width, and expected grade. -/
theorem blade?_sound {V : TensorBundle} {G raw : Nat} {b : Submanifold V G}
    (h : blade? raw = some b) :
    V.n ≤ 64 ∧ b.bits.toNat = raw ∧ raw < 2^V.n ∧ popcount b.bits = G := by
  obtain ⟨w, hw, hb⟩ := Option.bind_eq_some_iff.mp h
  have hg := guard_some
    (popcount w == G && w &&& ~~~(lowMask V.n) == 0) (⟨w⟩ : Submanifold V G) b hb
  have bitsEq : w = b.bits := congrArg Submanifold.bits hg.1
  have hs := word?_sound hw
  have gradeEq : popcount w = G := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hg.2).1
  exact ⟨hs.1, (congrArg UInt64.toNat bitsEq.symm).trans hs.2.2, hs.2.1,
    (congrArg popcount bitsEq.symm).trans gradeEq⟩

/-- Original-Nat scaled-blade ingress reuses the existing grade check and copies its coefficient.
No coefficient operations or algebraic laws are required. -/
@[specialize] def single? {V : TensorBundle} {G : Nat} {α : Type}
    (raw : Nat) (value : α) : Option (Single V G α) :=
  (word? V.n raw).bind (fun w => Single.ofBits? w value)

/-- An admitted scaled blade preserves exact mask, width, grade and the original coefficient. -/
theorem single?_sound {V : TensorBundle} {G raw : Nat} {α : Type} {value : α}
    {s : Single V G α} (h : single? raw value = some s) :
    V.n ≤ 64 ∧ s.bits.toNat = raw ∧ raw < 2^V.n ∧ popcount s.bits = G ∧ s.val = value := by
  obtain ⟨w, hw, hs⟩ := Option.bind_eq_some_iff.mp h
  have hg := guard_some
    (popcount w == G && w &&& ~~~(lowMask V.n) == 0) (⟨w, value⟩ : Single V G α) s hs
  have bitsEq : w = s.bits := congrArg Single.bits hg.1
  have valueEq : value = s.val := congrArg Single.val hg.1
  have hwf := word?_sound hw
  have gradeEq : popcount w = G := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hg.2).1
  exact ⟨hwf.1, (congrArg UInt64.toNat bitsEq.symm).trans hwf.2.2, hwf.2.1,
    (congrArg popcount bitsEq.symm).trans gradeEq, valueEq.symm⟩

end Grassmann.MaskIngress
