/- Original-Nat ingress boundaries and adversarial wrapping controls.
Attribution: independent Lean port of Michael Reed/chakravala's Grassmann ecosystem. -/
import Tests.Dynamic.RotorDecode
import Grassmann.MaskIngress

open Grassmann DirectSum DirectSum.Bits GrassmannTests
open scoped BitVec

namespace DynamicTests.MaskIngress

/-- Generic clients recover the original value from a checked word, without coefficient laws. -/
theorem originalValue {n raw : Nat} {w : UInt64} (h : Grassmann.MaskIngress.word? n raw = some w) :
    w.toNat = raw := (Grassmann.MaskIngress.word?_sound h).2.2

/-- First-overflow rejection is universal, rather than a bounded test enumeration. -/
theorem firstOverflow (n : Nat) : Grassmann.MaskIngress.bitVec? n (2^n) = none :=
  (Grassmann.MaskIngress.bitVec?_eq_none_iff n (2^n)).mpr (by omega)

/-- Consumers retain arbitrary coefficients exactly; no Coeff instance is needed. -/
theorem coefficientCopy {V : TensorBundle} {G raw : Nat} {α : Type} {x : α}
    {s : Single V G α} (h : Grassmann.MaskIngress.single? raw x = some s) : s.val = x :=
  (Grassmann.MaskIngress.single?_sound h).2.2.2.2

example : True := by
  fail_if_success have : (8 : Nat) < 2^3 := by decide
  fail_if_success have : UInt64 := Grassmann.MaskIngress.word? 3 1
  fail_if_success have : Submanifold ℝ3 1 := Grassmann.MaskIngress.blade? 1
  trivial

/-- Widths distinguish semantic BitVec capacity, word capacity, and printable descriptors. -/
def widths : List Nat := [0,1,3,8,62,63,64,65,128]

/-- Ten checks per width, including exact boundary, overflow, and wrapping contrast. -/
def checkWidth (t : Tally) (n : Nat) : Tally := Id.run do
  let maximum := 2^n - 1
  let overflow := 2^n
  let checked := Grassmann.MaskIngress.bitVec? n
  let word := Grassmann.MaskIngress.word? n
  let expectedZero : Option Nat := if n ≤ 64 then some 0 else none
  let expectedMaximum : Option Nat := if n ≤ 64 then some maximum else none
  let maximumProof : maximum < 2^n := Nat.sub_lt (Nat.two_pow_pos n) (by decide)
  let bounded := BitVec.ofNatLT maximum maximumProof
  let mut t := t
  t := t.check ((checked 0).map BitVec.toNat == some 0) s!"mask-ingress/{n}: scalar"
  t := t.check ((checked maximum).map BitVec.toNat == some maximum)
    s!"mask-ingress/{n}: exact maximum"
  t := t.check ((checked overflow).isNone) s!"mask-ingress/{n}: first overflow"
  t := t.check ((checked (overflow+1)).isNone) s!"mask-ingress/{n}: overflow plus one"
  t := t.check ((word 0).map UInt64.toNat == expectedZero) s!"mask-ingress/{n}: word scalar"
  t := t.check ((word maximum).map UInt64.toNat == expectedMaximum)
    s!"mask-ingress/{n}: word maximum"
  t := t.check ((word overflow).isNone) s!"mask-ingress/{n}: word overflow"
  t := t.check ((word (overflow+1)).isNone) s!"mask-ingress/{n}: word overflow plus one"
  t := t.check (checked bounded.toNat == some bounded) s!"mask-ingress/{n}: bounded roundtrip"
  t := t.check ((BitVec.ofNat n (overflow+1)).toNat == (if n == 0 then 0 else 1))
    s!"mask-ingress/{n}: unchanged modular BitVec conversion"
  return t

/-- Exact ingress and typed-blade integration, including over-wide and coefficient controls. -/
def run : IO Tally := do
  let mut t : Tally := {}
  for n in widths do t := checkWidth t n
  let huge := 2^64+1
  t := t.check ((Grassmann.MaskIngress.word? 64 huge).isNone)
    "mask-ingress: original 2^64+1 never becomes word one"
  t := t.check ((Grassmann.MaskIngress.bitVec? 65 huge).map BitVec.toNat == some huge)
    "mask-ingress: wider abstract masks preserve original 2^64+1"
  t := t.check ((Grassmann.MaskIngress.bitVec? 64 huge).isNone)
    "mask-ingress: 64-bit abstract ingress rejects 2^64+1"
  t := t.check (huge.toUInt64 == 1)
    "mask-ingress: legacy UInt64 narrowing still wraps"
  t := t.check ((Grassmann.MaskIngress.word? 3 huge).isNone &&
    (Submanifold.ofBits? (V := ℝ3) (G := 1) huge.toUInt64).isSome)
    "mask-ingress: checking after conversion cannot recover lost original bits"
  t := t.check ((Grassmann.MaskIngress.word? 64 (2^64)).isNone && (2^64 : Nat).toUInt64 == 0)
    "mask-ingress: first word overflow cannot masquerade as scalar zero"
  t := t.check ((Grassmann.MaskIngress.blade? (V := ℝ3) (G := 2) 3).map
    (fun b => b.bits.toNat) == some 3)
    "mask-ingress: typed e12 admission"
  t := t.check ((Grassmann.MaskIngress.blade? (V := ℝ3) (G := 1) 3).isNone)
    "mask-ingress: wrong static grade rejection"
  t := t.check ((Grassmann.MaskIngress.blade? (V := ℝ3) (G := 1) 8).isNone)
    "mask-ingress: original first invalid R3 bit rejection"
  t := t.check ((Grassmann.MaskIngress.blade? (V := ℝ3) (G := 1) huge).isNone)
    "mask-ingress: typed huge original rejection"
  t := t.check ((Grassmann.MaskIngress.blade? (V := TensorBundle.sig 0) (G := 0) 0).isSome)
    "mask-ingress: zero-width typed scalar"
  t := t.check ((Grassmann.MaskIngress.blade? (V := TensorBundle.sig 0) (G := 0) 1).isNone)
    "mask-ingress: zero-width overflow rejection"
  t := t.check ((Grassmann.MaskIngress.blade? (V := TensorBundle.sig 64) (G := 64)
    (2^64-1)).map (fun b => b.bits.toNat) == some (2^64-1))
    "mask-ingress: full executable word width preserves maximum"
  t := t.check ((Grassmann.MaskIngress.blade? (V := TensorBundle.sig 65) (G := 1) 1).isNone)
    "mask-ingress: typed width 65 rejects representational incompatibility"
  t := t.check ((Grassmann.MaskIngress.single? (V := ℝ3) (G := 2) 3 (-2/3 : Rat)).map
    (fun s => (s.bits.toNat,s.val)) == some (3,-2/3))
    "mask-ingress: exact rational scaled blade"
  t := t.check ((Grassmann.MaskIngress.single? (V := ℝ3) (G := 0) 3 (7 : Int)).isNone)
    "mask-ingress: scaled blade grade rejection"
  t := t.check ((Grassmann.MaskIngress.single? (V := ℝ3) (G := 1) huge (7 : Int)).isNone)
    "mask-ingress: scaled blade original overflow rejection"
  t := t.check ((Grassmann.MaskIngress.single? (V := ℝ3) (G := 1) 1 "payload").map
    (fun s => s.val) == some "payload")
    "mask-ingress: copying needs no coefficient operations"
  t := t.check ((Grassmann.MaskIngress.single? (V := ℝ3) (G := 1) 1 (-0.0 : Float)).map
    (fun s => s.val.toBits) == some (-0.0 : Float).toBits)
    "mask-ingress: exact signed-zero coefficient copying"
  t := t.check ((Grassmann.MaskIngress.bitVec? 3 9).isNone && (9#3).toNat == 1)
    "mask-ingress: ordinary literal wrapping stays separate from checked ingress"
  let literal : BitVec 3 := 7#'(by decide)
  t := t.check ((Grassmann.MaskIngress.word? 3 literal.toNat) == some (Proofs.mask literal))
    "mask-ingress: proof-bound literal uses existing word bridge"
  t := t.check ((Grassmann.MaskIngress.bitVec? 128 (2^128+1)).isNone &&
    (Grassmann.MaskIngress.word? 128 0).isNone)
    "mask-ingress: large abstract overflow and small over-wide word are distinct"
  return t

end DynamicTests.MaskIngress
