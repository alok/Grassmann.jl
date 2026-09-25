import PrimitiveBits
import Tests.AbstractLattices.Harness

/-!
PrimitiveBits tests: goldens from `oracle/primitivebits/gen.jl`
(`oracle/golden/primitivebits/bits.json`) plus the verbatim examples of
port-notes/small-algebra.md §6.2.
-/

open PrimitiveBits PrimitiveBits.Bits Tests.Small

namespace Tests.PrimitiveBits

/-! Compile-time checks (port-notes §6.2). -/

-- `PrimitiveBits16(7)[2:4] → Bool[1, 1, 0]`; statically bounds-checked indexing
example : (ofUInt16 7)[2] = true ∧ (ofUInt16 7)[3] = true ∧ (ofUInt16 7)[4] = false := by decide
example : (ofUInt16 7).toNat = 7 := by decide
-- out of range is a type error for `b[i]`, and `true` for Julia's indexer (quirk)
example : Julia.getindex (ofUInt16 7) 0 = true ∧ Julia.getindex (ofUInt16 7) 17 = true := by decide
example : (ofVector #v[true, false, true, true, false, false, false, false]).toNat = 13 := by decide
#guard toString (ofUInt16 7) == "[1110000000000000]"
#guard toString (ofUInt8 129) == "[10000001]"
#guard (ofBools (w := 8) #[true, false, true, true]).toOption.map toString == some "[10110000]"
#guard toString (ofNatMod 128 (2 ^ 127)) == "[" ++ String.ofList (List.replicate 127 '0') ++ "1]"
#guard toString (ofUInt64 0xFFFFFFFFFFFFFFFF) == "[" ++ String.ofList (List.replicate 64 '1') ++ "]"
#guard (ofInt? 8 300 |>.toOption).isNone && (ofInt? 8 (-1) |>.toOption).isNone

/-- Oracle comparison against `bits.json`. -/
def golden : TestM Unit := do
  let j ← readJson "oracle/golden/primitivebits/bits.json"
  for c in ← gArr j "words" do
    let w ← gNat c "w"
    let v ← gNat c "value"
    let b := ofNatMod w v
    let lbl := s!"w={w} v={v}"
    checkEq s!"{lbl} str" (toString b) (← gStr c "str")
    checkEq s!"{lbl} back" b.toNat (← gNat c "back")
    let idx ← (← jArr (← jField c "idx")).mapM jInt
    let iv ← jBools (← jField c "idxval")
    for (i, e) in idx.zip iv do
      checkEq s!"{lbl} b[{i}]" (Julia.getindex b i) e
    checkEq s!"{lbl} b[:]" b.toArray (← jBools (← jField c "all"))
    checkEq s!"{lbl} b[2:5]" (Julia.getRange b 2 5) (← jBools (← jField c "range25"))
    checkEq s!"{lbl} b[0:3]" (Julia.getRange b 0 3) (← jBools (← jField c "range03"))
    -- checked indexing agrees with the Julia indexer in range
    check s!"{lbl} get?" ((List.range w).all fun i => b.get? (i + 1) == some (Julia.getindex b (i + 1)))
  for c in ← gArr j "bools" do
    let w ← gNat c "w"
    let bits ← jBools (← jField c "bits")
    match (ofBools (w := w) bits) with
    | .ok b =>
      checkEq s!"ofBools {bits} value" b.toNat (← gNat c "value")
      checkEq s!"ofBools {bits} str" (toString b) (← gStr c "str")
    | .error e => check s!"ofBools {bits}" false fun _ => e
  for c in ← gArr j "errors" do
    let w ← gNat c "w"
    let case ← gStr c "case"
    let expected : Option String := (← jField c "err").getStr?.toOption
    let got : Option String ←
      match case with
      | "empty" => pure (errName (ofBools (w := w) #[]))
      | "overflow_bools" | "leading_zeros" =>
        pure (errName (ofBools (w := w) (← jBools (← jField c "bits"))))
      | _ =>
        let n ← match (← gStr c "int").toInt? with
          | some n => pure n
          | none => throw <| IO.userError "bad int"
        pure (errName (ofInt? w n))
    checkEq s!"error w={w} {case}" got expected
where
  errName {α : Type} (r : Except String α) : Option String :=
    match r with
    | .ok _ => none
    | .error e => some ((e.splitOn ":").headD e)

/-- Properties: round trips and extensionality. -/
def props : TestM Unit := do
  for v in [0, 1, 7, 13, 129, 255] do
    let b := ofUInt8 v.toUInt8
    checkEq s!"toUInt8∘ofUInt8 {v}" (toUInt8 b).toNat v
    let bools := b.toArray
    checkEq s!"ofBools∘toArray {v}" ((ofBools (w := 8) bools).toOption.map (·.toNat)) (some v)
  -- iteration visits the bits LSB-first (Julia's `iterate` is broken; this is the intent)
  let mut acc : List Bool := []
  for x in ofUInt16 7 do
    acc := acc ++ [x]
  checkEq "iterate" acc (ofUInt16 7).toList

/-- Suite entry point for the `lake test` driver. -/
def run : IO (Nat × Nat) := runSuite "PrimitiveBits" (do golden; props)

end Tests.PrimitiveBits
