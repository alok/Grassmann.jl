/-
  Grassmann/PrettyPrint.lean - Beautiful Multivector Formatting

  Provides comprehensive pretty-printing for multivectors with:
  - Unicode subscript notation: e₁, e₁₂, e₁₂₃
  - Smart coefficient formatting: 2e₁ instead of 2.0e₁ for integers
  - Proper sign handling: e₁ - 2e₂ instead of e₁ + -2e₂
  - Grade-sorted output: scalar + vectors + bivectors + ...
  - Configurable formats: compact, expanded, LaTeX
-/
import Grassmann.SparseMultivector
import Grassmann.DSL.Subscript

namespace Grassmann

open DSL (bitmaskToSubscript bitmaskToName)

/-! ## Formatting Utilities -/

/-- Format a Float nicely: show "2" instead of "2.0" for integers -/
def formatFloat (x : Float) : String :=
  let rounded := x.round
  if Float.abs (x - rounded) < 1e-9 && Float.abs rounded < 1e12 then
    toString rounded.toInt64
  else
    toString x

/-! ## Blade Formatting -/

/-- Format a single blade with coefficient using subscript notation -/
def formatBladeTerm (n : ℕ) (idx : Nat) (coeff : Float) (isFirst : Bool) : String :=
  if Float.abs coeff < 1e-15 then ""
  else if idx == 0 then
    -- Scalar term
    let absCoeff := Float.abs coeff
    let isNeg := coeff < 0
    let pfx := if isFirst then (if isNeg then "-" else "") else (if isNeg then " - " else " + ")
    pfx ++ formatFloat absCoeff
  else
    -- Non-scalar blade
    let bladeName := bitmaskToSubscript idx n
    let absCoeff := Float.abs coeff
    let isNeg := coeff < 0
    let pfx := if isFirst then (if isNeg then "-" else "") else (if isNeg then " - " else " + ")
    -- Omit coefficient of 1 (show e₁ not 1e₁)
    if Float.abs (absCoeff - 1.0) < 1e-9 then
      pfx ++ bladeName
    else
      pfx ++ formatFloat absCoeff ++ bladeName

/-! ## MultivectorS Formatting -/

/-- Sort terms by grade then index -/
def sortTermsByGrade (n : ℕ) (terms : List (Nat × Float)) : List (Nat × Float) :=
  terms.mergeSort fun (i1, _) (i2, _) =>
    let g1 := grade (BitVec.ofNat n i1)
    let g2 := grade (BitVec.ofNat n i2)
    if g1 != g2 then g1 ≤ g2 else i1 ≤ i2

/-- Format a sparse multivector with subscript notation -/
def formatMultivectorS {n : ℕ} {sig : Signature n} (m : MultivectorS sig Float) : String :=
  if m.isZero then "0"
  else
    let terms := m.coeffs.toList
    let sorted := sortTermsByGrade n terms

    -- Build formatted string
    let (result, _) := sorted.foldl (init := ("", true)) fun (acc, isFirst) (idx, coeff) =>
      let term := formatBladeTerm n idx coeff isFirst
      if term.isEmpty then (acc, isFirst)
      else (acc ++ term, false)

    if result.isEmpty then "0" else result

/-- Format with ASCII blade names (e12 instead of e₁₂) -/
def formatMultivectorSAscii {n : ℕ} {sig : Signature n} (m : MultivectorS sig Float) : String :=
  if m.isZero then "0"
  else
    let terms := m.coeffs.toList
    let sorted := sortTermsByGrade n terms

    let (result, _) := sorted.foldl (init := ("", true)) fun (acc, isFirst) (idx, coeff) =>
      let absCoeff := Float.abs coeff
      let isNeg := coeff < 0
      let pfx := if isFirst then (if isNeg then "-" else "")
                 else (if isNeg then " - " else " + ")
      let bladeName := if idx == 0 then "" else bitmaskToName idx n
      let coeffStr := if bladeName.isEmpty then formatFloat absCoeff
                      else if Float.abs (absCoeff - 1.0) < 1e-9 then ""
                      else formatFloat absCoeff
      let term := pfx ++ coeffStr ++ bladeName
      (acc ++ term, false)

    if result.isEmpty then "0" else result

/-! ## Repr Instances -/

instance {n : ℕ} {sig : Signature n} : Repr (MultivectorS sig Float) where
  reprPrec m _ := formatMultivectorS m

instance {n : ℕ} {sig : Signature n} : ToString (MultivectorS sig Float) where
  toString := formatMultivectorS

/-! ## LaTeX Formatting -/

/-- Format blade for LaTeX output -/
def formatBladeTermLaTeX (n : ℕ) (idx : Nat) (coeff : Float) (isFirst : Bool) : String :=
  if Float.abs coeff < 1e-15 then ""
  else if idx == 0 then
    let absCoeff := Float.abs coeff
    let isNeg := coeff < 0
    let pfx := if isFirst then (if isNeg then "-" else "") else (if isNeg then " - " else " + ")
    pfx ++ formatFloat absCoeff
  else
    let indices := (List.range n).filter fun i => idx &&& (1 <<< i) != 0
    let subscript := String.intercalate "" (indices.map fun i => toString (i + 1))
    let bladeName := "e_{" ++ subscript ++ "}"
    let absCoeff := Float.abs coeff
    let isNeg := coeff < 0
    let pfx := if isFirst then (if isNeg then "-" else "") else (if isNeg then " - " else " + ")
    if Float.abs (absCoeff - 1.0) < 1e-9 then pfx ++ bladeName
    else pfx ++ formatFloat absCoeff ++ bladeName

/-- Format sparse multivector for LaTeX -/
def formatMultivectorSLaTeX {n : ℕ} {sig : Signature n} (m : MultivectorS sig Float) : String :=
  if m.isZero then "0"
  else
    let terms := m.coeffs.toList
    let sorted := sortTermsByGrade n terms

    let (result, _) := sorted.foldl (init := ("", true)) fun (acc, isFirst) (idx, coeff) =>
      let term := formatBladeTermLaTeX n idx coeff isFirst
      if term.isEmpty then (acc, isFirst)
      else (acc ++ term, false)

    if result.isEmpty then "0" else result

/-! ## Grade Decomposition Display -/

/-- Format showing grade decomposition -/
def formatByGrade {n : ℕ} {sig : Signature n} (m : MultivectorS sig Float) : String :=
  if m.isZero then "0"
  else
    let maxGrade := m.coeffs.toList.foldl (init := 0) fun acc (idx, _) =>
      max acc (grade (BitVec.ofNat n idx))
    let grades := (List.range (maxGrade + 1)).filterMap fun g =>
      let gradeTerms := m.coeffs.toList.filter fun (idx, _) =>
        grade (BitVec.ofNat n idx) == g
      if gradeTerms.isEmpty then none
      else
        let gradeMV : MultivectorS sig Float := ⟨Std.TreeMap.ofList gradeTerms⟩
        some ("⟨" ++ formatMultivectorS gradeMV ++ "⟩_" ++ toString g)
    String.intercalate " + " grades

/-! ## Tests -/

section Tests

def testSig : Signature 3 := Signature.euclidean 3

def ppE1 : MultivectorS testSig Float := MultivectorS.basis ⟨0, by omega⟩
def ppE2 : MultivectorS testSig Float := MultivectorS.basis ⟨1, by omega⟩
def ppE3 : MultivectorS testSig Float := MultivectorS.basis ⟨2, by omega⟩

-- Test basic formatting
#eval! formatMultivectorS ppE1  -- "e₁"
#eval! formatMultivectorS (ppE1 + ppE2)  -- "e₁ + e₂"
#eval! formatMultivectorS (ppE1.smul 2.0)  -- "2e₁"
#eval! formatMultivectorS (ppE1 * ppE2)  -- "e₁₂"

-- Test with scalar
#eval! formatMultivectorS (MultivectorS.scalar 3.0 + ppE1)  -- "3 + e₁"

-- Test with negative coefficient
#eval! formatMultivectorS (ppE1 + ppE2.smul (-2.0))  -- "e₁ - 2e₂"

-- Test bivector
#eval! formatMultivectorS (ppE1 * ppE2 + ppE2 * ppE3)  -- "e₁₂ + e₂₃"

-- Test full multivector
#eval! let mv := MultivectorS.scalar 1.0 + ppE1 + ppE2.smul 2.0 + ppE1 * ppE2
       formatMultivectorS mv  -- "1 + e₁ + 2e₂ + e₁₂"

-- Test zero
#eval! formatMultivectorS (MultivectorS.zero : MultivectorS testSig Float)  -- "0"

-- Test LaTeX output
#eval! formatMultivectorSLaTeX (ppE1 * ppE2 + ppE2 * ppE3)  -- "e_{12} + e_{23}"

-- Test grade decomposition
#eval! let mv := MultivectorS.scalar 1.0 + ppE1 + ppE1 * ppE2
       formatByGrade mv  -- "⟨1⟩_0 + ⟨e₁⟩_1 + ⟨e₁₂⟩_2"

-- Test Repr instance (should show nice format now)
#eval! ppE1  -- e₁
#eval! ppE1 + ppE2  -- e₁ + e₂

#eval IO.println "✓ PrettyPrint module loaded"

end Tests

end Grassmann
