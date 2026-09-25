/-
Literal syntax (`S!`, `D!`, `V!`, `ℝ^n`, `′`, `⊕`) and hand-picked goldens from
the READMEs, the Grassmann test suite and port-notes/grassmann-parity.md §6.
Compile-time checks (`#guard`, `decide`) plus a runtime list counted in the
suite totals.
-/
import Tests.DirectSum.Common

open DirectSum DirectSum.Bits TensorBundle

namespace DirectSumTests.Literals

/-! ## Compile time -/

-- literals elaborate to structure constants
example : STA = { n := 4, metric := .signature 1 } := rfl
example : CGA3 = { n := 5, metric := .signature 2, hasinf := true, hasorigin := true } := rfl
example : ℝ^3 = sig 3 := rfl
example : V!"-+++" = S!"-+++" := rfl
example : V!"3" = ℝ3 := rfl
example : (S!"∞∅+++").options = 3 := by decide
example : (ℝ^3).tangent.diffmask = 0x8 := by decide
example : ((ℝ^3).tangent 1 2 ⊕ ((ℝ^3).tangent 1 2)′).diffmaskPair = (0xc0, 0x300) := by decide
#guard (S!"∞∅+++").toString == "⟨∞∅+++⟩"
#guard (S!"∞∅+++").showHandle == "⟨∞∅111⟩"
#guard ((ℝ^1)′ ⊕ ℝ^3).toString == "⟨-+++⟩"
#guard (let V := (ℝ^1)′ ⊕ ℝ^3; V ⊕ V′).toString == "⟨-++++---⟩*"

/-! ## `ℝ`, `+`, `^` and set theory (DirectSum README:43-76, 124, 167-183; test lines 5-12) -/

#guard ℝ.toString == "⟨+⟩"
#guard (ℝ′ ⊕ ℝ^3).toString == "⟨-+++⟩"
#guard (ℝ ⊕ ℝ′).toString == "⟨+-⟩*"
#guard (ℝ ^ 3) == ℝ^3
#guard ((ℝ^2)^2).toString == "⟨++++⟩"
#guard (ℝ^3)^0 == V0
#guard ((ℝ^3) + (ℝ^3)′).toString == "⟨+++---⟩*"
#guard ((ℝ^3).tangent + (ℝ^3).tangent′).toString == "T¹⟨+++---₁¹⟩*"
-- `ℝ⊕ℝ' ⊇ TensorBundle(1)`, `ℝ ∩ ℝ' == TensorBundle(0)`, `ℝ ∪ ℝ' == ℝ⊕ℝ'`
example : (ℝ ⊕ ℝ′) ⊇ V!"+" := by decide
#guard ℝ ∩ ℝ′ == V0
#guard equal (ℝ ∪ ℝ′) (ℝ ⊕ ℝ′)
#guard equal ℝ3 (ℝ^3) && equal (ℝ^3) S!"+++" && !equal (ℝ^3) (ℝ^4)
#guard ((ℝ^2)′ ∪ ℝ^2).toString == "⟨++--⟩*"
#guard ((ℝ^3) ∪ (ℝ^3).tangent).toString == "T¹⟨+++₁⟩"
#guard toString ((ℝ^3).sub [1, 2] ∪ (ℝ^3).sub [2, 3]) == "⟨+++⟩"
#guard toString ((ℝ^3).sub [1, 2] ∩ (ℝ^3).sub [2, 3]) == "⟨_+_⟩"
example : (ℝ^3).sub [1, 2] ⊆ ℝ^3 := by decide
example : ¬ ((ℝ^4) ⊆ (ℝ^3)) := by decide
-- blades: `v1 ⊆ v12`, `v12 ⊆ V`, `v1 ∪ v2 = v12`
example : (⟨0b1⟩ : Submanifold (ℝ^3) 1) ⊆ (⟨0b11⟩ : Submanifold (ℝ^3) 2) := by decide
example : (⟨0b11⟩ : Submanifold (ℝ^3) 2) ⊆ ℝ^3 := by decide
#guard toString (Submanifold.union (⟨0b1⟩ : Submanifold (ℝ^3) 1) (⟨0b10⟩ : Submanifold (ℝ^3) 1)) == "v₁₂"
#guard (match SubSpace.oplus ((ℝ^3).sub [2, 3]) ((ℝ^3).sub [1]) with
  | .ok x => toString x | .error e => e) == "⟨_+++__⟩"
#guard ((ℝ^4).sub [1, 4]).showBasis == "DirectSum.Basis{⟨+__+⟩,4}(v, v₁, v₄, v₁₄)"
#guard toString (ℝ^3).tangent.subtangent == "T¹⟨___₁⟩"

-- metric kinds (Julia `Signature(D"1,-2,3") = ⟨+-+⟩`, `DiagonalForm(S"-+-") = ⟨-1,1,-1⟩`, duals,
-- `Signature(D"0,1,1") = ⟨+++⟩`, `Signature((ℝ^3)(1,3)) = ⟨++⟩`, `Signature(D"1,-2,3"(2,3)) = ⟨-+⟩`)
#guard (match (D!"1,-2,3").toSignature with | .ok W => W.toString | .error e => e) == "⟨+-+⟩"
#guard (match (S!"-+-").toDiagonal with | .ok W => W.toString | .error e => e) == "⟨-1,1,-1⟩"
#guard (match (D!"1,-2,3")′.toSignature with | .ok W => W.toString | .error e => e) == "⟨-+-⟩'"
#guard (match (S!"-+-")′.toDiagonal with | .ok W => W.toString | .error e => e) == "⟨-1,1,-1⟩'"
#guard (match (D!"0,1,1").toSignature with | .ok W => W.toString | .error e => e) == "⟨+++⟩"
#guard ((ℝ^3).sub [1, 3]).toSignature.toString == "⟨++⟩"
#guard ((D!"1,-2,3").sub [2, 3]).toSignature.toString == "⟨-+⟩"

/-! ## Runtime goldens -/

/-- `(description, holds)` pairs. -/
def checks : List (String × Bool) :=
  let V := (ℝ^1)′ ⊕ ℝ^3
  let W := V ⊕ V′
  let E3 := ℝ^3
  let M4 := S!"-+++"
  let C5 := S!"∞∅+++"
  let C3 := S!"∞∅+"
  let D3 := D!"1,2,-3"
  let D3deg := D!"1,1,0"
  let MT3 := metricTensor #[#[1, 1/2, 0], #[1/2, 1, 1/2], #[0, 1/2, 1]]
  let mixed2 := ℝ^2 ⊕ (ℝ^2)′
  let tan22 := (ℝ^2).tangent 2 2
  let v := fun (_ : TensorBundle) (is : List Nat) => ofIndices is
  let showR := fun (V : TensorBundle) (r : BladeResult) => match r with
    | .zero => "𝟎" | .blade b => V.bladeLabel b | .single c b => V.showTerm c b
    | .sum t => ", ".intercalate (t.toList.map fun (b, c) => V.showTerm c b)
    | .nested z (.blade d) => V.bladeLabel z ++ "⊗" ++ V.bladeLabel d
    | .nested z (.single c d) => showNum c ++ V.bladeLabel z ++ "⊗" ++ V.bladeLabel d
    | .nested _ _ => "?"
  let ex := fun (V : TensorBundle) (r : Except String BladeResult) => match r with
    | .ok r => showR V r | .error e => "error: " ++ e
  [ -- DirectSum README (port-notes/directsum.md §6.1)
    ("ℝ^3 == V\"+++\"", ℝ^3 == V!"+++"),
    ("V = ℝ'⊕ℝ^3", V.toString == "⟨-+++⟩"),
    ("V'", V′.toString == "⟨+---⟩'"),
    ("W = V⊕V'", W.toString == "⟨-++++---⟩*"),
    ("(ℝ^5)(3,5)", toString ((ℝ^5).sub [3, 5]) == "⟨__+_+⟩"),
    ("Signature(\"∞∅++\")", (S!"∞∅++").toString == "⟨∞∅++⟩"),
    ("tangent(ℝ^3)", (ℝ^3).tangent.toString == "T¹⟨+++₁⟩"),
    ("tangent(tangent(ℝ^3)')", (ℝ^3).tangent′.tangent.toString == "T²⟨----¹⟩'"),
    ("tangent(ℝ^3)+tangent(ℝ^3)'", ((ℝ^3).tangent ⊕ (ℝ^3).tangent′).toString == "T¹⟨+++---₁¹⟩*"),
    ("collect(V)", V.showCollect.startsWith "DirectSum.Basis{⟨-+++⟩,16}(⟨____⟩, ⟨-___⟩, ⟨_+__⟩"),
    ("collect(Submanifold(V'))", V′.showBasis ==
      "DirectSum.Basis{⟨+---⟩',16}(w, w¹, w², w³, w⁴, w¹², w¹³, w¹⁴, w²³, w²⁴, w³⁴, w¹²³, w¹²⁴, w¹³⁴, w²³⁴, w¹²³⁴)"),
    ("Λ(22)", (V!"22").showBasis ==
      "DirectSum.SparseBasis{⟨1111111111111111111111⟩,4194304}(v, ..., v₁₂₃₄₅₆₇₈₉₀abcdefghijkl)"),
    ("volume of Λ(62)", (V!"62").bladeLabel (lowMask 62) ==
      "v₁₂₃₄₅₆₇₈₉₀abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"),
    ("ℝ3 display", ℝ3.toString == "⟨111⟩"),
    ("PGA3 display", PGA3.toString == "⟨0,1,1,1⟩"),
    -- grassmann-parity.md §6.2
    ("E3 v12*v2", showR E3 (E3.mul (v E3 [1, 2]) (v E3 [2])) == "1v₁"),
    ("E3 v12⋅v2", showR E3 (E3.contraction (v E3 [1, 2]) (v E3 [2])) == "-1v₁"),
    ("E3 v2⋅v12", showR E3 (E3.contraction (v E3 [2]) (v E3 [1, 2])) == "𝟎"),
    ("E3 v12∨v13", showR E3 (E3.vee (v E3 [1, 2]) (v E3 [1, 3])) == "v₁"),
    ("E3 v12∨v23", showR E3 (E3.vee (v E3 [1, 2]) (v E3 [2, 3])) == "v₂"),
    ("E3 ⋆v2", ex E3 (E3.complementrighthodge (v E3 [2])) == "-1v₁₃"),
    ("E3 v1×v2", ex E3 (E3.cross (v E3 [1]) (v E3 [2])) == "1v₃"),
    ("E3 v12⋅v12", showR E3 (E3.contraction (v E3 [1, 2]) (v E3 [1, 2])) == "v"),
    ("E3 ~v12", showR E3 (E3.reverse (v E3 [1, 2])) == "-1v₁₂"),
    ("E3 v1<v12", showR E3 (E3.contractionLeft (v E3 [1]) (v E3 [1, 2])) == "v₂"),
    ("M4 v1*v1", showR M4 (M4.mul 1 1) == "-1v"),
    ("C5 v∞*v∞", showR C5 (C5.mul 1 1) == "𝟎"),
    ("C5 v∞*v∅", showR C5 (C5.mul 1 2) == "-1v, 1v∞∅"),
    ("C5 v∅*v∞", showR C5 (C5.mul 2 1) == "-1v, -1v∞∅"),
    ("C5 v∞∅*v∞", showR C5 (C5.mul 3 1) == "-1v∞"),
    ("C5 v∞∅*v∅", showR C5 (C5.mul 3 2) == "1v∅"),
    ("C5 v∞∅^2", showR C5 (C5.mul 3 3) == "1v"),
    ("C5 v∞⋅v∅", showR C5 (C5.contraction 1 2) == "-1v"),
    ("C5 v∞×v∅", ex C5 (C5.cross 1 2) == "-1v₁₂₃"),
    ("C3 v∅*v∞", showR C3 (C3.mul 2 1) == "-1v, -1v∞∅"),
    ("C4neg v2*v2 (Julia defect 1: 1v)", showR (S!"∞∅+-") ((S!"∞∅+-").mul 8 8) == "-1v"),
    ("D3 v3*v3", showR D3 (D3.mul 4 4) == "-3v"),
    ("D3 ⋆v23", ex D3 (D3.complementrighthodge 6) == "-6v₁"),
    ("D3deg v3*v3", showR D3deg (D3deg.mul 4 4) == "0v"),
    ("D3deg v3⋅v3", showR D3deg (D3deg.contraction 4 4) == "𝟎"),
    ("mixed2 w1*v1", showR mixed2 (mixed2.mul 4 1) == "-1v₁w¹"),
    ("mixed2 v1w1⋅v1w1", showR mixed2 (mixed2.contraction 5 5) == "-1v"),
    ("tan22 ∂1*∂1", showR tan22 (tan22.mul 4 4) == "∂₁⊗∂₁"),
    ("tan22 ∂1*∂12", showR tan22 (tan22.mul 4 12) == "𝟎"),
    ("MT3 v12*v23 (Julia defect 2: -0.25v)", showR MT3 (MT3.mul 3 6) ==
      "-0.25v, -0.5v₁₂, 1v₁₃, -0.5v₂₃"),
    -- Grassmann test suite (runtests.jl, issuestests.jl)
    ("e124*e23 == e134", (S!"++++").mul (ofIndices [1, 2, 4]) (ofIndices [2, 3])
      == .single 1 (ofIndices [1, 3, 4]) || (S!"++++").mul (ofIndices [1, 2, 4]) (ofIndices [2, 3])
      == .blade (ofIndices [1, 3, 4])),
    ("signbit(S\"-+++\")", (S!"-+++").signbit.map (fun b => if b then 1 else 0)
      == #[0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1]),
    ("signbit(S\"-+++\",2)", (S!"-+++").signbitGrade 2 == #[false, false, false, true, true, true]) ]

/-- Run the literal/golden list. -/
def run : IO Tally := pure <| checks.foldl (fun t (d, ok) => t.check ok d) {}

end DirectSumTests.Literals
