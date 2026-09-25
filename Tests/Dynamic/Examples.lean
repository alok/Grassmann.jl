/-
Julia-checked examples of the dynamic layer: result kinds and display (`show` and the
compact form) of sums, products, sandwiches and unary maps in `ℝ³` (`S"+++"`) and the
conformal plane (`S"∞∅++"`); the sign of zero in `Float` products; `==`; `abs2` and
`norm`. The expected strings are Julia's (Grassmann.jl, the oracle environment).
-/
import Tests.Dynamic.Common

open Grassmann DirectSum StaticVectors AbstractTensors GrassmannTests

namespace DynamicTests

/-- An expected result: Julia's kind name and `show` string. -/
structure Expect where
  /-- The case. -/
  name : String
  /-- Julia's kind. -/
  kind : String
  /-- Julia's `show`. -/
  str : String

/-- Check one integer example (kind and `show`; the compact form drops the spaces around
`+`/`-` for these values). -/
def checkEx {V : TensorBundle} (t : Tally) (x : TA V Int) (e : Expect) : Tally :=
  let t := t.check (x.kind.name == e.kind) s!"{e.name}: kind {x.kind.name} vs {e.kind}"
  let t := t.check (x.showString == e.str) s!"{e.name}: show `{x.showString}` vs `{e.str}`"
  t.check (x.showCompact == (e.str.replace " + " "+").replace " - " "-")
    s!"{e.name}: compact `{x.showCompact}`"

/-- The `ℝ³` examples. -/
def e3Examples : List (TA E3 Int × Expect) :=
  let v1 : TA E3 Int := .blade 1
  let v2 : TA E3 Int := .blade 2
  let v12 : TA E3 Int := .blade 3
  let v123 : TA E3 Int := .blade 7
  let c := chainOfList E3 1 [1, 2, 3]
  let d := chainOfList E3 1 [4, 5, 6]
  let m := multiOfList E3 [1, 2, 3, 4, 5, 6, 7, 8]
  let sp := spinorOfList E3 [1, 2, 3, 4]
  [ (v1 + v2, ⟨"v1+v2", "Chain", "1v₁ + 1v₂ + 0v₃"⟩),
    (.single 1 2 + .single 3 3, ⟨"2v1+3v12", "Multivector", "0 + 2v₁ + 3v₁₂"⟩),
    (.one + v12, ⟨"1+v12", "Couple", "1 + 1v₁₂"⟩),
    (TA.mul v1 v2, ⟨"v1*v2", "Submanifold", "v₁₂"⟩),
    (TA.mul (.single 1 2) (.single 2 3), ⟨"2v1*3v2", "Single", "6v₁₂"⟩),
    (TA.wedge v1 v1, ⟨"v1∧v1", "Zero", "𝟎"⟩),
    (TA.mul c d, ⟨"c*d", "Spinor", "32 - 3v₁₂ - 6v₁₃ - 3v₂₃"⟩),
    (TA.wedge c d, ⟨"c∧d", "Chain", "-3v₁₂ - 6v₁₃ - 3v₂₃"⟩),
    (TA.contraction c d, ⟨"c⋅d", "Chain", "32v"⟩),
    (TA.vee c d, ⟨"c∨d", "Zero", "𝟎"⟩),
    (TA.contraction v12 v1, ⟨"v12⋅v1", "Submanifold", "v₂"⟩),
    (TA.hodge v1, ⟨"⋆v1", "Single", "1v₂₃"⟩),
    (TA.reverse v12, ⟨"~v12", "Single", "-1v₁₂"⟩),
    (TA.abs2 (chainOfList E3 1 [1, 2, 2]), ⟨"abs2(c)", "Chain", "9v"⟩),
    (TA.mul m c, ⟨"m*c", "Multivector",
      "20 + 29v₁ + 18v₂ - 17v₃ + 25v₁₂ - 14v₁₃ + 9v₂₃ + 10v₁₂₃"⟩),
    (TA.mul sp sp, ⟨"sp*sp", "Spinor", "-28 + 4v₁₂ + 6v₁₃ + 8v₂₃"⟩),
    (TA.sandwich c (.couple 3 1 1), ⟨"c⊘(1+v12)", "Chain", "-4v₁ + 2v₂ + 6v₃"⟩),
    -- Julia prints `1v₁ + 2v₂ - 3v₃`, `y⟑x⟑y` (oracle defect `tsandwich-submanifold-chain-sign`)
    (TA.tsandwich v12 c, ⟨"v12>>>c", "Chain", "-1v₁ - 2v₂ + 3v₃"⟩),
    (m - m, ⟨"m-m", "Multivector", "0v⃖"⟩),
    (c + v123, ⟨"c+v123", "CoSpinor", "1v₁ + 2v₂ + 3v₃ + 1v₁₂₃"⟩),
    (-c, ⟨"-c", "Chain", "-1v₁ - 2v₂ - 3v₃"⟩),
    (TA.abs2 (.couple 3 1 2), ⟨"abs2(1+2v12)", "Single", "5v"⟩) ]

/-- The conformal examples. -/
def cgaExamples : List (TA CGA2 Int × Expect) :=
  let c := chainOfList CGA2 1 [1, 2, 3, 4]
  [ (TA.mul (.blade 1) (.blade 2), ⟨"v∞*v∅", "Spinor",
      "-1 + 1v∞∅ + 0v∞₁ + 0v∞₂ + 0v∅₁ + 0v∅₂ + 0v₁₂ + 0v∞∅₁₂"⟩),
    (TA.contraction c c, ⟨"c⋅c", "Multivector", "21v⃖"⟩),
    (TA.contraction (.blade 1) c, ⟨"v∞⋅c", "Chain", "-2v"⟩) ]

/-- `examples`: kinds and strings, signed zeros, `==`, `norm`. -/
def examplesRun : IO Tally := do
  let mut t : Tally := {}
  for (x, e) in e3Examples do t := checkEx t x e
  for (x, e) in cgaExamples do t := checkEx t x e
  -- the sign of zero: Julia's `∑` starts from the first term
  let x := multiOfList E3 [0.0, 1.5, 0.0, -2.0, 0.0, 0.0, 0.0, 0.0]
  let y := chainOfList E3 1 [0.0, 0.0, -1.0]
  let w := TA.wedge x y
  t := t.check (w.showString == "0.0 - 1.5v₁₃") s!"x∧y: `{w.showString}`"
  t := t.check (denseBits w == [0.0, 0.0, 0.0, -0.0, 0.0, -1.5, 0.0, 0.0].map Float.toBits)
    s!"x∧y: dense {w.toDense.v.toList}"
  let yy := TA.mul y y
  t := t.check (yy.showString == "1.0 + 0.0v₁₂ + 0.0v₁₃ + 0.0v₂₃") s!"y*y: `{yy.showString}`"
  -- Julia's `==`
  let v1 : TA E3 Int := .blade 1
  let v2 : TA E3 Int := .blade 2
  t := t.check ((v1 + v2).equal (chainOfList E3 1 [1, 1, 0])) "v1+v2 == Chain(1,1,0)"
  t := t.check ((TA.one + .blade 3 : TA E3 Int).equal (.couple 3 1 1)) "1+v12 == Couple(1,1)"
  t := t.check (!(TA.couple 3 0 0 : TA E3 Int).equal (.single 1 0)) "Couple{v12}(0,0) ≠ 0v1"
  t := t.check ((TA.couple 3 0 0 : TA E3 Int).equal (.single 3 0)) "Couple{v12}(0,0) == 0v12"
  t := t.check ((TA.infinity : TA E3 Float).equal .infinity) "∞ == ∞"
  -- `norm`
  t := t.check ((chainOfList E3 1 [1, 2, 2] : TA E3 Int).norm == 3.0) "norm(c) = 3.0"
  t := t.check ((TA.couple 3 1 2 : TA E3 Int).norm == 2.23606797749979) "norm(1+2v12)"
  return t

end DynamicTests
