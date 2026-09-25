import Tests.Forms.Common

/-!
# Static types and notation of the Forms layer (compile-time checks, and a few goldens)

The result types of application, composition, outermorphisms, diagonal operators and
rank-one forms are static (they follow the layouts in the types); these `example`s fail
to compile if an instance picks a different type. The runtime checks reproduce the
worked examples of port-notes/grassmann-forms.md §6 through the notation.
-/

namespace Tests.FormsTests.Types

open Lean Tests.Units Grassmann DirectSum StaticVectors Tests.FormsTests

section StaticTypes

variable (T U : Endomorphism ℝ3 (.chain 1) Int) (x : Chain ℝ3 1 Int) (B : Chain ℝ3 2 Int)
  (A : Simplex ℝ2 ℝ3 Int) (y : Chain ℝ2 1 Int) (O : Outermorphism ℝ3 ℝ3 Int)
  (s : Spinor ℝ3 Int) (o : CoSpinor ℝ3 Int) (m : Multivector ℝ3 Int)
  (D : DiagonalMorphism ℝ3 Int) (DO : DiagonalOutermorphism ℝ3 Int)
  (S2 : Endomorphism ℝ3 .even Int) (Tf : Endomorphism ℝ3 (.chain 1) Float)

example : Chain ℝ3 1 Int := T x
example : Chain ℝ3 1 Int := T * x
example : Chain ℝ3 1 Int := T ⋅ x
example : Chain ℝ3 1 Int := x ⋅ T
example : Endomorphism ℝ3 (.chain 1) Int := T * U
example : Endomorphism ℝ3 (.chain 1) Int := T ⋅ U
example : Chain ℝ3 1 Int := A * y
example : Chain ℝ2 1 Int := x ⋅ A
example : Simplex ℝ3 ℝ2 Int := A.transpose
example : Endomorphism ℝ3 (.chain 2) Int := T.compound 2
example : Chain ℝ3 2 Int := O * B
example : Spinor ℝ3 Int := O * s
example : CoSpinor ℝ3 Int := O * o
example : Multivector ℝ3 Int := O * m
example : Outermorphism ℝ3 ℝ3 Int := O * O
example : Chain ℝ3 1 Int := D * x
example : Chain ℝ3 2 Int := DO * B
example : CoSpinor ℝ3 Int := DO * o
example : Endomorphism ℝ3 (.chain 1) Int := D * T
example : Endomorphism ℝ3 (.chain 1) Int := T * D
example : Spinor ℝ3 Int := S2 * s
example : Spinor ℝ3 Int := S2 s
example : Dyadic ℝ3 1 ℝ3 1 Int := x ⊗ x
example : Chain ℝ3 1 Int := (x ⊗ x : Dyadic ℝ3 1 ℝ3 1 Int) * x
example : Endomorphism ℝ3 (.chain 1) Float := Tf.inv
example : Endomorphism ℝ3 (.chain 1) Float := Tf.exp
example : Chain ℝ3 1 Float := Tf.characteristic
example : Endomorphism ℝ3 (.chain 1) Int := T + AbstractTensors.UniformScaling.mk (1 : Int)
example : Chain ℝ3 1 Int := T.pfaffian

end StaticTypes

/-- The worked examples of port-notes/grassmann-forms.md §6.2 through the notation. -/
def suite : IO Tally := do
  let c := fun (l : List Int) => (chainOf ℝ3 1 l : Chain ℝ3 1 Int)
  let T : Endomorphism ℝ3 (.chain 1) Int := endo ℝ3 [[1, 4, 7], [2, 5, 8], [3, 6, 10]]
  let U : Endomorphism ℝ3 (.chain 1) Int := endo ℝ3 [[2, 0, 1], [0, 1, 0], [1, 0, 3]]
  let x := c [1, 1, 1]
  let mut t := Tally.new "forms/types"
  t := t.ok (toString (T x) == "12v₁ + 15v₂ + 19v₃") fun _ => s!"T(x) = {T x}"
  t := t.ok (toString (x ⋅ T : Chain ℝ3 1 Int) == "6v₁ + 15v₂ + 25v₃") fun _ => "x⋅T"
  t := t.ok (T.form x x == 46) fun _ => "T(x,x)"
  t := t.ok ((T * U).toRows == [[9, 4, 22], [12, 5, 26], [16, 6, 33]]) fun _ => "T*U"
  t := t.ok (T.det == -3 && toString T.wedgeAll == "-3v₁₂₃" && T.tr == 16) fun _ => "det, ∧, tr"
  t := t.ok (toString (Endomorphism.bivector T) == "2v₁₂ + 3v₁₃ + 6v₂₃") fun _ => "bivector"
  t := t.ok (toString (Endomorphism.pfaffian T) == "6v₁ - 3v₂ + 2v₃") fun _ => "pfaffian"
  let O := T.outermorphism
  t := t.ok (O.tr == 2 && O.det == -3) fun _ => "tr(O), det(O)"
  t := t.ok (toString (O * (c [1, 1, 1] ∧ c [0, 1, 0]) : Chain ℝ3 2 Int) ==
    toString ((T * c [1, 1, 1] : Chain ℝ3 1 Int) ∧ (T * c [0, 1, 0] : Chain ℝ3 1 Int))) fun _ => "O(x∧y)"
  t := t.ok ((lieBracket [T, U]).toRows == [[4, -10, -2], [10, 0, 18], [6, -16, -4]]) fun _ => "𝓛[T,U]"
  let Tf := T.map Float.ofInt
  t := t.ok (toString Tf.characteristic == "3.0v₁ - 12.0v₂ - 16.0v₃") fun _ => s!"characteristic {Tf.characteristic}"
  t := t.ok (toString Tf.eigpolys == "5.33333v₁ - 4.0v₂ - 3.0v₃") fun _ => "eigpolys"
  t := t.ok (toString (Endomorphism.companion (n := 3) (Values.ofFn fun i => (i.1 + 1 : Int))) ==
    "(0v₁+1v₂+0v₃)v₁ + (0v₁+0v₂+1v₃)v₂ + (-1v₁-2v₂-3v₃)v₃") fun _ => "companion"
  t := t.ok (lieBracketString == "LieBracket[...]") fun _ => "LieBracket"
  -- indexing with basis blades (Julia `T ⋅ v₂`, `T ⋅ 2v₃`, `Λ²T ⋅ v₁₃`, `d[2]`)
  let v2 : Submanifold ℝ3 1 := ⟨2⟩
  let v13 : Submanifold ℝ3 2 := ⟨5⟩
  t := t.ok (toString (T.columnOfBlade v2 : Chain ℝ3 1 Int) == "4v₁ + 5v₂ + 6v₃") fun _ => "T⋅v₂"
  t := t.ok (toString (T.applySingle (⟨4, 2⟩ : Single ℝ3 1 Int) : Chain ℝ3 1 Int) == "14v₁ + 16v₂ + 20v₃")
    fun _ => "T⋅2v₃"
  t := t.ok (toString ((T.compound 2).columnOfBlade v13 : Chain ℝ3 2 Int) == "-6v₁₂ - 11v₁₃ - 4v₂₃")
    fun _ => "Λ²T⋅v₁₃"
  let d : DiagonalMorphism ℝ3 Int := ⟨Values.ofFn fun i => (i.1 + 1 : Int)⟩
  t := t.ok (toString (DiagonalMorphism.term d 1) == "2v₂") fun _ => "d[2]"
  -- barycentric interpolation reproduces affine functions; affinehull picks the vertices
  let cf := fun (l : List Float) => (chainOf ℝ3 1 l : Chain ℝ3 1 Float)
  let pts : Array (Chain ℝ3 1 Float) := #[cf [1, 0, 0], cf [1, 2, 0], cf [1, 0, 3], cf [1, 5, 5]]
  match (affinehull (V := ℝ3) pts [1, 2, 3] : Option (Simplex ℝ3 ℝ3 Float)) with
  | some S =>
    let f : Values Float 3 := Values.ofFn fun i => #[1.0, 5.0, 7.0][i.1]!   -- f = 1 + 2x + 2y
    let v := S.interpolate f (cf [1, 0.5, 0.75])
    t := t.ok ((v - 3.5).abs < 1e-12) fun _ => s!"interpolate: {v}"
    t := t.ok ((S.volume - 3).abs < 1e-12) fun _ => s!"volume: {S.volume}"
  | none => t := t.ok false fun _ => "affinehull"
  return t

end Tests.FormsTests.Types
