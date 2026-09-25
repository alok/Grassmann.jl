import Tests.Forms.Common
import Grassmann.Forms.Literal

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

-- operator literals (Julia `@TensorOperator`, `@Endomorphism`, `@Outermorphism`,
-- `@SpectralOperator`): the shape is in the type
example : TensorOperator (En 3) (.chain 1) (En 2) (.chain 1) Int := op![[1, 2, 3], [4, 5, 6]]
example : Endomorphism (En 2) (.chain 1) Float := endo![[1, 2], [3, 4]]
example : Outermorphism (En 2) (En 2) Float := outer![[1, 2], [3, 4]]
example : TensorOperator.EigenResult (En 2) := spectral![[2, 1], [1, 2]]

/-- error: operator literal: row 2 has 1 entries, row 1 has 2 -/
#guard_msgs in example : Endomorphism (En 2) (.chain 1) Int := endo![[1, 2], [3]]

/-- error: endo![…]: a square literal is expected, got 1 × 2 -/
#guard_msgs in example : Endomorphism (En 2) (.chain 1) Int := endo![[1, 2]]

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
  -- literals: `op!` rows are Julia's rows; docs algebra.md:1053 `@TensorOperator([1 2; 3 4])\Chain(5,6)`
  let L : Endomorphism (En 2) (.chain 1) Float := endo![[1, 2], [3, 4]]
  let sol := L.solve (chainOf (En 2) 1 [5, 6])
  t := t.ok ((getD sol.v 0 + 4).abs < 1e-12 && (getD sol.v 1 - 4.5).abs < 1e-12) fun _ => s!"[1 2; 3 4]\\(5,6) = {sol}"
  t := t.ok ((op![[1, 2, 3], [4, 5, 6]] : TensorOperator (En 3) (.chain 1) (En 2) (.chain 1) Int).toRows ==
    [[1, 2, 3], [4, 5, 6]]) fun _ => "op! rows"
  t := t.ok ((outer![[1, 2], [3, 4]] : Outermorphism (En 2) (En 2) Int).det == -2) fun _ => "outer! det"
  t := t.ok (toString (O * (c [1, 1, 1] ∧ c [0, 1, 0]) : Chain ℝ3 2 Int) ==
    toString ((T * c [1, 1, 1] : Chain ℝ3 1 Int) ∧ (T * c [0, 1, 0] : Chain ℝ3 1 Int))) fun _ => "O(x∧y)"
  t := t.ok ((lieBracket [T, U]).toRows == [[4, -10, -2], [10, 0, 18], [6, -16, -4]]) fun _ => "𝓛[T,U]"
  t := t.ok ((𝓛[T, U]).toRows == (lieBracket [T, U]).toRows) fun _ => "𝓛[…] notation"
  let Tf := T.map Float.ofInt
  t := t.ok (toString Tf.characteristic == "3.0v₁ - 12.0v₂ - 16.0v₃") fun _ => s!"characteristic {Tf.characteristic}"
  t := t.ok (toString Tf.eigpolys == "5.33333v₁ - 4.0v₂ - 3.0v₃") fun _ => "eigpolys"
  t := t.ok (Tf.disc == Tf.discriminant && Tf.disccomplex == Tf.discriminantcomplex &&
    (match Tf.discreal, Tf.discriminantreal with | .ok a, .ok b => a == b | .error _, .error _ => true | _, _ => false))
    fun _ => "disc, discreal, disccomplex"
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
  -- spectral operators: `S = eigen([2 1; 1 2])` (Julia: `S(1v₁) = 2.0v₁ + 1.0v₂`, `tr(S) = 4.0`,
  -- `Chain(S) = (2.0v₁+1.0v₂)v₁ + (1.0v₁+2.0v₂)v₂`, `inv(S).λ = (1.0, 0.333333)`)
  let S2 : Endomorphism (En 2) (.chain 1) Float := endo (En 2) [[2, 1], [1, 2]]
  match S2.eigen with
  | .real S =>
    let y : Chain (En 2) 1 Float := S * (chainOf (En 2) 1 [1.0, 0.0])
    t := t.ok ((getD y.v 0 - 2).abs < 1e-12 && (getD y.v 1 - 1).abs < 1e-12) fun _ => s!"S(v₁) = {y}"
    t := t.ok ((S.tr - 4).abs < 1e-12) fun _ => "tr(S)"
    t := t.ok (toString S.toOperator == "(2.0v₁+1.0v₂)v₁ + (1.0v₁+2.0v₂)v₂") fun _ => s!"Chain(S) = {S.toOperator}"
    t := t.ok (toString (⟨S.inv.vals⟩ : Chain (En 2) 1 Float) == "1.0v₁ + 0.333333v₂") fun _ => "inv(S)"
    t := t.ok (toString (⟨S.exp.vals⟩ : Chain (En 2) 1 Float) == "2.71828v₁ + 20.0855v₂") fun _ => "exp(S)"
  | .complex _ => t := t.ok false fun _ => "eigen([2 1; 1 2]) is real"
  -- Julia `Proj(Chain(x,y))` with x = (1,2), y = (3,4) in ℝ²: `P ⋅ x = 2.32v₁ + 3.76v₂`,
  -- with λ = (2, 3): `P ⋅ x = 5.96v₁ + 9.28v₂`, `Chain(P) = (1.48v₁+2.24v₂)v₁ + (2.24v₁+3.52v₂)v₂`
  let XY : Endomorphism (En 2) (.chain 1) Float := endo (En 2) [[1, 3], [2, 4]]
  let x2 : Chain (En 2) 1 Float := chainOf (En 2) 1 [1, 2]
  let P1 := SpectralOperator.ofVectors XY (Values.replicate 1)
  let P2 := SpectralOperator.ofVectors XY (Values.ofFn fun i => #[2.0, 3.0][i.1]!)
  t := t.ok (toString (P1 * x2) == "2.32v₁ + 3.76v₂") fun _ => s!"Proj(x,y)⋅x = {P1 * x2}"
  t := t.ok (toString (P2 * x2) == "5.96v₁ + 9.28v₂") fun _ => s!"Proj(x,y;λ)⋅x = {P2 * x2}"
  t := t.ok (toString P2.toOperator == "(1.48v₁+2.24v₂)v₁ + (2.24v₁+3.52v₂)v₂") fun _ => s!"Chain(P) = {P2.toOperator}"
  -- the shoelace area of the unit square (homogeneous points): Julia `area` = 1.0
  let sq : List (Chain ℝ3 1 Float) := [cf [1, 0, 0], cf [1, 1, 0], cf [1, 1, 1], cf [1, 0, 1]]
  t := t.ok ((TensorOperator.area sq - 1).abs < 1e-12) fun _ => s!"area = {TensorOperator.area sq}"
  -- the outermorphism on a couple: `O(1 + 2v₁₂) = 1 + 2 Λ²T[:, v₁₂]`
  let z : Couple ℝ3 Int := ⟨3, 1, 2⟩
  t := t.ok (toString (O.applyCouple z) == "1 - 6v₁₂ - 12v₁₃ - 6v₂₃") fun _ => s!"O(1+2v₁₂) = {O.applyCouple z}"
  return t

end Tests.FormsTests.Types
