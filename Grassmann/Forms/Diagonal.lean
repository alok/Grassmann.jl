/-
`DiagonalOperator`: an operator stored by its diagonal (Julia
`DiagonalOperator{V,T}`, `DiagonalMorphism` = grade 1, `DiagonalOutermorphism`
= full algebra; Grassmann.jl `src/forms.jl:474-553, 1016-1048`;
port-notes/grassmann-forms.md §2.6).

The diagonal is a coefficient vector in a DirectSum `Layout` (`.chain g`,
`.even`, `.odd` or `.full`), exactly Julia's `v::Chain{V,G}` / `Spinor` /
`CoSpinor` / `Multivector`. Application is the entrywise product with the
argument (or with its part in the diagonal's layout).

Fixed Julia defects (port-notes §8.4): `Endomorphism ⋅ DiagonalOperator` is
`A·D` (Julia returns `(A·D)ᵀ`, item 1) and a diagonal outermorphism acts on a
`CoSpinor` through its odd part (Julia uses the even part, item 2).
-/
import Grassmann.Forms.Outermorphism

namespace Grassmann

open DirectSum StaticVectors AbstractTensors Grassmann.Forms

/-- Julia `DiagonalOperator{V,T}`: the diagonal in layout `l` of `V`. -/
structure DiagonalOperator (V : TensorBundle) (l : Layout) (α : Type) [Coeff α] where
  /-- The diagonal entries (Julia `value(t)`). -/
  d : Values α (l.size V.n)

/-- Julia `DiagonalMorphism{V} = DiagonalOperator{V,<:Chain{V,1}}`. -/
abbrev DiagonalMorphism (V : TensorBundle) (α : Type) [Coeff α] := DiagonalOperator V (.chain 1) α

/-- Julia `DiagonalOutermorphism{V} = DiagonalOperator{V,<:Multivector{V}}`. -/
abbrev DiagonalOutermorphism (V : TensorBundle) (α : Type) [Coeff α] := DiagonalOperator V .full α

namespace DiagonalOperator

variable {V : TensorBundle} {l : Layout} {α : Type} [Coeff α]

/-- Julia `DiagonalOperator(t)` of an element (a `Chain`, `Spinor`, `CoSpinor`
or `Multivector`), `forms.jl:476-484`. -/
@[inline] def ofElem {X : Type} [InLayout X V l α] (x : X) : DiagonalOperator V l α := ⟨InLayout.vals x⟩

/-- The diagonal as an element (Julia `value(t)`). -/
@[inline] def value {Y : Type} [OfLayout V l α Y] (D : DiagonalOperator V l α) : Y :=
  OfLayout.ofVals (V := V) (l := l) D.d

/-- Julia `DiagonalOperator(T)` of an endomorphism: its diagonal (`forms.jl:636`). -/
@[inline] def ofEndomorphism (T : Endomorphism V l α) : DiagonalOperator V l α :=
  ⟨Values.ofFn fun i => T.entry i.1 i.1⟩

/-- Julia `DiagonalOperator{V}(m::AbstractMatrix)`: the diagonal of a row-wise
matrix (`forms.jl:494`). -/
def ofRows? (rows : List (List α)) : Option (DiagonalOperator V l α) :=
  if rows.length == l.size V.n then
    some ⟨Values.ofFn fun i => (rows[i.1]?.bind (·[i.1]?)).getD Coeff.zero⟩
  else none

/-- Julia `t[i+1, j+1]` (`forms.jl:503`). -/
@[inline] def entry (D : DiagonalOperator V l α) (i j : Nat) : α :=
  if i = j then getD D.d i else Coeff.zero

/-- The materialized operator (Julia `TensorOperator(t)`, `forms.jl:620-631`). -/
@[inline] def toOperator (D : DiagonalOperator V l α) : Endomorphism V l α :=
  TensorOperator.ofFn fun i j => if i.1 = j.1 then D.d.get i else Coeff.zero

/-- Julia `tr(t) = sum(value(t))` (`forms.jl:512`), a left fold from the first entry. -/
@[inline] def tr (D : DiagonalOperator V l α) : α := D.d.reduce (· + ·) Coeff.zero

/-- Julia `scalar(t) = tr(t)/length(value(t))` (`forms.jl:511`). -/
@[inline] def scalar [Div α] (D : DiagonalOperator V l α) : α := D.tr / Coeff.ofInt (l.size V.n)

/-- Map the diagonal (Julia `map(f, t)`, `forms.jl:1125`). -/
@[inline] def map {β : Type} [Coeff β] (f : α → β) (D : DiagonalOperator V l α) :
    DiagonalOperator V l β := ⟨D.d.map f⟩

/-- Apply to coefficients in the same layout: the entrywise product. -/
@[inline] def applyValues (D : DiagonalOperator V l α) (x : Values α (l.size V.n)) :
    Values α (l.size V.n) := Values.zipWith (· * ·) D.d x

/-- Julia `D ⋅ x` for an element of the diagonal's layout (`forms.jl:1029`):
the entrywise product. -/
@[inline] def apply {X Y : Type} [InLayout X V l α] [OfLayout V l α Y]
    (D : DiagonalOperator V l α) (x : X) : Y :=
  OfLayout.ofVals (V := V) (l := l) (D.applyValues (InLayout.vals x))

/-- Julia `x ⋅ D` (`forms.jl:1030`): the entrywise product, `x` on the left. -/
@[inline] def rowApply {X Y : Type} [InLayout X V l α] [OfLayout V l α Y]
    (x : X) (D : DiagonalOperator V l α) : Y :=
  OfLayout.ofVals (V := V) (l := l) (Values.zipWith (· * ·) (InLayout.vals x) D.d)

/-- Julia's bilinear form `D(x, y) = vecdot(D ⋅ x, y)` (`forms.jl:497-499`). -/
@[inline] def form {X : Type} [Conj α] [InLayout X V l α] (D : DiagonalOperator V l α) (x y : X) : α :=
  let dx := D.applyValues (InLayout.vals x)
  Mat.sdot0 (α := α) conj dx.data (InLayout.vals y).data 1 1 (l.size V.n) 0 0

/-- Julia `D ⋅ D'` (`forms.jl:1031`): the entrywise product. -/
@[inline] def comp (A B : DiagonalOperator V l α) : DiagonalOperator V l α :=
  ⟨Values.zipWith (· * ·) A.d B.d⟩

instance : Add (DiagonalOperator V l α) := ⟨fun a b => ⟨a.d + b.d⟩⟩
instance : Sub (DiagonalOperator V l α) := ⟨fun a b => ⟨a.d - b.d⟩⟩
instance : Neg (DiagonalOperator V l α) := ⟨fun a => ⟨-a.d⟩⟩
instance : HMul α (DiagonalOperator V l α) (DiagonalOperator V l α) := ⟨fun s D => ⟨D.d.map (s * ·)⟩⟩
instance : HMul (DiagonalOperator V l α) α (DiagonalOperator V l α) := ⟨fun D s => ⟨D.d.map (· * s)⟩⟩
/-- Julia `D / s = D * (1/s)` (through the reciprocal, `algebra.jl:704-706`). -/
instance [Div α] : HDiv (DiagonalOperator V l α) α (DiagonalOperator V l α) :=
  ⟨fun D s => let r := Coeff.one / s; ⟨D.d.map (· * r)⟩⟩
/-- Julia `a == b` (master `forms.jl:506`). -/
instance [BEq α] : BEq (DiagonalOperator V l α) := ⟨fun a b => a.d == b.d⟩
instance : Inhabited (DiagonalOperator V l α) := ⟨⟨zeroValues _⟩⟩

instance {X Y : Type} [InLayout X V l α] [OfLayout V l α Y] :
    HMul (DiagonalOperator V l α) X Y := ⟨apply⟩
instance {X Y : Type} [InLayout X V l α] [OfLayout V l α Y] :
    Contraction (DiagonalOperator V l α) X Y := ⟨apply⟩
instance {X Y : Type} [InLayout X V l α] [OfLayout V l α Y] :
    Contraction X (DiagonalOperator V l α) Y := ⟨rowApply⟩
instance : HMul (DiagonalOperator V l α) (DiagonalOperator V l α) (DiagonalOperator V l α) := ⟨comp⟩
instance : Contraction (DiagonalOperator V l α) (DiagonalOperator V l α) (DiagonalOperator V l α) := ⟨comp⟩
/-- Julia `D ∧ x` (`forms.jl:1016`): entrywise `∧` of scalars, the product. -/
instance {X Y : Type} [InLayout X V l α] [OfLayout V l α Y] : Wedge (DiagonalOperator V l α) X Y := ⟨apply⟩
/-- Julia `D ∨ x`: entrywise `∨` of scalars, zero. -/
instance {X Y : Type} [InLayout X V l α] [OfLayout V l α Y] : Vee (DiagonalOperator V l α) X Y :=
  ⟨fun _ _ => OfLayout.ofVals (V := V) (l := l) (zeroValues (α := α) _)⟩

/-- `D ⋅ T` (Julia `forms.jl:1047`): `D·A`, row `i` scaled by `dᵢ`. -/
@[inline] def compOperator {W : TensorBundle} {lw : Layout} (D : DiagonalOperator V l α)
    (T : TensorOperator W lw V l α) : TensorOperator W lw V l α :=
  TensorOperator.ofFn fun i j => D.d.get i * T.entry i.1 j.1

/-- `T ⋅ D` (Julia `forms.jl:1048` returns `(A·D)ᵀ`; here `A·D`): column `j`
scaled by `dⱼ`. -/
@[inline] def operatorComp {W : TensorBundle} {lw : Layout} (T : TensorOperator V l W lw α)
    (D : DiagonalOperator V l α) : TensorOperator V l W lw α :=
  TensorOperator.ofFn fun i j => T.entry i.1 j.1 * D.d.get j

instance {W : TensorBundle} {lw : Layout} :
    HMul (DiagonalOperator V l α) (TensorOperator W lw V l α) (TensorOperator W lw V l α) := ⟨compOperator⟩
instance {W : TensorBundle} {lw : Layout} :
    Contraction (DiagonalOperator V l α) (TensorOperator W lw V l α) (TensorOperator W lw V l α) :=
  ⟨compOperator⟩
instance {W : TensorBundle} {lw : Layout} :
    HMul (TensorOperator V l W lw α) (DiagonalOperator V l α) (TensorOperator V l W lw α) := ⟨operatorComp⟩
instance {W : TensorBundle} {lw : Layout} :
    Contraction (TensorOperator V l W lw α) (DiagonalOperator V l α) (TensorOperator V l W lw α) :=
  ⟨operatorComp⟩

/-- `A + D` (Julia `forms.jl:1083`). -/
instance : HAdd (Endomorphism V l α) (DiagonalOperator V l α) (Endomorphism V l α) :=
  ⟨fun A D => A + D.toOperator⟩
/-- `D + A` (Julia `forms.jl:1084`). -/
instance : HAdd (DiagonalOperator V l α) (Endomorphism V l α) (Endomorphism V l α) :=
  ⟨fun D A => D.toOperator + A⟩

/-- `Π_{i ∈ I} dᵢ` over the generators of blade `b` in ascending order, a left
fold from the first factor (Julia's generated `*(m.v[i]...)`); `1` for the
scalar blade. -/
@[specialize] def bladeProduct {n : Nat} (d : Values α n) (b : UInt64) : α :=
  match (DirectSum.Bits.indices b).toList with
  | [] => Coeff.one
  | i :: is => is.foldl (fun acc k => acc * getD d (k - 1)) (getD d (i - 1))

end DiagonalOperator

namespace DiagonalMorphism

variable {V : TensorBundle} {α : Type} [Coeff α]

/-- Julia `compound(D, g)` (`forms.jl:517-520`): the diagonal of the products
`Π_{i∈I} dᵢ` over the `g`-subsets `I`. -/
@[specialize] def compound (D : DiagonalMorphism V α) (g : Nat) : DiagonalOperator V (.chain g) α :=
  ⟨Values.ofFn fun k => DiagonalOperator.bladeProduct D.d (Leibniz.indexBasis V.n g)[k.1]!⟩

/-- Julia `outermorphism(D)` (`forms.jl:521-523`): the diagonal outermorphism,
`1` on the scalar and `Π_{i∈I} dᵢ` on every blade `I`. -/
@[specialize] def outermorphism (D : DiagonalMorphism V α) : DiagonalOutermorphism V α :=
  ⟨Values.ofFn fun k =>
    if k.1 = 0 then Coeff.one else DiagonalOperator.bladeProduct D.d (Leibniz.indexBasisAll V.n)[k.1]!⟩

/-- Julia `∧(D) = Chain{V,n}(prod(diagonal))` (`forms.jl:515`). -/
@[specialize] def wedgeAll (D : DiagonalMorphism V α) : Chain V V.n α :=
  ⟨Values.ofFn fun _ => DiagonalOperator.bladeProduct D.d (DirectSum.Bits.lowMask V.n)⟩

/-- Julia `det(D) = !∧(D)` (`forms.jl:513`): the product of the diagonal. -/
@[inline] def det (D : DiagonalMorphism V α) : α := DiagonalOperator.bladeProduct D.d (DirectSum.Bits.lowMask V.n)

/-- Julia `adjugate(D)` (`forms.jl:526-528`): `(Π_{j≠i} dⱼ)ᵢ`, the reversed
`(n-1)`-th compound. -/
@[specialize] def adjugate (D : DiagonalMorphism V α) : DiagonalMorphism V α :=
  let c := (compound D (V.n - 1)).d
  ⟨Values.ofFn fun i => getD c (V.n - 1 - i.1)⟩

/-- Julia `cofactor(D) = adjugate(D)` (`forms.jl:525`). -/
@[inline] def cofactor (D : DiagonalMorphism V α) : DiagonalMorphism V α := adjugate D

/-- Julia `inv(D)`: entrywise (`forms.jl:532-537`). -/
@[inline] def inv [Div α] (D : DiagonalMorphism V α) : DiagonalMorphism V α := D.map (Coeff.one / ·)

/-- Julia `invdet(D) = (inv(D), det(D))`. -/
@[inline] def invdet [Div α] (D : DiagonalMorphism V α) : DiagonalMorphism V α × α := (D.inv, D.det)

/-- Julia `exp(D)`, `expm1(D)`, `log(D)`: entrywise (`forms.jl:532-537`). -/
@[inline] def exp [Analytic α] (D : DiagonalMorphism V α) : DiagonalMorphism V α := D.map Analytic.exp
/-- Julia `expm1(D)`: entrywise. -/
@[inline] def expm1 [Analytic α] (D : DiagonalMorphism V α) : DiagonalMorphism V α := D.map Analytic.expm1
/-- Julia `log(D)`: entrywise. -/
@[inline] def log [Analytic α] (D : DiagonalMorphism V α) : DiagonalMorphism V α := D.map Analytic.log

end DiagonalMorphism

namespace DiagonalOutermorphism

variable {V : TensorBundle} {α : Type} [Coeff α]

/-- The grade-`g` part of the diagonal (Julia `value(t)(Val(g))`). -/
@[inline] def gradeDiag (D : DiagonalOutermorphism V α) (g : Nat) : DiagonalOperator V (.chain g) α :=
  ⟨Forms.gradeBlock V.n .full D.d g⟩

/-- Julia `DiagonalMorphism(t::DiagonalOutermorphism)`: the grade-1 part (`forms.jl:485`). -/
@[inline] def base (D : DiagonalOutermorphism V α) : DiagonalMorphism V α := D.gradeDiag 1

/-- Julia `∧(D) = value(D)(Val(n))` (`forms.jl:516`): the top-grade part. -/
@[inline] def wedgeAll (D : DiagonalOutermorphism V α) : Chain V V.n α := ⟨(D.gradeDiag V.n).d⟩

/-- Julia `det(D) = !∧(D)`: the pseudoscalar coefficient. -/
@[inline] def det (D : DiagonalOutermorphism V α) : α := getD D.d (2 ^ V.n - 1)

/-- Julia `adjugate(D) = outermorphism(adjugate(grade 1))` (`forms.jl:529`). -/
@[inline] def adjugate (D : DiagonalOutermorphism V α) : DiagonalOutermorphism V α :=
  DiagonalMorphism.outermorphism (DiagonalMorphism.adjugate D.base)

/-- Julia `inv(D) = outermorphism(inv(grade 1))` (`forms.jl:532-537`). -/
@[inline] def inv [Div α] (D : DiagonalOutermorphism V α) : DiagonalOutermorphism V α :=
  DiagonalMorphism.outermorphism (DiagonalMorphism.inv D.base)

/-- Julia `exp(D) = outermorphism(exp(grade 1))`. -/
@[inline] def exp [Analytic α] (D : DiagonalOutermorphism V α) : DiagonalOutermorphism V α :=
  DiagonalMorphism.outermorphism (DiagonalMorphism.exp D.base)

/-- Julia `log(D) = outermorphism(log(grade 1))`. -/
@[inline] def log [Analytic α] (D : DiagonalOutermorphism V α) : DiagonalOutermorphism V α :=
  DiagonalMorphism.outermorphism (DiagonalMorphism.log D.base)

/-- Julia `D ⋅ x` for any element of the algebra (`forms.jl:1033-1041`): the
entrywise product with the part of the diagonal in the element's layout (the
odd part for a `CoSpinor`, where Julia uses the even part). -/
@[inline] def apply {l : Layout} {X Y : Type} [InLayout X V l α] [OfLayout V l α Y]
    (D : DiagonalOutermorphism V α) (x : X) : Y :=
  let dl : Values α (l.size V.n) := convertLayout V.n .full l D.d
  OfLayout.ofVals (V := V) (l := l) (Values.zipWith (· * ·) dl (InLayout.vals x))

/-- Julia `x ⋅ D` for any element (`forms.jl:1033-1041`). -/
@[inline] def rowApply {l : Layout} {X Y : Type} [InLayout X V l α] [OfLayout V l α Y]
    (x : X) (D : DiagonalOutermorphism V α) : Y :=
  let dl : Values α (l.size V.n) := convertLayout V.n .full l D.d
  OfLayout.ofVals (V := V) (l := l) (Values.zipWith (· * ·) (InLayout.vals x) dl)

instance (priority := low) {l : Layout} {X Y : Type} [InLayout X V l α] [OfLayout V l α Y] :
    HMul (DiagonalOutermorphism V α) X Y := ⟨apply⟩
instance (priority := low) {l : Layout} {X Y : Type} [InLayout X V l α] [OfLayout V l α Y] :
    Contraction (DiagonalOutermorphism V α) X Y := ⟨apply⟩
instance (priority := low) {l : Layout} {X Y : Type} [InLayout X V l α] [OfLayout V l α Y] :
    Contraction X (DiagonalOutermorphism V α) Y := ⟨rowApply⟩

/-- Julia `DiagonalOperator(O::Outermorphism)` (`forms.jl:737`): the diagonal
outermorphism of the grade-1 diagonal. -/
@[inline] def ofOutermorphism (O : Outermorphism V V α) : DiagonalOutermorphism V α :=
  DiagonalMorphism.outermorphism (DiagonalOperator.ofEndomorphism O.base)

end DiagonalOutermorphism

end Grassmann
