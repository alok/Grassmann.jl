/-
`TensorOperator`: linear maps between graded components of two algebras
(Julia `TensorOperator{V,W,T}` / `Endomorphism{V,T}`, Grassmann.jl
`src/forms.jl:555-710`; port-notes/grassmann-forms.md §2.7, §3.2, §4.7).

Julia stores a map `Λ^g V → Λ^h W` as a nested chain `Chain{V,g,Chain{W,h,T}}`
(outer index = domain blade = column, inner = codomain component = row) and the
same for the even (`Spinor`), odd (`CoSpinor`) and full (`Multivector`)
gradings. Here the grading of each side is a DirectSum `Layout` in the type:

  `TensorOperator V ld W lc α`  ≅  Julia `TensorOperator{V,W,<:ld{V,<:lc{W,α}}}`

with `ld`/`lc ∈ {.chain g, .even, .odd, .full}` and the entries in one
column-major `Forms.Mat` (a `FloatArray` at `Float`). A column is a cheap
`Chain W h α` / `Half` / `Multivector` view (`column`).

All operator linear algebra is **metric-free** (apply, compose, transpose,
trace, the compound family, inverses, characteristic polynomials): Julia's square
`A ⋅ x` uses `matmul` (`forms.jl:950`); its non-square `A ⋅ x` falls back to the
domain-metric contraction (`products.jl:1165`), which agrees for Euclidean
domains and is replaced by `matmul` here (port-notes §4.7).

Julia's quirks fixed here (port-notes §8.4): `transpose` of non-grade-1
nestings (Julia returns the operator unchanged: item 4), `diag` of a
`CoSpinor` endomorphism (Julia returns a `Spinor`: item 3), `T ± λI` for every
square operator (Julia: grade-1 only), and `==` (a `StackOverflowError` in
Grassmann 0.8.46: item 12).
-/
import Grassmann.Forms.Mat
import Grassmann.Algebra.Norms

namespace Grassmann

open DirectSum StaticVectors AbstractTensors Grassmann.Forms

/-! ## Element carriers of a layout -/

/-- `X` stores its coefficients in layout `l` of `V` (the domain side of an
operator application): `Chain V G` in `.chain G`, `Spinor` in `.even`,
`CoSpinor` in `.odd`, `Multivector` in `.full`, and the terms `Single`,
`Submanifold` in their grade. -/
class InLayout (X : Type) (V : outParam TensorBundle) (l : outParam Layout) (α : outParam Type)
    [Coeff α] where
  /-- The coefficient vector in layout `l`. -/
  vals : X → Values α (l.size V.n)

/-- The element type holding layout `l` of `V` (the codomain side): `Chain`,
`Spinor`, `CoSpinor` or `Multivector`. -/
class OfLayout (V : TensorBundle) (l : Layout) (α : Type) [Coeff α] (X : outParam Type) where
  /-- The element with these coefficients. -/
  ofVals : Values α (l.size V.n) → X

section Carriers

variable {V : TensorBundle} {G : Nat} {α : Type} [Coeff α]

instance : InLayout (Chain V G α) V (.chain G) α := ⟨Chain.v⟩
instance : InLayout (Half V false α) V .even α := ⟨Half.v⟩
instance : InLayout (Half V true α) V .odd α := ⟨Half.v⟩
instance : InLayout (Multivector V α) V .full α := ⟨Multivector.v⟩
instance : InLayout (Single V G α) V (.chain G) α := ⟨fun s => (Chain.ofSingle s).v⟩
instance : InLayout (Submanifold V G) V (.chain G) Int := ⟨fun b => (Chain.ofBlade b 1).v⟩

instance : OfLayout V (.chain G) α (Chain V G α) := ⟨Chain.mk⟩
instance : OfLayout V .even α (Half V false α) := ⟨fun v => (⟨v⟩ : Half V false α)⟩
instance : OfLayout V .odd α (Half V true α) := ⟨fun v => (⟨v⟩ : Half V true α)⟩
instance : OfLayout V .full α (Multivector V α) := ⟨Multivector.mk⟩

end Carriers

/-! ## The operator type -/

/-- A linear map from layout `ld` of `V` (domain, the columns) to layout `lc`
of `W` (codomain, the rows): Julia `TensorOperator{V,W,T}` (`forms.jl:555`). -/
structure TensorOperator (V : TensorBundle) (ld : Layout) (W : TensorBundle) (lc : Layout)
    (α : Type) [Coeff α] where
  /-- The matrix: `lc.size W.n` rows, `ld.size V.n` columns. -/
  mat : Mat (lc.size W.n) (ld.size V.n) α

/-- Julia `Endomorphism{V,T} = TensorOperator{V,V,T}` (`forms.jl:563`). -/
abbrev Endomorphism (V : TensorBundle) (l : Layout) (α : Type) [Coeff α] :=
  TensorOperator V l V l α

/-- Julia `Simplex{V,<:Chain{W,1}}` as an operator: a grade-1 map `V → W`,
i.e. a list of `n` vectors of `W` (`multivectors.jl:94`). -/
abbrev Simplex (V W : TensorBundle) (α : Type) [Coeff α] := TensorOperator V (.chain 1) W (.chain 1) α

namespace TensorOperator

variable {V W U : TensorBundle} {ld lc lu : Layout} {α : Type} [Coeff α]

/-- Number of rows (Julia `size(T, 1)`: the codomain dimension). -/
@[inline] def rows (_ : TensorOperator V ld W lc α) : Nat := lc.size W.n

/-- Number of columns (Julia `size(T, 2)`: the domain dimension). -/
@[inline] def cols (_ : TensorOperator V ld W lc α) : Nat := ld.size V.n

/-! ### Construction -/

/-- Build from the entries `f i j` (row `i`, column `j`, 0-based). -/
@[inline] def ofFn (f : Fin (lc.size W.n) → Fin (ld.size V.n) → α) : TensorOperator V ld W lc α :=
  ⟨Mat.ofFn f⟩

/-- Build from the columns (Julia `TensorOperator(Chain{V,G}(col₁, …, colₙ))`,
`forms.jl:565-569`): column `j` is the image of domain blade `j`. -/
@[inline] def ofColumns {X : Type} [InLayout X W lc α] (f : Fin (ld.size V.n) → X) :
    TensorOperator V ld W lc α :=
  ⟨Mat.ofCols fun j => InLayout.vals (f j)⟩

/-- Build from a list of columns, if there is one per domain blade. -/
def ofColumnList? {X : Type} [InLayout X W lc α] (cols : List X) : Option (TensorOperator V ld W lc α) :=
  if h : cols.length = ld.size V.n then
    some (ofColumns fun j => cols[j.1]'(by rw [h]; exact j.2))
  else none

/-- Build from Julia's row-wise matrix literal (`Endomorphism([1 2; 3 4])`:
row `i` lists the `i`-th components of the column images), if the shape fits
(`forms.jl:624-633`). -/
def ofRows? (rows : List (List α)) : Option (TensorOperator V ld W lc α) :=
  (Mat.ofRows? rows).map (⟨·⟩)

/-- The zero operator (Julia `zero(T)`, `forms.jl:599`). -/
@[inline] def zero : TensorOperator V ld W lc α := ⟨Mat.zero⟩

/-- The identity (Julia `Chain{V,G}(I)`, `Spinor{V}(I)`, `Multivector{V}(I)`,
`forms.jl:1166-1169`); ones on the diagonal. -/
@[inline] def identity : TensorOperator V ld W lc α := ⟨Mat.identity⟩

/-- Julia `λ*Chain{V,G}(I)`: a uniform scaling. -/
@[inline] def uniform (s : α) : TensorOperator V ld W lc α :=
  ⟨Mat.ofFn fun i j => if i.1 = j.1 then s else Coeff.zero⟩

/-! ### Access -/

/-- Entry `(i, j)`, 0-based (Julia `T[i+1, j+1] = value(value(T.v)[j+1])[i+1]`,
`forms.jl:588`); zero out of range. -/
@[inline] def entry (T : TensorOperator V ld W lc α) (i j : Nat) : α := T.mat.getD i j

/-- Column `j` as a coefficient vector. -/
@[inline] def colValues (T : TensorOperator V ld W lc α) (j : Fin (ld.size V.n)) : Values α (lc.size W.n) :=
  T.mat.col j

/-- Column `j` as an element of `W` (Julia `T[j+1]`, the image of the
`j`-th domain blade, `forms.jl:589`). -/
@[inline] def column {Y : Type} [OfLayout W lc α Y] (T : TensorOperator V ld W lc α)
    (j : Fin (ld.size V.n)) : Y :=
  OfLayout.ofVals (V := W) (l := lc) (T.colValues j)

/-- Julia `T ⋅ b` for a basis blade `b` of the domain grade (`forms.jl:945-946`):
the column of `b` (Julia `x[bladeindex(y)]`), for any coefficient type. -/
def columnOfBlade {G : Nat} {Y : Type} [OfLayout W lc α Y] (T : TensorOperator V (.chain G) W lc α)
    (b : Submanifold V G) : Y :=
  let j := Leibniz.bladeRank V.n b.bits
  let r := lc.size W.n
  let a := T.mat.v.data
  OfLayout.ofVals (V := W) (l := lc) (Mat.finish (Mat.pushLoop (fun i => Mat.rd a (j * r + i)) r 0 (Packed.mkEmpty r)))

/-- Julia `T ⋅ (s·b)` for a scaled basis blade (`forms.jl:945`): `s` times its column. -/
def applySingle {G : Nat} {Y : Type} [OfLayout W lc α Y] (T : TensorOperator V (.chain G) W lc α)
    (s : Single V G α) : Y :=
  let j := Leibniz.bladeRank V.n s.bits
  let r := lc.size W.n
  let a := T.mat.v.data
  OfLayout.ofVals (V := W) (l := lc)
    (Mat.finish (Mat.pushLoop (fun i => s.val * Mat.rd a (j * r + i)) r 0 (Packed.mkEmpty r)))

/-- The columns in order (Julia `value(T)`, the nested chain's entries). -/
def columns {Y : Type} [OfLayout W lc α Y] (T : TensorOperator V ld W lc α) : List Y :=
  (List.finRange (ld.size V.n)).map T.column

/-- The rows as lists (Julia `Matrix(T)` row by row, `forms.jl:326-334`). -/
@[inline] def toRows (T : TensorOperator V ld W lc α) : List (List α) := T.mat.toRows

/-- Julia `T[i+1, j+1]` as `T[(i, j)]`. -/
instance : GetElem (TensorOperator V ld W lc α) (Nat × Nat) α
    (fun _ p => p.1 < lc.size W.n ∧ p.2 < ld.size V.n) where
  getElem T p h := T.mat.get ⟨p.1, h.1⟩ ⟨p.2, h.2⟩

/-- Julia `T[j+1]`: the `j`-th column as an element of `W`. -/
instance {Y : Type} [OfLayout W lc α Y] :
    GetElem (TensorOperator V ld W lc α) Nat Y (fun _ j => j < ld.size V.n) where
  getElem T j h := T.column ⟨j, h⟩

/-! ### Application -/

/-- `T x` on coefficient vectors (Julia `matmul`, `forms.jl:957-968`). -/
@[inline] def applyValues (T : TensorOperator V ld W lc α) (x : Values α (ld.size V.n)) :
    Values α (lc.size W.n) :=
  T.mat.mulVec x

/-- Julia `T(x) = T ⋅ x` (`forms.jl:572`): the image of a domain element. -/
@[inline] def apply {X Y : Type} [InLayout X V ld α] [OfLayout W lc α Y]
    (T : TensorOperator V ld W lc α) (x : X) : Y :=
  OfLayout.ofVals (V := W) (l := lc) (T.applyValues (InLayout.vals x))

/-- Row application `x ⋅ T` (Julia `contraction(a::Chain, b::Chain{V,G,<:Chain})`,
`forms.jl:940`): `out[j] = Σ_i conj(x[i]) T[i,j]`, an element of the domain. -/
@[inline] def rowApply {X Y : Type} [Conj α] [InLayout X W lc α] [OfLayout V ld α Y]
    (x : X) (T : TensorOperator V ld W lc α) : Y :=
  OfLayout.ofVals (V := V) (l := ld) (Mat.vecMulWith conj (InLayout.vals x) T.mat)

/-- Composition `A ∘ B` (Julia `A ⋅ B`, `forms.jl:941, 948`): `B` first. -/
@[inline] def comp (A : TensorOperator W lc U lu α) (B : TensorOperator V ld W lc α) :
    TensorOperator V ld U lu α :=
  ⟨A.mat.mul B.mat⟩

/-- Julia's bilinear form `T(x, y) = vecdot(T ⋅ x, y)` (`forms.jl:573-575`):
the coefficient dot `Σ_i conj((T x)[i]) y[i]` (metric-free). -/
@[inline] def form {X Y : Type} [Conj α] [InLayout X V ld α] [InLayout Y W lc α]
    (T : TensorOperator V ld W lc α) (x : X) (y : Y) : α :=
  let tx := T.applyValues (InLayout.vals x)
  let yv := InLayout.vals y
  Mat.sdot0 (α := α) conj tx.data yv.data 1 1 (lc.size W.n) 0 0

/-- Julia `T ⋅ x` for an operator whose entries are combined with `∧`
(`matwedge`, `forms.jl:969-971`): for scalar entries `∧` is the product, so this
is `T x`. -/
@[inline] def wedgeApply {X Y : Type} [InLayout X V ld α] [OfLayout W lc α Y]
    (T : TensorOperator V ld W lc α) (x : X) : Y := T.apply x

/-- Julia `T ∨ x` (`matvee`, `forms.jl:972-974`): the regressive product of two
scalars is zero, so the result is the zero element. -/
@[inline] def veeApply {X Y : Type} [InLayout X V ld α] [OfLayout W lc α Y]
    (_ : TensorOperator V ld W lc α) (_ : X) : Y := OfLayout.ofVals (V := W) (l := lc) (zeroValues (α := α) _)

/-! ### Linear-algebra basics -/

/-- The transpose `W → V` (Julia `transpose(T)`, `forms.jl:307-308, 591`; also
for the Spinor/Multivector/grade-`g` nestings, where Julia returns `T` itself). -/
@[inline] def transpose (T : TensorOperator V ld W lc α) : TensorOperator W lc V ld α :=
  ⟨T.mat.transpose⟩

/-- The trace `Σ_i T[i,i]` over `min(rows, cols)` (Julia `tr`, `forms.jl:314-322`). -/
@[inline] def tr (T : TensorOperator V ld W lc α) : α := T.mat.trace

/-- Julia `scalar(T) = tr(T)/length(value(T))` (`forms.jl:593`): the mean
eigenvalue of an endomorphism (Julia returns a `Float` for `Int` entries; use a
field coefficient type). -/
@[inline] def scalar [Div α] (T : TensorOperator V ld W lc α) : α :=
  T.tr / Coeff.ofInt (ld.size V.n)

/-- The diagonal `T[i,i]`, `i < min(rows, cols)` (Julia `diag`, `forms.jl:638-656`). -/
@[inline] def diagValues (T : TensorOperator V ld W lc α) : Values α (min (lc.size W.n) (ld.size V.n)) :=
  T.mat.diag

/-- Map every entry (Julia `map(f, T)`, `forms.jl:1126-1129`). -/
@[inline] def map {β : Type} [Coeff β] (f : α → β) (T : TensorOperator V ld W lc α) :
    TensorOperator V ld W lc β :=
  ⟨T.mat.map f⟩

/-- Whether every entry is exactly zero. -/
@[inline] def isZero (T : TensorOperator V ld W lc α) : Bool := T.mat.isZero

/-- Julia `A : B` (`forms.jl:936`): `Σ_j value(A[j]) ⋅ value(B[j])`, the
Frobenius pairing `Σ_{ij} conj(A[i,j]) B[i,j]` (Julia returns it as a grade-0
chain, `T:T = 5v`). -/
@[inline] def frobenius [Conj α] (A B : TensorOperator V ld W lc α) : α := Mat.frobenius conj A.mat B.mat

/-- Julia's Gershgorin row radii `Σ_{j≠i} |T[i,j]|` (`forms.jl:1521-1523`),
as `Float`s. -/
@[specialize] def gerschgorin [JNorm α] (T : TensorOperator V ld W lc α) : Values Float (lc.size W.n) :=
  Values.ofFn fun i =>
    (List.range (ld.size V.n)).foldl (fun acc j =>
      acc + (if j == i.1 then 0 else JNorm.norm (T.entry i.1 j))) 0

instance : Add (TensorOperator V ld W lc α) := ⟨fun A B => ⟨A.mat + B.mat⟩⟩
instance : Sub (TensorOperator V ld W lc α) := ⟨fun A B => ⟨A.mat - B.mat⟩⟩
instance : Neg (TensorOperator V ld W lc α) := ⟨fun A => ⟨-A.mat⟩⟩
instance : HMul α (TensorOperator V ld W lc α) (TensorOperator V ld W lc α) := ⟨fun s A => ⟨s * A.mat⟩⟩
instance : HMul (TensorOperator V ld W lc α) α (TensorOperator V ld W lc α) := ⟨fun A s => ⟨A.mat * s⟩⟩
/-- Julia `T / s = T * (1/s)` (Grassmann divides a tensor by a number through the
reciprocal, `algebra.jl:704-706`, so `T/10` has the entries `7 * 0.1`). -/
instance [Div α] : HDiv (TensorOperator V ld W lc α) α (TensorOperator V ld W lc α) :=
  ⟨fun A s => let r := Coeff.one / s; ⟨A.mat * r⟩⟩
instance : Inhabited (TensorOperator V ld W lc α) := ⟨zero⟩
/-- Julia `a == b` on operators: equality of the nested values (master
`forms.jl:658`; `StackOverflowError` in 0.8.46). -/
instance [BEq α] : BEq (TensorOperator V ld W lc α) := ⟨fun A B => A.mat == B.mat⟩

/-- `T + s I` (Julia `T + s*I`, `forms.jl:1143-1153`). -/
@[inline] def addScalar (T : TensorOperator V ld W lc α) (s : α) : TensorOperator V ld W lc α :=
  ⟨T.mat.addDiag s⟩

/-- `s I - T` (Julia `s*I - T`). -/
@[inline] def scalarSub (s : α) (T : TensorOperator V ld W lc α) : TensorOperator V ld W lc α :=
  ⟨(-T.mat).addDiag s⟩

/-- `T + λI` for a uniform scaling (Julia `T + I`, `T + 2I`). -/
instance : HAdd (TensorOperator V ld W lc α) (UniformScaling α) (TensorOperator V ld W lc α) :=
  ⟨fun T s => T.addScalar s.val⟩
instance : HAdd (UniformScaling α) (TensorOperator V ld W lc α) (TensorOperator V ld W lc α) :=
  ⟨fun s T => T.addScalar s.val⟩
instance : HSub (TensorOperator V ld W lc α) (UniformScaling α) (TensorOperator V ld W lc α) :=
  ⟨fun T s => T.addScalar (-s.val)⟩
instance : HSub (UniformScaling α) (TensorOperator V ld W lc α) (TensorOperator V ld W lc α) :=
  ⟨fun s T => scalarSub s.val T⟩

/-! ### Products as notation -/

/-- `T * x`, `T ⋅ x`, `T ⟑ x` apply the operator (Julia `forms.jl:1103-1109`). -/
instance {X Y : Type} [InLayout X V ld α] [OfLayout W lc α Y] :
    HMul (TensorOperator V ld W lc α) X Y := ⟨apply⟩
instance {X Y : Type} [InLayout X V ld α] [OfLayout W lc α Y] :
    Contraction (TensorOperator V ld W lc α) X Y := ⟨apply⟩
/-- `x ⋅ T`: row application. -/
instance {X Y : Type} [Conj α] [InLayout X W lc α] [OfLayout V ld α Y] :
    Contraction X (TensorOperator V ld W lc α) Y := ⟨rowApply⟩
/-- `A * B`, `A ⋅ B`: composition, `B` first. -/
instance : HMul (TensorOperator W lc U lu α) (TensorOperator V ld W lc α) (TensorOperator V ld U lu α) :=
  ⟨comp⟩
instance : Contraction (TensorOperator W lc U lu α) (TensorOperator V ld W lc α)
    (TensorOperator V ld U lu α) := ⟨comp⟩
/-- `A ∧ B` (Julia `matwedge` on scalar entries: the product). -/
instance : Wedge (TensorOperator W lc U lu α) (TensorOperator V ld W lc α) (TensorOperator V ld U lu α) :=
  ⟨comp⟩
/-- `A ∨ B`: the regressive product of scalar entries vanishes (Julia: a zero matrix). -/
instance : Vee (TensorOperator W lc U lu α) (TensorOperator V ld W lc α) (TensorOperator V ld U lu α) :=
  ⟨fun _ _ => zero⟩
/-- `T ∧ x` (Julia `matwedge`): `T x` for scalar entries. -/
instance {X Y : Type} [InLayout X V ld α] [OfLayout W lc α Y] :
    Wedge (TensorOperator V ld W lc α) X Y := ⟨wedgeApply⟩
/-- `T ∨ x` (Julia `matvee`): zero for scalar entries. -/
instance {X Y : Type} [InLayout X V ld α] [OfLayout W lc α Y] :
    Vee (TensorOperator V ld W lc α) X Y := ⟨veeApply⟩

/-- Julia's call syntax `T(x)` (`forms.jl:572`). -/
instance {X Y : Type} [OfLayout V ld α X] [InLayout X V ld α] [OfLayout W lc α Y] :
    CoeFun (TensorOperator V ld W lc α) (fun _ => X → Y) := ⟨apply⟩

end TensorOperator

/-! ## Endomorphism-specific operations -/

namespace Endomorphism

variable {V : TensorBundle} {l : Layout} {α : Type} [Coeff α]

/-- The diagonal as an element (Julia `diag(T)`, `forms.jl:642-656`; a
`CoSpinor` endomorphism gives a `CoSpinor`, where Julia returns a `Spinor`). -/
@[inline] def diag {Y : Type} [OfLayout V l α Y] (T : Endomorphism V l α) : Y :=
  OfLayout.ofVals (V := V) (l := l) (Values.ofFn fun i => T.entry i.1 i.1)

/-- The identity endomorphism (Julia `Chain{V,G}(I)`). -/
@[inline] def one : Endomorphism V l α := TensorOperator.identity

/-- Julia `bivector(A)` of a grade-1 endomorphism (`forms.jl:614-616`): the
coefficient of `eᵢ ∧ eⱼ` (`i < j`) is `A[j,i]` (the lower triangle). -/
@[specialize] def bivector (A : Endomorphism V (.chain 1) α) : Chain V 2 α :=
  Chain.ofFn fun k =>
    let b := (Leibniz.indexBasis V.n 2)[k.1]!
    let i := (DirectSum.Bits.indices b)[0]!
    let j := (DirectSum.Bits.indices b)[1]!
    A.entry (j - 1) (i - 1)

/-- Julia `companion(x)` (`forms.jl:829-835`): the companion matrix of the monic
polynomial `zⁿ + xₙ zⁿ⁻¹ + … + x₁`, columns `e₂, …, eₙ, -x`. -/
@[specialize] def companion {n : Nat} (x : Values α n) : Endomorphism (TensorBundle.euclidean n) (.chain 1) α :=
  TensorOperator.ofFn fun i j =>
    if j.1 + 1 = n then -(x.get ⟨i.1, Nat.lt_of_lt_of_eq i.2 (Forms.chainOne_size n)⟩)
    else if i.1 = j.1 + 1 then Coeff.one else Coeff.zero

end Endomorphism

end Grassmann
