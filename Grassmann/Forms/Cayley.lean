/-
Operators built from the algebra itself (Grassmann.jl `src/forms.jl:802-835,
1157-1213, 1578-1598`; port-notes/grassmann-forms.md §2.9, §2.13, §4.7, §4.11):

* `operator(t, G)`: the matrix of the sandwich `x ↦ x ⊘ t` on the grade-`G`
  basis (column `j` = `eⱼ ⊘ t`), and `gradedoperator(t)` = `outermorphism(t)`,
  the tuple of those matrices for `G = 1 … n`;
* `operator(f, V, G)`: the matrix of an arbitrary linear map of grade-`G` chains;
* `cayley(V, op)`: the multiplication table `op(eᵢ, eⱼ)` of the basis blades of a
  layout, with Julia's result kinds (`Submanifold`, `Single`, `Zero`, ...), for
  display and `printtex`;
* `metrictensor(V)`: the Gram matrix `gᵢⱼ = eᵢ ⋅ eⱼ` as an endomorphism,
  `metricextensor(V)` its outermorphism, `antimetrictensor(V, G)`.

`metrictensor` of a conformal space uses the correct Gram matrix (the null pair
`g(e∞, e∅) = -1` and each other generator's own signature); Julia hard-codes `+1`
on the non-null generators (defect C4neg, `forms.jl:1586-1593`), which differs only
for conformal spaces with negative generators.
-/
import Grassmann.Forms.Spectral

namespace Grassmann

open DirectSum StaticVectors AbstractTensors Grassmann.Forms

variable {V : TensorBundle} {α : Type} [Coeff α]

/-! ## Operators of linear maps -/

/-- Julia `operator(fun, V, G)` (`forms.jl:1198-1201`): the matrix of a linear map
of grade-`G` chains, column `j` = `f(eⱼ)`. -/
@[specialize] def TensorOperator.ofLinear {W : TensorBundle} {H G : Nat} (f : Chain V G α → Chain W H α) :
    TensorOperator V (.chain G) W (.chain H) α :=
  ⟨Mat.ofCols fun j => (f (Chain.ofFn fun i => if i.1 = j.1 then Coeff.one else Coeff.zero)).v⟩

/-- Julia `operator(t, G)` (`forms.jl:1186-1188`): the matrix of `x ↦ x ⊘ t` on
grade `G`, column `j` = `eⱼ ⊘ t = (~t) ⟑ eⱼ ⟑ involute(t)` projected on grade `G`
(for a versor `t` the sandwich preserves the grade). -/
@[specialize] def operator {X : Type} [Kernels V] [DenseLayout X V α] (t : X) (G : Nat) : Endomorphism V (.chain G) α :=
  let r := DenseLayout.values t
  ⟨Mat.ofCols fun j =>
    sandwichCore (layoutOf X) (.chain G) .full (.chain G) none r
      (Values.ofFn fun i => if i.1 = j.1 then Coeff.one else Coeff.zero)⟩

/-- Julia `operator(t)` for a term in a diagonal space (`forms.jl:1183-1185`):
the diagonal of the sandwich matrix, a `DiagonalOperator`. -/
def operatorDiag {X : Type} [Kernels V] [DenseLayout X V α] (t : X) (G : Nat) : DiagonalOperator V (.chain G) α :=
  DiagonalOperator.ofEndomorphism (operator t G)

/-- Julia `gradedoperator(t)` / `outermorphism(t)` of an element
(`forms.jl:1190-1196`): the sandwich matrices of every grade `1 … n` as an
`Outermorphism` (each grade computed, not the compounds of the grade-1 one). -/
@[specialize] def gradedoperator {X : Type} [Kernels V] [DenseLayout X V α] (t : X) : Outermorphism V V α :=
  ⟨((List.range V.n).map fun k => DMat.ofMat (operator t (k + 1)).mat).toArray⟩

/-! ## Metric tensors -/

/-- Julia `metricdyad(V)` / `metrictensor(V)` (`forms.jl:1582-1593`): the Gram
matrix `gᵢⱼ = eᵢ ⋅ eⱼ` as a grade-1 endomorphism (`Rat` metric values embedded with
`Coeff.ofRat`). -/
@[specialize] def metrictensor (V : TensorBundle) : Endomorphism V (.chain 1) α :=
  let g := V.gram
  TensorOperator.ofFn fun i j => Coeff.ofRat ((g[i.1]?.bind (·[j.1]?)).getD 0)

/-- Julia `metrictensor(V, G) = compound(metrictensor(V), G)` (`forms.jl:1629`). -/
@[inline] def metrictensorGrade (V : TensorBundle) (G : Nat) : Endomorphism V (.chain G) α :=
  (metrictensor (α := α) V).compound G

/-- Julia `antimetrictensor(V, G) = compound(metrictensor(V), n - G)` (`forms.jl:1580`). -/
@[inline] def antimetrictensor (V : TensorBundle) (G : Nat := 1) : Endomorphism V (.chain (V.grade - G)) α :=
  (metrictensor (α := α) V).compound (V.grade - G)

/-- Julia `metricextensor(V) = Outermorphism(metrictensor(V))` (`forms.jl:1597`). -/
@[inline] def metricextensor (V : TensorBundle) : Outermorphism V V α :=
  (metrictensor (α := α) V).outermorphism

/-! ## Cayley tables -/

/-- Julia's `cayley(V, op)` table (`forms.jl:807-823`): entry `(i, j)` is
`op(bᵢ, bⱼ)` for the blades `b` of a layout, as DirectSum's blade result (the
Julia kind: `Submanifold`, `Single`, `Zero`, or a sum), or the error Julia throws. -/
structure CayleyTable (V : TensorBundle) where
  /-- The layout whose blades index rows and columns. -/
  layout : Layout
  /-- The entries, row-major. -/
  entries : Array (Array (Except String BladeResult))

/-- Julia `cayley(V, op)` over the full basis, or a grade (`cayley(V, G, op)`),
the even (`cayleyeven`) or odd (`cayleyodd`) blades. -/
def cayley (V : TensorBundle) (op : BinOp) (l : Layout := .full) : CayleyTable V :=
  let bs := l.blades V.n
  ⟨l, bs.map fun a => bs.map fun b => V.apply₂ op a b⟩

/-! ## Eigenvalues of elements (their sandwich operators) -/

namespace Forms

variable {V : TensorBundle}

/-- Julia's test for the closed-form spinor eigenvalues (`forms.jl:1352-1373`): the
Euclidean plane or space (`S == 2 || S === S"2" || S === 3 || S === S"3"`). -/
def euclid23 (V : TensorBundle) : Bool :=
  (V.n == 2 || V.n == 3) && !V.hasinf && !V.hasorigin && V.diffvars == 0 && V.dyadmode == 0 &&
    match V.metric with
    | .euclid => true
    | .signature neg => neg == 0
    | _ => false

/-- The closed-form eigenvalues of `x ↦ x ⊘ X` for an even element `X` of the Euclidean
plane or space (`forms.jl:1360-1373`): with `X² = re + B`, `re ∓ i|B|` (and `|X|²` in
3-D). Julia's 2-D `Spinor` case throws (`imaginary(::Spinor)` has no method, port-notes
§8.4 item 17); here it is the same formula. -/
def spinorEigvals [Kernels V] (X : Spinor V Float) : Spectrum ((Layout.chain 1).size V.n) :=
  let X2 : Spinor V Float := ((X * X : Half V (false ^^ false) Float)).cast (by simp)
  let re := getD X2.v 0
  let b : Chain V 2 Float := X2.grade 2
  let sq := Float.sqrt (getD b.abs2.v 0)
  let third := getD (X.abs2).v 0
  .complex (Values.ofFn fun i => match i.1 with
    | 0 => ⟨re, -sq⟩ | 1 => ⟨re, sq⟩ | _ => ⟨third, 0⟩)

end Forms

open Forms in
/-- Julia `eigvals(X)` of a chain (`forms.jl:1350-1359`): a scalar `s` has the triple
eigenvalue `s²` (`abs2`); an even chain of the Euclidean plane/space the closed form of
its spinor; otherwise the eigenvalues of `operator(X)`. -/
def Chain.eigvals {G : Nat} [Kernels V] (X : Chain V G Float) : Spectrum ((Layout.chain 1).size V.n) :=
  if G = 0 then
    let s := getD X.v 0
    .real (Values.replicate (s * s))
  else if G % 2 == 0 && euclid23 V then spinorEigvals (Grassmann.toHalf X false)
  else (operator X 1).eigvals

open Forms in
/-- Julia `eigvals(X::Spinor)` (`forms.jl:1360-1373`). -/
def Half.eigvals [Kernels V] (X : Spinor V Float) : Spectrum ((Layout.chain 1).size V.n) :=
  if euclid23 V then spinorEigvals X else (operator X 1).eigvals

open Forms in
/-- Julia `eigvals(X::Couple)` (`forms.jl:1360-1373`): the spinor closed form for an
even blade of the Euclidean plane/space, else the eigenvalues of `operator(X)`. -/
def Couple.eigvals [Kernels V] (X : Couple V Float) : Spectrum ((Layout.chain 1).size V.n) :=
  if euclid23 V && DirectSum.Bits.popcount X.bits % 2 == 0 then spinorEigvals (Grassmann.toHalf X false)
  else (operator X 1).eigvals

end Grassmann
