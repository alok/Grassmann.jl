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
def TensorOperator.ofLinear {W : TensorBundle} {H G : Nat} (f : Chain V G α → Chain W H α) :
    TensorOperator V (.chain G) W (.chain H) α :=
  ⟨Mat.ofCols fun j => (f (Chain.ofFn fun i => if i.1 = j.1 then Coeff.one else Coeff.zero)).v⟩

/-- Julia `operator(t, G)` (`forms.jl:1186-1188`): the matrix of `x ↦ x ⊘ t` on
grade `G`, column `j` = `eⱼ ⊘ t = (~t) ⟑ eⱼ ⟑ involute(t)` projected on grade `G`
(for a versor `t` the sandwich preserves the grade). -/
def operator {X : Type} [Kernels V] [DenseLayout X V α] (t : X) (G : Nat) : Endomorphism V (.chain G) α :=
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
def gradedoperator {X : Type} [Kernels V] [DenseLayout X V α] (t : X) : Outermorphism V V α :=
  ⟨((List.range V.n).map fun k => DMat.ofMat (operator t (k + 1)).mat).toArray⟩

/-! ## Metric tensors -/

/-- Julia `metricdyad(V)` / `metrictensor(V)` (`forms.jl:1582-1593`): the Gram
matrix `gᵢⱼ = eᵢ ⋅ eⱼ` as a grade-1 endomorphism (`Rat` metric values embedded with
`Coeff.ofRat`). -/
def metrictensor (V : TensorBundle) : Endomorphism V (.chain 1) α :=
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

end Grassmann
