/-
The user-facing vocabulary of `open Grassmann` (DESIGN.md §4.4).

`Grassmann` re-exports the user API of its dependencies, as Julia's
`Grassmann` does (`src/Grassmann.jl:26-29`): after `import Grassmann` and
`open Grassmann`,

* spaces and their literals: `TensorBundle`, `ℝ2 … ℝ9`, `STA`, `PGA2`, `PGA3`,
  `CGA2`, `CGA3`, `S!"…"`, `D!"…"`, `V!"…"`, `ℝ^n`, `V′`, `V ⊕ W`;
* element types: `Chain`, `Spinor`, `CoSpinor`, `Half`, `Multivector`,
  `Single`, `Submanifold`, `Couple`, `PseudoCouple`, `Phasor`, `Values`;
* coefficient classes `Coeff`, `Analytic` and `Complex`;
* the operator functions (`wedge`, `vee`, `contraction`, `hodge`, ...) and
  their notation.

## Notation

The operator notation is AbstractTensors' (DESIGN.md §4.4), declared again
here as `scoped` notation of `Grassmann`, so that `open Grassmann` activates it:

| op | token | precedence |
|---|---|---|
| geometric product | `*`, `⟑` (`⊖` at `+` level) | 70 |
| exterior / regressive | `∧` / `∨` | 35 / 30, right-assoc (overload `And`/`Or`: write `(a ∧ b) + c`) |
| contractions | `⋅`, `⨽`, `⨼` | 70 |
| cross, sandwich | `×` (overloads `Prod`), `⊘` | 35, 70 |
| antiproducts | `⟇` | 65 |
| reverse product, scalar product | `∗`, `⊛` | 70 |
| complements | prefix `⋆`, `!` (overloads `not`) | max |
| reverse, parts, conjugate, involute | prefix `~`, postfix `₊ ₋ ǂ ˣ` | max |
| versor action | `R >>> x` | 75 |

**Open `Grassmann` or `AbstractTensors`, not both**: the two namespaces declare
the same notation, and with both open every operator is ambiguous.
-/
import AbstractTensors
import DirectSum
import StaticVectors
import JuliaBase

namespace Grassmann

open AbstractTensors

export DirectSum (TensorBundle Metric Submanifold SubSpace Layout BinOp UnOp
  ℝ0 ℝ1 ℝ2 ℝ3 ℝ4 ℝ5 ℝ6 ℝ7 ℝ8 ℝ9 R2 R3 R4 R5 STA PGA2 PGA3 CGA2 CGA3)
export StaticVectors (Values Conj JNorm JApprox)
export AbstractTensors (Coeff Analytic Wedge Vee WedgeDot VeeDot Contraction Expansion Cross Sandwich
  Hodge ComplementLeft ComplementRight Reverse Involute Clifford Even Odd GradeProj Volume
  wedge vee wedgedot veedot contraction expansion cross sandwich hodge complementLeft
  complementRight involute clifford even odd volume scalar vector bivector trivector
  leftContraction reverseProduct scalarProduct shiftLeftContraction shiftRightContraction
  UniformScaling)
export JuliaBase (Complex)

/-- Exterior product; overloads `And` (35, right-assoc) through a choice node. -/
scoped infixr:35 " ∧ " => Wedge.wedge
/-- Regressive product; overloads `Or` (30, right-assoc) through a choice node. -/
scoped infixr:30 " ∨ " => Vee.vee
/-- Cross product; overloads `Prod` (35, right-assoc) through a choice node. -/
scoped infixr:35 " × " => Cross.cross
/-- Geometric product at `+` precedence (Julia `⊖`). -/
scoped infixl:65 " ⊖ " => WedgeDot.wedgedot
/-- Geometric product (Julia `⟑`, precedence of `*`). -/
scoped infixl:70 " ⟑ " => WedgeDot.wedgedot
/-- Anti-geometric product (Julia `⟇`, precedence of `+`). -/
scoped infixl:65 " ⟇ " => VeeDot.veedot
/-- Right contraction (Julia `⨽`, `>`, `|`). -/
scoped infixl:70 " ⨽ " => Contraction.contraction
/-- Right contraction (Julia `⋅`, `dot`). -/
scoped infixl:70 " ⋅ " => Contraction.contraction
/-- Left contraction (Julia `⨼`, `<`). -/
scoped infixl:70 " ⨼ " => leftContraction
/-- Reverse-geometric product (Julia `∗`). -/
scoped infixl:70 " ∗ " => reverseProduct
/-- Scalar product (Julia `⊛`). -/
scoped infixl:70 " ⊛ " => scalarProduct
/-- Sandwich (Julia `⊘`): `x ⊘ R = (~R) ⟑ x ⟑ involute(R)`. -/
scoped infixl:70 " ⊘ " => Sandwich.sandwich
/-- Tensor product (Julia `⊗`). -/
scoped infixl:70 " ⊗ " => TensorProd.tensorProd
/-- Symmetrized product (Julia `⊙`). -/
scoped infixl:70 " ⊙ " => SymProd.symProd
/-- Antisymmetrized product (Julia `⊠`). -/
scoped infixl:70 " ⊠ " => AntiSymProd.antiSymProd
/-- Hodge complement (Julia prefix `⋆`). -/
scoped prefix:max "⋆" => Hodge.hodge
/-- Right complement (Julia `!`); overloads `not` with the same operand precedence (40). -/
scoped notation:max "!" t:40 => ComplementRight.complementRight t
/-- Reverse (Julia prefix `~`). -/
scoped prefix:max "~" => Reverse.reverse
/-- Even part (Julia postfix `₊`). -/
scoped postfix:max "₊" => Even.even
/-- Odd part (Julia postfix `₋`). -/
scoped postfix:max "₋" => Odd.odd
/-- Conjugate (Julia postfix `ǂ`; the reverse on tensors). -/
scoped postfix:max "ǂ" => StaticVectors.Conj.conj
/-- Grade involution (Julia postfix `ˣ`). -/
scoped postfix:max "ˣ" => Involute.involute

end Grassmann
