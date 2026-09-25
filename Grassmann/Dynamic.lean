import Grassmann.Dynamic.Basic
import Grassmann.Dynamic.Arith
import Grassmann.Dynamic.Show
import Grassmann.Dynamic.Loops
import Grassmann.Dynamic.Unary
import Grassmann.Dynamic.Products
import Grassmann.Dynamic.Fast
import Grassmann.Dynamic.Norms
import Grassmann.Dynamic.Layout
import Grassmann.Dynamic.Laws
import Grassmann.Dynamic.Equal
import Grassmann.Dynamic.Ops
import Grassmann.Dynamic.Division
import Grassmann.Dynamic.Composite
import Grassmann.Dynamic.Project

/-!
# The dynamic, Julia-exact element layer (`Grassmann.TA`)

DESIGN.md §4.3. One type `TA V α` holds every Julia `TensorAlgebra{V}` value
(`Zero`, `One`, `Infinity`, basis blades, `Single`, `Chain`, `Couple`,
`PseudoCouple`, `Spinor`, `CoSpinor`, `Multivector`, `Phasor`); operations decide the
result *kind* at runtime exactly as Julia's dispatch decides the result type, and
compute the entries with the static layer's kernels.

| module | contents |
|---|---|
| `Grassmann.Dynamic.Basic` | `TA`, kinds, `coeff`, `toDense`, `multispin`, coefficient maps |
| `Grassmann.Dynamic.Arith` | the `+`/`-` representation lattice, negation, scalar actions, numbers in sums |
| `Grassmann.Dynamic.Show` | Julia `show`/compact display of every kind |
| `Grassmann.Dynamic.Loops` | Julia's generated product, sandwich and metric loops, bit for bit (summation order and the sign of zero) |
| `Grassmann.Dynamic.Unary` | involutions, complements, metrics, parity/reality parts, grade projections |
| `Grassmann.Dynamic.Products` | `⟑ ∧ ∨ contraction` with Julia's result kinds, the derived products, sandwiches |
| `Grassmann.Dynamic.Fast` | `DynKernels`: container products and unary maps through generated kernels where they are Julia's loops bit for bit |
| `Grassmann.Dynamic.Norms` | `abs2`, `norm`, `isscalar` with Julia's kinds |
| `Grassmann.Dynamic.Layout` | `LayoutInv n`: the index-table round trips the proofs use (kernel-checked, `n ≤ 8`) |
| `Grassmann.Dynamic.Equal` | Julia's `==` (`equal`), coefficientwise `denseEq` and its correctness |
| `Grassmann.Dynamic.Laws` | `toDense_add`, `toDense_neg`, `toDense_sub`, `toDense_smul` over any `LawfulCoeff` |
-/
