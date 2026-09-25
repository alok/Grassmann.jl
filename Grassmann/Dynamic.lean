import Grassmann.Dynamic.Basic
import Grassmann.Dynamic.Arith
import Grassmann.Dynamic.Show
import Grassmann.Dynamic.Unary
import Grassmann.Dynamic.Products
import Grassmann.Dynamic.Layout
import Grassmann.Dynamic.Laws

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
| `Grassmann.Dynamic.Unary` | involutions, complements, metrics, parity/reality parts, grade projections |
| `Grassmann.Dynamic.Products` | `⟑ ∧ ∨ contraction` with Julia's result kinds, the derived products, sandwiches |
| `Grassmann.Dynamic.Layout` | `LayoutInv n`: the index-table round trips the proofs use (kernel-checked, `n ≤ 8`) |
| `Grassmann.Dynamic.Laws` | `toDense_add`, `toDense_neg`, `toDense_sub`, `toDense_smul` over any `LawfulCoeff` |
-/
