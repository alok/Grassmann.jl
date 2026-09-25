import Grassmann.Dynamic.Basic
import Grassmann.Dynamic.Arith
import Grassmann.Dynamic.Show

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
-/
