import Grassmann.Proofs.Link
import Grassmann.Proofs.Tables
import Grassmann.Proofs.Conformal
import Grassmann.Proofs.Regressive

/-!
# Grassmann.Proofs: the implementation meets the specification

Links DirectSum's blade rules and the reference kernels to the proved model
`Grassmann.Spec` (docs/PROOFS.md has the full inventory, and says what is
proved in general, what is checked by kernel evaluation and what is tested):

* `Grassmann.Proofs.Link`: reading implementation term lists as spec
  multivectors; a blade table that agrees with the spec gives the spec product
  on all multivectors (`implMul_eq_mul`); the signature-space sign
  `TensorBundle.mulSign` is the spec coefficient for every width `≤ 64`
  (`mulSign_eq_coef`, general).
* `Grassmann.Proofs.Tables`: `decide +kernel` checks of the geometric and
  exterior products, reversion, involution, complement and Hodge tables, and of
  the reference plans, in `ℝ2`, `ℝ3`, `STA`, `PGA2`, `PGA3` and `D!"1,2,-3"`;
  the contraction `⋅` (lifted to all multivectors: `R3_contract`, …).
* `Grassmann.Proofs.Regressive`: the regressive product `∨` on every pair of
  blades.
* `Grassmann.Proofs.Conformal`: the conformal (null-basis, Chevalley) product
  by transport of structure to a diagonal metric: a transported blade table
  makes the product isomorphic to `Cl(p,q)` and associative on all multivectors
  (proved); the table itself is checked exhaustively by the test suite.
-/
