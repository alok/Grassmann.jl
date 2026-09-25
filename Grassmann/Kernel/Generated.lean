import Grassmann.Kernel.Generated.R2
import Grassmann.Kernel.Generated.R3
import Grassmann.Kernel.Generated.R4
import Grassmann.Kernel.Generated.STA
import Grassmann.Kernel.Generated.PGA2
import Grassmann.Kernel.Generated.PGA3
import Grassmann.Kernel.Generated.CGA2
import Grassmann.Kernel.Generated.CGA3

/-!
# Pre-generated kernels for the standard spaces (DESIGN.md §5.2)

`grassmann_kernels` output for `ℝ2`, `ℝ3`, `ℝ4`, `STA` (`S!"-+++"`), `PGA2`
(`D!"0,1,1"`), `PGA3` (`D!"0,1,1,1"`), `CGA2` (`S!"∞∅++"`) and `CGA3`
(`S!"∞∅+++"`), under `Grassmann.Kernel.Gen.<space>`, each with a `Kernels`
instance (`Grassmann.Kernel.Gen.<space>.instKernels`). The literals `S!"+++"`,
`V!"3"`, `ℝ^3`, ... elaborate to the same structure as `ℝ3`, so these instances
serve them too, and `basis!` of one of these spaces reuses them.

Every emission policy default applies (`Grassmann.Kernel.Codegen.Policy.default`):
all typed and dense families of `*`, `∧`, `∨`, `⋅` and `∗`, the sandwich
projections, `Chain×Chain` of the other products and every unary map. The
`CGA3` module, the largest, has 876 kernels with 30 944 multiply-accumulate
entries (its `Multivector×Multivector` product has 1024) and builds in about
10 s. Kernel and entry counts per space: `set_option trace.grassmann.codegen true`.
-/
