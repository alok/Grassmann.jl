import DirectSum.Bits
import DirectSum.Space
import DirectSum.Show
import DirectSum.SpaceOps
import DirectSum.Parse
import DirectSum.Common
import DirectSum.Parity
import DirectSum.BladeAlgebra
import DirectSum.Compat
import DirectSum.Blade
import DirectSum.Names
import DirectSum.SetOps
import DirectSum.Euler
import DirectSum.Derived
import DirectSum.Ops

/-!
# DirectSum.Core: the runtime space and basis-blade layer (without elaborator `DirectSum.Basis`)

Everything in `DirectSum` except the compile-time `Λ(V).name` elaborator (`DirectSum.Basis`,
which imports `Lean.Elab`/`Lean.Meta`) and the standalone proof modules (`DirectSum.Proofs`).
Runtime packages (`Grassmann.Types`, `Grassmann.Kernel`, `Grassmann.Projective`, etc.) import
`DirectSum.Core`; users importing the umbrella `DirectSum` still receive `DirectSum.Basis` and
`DirectSum.Proofs` transparently.
-/
