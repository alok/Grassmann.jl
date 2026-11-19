module

public import DirectSum.Bits
public import DirectSum.Space
public import DirectSum.Show
public import DirectSum.SpaceOps
public import DirectSum.Parse
public import DirectSum.Common
public import DirectSum.Parity
public import DirectSum.BladeAlgebra
public import DirectSum.Compat
public import DirectSum.Blade
public import DirectSum.Names
public import DirectSum.SetOps
public import DirectSum.Euler
public import DirectSum.Derived
public import DirectSum.Ops

@[expose] public section

/-!
# DirectSum.Core: the runtime space and basis-blade layer (without elaborator `DirectSum.Basis`)

Everything in `DirectSum` except the compile-time `Λ(V).name` elaborator (`DirectSum.Basis`,
which imports `Lean.Elab`/`Lean.Meta`) and the standalone proof modules (`DirectSum.Proofs`).
Runtime packages (`Grassmann.Types`, `Grassmann.Kernel`, `Grassmann.Projective`, etc.) import
`DirectSum.Core`; users importing the umbrella `DirectSum` still receive `DirectSum.Basis` and
`DirectSum.Proofs` transparently.
-/
