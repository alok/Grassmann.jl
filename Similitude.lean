import Similitude.Constants
import Similitude.UnitNames
import Similitude.Scalar
import Similitude.Hom
import Similitude.Registry
import Similitude.Ratio
import Similitude.Quantity
import Similitude.Physics
import Similitude.Derived
import Similitude.Quotient
import Similitude.LogQuantity

/-!
# Similitude

Lean port of `chakravala/Similitude.jl` (v0.3.3): dimensions and quantities for
UnitSystems, with exact constants.

* `Similitude.Consts` (`Constants`): the free abelian group on 44 physical and
  mathematical constants; `Scalar` is Similitude's number tower (exact groups,
  plain `Int64`/`Float64`, `Rational`) with Julia's mixed arithmetic, and
  `UnitAlg Scalar` evaluates every UnitSystems formula exactly.
* `Sys.hom` (`Hom`): each unit system as a projection of the USQ dimension group
  (kernel-checked), and `usqMap`, Similitude's `UnitSystem(d)`.
* `Registry`: unit names (`J`, `lbf⋅ft`, `Mx`, …) and base-unit spelling.
* `ratio`, `ConvertUnit` (`Ratio`): exact conversion factors.
* `Quantity U d α` (`Quantity`): the unit system and the USQ dimension are in
  the type, erased at runtime; `+` of different dimensions is a type error and
  products compute their dimension during elaboration.
* `Physics`: the 39 typed physical constants, each with a `decide` proof that
  its type is the dimension of UnitSystems' formula; `Units` (`Derived`): ~190
  derived units; `quotient` (`Quotient`): `U/~`.

See `docs/port-notes/similitude-fieldalgebra-measure.md`.
-/
