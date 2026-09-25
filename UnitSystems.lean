import UnitSystems.Alg
import UnitSystems.System
import UnitSystems.Systems
import UnitSystems.Physics
import UnitSystems.Convert
import UnitSystems.Derived
import UnitSystems.Registry
import UnitSystems.Show
import UnitSystems.Dim
import UnitSystems.DimModel
import UnitSystems.DimProofs

/-!
# UnitSystems

Lean port of `chakravala/UnitSystems.jl` (v0.3.9), Reed's Unified System of
Quantities: 48 named unit systems, each fixed by eleven dimensional constants
and a coupling; 131 convertible quantities (`Conv`, with `q U S` the number of
`S`-units per `U`-unit); 28 physics constants, 6 couplings and 193 standardized
units as functions of the system; prefixes and module constants.

All formulas are written once, generic in the scalar (`UnitAlg`):

* `UnitSystem FieldConstants.Num` reproduces Julia's `Float64`/`Int64` values
  bit for bit (every golden in `oracle/golden/unitsystems` is bit-exact);
* Similitude instantiates the same code with exact constant groups, and
  MeasureSystems with measured groups;
* `UnitSystems.Dims` instantiates it with dimension exponents and proves the
  physical dimension of every conversion chain.

See `docs/port-notes/unitsystems.md`.
-/
