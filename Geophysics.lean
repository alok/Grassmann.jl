import Geophysics.JuliaMath
import Geophysics.Units
import Geophysics.Planet
import Geophysics.Gas
import Geophysics.Layer
import Geophysics.Atmosphere
import Geophysics.Data
import Geophysics.Show
import Geophysics.Typed

/-!
# Geophysics

Lean port of `chakravala/Geophysics.jl` (v0.3.8, `381a792`): planetary science
data for atmospheric geophysical models, on top of the UnitSystems and
Similitude ports. See `docs/port-notes/applied-misc.md` §1.1–§6.5.

| module | Julia | contents |
|---|---|---|
| `Planet` | `Geophysics.jl:66-425` | reference ellipsoids, latitudes, radii, `J₂`, Hirvonen/Somigliana normal gravity, gravity with altitude |
| `Gas` | `chemistry.jl` | ideal gases (Sutherland transport, Einstein heat capacity), mixtures, fluid states |
| `Atmosphere`, `Layer` | `Geophysics.jl:427-884` | layered atmospheres, hydrostatic integration, the 21 altitude functions and their ratios |
| `Data` | `planets.jl` | 13 bodies, 11 gases and 5 mixtures, 14 tables, 14 standard weathers |
| `Show` | `show`/`display` | Julia's printed forms |
| `Typed` | (Similitude branch) | the same API on `Similitude.Quantity U d Float`, dimensions derived from the formulas |
| `Units`, `JuliaMath`, `Lit` | UnitSystems, `Base.Math` | unit factors, Julia's own `sin/…/^`, bit-constant literals |

Every value agrees with Julia bit for bit (679 602 oracle checks in
`Tests/Geophysics`), including the Julia-specific quirks the port notes list;
Julia defects are fixed or replaced by their evident intent and documented where
they occur. Typical use:

    open Geophysics in
    #eval (Standard.temperature 1000.0, Standard.pressure 1000.0 .English)
    -- a column for repeated evaluation in one unit system:
    open Geophysics in
    #eval let C := Earth1976.column .Metric; (C.eval .density 5000.0, C.ratio .pressure 5000.0)
-/
