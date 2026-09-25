import Grassmann

/-!
# The spaces of the Grassmann README figures

Each `basis!` (Julia `@basis`) lives in its own namespace, as the README switches spaces
between examples: `ℝ²` (`basis"2"`), the hyperbolic plane `S"+-"`, the Riemann sphere
`S"∞+++"` and conformal space `S"∞∅+++"`.
-/

-- `basis"2"`: the Euclidean plane of the `plane-1 … plane-4` figures.
namespace Gallery.E2
open Grassmann
basis! S!"++"
end Gallery.E2

-- `@basis S"+-"`: the hyperbolic plane of `plane-5`, `plane-6`.
namespace Gallery.H2
open Grassmann
basis! S!"+-"
end Gallery.H2

-- `@basis S"∞+++"`: the Riemann sphere over `ℝ³` (torus, orbit, orb, wave figures).
namespace Gallery.Inf3
open Grassmann
basis! S!"∞+++"
end Gallery.Inf3

-- `@basis S"∞∅+++"`: conformal space over `ℝ³` (the helix figure).
namespace Gallery.CGA3
open Grassmann
basis! S!"∞∅+++"
end Gallery.CGA3
