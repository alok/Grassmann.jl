import Fatou.Util
import Fatou.Complex
import Fatou.Grid
import Fatou.Define
import Fatou.Kernel
import Fatou.Orbit
import Fatou.Raster
import Fatou.Couple

/-!
# Fatou

Lean port of Michael Reed's [Fatou.jl](https://github.com/chakravala/Fatou.jl): escape-time
and Newton-basin fractals of holomorphic maps (Julia sets, Mandelbrot-type parameter sets,
generalized Newton fractals), real cobweb orbits, and the titles and colourings Julia's
plotting backends use. See `docs/port-notes/fatou.md` for the Julia semantics.

* `Fatou.Complex`: Julia-exact `ComplexF64` arithmetic (`C64`) for writing maps.
* `Fatou.Grid`: `Bounds`, `Rectangle` (sizes, bit-exact `x' .+ im*y` axes), `Plane` rasters.
* `Fatou.Define`: `juliafill`, `mandelbrot`, `newton` with Julia's per-front-end defaults;
  titles (`String(K)`, PyPlot LaTeX) and `basin` templates.
* `Fatou.Kernel`: `Define.orbit` (reference per-pixel semantics, `iter ≤ N` proved), the
  parallel tail-recursive raster kernel (output sizes proved), `fatou`, chaining,
  `FilledSet rows cols`, basin indices.
* `Fatou.Orbit`: `realOrb` cobweb data, limits, titles and legends.
* `Fatou.Raster`: `Raster.toRGBA8` (matplotlib colouring with any lookup table) and the
  ColorSchemes colouring of Julia's terminal display.
* `Fatou.Couple`: Grassmann `Couple` arithmetic (`B² = ±1, 0`) for hyperbolic and dual maps,
  the intended semantics of Fatou's broken Grassmann extension.

```lean
open Fatou in
#eval (fatou (mandelbrot (fun z c => z ^ 2 + c) { n := 64, N := 20, label := "z ^ 2 + c" })).title
-- "f : z ↦ z ^ 2 + c, limit"
```

Write real constants as `Float`s (`z ^ 3 - (1 : Float)`, `(2 : Float) * z`): mixed
real/complex operations then follow Julia's rules exactly (a real scales, it is not promoted to
`x + 0im`). Keep the `Define` visible to the compiler (inline in the `fatou` call, or an
`@[inline] def`/`abbrev`) so the kernel specializes on the map and runs on unboxed floats.
-/
