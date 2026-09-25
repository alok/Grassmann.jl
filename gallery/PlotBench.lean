import Bench.Harness
import Gallery.Cartan.Fiber

/-!
# `lake exe plotbench`: the hot paths of GrassmannPlot against Cartan/Makie

The `plot` suite on the root package's harness (`Bench/Harness.lean`, `docs/perf/README.md`);
Julia twin `oracle/gallery/bench.jl` (Cartan 0.4.16, Makie's `streamplot_impl`). The fields are
the gallery's (`Gallery.Cartan.Fiber`), built once outside the timing.

* `speed_riemann`: Cartan `speed` of the 125 664-point Riemann-sphere curve (ns per point);
* `eval2_bivector`: `t(x, y)` of the 31×31 bivector grid field (bilinear interpolation) on a
  1000-point sweep (ns per evaluation);
* `stream2_bivector`: `streamplot` of that field (Makie's `streamplot_impl` of the interpolated
  field, 32×32 cells);
* `stream3_conformal`: the 3-D conformal field on its 31³ grid, `gridsize = (10,10,10)`;
* `figure_riemann`, `figure_bivector`: a whole figure, `lines(curve)` in an `Axis3` and
  `streamplot(field)`, rendered to PNG bytes in memory (Julia: CairoMakie `show(io,
  MIME"image/png"(), fig)` at `px_per_unit = 1`); the check is the pixel count.

```
lake exe plotbench [--json out.json] [--smoke] [--filter substr]…
julia --startup-file=no --project=oracle oracle/gallery/bench.jl [--json out.json]
uv run scripts/bench/compare.py --lean lean.json --julia julia.json --no-record
```
-/

open Bench GrassmannPlot Gallery.CartanFigs Gallery.CartanVersors

/-- `Σ` of a float array. -/
def sumData (a : FloatArray) : Float := a.foldl (· + ·) 0

/-- `-1.5`. -/
def c15 : Float := -1.5
/-- `-1.4`. -/
def c14 : Float := -1.4
/-- `2.9`. -/
def c29 : Float := 2.9

/-- The sweep of `eval2_bivector`: `(-1.5 + 3k/1000, -1.4 + 2.9k/1000)`, first components summed. -/
def sweep2 {b : Cartan.GridBundle 2 (Cartan.AffinePoint 2)} (t : Cartan.TensorField b (Grassmann.Chain DirectSum.ℝ2 1 Float))
    (n : Nat) : Float :=
  go (grid2Eval t) 0 0
where
  /-- The tail-recursive sweep. -/
  go (g : Grid2Eval) (k : Nat) (acc : Float) : Float :=
    if k < n then
      let kf := k.toUInt64.toFloat
      let v := g.eval (c15 + 3 * kf / 1000) (c14 + c29 * kf / 1000)
      go g (k + 1) (acc + v.x)
    else acc
  termination_by n - k

/-- The suite. -/
def plotSuite : Suite := ⟨"plot", do
  let curve := curveField fun t => pick3 (torus t) 1 2 3
  bench "speed_riemann" (ops := 125664) (param := "n=125664") fun s =>
    match speed (blackBox s curve) with | some sp => sumData sp.data | none => 0
  let bv := bivectorField 1
  bench "eval2_bivector" (ops := 1000) (param := "31x31, 1000 points") fun s => sweep2 (blackBox s bv) 1000
  bench "stream2_bivector" (param := "31x31, gridsize 32x32") fun s => (stream2 (blackBox s bv) {}).linePoints.size
  let cf := conformalField 0 1 2
  bench "stream3_conformal" (param := "31^3, gridsize 10^3") fun s =>
    (stream3 (blackBox s cf) { gridsize := some #[10, 10] }).1.linePoints.size
  -- whole figures: the Cartan method, the layout, the raster and the PNG encoding
  bench "figure_riemann" (param := "lines, 125664 points, 600x500 PNG") fun s =>
    if ((GrassmannPlot.lines (blackBox s curve)).figure (600, 500)).toPNG.size > 0 then 300000 else 0
  bench "figure_bivector" (param := "streamplot, 600x450 PNG") fun s =>
    if (GrassmannPlot.streamplot (blackBox s bv)).figure.toPNG.size > 0 then 270000 else 0⟩

/-- `lake exe plotbench [--json out.json] [--smoke] [--filter substr]…`. -/
def main (args : List String) : IO UInt32 := do
  let rec parse : List String → Config × Option String → Config × Option String
    | [], acc => acc
    | "--json" :: p :: r, (c, _) => parse r (c, some p)
    | "--smoke" :: r, (c, j) => parse r ({ c with smoke := true, sampleNs := 1000000 }, j)
    | "--filter" :: f :: r, (c, j) => parse r ({ c with filters := c.filters.push f }, j)
    | _ :: r, acc => parse r acc
  let (cfg, json) := parse args ({}, none)
  let rs ← runSuites cfg [plotSuite]
  if let some p := json then
    IO.FS.writeFile p (toJson cfg rs)
    IO.println s!"wrote {rs.size} results to {p}"
  return 0
