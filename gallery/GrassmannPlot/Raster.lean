import GrassmannPlot.Animate

/-!
# `raster`: incidence rasters of projective elements (ColorTypesExt)

Cartan's `raster(ga, R = _rectangle(3))` (`ext/ColorTypesExt.jl:18-35`) rasterizes elements of
the projective plane: for every pixel of a 100×100 grid on `[-3, 3]²` (`range(-3,3,100)` in both
directions; `_rectangle` ignores its argument), with `P = Chain(1, x, y)`, it counts the elements
`g` with `norm(P∧g) < δ`, `δ = √(δx² + δy²)/2` the half pixel diagonal, and stores the count as a
`GrayA(c, c)` pixel (white ink, opacity `c`) at row `1+ny-y`, column `x`.

`raster` returns the counts in Makie's `z[i, j]` order (`i ↔ x`, `j ↔ y` from the bottom);
`drawRaster` shows them as an image of the square, white ink with opacity `min(c, 1)`.
-/

namespace GrassmannPlot

open LeanPlot Grassmann DirectSum StaticVectors

/-- The pixel axis of `_rectangle`: Julia `range(-3, 3, 100)`. -/
def rasterAxis : Cartan.Axis := .range (-3) 3 100

/-- Julia `raster(ga)` (`ColorTypesExt.jl:20-34`): the incidence counts of the 100×100 pixel
centres with the elements `ga` (grade `G` elements of a 3-dimensional algebra), in `z[i, j]`
order. -/
def raster {V : TensorBundle} [Kernels V] {G : Nat} (ga : Array (Chain V G Float)) : FloatArray :=
  let ax := rasterAxis
  let n := ax.length
  let s := (ax.step?).getD 0
  let δ := Float.sqrt (s * s + s * s) / 2
  Cartan.buildFlat (F := Float) (n * n) fun k =>
    let x := ax.get (k % n)
    let y := ax.get (k / n)
    let P : Chain V 1 Float := Chain.ofFn fun i => if i.1 = 0 then 1 else if i.1 = 1 then x else if i.1 = 2 then y else 0
    ga.foldl (fun c g => if Grassmann.norm (P ∧ g : Chain V (1 + G) Float) < δ then c + 1 else c) 0

/-- Draw raster counts (in `z[i, j]` order) as an image of `[-3, 3]²`: white ink with opacity
`min(c, 1)` (Makie's `GrayA(c, c)`), nearest-neighbour. -/
def drawRaster (c : Canvas) (counts : FloatArray) (n : Nat := 100) : Canvas :=
  let rgba := counts.foldl (init := ByteArray.emptyWithCapacity (4 * counts.size)) fun acc v =>
    RGBA.pushRGBA8 acc ⟨1, 1, 1, Num.clamp v 0 1⟩
  c.map2 fun ax => ax.image (-3) 3 (-3) 3 n n rgba (interpolate := false)

end GrassmannPlot
