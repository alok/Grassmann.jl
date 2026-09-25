import Fatou.Kernel

/-!
# Colouring a Fatou raster

Julia shows a `FilledSet` through one of two colouring paths (port-notes/fatou.md §4.8):

* **PyPlot `imshow`** (`ext/PyPlotExt.jl:21-28`, every README/wiki image): the plotted matrix
  (`K.iter` if `iter`, else `K.mix`) is normalized linearly between its NaN-ignoring minimum
  and maximum (matplotlib `Normalize`), mapped through an `N`-entry lookup table
  (`idx = trunc(x·N)`, with `x = 1` going to `N - 1`), and NaN pixels get the transparent
  "bad" colour. `Raster.toRGBA8` does exactly this with a caller-supplied table, so LeanPlot
  (or anything else) can render without `Fatou` depending on it.
* **ColorSchemes** (`(C::ColorScheme)(K)`, `src/Fatou.jl:376-390`, the ImageInTerminal
  display): iteration counts index the stops directly with `⌈L·(iter+1)/(max iter + 1)⌉`,
  and `mix` values are clamped to `[0, 1]` (NaN → 0) and linearly interpolated between
  stops, so negative angles all get the first colour. `FilledSet.colorScheme` reproduces it
  in `Float64` RGB.
-/

namespace Fatou

open JuliaBase

/-- A scalar image: `rows × cols` values, row-major with row 0 at the top (matplotlib
`origin = "upper"`), NaN marking "bad" pixels, and the axis extent. -/
structure Raster (rows cols : Nat) where
  /-- pixel values -/
  data : FloatArray
  /-- `[xa, xb, ya, yb]`, the `extent` of `imshow` -/
  extent : Bounds
  /-- one value per pixel -/
  size_data : data.size = rows * cols

namespace FilledSet

variable {rows cols : Nat}

/-- The iteration counts as a float image. -/
def iterRaster (Z : FilledSet rows cols) : Raster rows cols :=
  ⟨floatArrayOfFn (rows * cols) fun i => Float.ofNat (Z.iterFlat i), Z.bounds, by simp⟩

/-- The colouring values `mix` as an image. -/
def mixRaster (Z : FilledSet rows cols) : Raster rows cols := ⟨Z.mix, Z.bounds, Z.size_mix⟩

/-- What Julia's `plot`/`imshow` shows (`ext/PyPlotExt.jl:24-26`): `iter` when the set was
defined with `iter = true`, else `mix`. -/
def raster (Z : FilledSet rows cols) : Raster rows cols :=
  if Z.define.spec.iter then Z.iterRaster else Z.mixRaster

end FilledSet

namespace Raster

variable {rows cols : Nat}

/-- The NaN-ignoring `(min, max)` of the pixel values (matplotlib autoscaling on the
invalid-masked image), or `none` if every pixel is NaN. -/
def extrema (r : Raster rows cols) : Option (Float × Float) :=
  r.data.foldl (init := none) fun acc v =>
    if v.isNaN then acc
    else match acc with
      | none => some (v, v)
      | some (lo, hi) => some (if v < lo then v else lo, if v > hi then v else hi)

/-- matplotlib's lookup-table index of a value (`Normalize` then `Colormap.__call__`):
`x = (v - vmin)/(vmax - vmin)` (`0` when `vmin == vmax`), `idx = trunc(x·N)` with `x·N = N`
mapped to `N - 1`, under-range to `0` and over-range to `N - 1`; `none` for NaN (the bad
colour). -/
def lutIndex (v vmin vmax : Float) (N : Nat) : Option Nat :=
  if v.isNaN then none
  else
    let x := if vmin == vmax then 0 else (v - vmin) / (vmax - vmin)
    let xa := x * Float.ofNat N
    let xa := if xa == Float.ofNat N then Float.ofNat (N - 1) else xa
    if xa < 0 then some 0
    else if xa ≥ Float.ofNat N then some (N - 1)
    else some (F64.toIntTrunc xa).toNat

/-- Render to 8-bit RGBA, four bytes per pixel, row-major from the top (matplotlib
`imshow(data, cmap)` without resampling). `cmap i` is entry `i` of an `lutSize`-entry lookup
table (matplotlib's default is 256); NaN pixels get `bad` (transparent black by default). -/
def toRGBA8 (r : Raster rows cols) (cmap : Nat → UInt8 × UInt8 × UInt8) (lutSize : Nat := 256)
    (bad : UInt8 × UInt8 × UInt8 × UInt8 := (0, 0, 0, 0)) : ByteArray :=
  let (vmin, vmax) := r.extrema.getD (0, 0)
  r.data.foldl (init := ByteArray.emptyWithCapacity (4 * (rows * cols))) fun acc v =>
    match lutIndex v vmin vmax lutSize with
    | none => ((acc.push bad.1).push bad.2.1 |>.push bad.2.2.1).push bad.2.2.2
    | some i =>
      let (cr, cg, cb) := cmap i
      ((acc.push cr).push cg |>.push cb).push 255

end Raster

/-- Render a computed set as Julia's `plot(K)` would colour it (`raster` + `toRGBA8`). -/
def FilledSet.toRGBA8 {rows cols : Nat} (Z : FilledSet rows cols) (cmap : Nat → UInt8 × UInt8 × UInt8)
    (lutSize : Nat := 256) (bad : UInt8 × UInt8 × UInt8 × UInt8 := (0, 0, 0, 0)) : ByteArray :=
  Z.raster.toRGBA8 cmap lutSize bad

/-! ## ColorSchemes (`src/Fatou.jl:374-390`) -/

/-- Fatou `nonan(x)` (`src/Fatou.jl:375`): `NaN ↦ 0`. -/
@[inline] def nonan (x : Float) : Float := if x.isNaN then 0 else x

/-- The stop `i` (0-based) of a colour scheme stored as `3·L` floats `r, g, b, …`. -/
@[inline] def schemeStop (colors : FloatArray) (i : Nat) : Float × Float × Float :=
  (colors[3 * i]!, colors[3 * i + 1]!, colors[3 * i + 2]!)

/-- ColorSchemes `get(C, x)` with the default range `(0, 1)` (ColorSchemes.jl:317-331):
clamp, locate the two stops around `x·(L-1) + 1`, and blend them as
`w·c₁ + (1-w)·c₂` with `w = 1 - t` (ColorVectorSpace arithmetic). -/
def schemeGet (colors : FloatArray) (x : Float) : Float × Float × Float :=
  let L := colors.size / 3
  let scaleby := Float.ofNat (L - 1) / C64.fOne
  let xc := if x > 1 then 1 else if x < 0 then 0 else x
  let beforeFp := (xc - 0) * scaleby + 1
  let before := (F64.toIntTrunc beforeFp.floor).toNat
  let after := min (before + 1) L
  let cpt := beforeFp - Float.ofNat before
  let w := 1 - cpt
  let (r1, g1, b1) := schemeStop colors (before - 1)
  let (r2, g2, b2) := schemeStop colors (after - 1)
  (w * r1 + (1 - w) * r2, w * g1 + (1 - w) * g2, w * b1 + (1 - w) * b2)

/-- The 1-based stop index Fatou's iteration colouring picks (`src/Fatou.jl:380-383`):
`ceil(Int, M·(iter+1))` with `M = L/(max iter + 1)` in `Float64`, clamped to `[1, L]` (Julia
would throw on the rare float overshoot past `L`). -/
def schemeIterIndex (L maxIter k : Nat) : Nat :=
  let M := Float.ofNat L / Float.ofNat (maxIter + 1)
  let i := (F64.toIntTrunc (M * Float.ofNat (k + 1)).ceil).toNat
  max 1 (min i L)

/-- Push the RGB triples `color i` for `i, i+1, …` (`k` of them). -/
def pushRGB (color : Nat → Float × Float × Float) : Nat → Nat → FloatArray → FloatArray
  | 0, _, acc => acc
  | k + 1, i, acc =>
    let (r, g, b) := color i
    pushRGB color k (i + 1) (((acc.push r).push g).push b)

/-- Julia `(C::ColorScheme)(K::FilledSet)` (`src/Fatou.jl:376-390`): `Float64` RGB triples per
pixel (row-major, `3·rows·cols` floats) for a scheme of `L` stops given as `3·L` floats. -/
def FilledSet.colorScheme {rows cols : Nat} (Z : FilledSet rows cols) (colors : FloatArray) :
    FloatArray :=
  let L := colors.size / 3
  let total := rows * cols
  let acc := FloatArray.emptyWithCapacity (3 * total)
  if Z.define.spec.iter then
    let mx := (List.range total).foldl (fun m i => max m (Z.iterFlat i)) 0
    pushRGB (fun i => schemeStop colors (schemeIterIndex L mx (Z.iterFlat i) - 1)) total 0 acc
  else
    pushRGB (fun i => schemeGet colors (nonan Z.mix[i]!)) total 0 acc

end Fatou
