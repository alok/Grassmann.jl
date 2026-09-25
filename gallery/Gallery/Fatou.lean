import Fatou
import Gallery.Common
import Gallery.ColormapData

/-!
# Fatou.jl README figures (`README.md:58-116`)

| name | Julia |
|---|---|
| `fatou-orbit` | `juliafill(:(z^2-0.67),∂=[-1.25,1.5],x0=1.25,orbit=17,depth=3,n=147) \|> orbit` |
| `fatou-filled-julia` | `juliafill(:(z^2+$c),∂=[-1.5,1.5,-1,1],N=80,n=1501,cmap="gnuplot",iter=true)`, `plot(fatou(nf), bare=true)` |
| `fatou-mandelbrot` | `mandelbrot(:(z^2+c),n=800,N=20,∂=[-1.91,0.51,-1.21,1.21],cmap="gist_earth") \|> fatou \|> plot` |
| `fatou-newton` | `newton(:(z^3-1),n=800,ϵ=0.1,N=25,iter=true,cmap="jet") \|> fatou \|> plot` |
| `fatou-generalized-newton` | `newton(:(sin(z)-1),m=1-1im,∂=[-2π/3,-π/3,-π/6,π/6],n=500,N=33,iter=true,ϵ=0.05,cmap="cubehelix")` |

The rasters come from `Fatou.fatou` at full README resolution; `Fatou.Raster.toRGBA8` colours
them the way Julia's `plot` (PyPlot `imshow`) does, with a 256-entry lookup table sampled
from the LeanPlot (Makie) colormap of the same name, and the image is placed on an `Axis2`
over the raster's extent (`DataAspect`). Titles, y-label and colorbar follow
`ext/PyPlotExt.jl:19-40` (plain-text titles, `String(K)`); the orbit plot follows
`ext/PyPlotExt.jl:42-73`.

The data checks compare the iteration counts (histogram and FNV-1a hash, exact for the
rational maps) and the colouring values with `fatou(K)` dumped by
`oracle/gallery/fatou-*.jl`.
-/

namespace Gallery.FatouFigs

open _root_.Fatou LeanPlot

/-! ## The README sets -/

/-- `c = -0.06 + 0.67im` of the filled Julia set. -/
def c₀ : C64 := ⟨-0.06, 0.67⟩

/-- README filled Julia set (`README.md:68-74`). -/
@[inline] def filledJulia : Define :=
  juliafill (fun z _ => z ^ 2 + c₀)
    { bounds := ⟨-1.5, 1.5, -1, 1⟩, N := 80, n := 1501, cmap := "gnuplot", iter := true,
      label := "z ^ 2 + (-0.06 + 0.67im)" }

/-- README Mandelbrot set (`README.md:78-82`). -/
@[inline] def mandel : Define :=
  mandelbrot (fun z c => z ^ 2 + c)
    { n := 800, N := 20, bounds := ⟨-1.91, 0.51, -1.21, 1.21⟩, cmap := "gist_earth", label := "z ^ 2 + c" }

/-- REDUCE's Newton map of `z^3 - 1` with `m = 1`: `(2 * z ^ 3 + 1) / (3 * z ^ 2)`. -/
@[inline] def newtonCubic (z _c : C64) : C64 := ((2 : Float) * z ^ 3 + (1 : Float)) / ((3 : Float) * z ^ 2)

/-- README Newton fractal of `z^3 - 1` (`README.md:98-104`). -/
@[inline] def newtonSet : Define :=
  newton (fun z _ => z ^ 3 - (1 : Float)) (fun z _ => (3 : Float) * z ^ 2)
    { n := 800, ϵ := some 0.1, N := 25, iter := true, cmap := "jet", label := "z ^ 3 - 1" }
    (map := some newtonCubic)

/-- REDUCE's generalized Newton map of `sin(z) - 1` with `m = 1 - 1im`. -/
@[inline] def newtonSin (z _c : C64) : C64 :=
  ((C64.sin z - (1 : Float)) * (⟨-1, 1⟩ : C64) + C64.cos z * z) / C64.cos z

/-- README generalized Newton fractal (`README.md:108-116`). -/
@[inline] def genNewton : Define :=
  newton (fun z _ => C64.sin z - (1 : Float)) (fun z _ => C64.cos z)
    { m := some (.complexInt 1 (-1)), bounds := ⟨-2 * pi / 3, -pi / 3, -pi / 6, pi / 6⟩, n := 500, N := 33,
      iter := true, ϵ := some 0.05, cmap := "cubehelix", label := "sin(z) - 1" }
    (map := some newtonSin)

/-! ## Four figures of the Fatou.jl wiki (`Explore-Fatou-sets-&-fractals.md`) -/

/-- Wiki (1): `newton(:(z^3-1),ϵ=0.001,n=800,cmap="brg")`, coloured by the angle of the root
reached. -/
@[inline] def wikiRoots : Define :=
  newton (fun z _ => z ^ 3 - (1 : Float)) (fun z _ => (3 : Float) * z ^ 2)
    { n := 800, ϵ := some 0.001, cmap := "brg", label := "z ^ 3 - 1" } (map := some newtonCubic)

/-- Wiki (2): `newton(:(z^3-1),m=2,n=800,N=37,ϵ=0.27,iter=true,cmap="ocean")`; REDUCE's map
`(z^3 + 2)/(3z^2)`. -/
@[inline] def wikiSnowflake : Define :=
  newton (fun z _ => z ^ 3 - (1 : Float)) (fun z _ => (3 : Float) * z ^ 2)
    { m := some 2, n := 800, N := 37, ϵ := some 0.27, iter := true, cmap := "ocean", label := "z ^ 3 - 1" }
    (map := some fun z _ => (z ^ 3 + (2 : Float)) / ((3 : Float) * z ^ 2))

/-- Wiki (3): `newton(:(z^3-1),m=-0.5,n=800,N=10,cmap="hsv")`; REDUCE's map
`(7z^3 - 1)/(6z^2)`. -/
@[inline] def wikiHsv : Define :=
  newton (fun z _ => z ^ 3 - (1 : Float)) (fun z _ => (3 : Float) * z ^ 2)
    { m := some (-0.5), n := 800, N := 10, cmap := "hsv", label := "z ^ 3 - 1" }
    (map := some fun z _ => ((7 : Float) * z ^ 3 - (1 : Float)) / ((6 : Float) * z ^ 2))

/-- Wiki orbit example (3): the basilica, `juliafill("z^2-1",∂=[-2,2],iter=true,n=800)`. -/
@[inline] def wikiBasilica : Define :=
  juliafill (fun z _ => z ^ 2 - (1 : Float)) { bounds := .interval (-2) 2, iter := true, n := 800, label := "z ^ 2 - 1" }

/-! ## Rendering -/

/-- A LeanPlot colormap by name, including the gallery's extra tables (`gist_earth`). -/
def colormap (name : String) : Colormap :=
  match Colormap.named? name with
  | some c => c
  | none => (Gallery.ColormapData.named? name).getD Colormap.viridis

/-- matplotlib's `N`-entry lookup table of a colormap (`Colormap._init`: the map sampled at
`i/(N-1)`), as 8-bit RGB. -/
def lut (cm : Colormap) (N : Nat := 256) : Array (UInt8 × UInt8 × UInt8) :=
  (Array.range N).map fun i =>
    let c := cm.interpolatedGetIndex (i.toUInt64.toFloat / (N - 1).toUInt64.toFloat)
    (RGBA.to8 c.r, RGBA.to8 c.g, RGBA.to8 c.b)

/-- The raster Julia's `plot(K)` shows (`iter` or `mix`), coloured through `cmap` with
`Fatou.Raster.toRGBA8`, on an `Axis2` over its extent. Returns the axis and the colour range. -/
def rasterAxis {rows cols : Nat} (Z : FilledSet rows cols) (cm : Colormap) (title ylabel : String) :
    Axis2 × Float × Float :=
  let r := Z.raster
  let table := lut cm
  let rgba := r.toRGBA8 (fun i => table[i]!) 256
  let (vmin, vmax) := r.extrema.getD (0, 1)
  let b := r.extent
  let ax := Axis2.new (title := title) (ylabel := ylabel) (aspect := .data)
  -- `toRGBA8` rows are top-first, the layout of the `image` mark
  let ax := ax.add (.image b.xa b.xb b.ya b.yb cols rows rgba .nearest)
  (ax, vmin, vmax)

/-- A README fractal figure: the raster axis plus, unless `bare`, a colorbar. -/
def rasterFigure {rows cols : Nat} (Z : FilledSet rows cols) (size : Nat × Nat) (bare : Bool)
    (title ylabel : String) : Figure :=
  let cm := colormap Z.define.spec.cmap
  let (ax, lo, hi) := rasterAxis Z cm title ylabel
  let f := Figure.new size |>.axis 1 1 ax
  if bare then f else f.colorbarExplicit 1 2 cm lo hi

/-! ## Data checks -/

/-- Iteration-count histogram, FNV hash and colouring statistics against the Julia dump. -/
def rasterChecks {rows cols : Nat} (Z : FilledSet rows cols) (j : Lean.Json) (exact : Bool) :
    Array Check := Id.run do
  let hist := Z.iterHistogram
  let jh := jnats (jget j "hist")
  let fnv := hex16 (fnv1aU16 Z.iterFlat (rows * cols))
  let mut cs : Array Check := #[eqCheck "raster size (rows × cols)" s!"{rows}×{cols}"
    s!"{jnat (jget j "rows")}×{jnat (jget j "cols")}"]
  if exact then
    cs := cs.push { label := "iteration histogram", ok := hist == jh
                    detail := if hist == jh then s!"equal ({hist.size} bins, {rows * cols} pixels)" else "differs" }
    cs := cs.push (eqCheck "FNV-1a of the iteration counts" fnv (jstr (jget j "fnv")))
  else
    let tv := (hist.zip jh).foldl (fun a (x, y) => a + (if x ≥ y then x - y else y - x)) 0
    let total := rows * cols
    cs := cs.push { label := "iteration histogram (libm tier)", ok := hist.size == jh.size && tv * 1000 ≤ 2 * total
                    detail := s!"total variation {tv} of {2 * total} (tol 0.1%)" }
  let mix := Z.mix
  let nan := mix.foldl (fun k v => if v.isNaN then k + 1 else k) 0
  cs := cs.push (eqCheck "mix NaN count" nan (jnat (jget j "mix_nan")))
  let s := sumFinite mix
  let js := jfloat (jget j "mix_sum")
  -- relative to Σ|mix| (the angle colouring sums to about zero)
  let scale := jfloat (jget j "mix_abs_sum")
  let rel := (s - js).abs / (if scale > 1 then scale else 1)
  cs := cs.push { label := "Σ mix", ok := rel ≤ (if exact then 1e-12 else 1e-4)
                  detail := s!"|Δ| / Σ|mix| = {sci rel}" }
  return cs

/-- Build a README raster figure and its checks. -/
def rasterEntry {rows cols : Nat} (Z : FilledSet rows cols) (size : Nat × Nat) (bare exact : Bool)
    (ylabel : String) (j? : Option Lean.Json) : Outcome :=
  let title := if bare then "" else Z.title
  { fig := rasterFigure Z size bare title ylabel
    checks := match j? with | some j => rasterChecks Z j exact | none => #[] }

/-! ## The cobweb orbit -/

/-- README orbit (`README.md:58-64`). -/
@[inline] def orbitSet : Define :=
  juliafill (fun z _ => z ^ 2 - (0.67 : Float))
    { bounds := .interval (-1.25) 1.5, x0 := some 1.25, orbit := 17, depth := 3, n := 147, label := "z ^ 2 - 0.67" }

/-- The orbit figure (`ext/PyPlotExt.jl:42-73` with Makie's palette): `y = x` dashed black, `ϕ`
and its compositions, the red cobweb, and the orbit as a gray dotted time series with `×`
markers; limits `xlim = (a, b)`, `ylim` from `RealOrbit.ylim`, a legend at the top centre. -/
def orbitFigure (K : Define) (o : RealOrbit) (size : Nat × Nat) : Figure :=
  let x := o.x
  let (ylo, yhi) := o.ylim
  let (xlo, xhi) := o.xlim
  let title := s!"x ↦ {K.label}, IC: x₀ = {JuliaBase.F64.showString (K.spec.x0.getD 0)}, n∈0:{K.spec.orbit}"
  let ax := Axis2.new (title := title)
    |>.lines x o.comps[0]! (color := some (.solid RGBA.black)) (linestyle := .dash) (label := some "y=x")
    |>.lines x o.comps[1]! (label := some "ϕ(x)")
    |>.lines o.cobwebX o.cobwebY (color := some (ColorSpec.ofName "red")) (label := some "(xₙ,ϕ(xₙ))")
  let ax := (List.range (o.comps.size - 2)).foldl (fun ax k =>
    ax.lines x o.comps[k + 2]! (linewidth := 1) (label := some s!"ϕ^{k + 2}(x)")) ax
  let gray := ColorSpec.ofName "gray"
  let ax := ax.lines o.orbitXs o.orbit (color := some gray) (linestyle := .dot) (linewidth := 1)
      (label := some s!"ϕ(x₀:{K.spec.orbit})")
    |>.scatter o.orbitXs o.orbit (color := some gray) (marker := .xcross)
    |>.limits xlo xhi ylo yhi
    |>.axislegend (position := .ct)
  Figure.new size |>.axis 1 1 ax

/-- The orbit data checks: every series against Julia's `real_orb`. -/
def orbitChecks (o : RealOrbit) (j : Lean.Json) : Array Check :=
  let cols := jarr (jget j "N_cols")
  let comps := (List.range o.comps.size).map fun k =>
    closeCheck s!"ϕ^{k}(x) samples" o.comps[k]! (jfloats (cols[k]?.getD .null)) 0
  #[closeCheck "orbit x₀…x₁₇ (N2)" o.orbit (jfloats (jget j "N2")) 0,
    closeCheck "cobweb x" o.cobwebX (jfloats (jget j "cobweb_x")) 0,
    closeCheck "cobweb y" o.cobwebY (jfloats (jget j "cobweb_y")) 0,
    closeCheck "ylim" ⟨#[o.ylim.1, o.ylim.2]⟩ (jfloats (jget j "ylim")) 0] ++ comps.toArray

/-! ## Entries -/

/-- The URL of a Fatou.jl README image. -/
def fatouImg (stem : String) : String :=
  s!"https://raw.githubusercontent.com/chakravala/Fatou.jl/master/img/{stem}.png"

/-- The five Fatou README figures. -/
def entries : List Entry := [
  { name := "fatou-orbit", group := "Fatou", upstream := fatouImg "orbit"
    title := "Cobweb orbit of x ↦ x² − 0.67"
    source := "`juliafill(:(z^2-0.67),∂=[-1.25,1.5],x0=1.25,orbit=17,depth=3,n=147) |> orbit` (Fatou.jl `README.md:58-64`)"
    build := fun j? => do
      let o := orbitSet.realOrbit
      return { fig := orbitFigure orbitSet o (640, 480)
               checks := match j? with | some j => orbitChecks o j | none => #[] } },
  { name := "fatou-filled-julia", group := "Fatou", upstream := fatouImg "filled-julia"
    title := "Filled Julia set of z² − 0.06 + 0.67i (iteration counts, gnuplot)"
    source := "`plot(fatou(juliafill(:(z^2+$c),∂=[-1.5,1.5,-1,1],N=80,n=1501,cmap=\"gnuplot\",iter=true)), bare=true)` (`README.md:66-74`)"
    build := fun j? => pure (rasterEntry (fatou filledJulia) (640, 440) true true "" j?) },
  { name := "fatou-mandelbrot", group := "Fatou", upstream := fatouImg "mandelbrot"
    title := "Mandelbrot set, limit colouring exp(−|z₂₀|) (gist_earth)"
    source := "`mandelbrot(:(z^2+c),n=800,N=20,∂=[-1.91,0.51,-1.21,1.21],cmap=\"gist_earth\") |> fatou |> plot` (`README.md:76-82`)"
    build := fun j? => pure (rasterEntry (fatou mandel) (600, 500) false true "" j?) },
  { name := "fatou-newton", group := "Fatou", upstream := fatouImg "newton"
    title := "Newton fractal of z³ − 1 (iteration counts, jet)"
    source := "`newton(:(z^3-1),n=800,ϵ=0.1,N=25,iter=true,cmap=\"jet\") |> fatou |> plot` (`README.md:96-104`)"
    build := fun j? => pure (rasterEntry (fatou newtonSet) (620, 500) false true
      (newtonSet.yLabel.getD "") j?) },
  { name := "fatou-generalized-newton", group := "Fatou", upstream := fatouImg "generalized-newton"
    title := "Generalized Newton fractal of sin z − 1, m = 1 − i (cubehelix)"
    source := "`newton(:(sin(z)-1),m=1-1im,∂=[-2π/3,-π/3,-π/6,π/6],n=500,N=33,iter=true,ϵ=0.05,cmap=\"cubehelix\") |> fatou |> plot` (`README.md:106-116`)"
    build := fun j? => pure (rasterEntry (fatou genNewton) (620, 500) false false
      (genNewton.yLabel.getD "") j?) }
]

/-- The URL of a Fatou.jl wiki image. -/
def wikiImg (stem : String) : String :=
  s!"https://raw.githubusercontent.com/wiki/chakravala/Fatou.jl/img/{stem}.png"

/-- Four wiki figures (`Explore-Fatou-sets-&-fractals.md`; strings there are `Expr`s here,
since `parse(::String)` is gone from Julia). -/
def wikiEntries : List Entry := [
  { name := "fatou-wiki-newton-roots", group := "Fatou wiki", upstream := wikiImg "nf1-roots"
    title := "Newton basins of z³ − 1 by the root reached (brg)"
    source := "`newton(:(z^3-1),ϵ=0.001,n=800,cmap=\"brg\") |> fatou |> plot` (wiki example (1))"
    build := fun j? => pure (rasterEntry (fatou wikiRoots) (620, 500) false true (wikiRoots.yLabel.getD "") j?) },
  { name := "fatou-wiki-newton-snowflake", group := "Fatou wiki", upstream := wikiImg "nf2-iter"
    title := "Newton fractal of z³ − 1 with multiplicity m = 2 (ocean)"
    source := "`newton(:(z^3-1),m=2,n=800,N=37,ϵ=0.27,iter=true,cmap=\"ocean\") |> fatou |> plot` (wiki example (2))"
    build := fun j? => pure (rasterEntry (fatou wikiSnowflake) (620, 500) false true (wikiSnowflake.yLabel.getD "") j?) },
  { name := "fatou-wiki-newton-hsv", group := "Fatou wiki", upstream := wikiImg "nf3-limit"
    title := "Generalized Newton fractal of z³ − 1 with m = −0.5, limit angle (hsv)"
    source := "`newton(:(z^3-1),m=-0.5,n=800,N=10,cmap=\"hsv\") |> fatou |> plot` (wiki example (3))"
    build := fun j? => pure (rasterEntry (fatou wikiHsv) (620, 500) false true (wikiHsv.yLabel.getD "") j?) },
  { name := "fatou-wiki-basilica", group := "Fatou wiki", upstream := wikiImg "o3-iter"
    title := "The basilica, filled Julia set of z² − 1 (iteration counts, default colormap)"
    source := "`juliafill(:(z^2-1),∂=[-2,2],iter=true,n=800) |> fatou |> plot` (wiki orbit example (3))"
    build := fun j? => pure (rasterEntry (fatou wikiBasilica) (620, 500) false true "" j?) }
]

end Gallery.FatouFigs
