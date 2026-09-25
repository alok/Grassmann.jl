import Gallery.Common
import Gallery.ColormapData
import Gallery.Versor
import Gallery.Fatou
import Gallery.Grassmann.Figures
import Gallery.Grassmann.Graphs
import Gallery.Wilkinson
import Gallery.ImageDiff
import Gallery.Index

/-!
# GrassmannGallery

The plot gallery of the chakravala ecosystem (`docs/port-notes/plot-inventory.md`), rebuilt
with the Lean port and [LeanPlot](https://github.com/alok/LeanPlot). `lake exe gallery` renders
every figure to `gallery/out/`, compares the plotted data with the Julia dumps under
`oracle/gallery/data/`, and (with `--docs`) regenerates `docs/gallery/index.md`.

| module | figures |
|---|---|
| `Gallery.Fatou` | Fatou.jl README: cobweb orbit, filled Julia set, Mandelbrot set, Newton fractals |
| `Gallery.Grassmann.Figures` | Grassmann.jl README: plane versor streamplots, Riemann-sphere and conformal curves, 3D conformal streamplots |
| `Gallery.Grassmann.Graphs` | Grassmann paper: multivectors drawn as directed graphs |
| `Gallery.Wilkinson` | Wilkinson.jl: `plot(::PolynomialComparison)` error curves |
| `Gallery.Versor`, `Gallery.Grassmann.Fields` | Julia's `exp` of even elements, Riemann-sphere and conformal `↑`/`↓`, the README fields |
| `Gallery.Index` | the static page and the list of figures waiting for Cartan/Adapode |
-/

namespace Gallery

/-- Every figure, in page order. -/
def registry : List Entry :=
  FatouFigs.entries ++ GrassmannFigs.entries ++ Graphs.entries ++ WilkinsonFigs.entries

end Gallery
