import Gallery.Common
import Gallery.ColormapData
import Gallery.Versor
import Gallery.Fatou
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
| `Gallery.Versor` | Julia's `exp` of even elements, Riemann-sphere and conformal `↑`/`↓` |
| `Gallery.Index` | the static page and the list of figures waiting for Cartan/Adapode |
-/

namespace Gallery

/-- Every figure, in page order. -/
def registry : List Entry := FatouFigs.entries

end Gallery
