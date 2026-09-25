import Gallery.Common

/-!
# `docs/gallery/index.md`

The static gallery page: one table row per figure with the Lean render
(`docs/gallery/lean/<name>.png`) next to the Julia/CairoMakie original
(`docs/gallery/julia/<name>.png`), the Julia call, and the numeric agreement of the plotted
data; then the figures that wait for the Cartan/Adapode ports.
-/

namespace Gallery.Index

/-- A figure of the ecosystem that the gallery cannot reproduce yet, with what it waits for. -/
structure Pending where
  /-- inventory id (`docs/port-notes/plot-inventory.md` §6) -/
  id : String
  /-- the figure -/
  what : String
  /-- the blocking port -/
  needs : String

/-- The figures of `docs/port-notes/plot-inventory.md` §6 that need Cartan, Adapode or other
unported packages. -/
def pending : List Pending := [
  ⟨"C1", "plane curve with unit frames, arclength/speed/curvature (Cartan `fiber.md:442-451`)", "Cartan (TensorField, frames, `scaledarrows`)"⟩,
  ⟨"C2", "plane curves from curvature, `planecurve` (`fiber.md:452-457`)", "Cartan (`planecurve`, cumulative integrals)"⟩,
  ⟨"C3", "Lorenz vector-field 3D streamplot (`fiber.md:460-468`)", "Cartan (TensorField over ProductSpace)"⟩,
  ⟨"C4 / A1", "Lorenz, Rössler, dynamo attractors (`fiber.md:470-474`, Adapode `examples/chaos.jl`)", "Adapode (`odesolve`, RK4/ABM4 on Chains)"⟩,
  ⟨"C5", "Riemann-sphere curves as TensorFields (`fiber.md:477-493`)", "Cartan (same curves as `grassmann-torus` etc. over `TensorField`)"⟩,
  ⟨"C6", "bivector streamplots over 31×31 grid fields (`fiber.md:495-509`)", "Cartan (grid interpolation of `tensorfield`)"⟩,
  ⟨"C7", "conformal 3D streamplots over grids (`fiber.md:511-523`)", "Cartan"⟩,
  ⟨"C8", "Lie bracket streamplots on the torus (`fiber.md:552-563`)", "Cartan (`gradient`, `Lie`)"⟩,
  ⟨"C9", "circle and sphere wireframe (`fiber.md:602-613`)", "Cartan (`SphereParameter`, `surfacearea`)"⟩,
  ⟨"C10", "link curves and linkmap meshes (`fiber.md:649-656`)", "Cartan (`linkmap`, `linknumber`)"⟩,
  ⟨"C11 / C12", "torus and wiggle coloured by curvature (`fiber.md:669-695`)", "Cartan (shape operator, `meancurvature`, `gaussintrinsic`)"⟩,
  ⟨"C13 / C14 / C15", "torus, Klein-bottle and half-plane geodesics (`fiber.md:709-763`)", "Cartan + Adapode (`geodesic`, `geosolve`)"⟩,
  ⟨"C16", "Hopf fibration wireframes (`fiber.md:765-775`)", "Cartan (`HopfParameter`, `alteration!`)"⟩,
  ⟨"C17", "tangent-space streamplots on sphere and torus (`fiber.md:778-797`)", "Cartan (streamplot transform hook over TensorFields)"⟩,
  ⟨"C18", "da Rios vortex filament (`fiber.md:800-811`)", "Adapode (`odesolve` on curve fields; upstream bug P9)"⟩,
  ⟨"C19", "Bishop frame (`fiber.md:813-820`)", "Cartan (`bishopunitframe`)"⟩,
  ⟨"C20 / A11", "disk eigenmodes (`fiber.md:823-834`)", "Adapode (FEM assembly, generalized eigensolver; MATLAB mesh upstream)"⟩,
  ⟨"C21 / A12", "heat flow around a NACA airfoil (`fiber.md:874-895`)", "Adapode + FlowGeometry + a 2D mesher"⟩,
  ⟨"C22 / A13", "Poisson on a sphere-in-cube tetrahedral mesh (`fiber.md:898-910`)", "Adapode + TetGen-like mesher"⟩,
  ⟨"C23", "Stokes theorem on a paraboloid (`fiber.md:932-962`)", "Cartan (`graph`, `unitnormal`, `curl`)"⟩,
  ⟨"M-*", "the 32 Makie-gallery ports of Cartan `docs/src/plot.md`", "Cartan (TensorField plot recipes)"⟩,
  ⟨"A2–A9", "leapfrog, wave, heat and rest-wave PDE surfaces and isosurfaces (Adapode `README.md:151-231`)", "Adapode (spectral solvers, FFT)"⟩,
  ⟨"A10", "L2 projector (Adapode `README.md:235-240`)", "Adapode (1D FEM)"⟩,
  ⟨"W1–W4", "NACA airfoils, double arc, wing surface, Rakich C-mesh (FlowGeometry)", "FlowGeometry port"⟩,
  ⟨"D1", "Tamari associahedron coloured by grove sums (Dendriform README)", "external gist, not in the repositories"⟩,
  ⟨"G10", "`vandermonde` terminal plot (`ext/UnicodePlotsExt.jl`)", "UnicodePlots-style terminal backend (API only, no documented call)"⟩
]

/-- Escape `|` for a Markdown table cell. -/
def cell (s : String) : String := s.replace "|" "\\|"

/-- The agreement column of a figure. -/
def agreement (cs : Array Check) : String :=
  if cs.isEmpty then "no data dump" else
  let bad := cs.filter (!·.ok)
  let head := if bad.isEmpty then s!"✅ {cs.size}/{cs.size} checks" else s!"❌ {cs.size - bad.size}/{cs.size} checks"
  head ++ "<br>" ++ "<br>".intercalate (cs.toList.map fun c =>
    s!"{if c.ok then "" else "**FAIL** "}{cell c.label}: {cell c.detail}")

/-- Render the page. `extra` is the per-figure note of `docs/gallery/notes/<name>.md` if any. -/
def render (root : System.FilePath) (rows : Array (Entry × Array Check)) : IO String := do
  let mut s := "# Gallery: the chakravala figures in Lean\n\n"
  s := s ++ "Every figure of the Julia ecosystem that the Lean port can compute today, rendered with " ++
    "[LeanPlot](https://github.com/alok/LeanPlot) (left) next to the Julia/CairoMakie original " ++
    "(right, same data, same figure size). Regenerate with\n\n" ++
    "```\ncd gallery && lake exe gallery --docs            # Lean renders, data checks, this page\n" ++
    "julia --startup-file=no --project=oracle oracle/gallery/run_all.jl   # Julia renders and data dumps\n```\n\n" ++
    "The data column compares the numbers behind each plot with the Julia dump " ++
    "(`oracle/gallery/data/<name>.json`): iteration counts of the fractals, curve samples, " ++
    "streamlines, graph edges and error curves. Images are compared by eye (DESIGN.md §0: " ++
    "plot data numerically, images visually).\n\n"
  let groups := rows.foldl (fun (acc : Array String) (e, _) => if acc.contains e.group then acc else acc.push e.group) #[]
  for g in groups do
    s := s ++ s!"## {g}\n\n| figure | Lean (LeanPlot) | Julia (CairoMakie) | data agreement |\n|---|---|---|---|\n"
    for (e, cs) in rows do
      if e.group != g then continue
      let notePath := root / "docs" / "gallery" / "notes" / s!"{e.name}.md"
      let note ← if ← notePath.pathExists then pure ((← IO.FS.readFile notePath).trimAscii.toString) else pure ""
      let fig := s!"**{e.name}**<br>{cell e.title}<br><sub>{cell e.source}</sub>" ++
        (if note.isEmpty then "" else s!"<br><sub>{cell (note.replace "\n" " ")}</sub>")
      s := s ++ s!"| {fig} | ![{e.name} (Lean)](lean/{e.name}.png) | ![{e.name} (Julia)](julia/{e.name}.png) | {agreement cs} |\n"
    s := s ++ "\n"
  s := s ++ "## Pending (need Cartan, Adapode or other unported packages)\n\n" ++
    "From the ranked inventory in `docs/port-notes/plot-inventory.md` §6-§7.\n\n" ++
    "| id | figure | waits for |\n|---|---|---|\n"
  for p in pending do
    s := s ++ s!"| {p.id} | {cell p.what} | {cell p.needs} |\n"
  s := s ++ "\nVideos (21 YouTube talks) and LaTeX formula images (Fatou basins, Dendriform) are " ++
    "out of scope (`plot-inventory.md` §1).\n"
  return s

end Gallery.Index
