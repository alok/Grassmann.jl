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

/-- The figures of `docs/port-notes/plot-inventory.md` §6 that need Cartan's differential geometry,
Adapode or other unported packages, or that LeanPlot or Cartan.jl cannot draw. -/
def pending : List Pending := [
  ⟨"C1", "plane curve with unit frames, arclength/speed/curvature (Cartan `fiber.md:442-451`)", "Cartan differential geometry (`unitframe`, `arclength`, `curvature`); the `scaledarrows` recipe itself is `cartan-scaledarrows-*`"⟩,
  ⟨"C2", "plane curves from curvature, `planecurve` (`fiber.md:452-457`)", "Cartan differential geometry (`planecurve`, cumulative integrals)"⟩,
  ⟨"C3", "Lorenz vector-field 3D streamplot (`fiber.md:460-468`)", "a 401³ grid field (64 M points, 1.5 GB in Julia); GrassmannPlot's grid streamplot is ready"⟩,
  ⟨"C4 / A1", "Lorenz, Rössler, dynamo attractors (`fiber.md:470-474`, Adapode `examples/chaos.jl`)", "Adapode (`odesolve`, RK4/ABM4 on Chains)"⟩,
  ⟨"C8", "Lie bracket streamplots on the torus (`fiber.md:552-563`)", "Cartan differential geometry (`gradient`, `Lie`)"⟩,
  ⟨"C10", "link curves and linkmap meshes (`fiber.md:649-656`)", "Cartan differential geometry (`linkmap`, `linknumber`)"⟩,
  ⟨"C11 / C12", "torus and wiggle coloured by curvature (`fiber.md:669-695`)", "Cartan differential geometry (shape operator, `meancurvature`, `gaussintrinsic`)"⟩,
  ⟨"C13 / C14 / C15", "torus, Klein-bottle and half-plane geodesics (`fiber.md:709-763`)", "Cartan + Adapode (`geodesic`, `geosolve`)"⟩,
  ⟨"C17 (sphere)", "tangent-space streamplot of a gradient on the sphere (`fiber.md:778-797`)", "Cartan differential geometry (`gradient`); the torus half is `cartan-torus-tangent-stream`"⟩,
  ⟨"C18", "da Rios vortex filament (`fiber.md:800-811`)", "Adapode (`odesolve` on curve fields; upstream bug P9)"⟩,
  ⟨"C19", "Bishop frame (`fiber.md:813-820`)", "Cartan differential geometry (`bishopunitframe`)"⟩,
  ⟨"C20 / A11", "disk eigenmodes (`fiber.md:823-834`)", "Adapode (FEM assembly, generalized eigensolver; MATLAB mesh upstream)"⟩,
  ⟨"C21 / A12", "heat flow around a NACA airfoil (`fiber.md:874-895`)", "Adapode + FlowGeometry + a 2D mesher"⟩,
  ⟨"C22 / A13", "Poisson on a sphere-in-cube tetrahedral mesh (`fiber.md:898-910`)", "Adapode + TetGen-like mesher"⟩,
  ⟨"C23", "Stokes theorem on a paraboloid (`fiber.md:932-962`)", "Cartan differential geometry (`graph`, `unitnormal`, `curl`)"⟩,
  ⟨"M-contour_himmelblau, M-heatmap_logscale", "labelled isolines with a `ReversibleScale`; an `asinh` axis scale (`plot.md:66-76, 202-214`)", "LeanPlot contour labels and custom scales"⟩,
  ⟨"M-contour_curvilinear, M-contourf", "curvilinear mesh + contour; contourf over a TensorField (`plot.md:77-98, 159-170`)", "broken upstream (`Mesh(::GridBundle{PointMatrix})`, `FieldError`): no Julia render"⟩,
  ⟨"M-volume*, M-contour_volume*, M-voxels_cube_with_holes", "volume renderings and 3D contours of volumes (`plot.md:127-153, 350-388`)", "a LeanPlot `volume` mark (blank in CairoMakie anyway); a 100³ voxel chunk"⟩,
  ⟨"A2–A9", "leapfrog, wave, heat and rest-wave PDE surfaces and isosurfaces (Adapode `README.md:151-231`)", "Adapode (spectral solvers, FFT)"⟩,
  ⟨"A10", "L2 projector (Adapode `README.md:235-240`)", "Adapode (1D FEM)"⟩,
  ⟨"W1–W4", "NACA airfoils, double arc, wing surface, Rakich C-mesh (FlowGeometry)", "FlowGeometry port"⟩,
  ⟨"D1", "Tamari associahedron coloured by grove sums (Dendriform README)", "external gist, not in the repositories"⟩,
  ⟨"G10", "`vandermonde` terminal plot (`ext/UnicodePlotsExt.jl`)", "UnicodePlots-style terminal backend (API only, no documented call)"⟩
]

/-- Escape `|` for a Markdown table cell. -/
def cell (s : String) : String := s.replace "|" "\\|"

/-- The agreement column of a figure: a pass count that unfolds into the individual checks. -/
def agreement (cs : Array Check) : String :=
  if cs.isEmpty then "no data dump" else
  let bad := cs.filter (!·.ok)
  let head := if bad.isEmpty then s!"✅ {cs.size}/{cs.size} checks" else s!"❌ {cs.size - bad.size}/{cs.size} checks"
  s!"<details><summary>{head}</summary>" ++ "<br>".intercalate (cs.toList.map fun c =>
    s!"{if c.ok then "" else "**FAIL** "}{cell c.label}: {cell c.detail}") ++ "</details>"

/-- Render the page. `extra` is the per-figure note of `docs/gallery/notes/<name>.md` if any. -/
def render (root : System.FilePath) (rows : Array (Entry × Array Check × String)) : IO String := do
  let mut s := "# Gallery: the chakravala figures in Lean\n\n"
  s := s ++ "Every figure of the Julia ecosystem that the Lean port can compute today, rendered with " ++
    "[LeanPlot](https://github.com/alok/LeanPlot) (left) next to the Julia/CairoMakie original " ++
    "(right, same data, same figure size). Regenerate with\n\n" ++
    "```\njulia --startup-file=no --project=oracle oracle/gallery/run_all.jl   # Julia renders and data dumps\n" ++
    "cd gallery && lake exe gallery --docs   # Lean renders (gallery/out/*.png, *.svg), data checks, this page\n" ++
    "cd gallery && lake test                 # the data checks alone\n```\n\n" ++
    "`gallery/` is a Lake package of its own (it requires the root package and LeanPlot " ++
    "`f141f59`); both sides render at one pixel per unit of the same figure size.\n\n" ++
    "The Cartan figures are drawn with `GrassmannPlot` (`gallery/GrassmannPlot/`), the port of " ++
    "Cartan's Makie extension (`ext/MakieExt.jl`): `lines(t)`, `streamplot(t)`, `mesh(M, f)`, " ++
    "`scaledarrows(M, t)`, … dispatch on the field's base and fiber types as in Julia. The Julia " ++
    "originals are drawn by Cartan's own methods; where CairoMakie needs an `Axis3` for comparable " ++
    "framing (Julia's automatic `LScene`), the scripts pass it.\n\n" ++
    "The data column compares the numbers behind each plot with the Julia dump " ++
    "(`oracle/gallery/data/<name>.json`): iteration counts of the fractals, curve samples, " ++
    "streamlines, graph edges and error curves. Images are compared by eye (DESIGN.md §0: " ++
    "plot data numerically, images visually).\n\n"
  let groups := rows.foldl (fun (acc : Array String) (e, _, _) => if acc.contains e.group then acc else acc.push e.group) #[]
  for g in groups do
    s := s ++ s!"## {g}\n\n| figure | Lean (LeanPlot) | Julia (CairoMakie) | data agreement |\n|---|---|---|---|\n"
    for (e, cs, img) in rows do
      if e.group != g then continue
      let notePath := root / "docs" / "gallery" / "notes" / s!"{e.name}.md"
      let note ← if ← notePath.pathExists then pure ((← IO.FS.readFile notePath).trimAscii.toString) else pure ""
      let up := if e.upstream.isEmpty then "" else s!" ([original]({e.upstream}))"
      let fig := s!"**{e.name}**{up}<br>{cell e.title}<br><sub>{cell e.source}</sub>" ++
        (if note.isEmpty then "" else s!"<br><sub>{cell (note.replace "\n" " ")}</sub>")
      s := s ++ s!"| {fig} | <img src=\"lean/{e.name}.png\" width=\"340\" alt=\"{e.name} (Lean)\"> | " ++
        s!"<img src=\"julia/{e.name}.png\" width=\"340\" alt=\"{e.name} (Julia)\"> | {agreement cs}<br><sub>pixels: {cell img}</sub> |\n"
    s := s ++ "\n"
  s := s ++ "## Pending\n\n" ++
    "From the ranked inventory in `docs/port-notes/plot-inventory.md` §6-§7.\n\n" ++
    "| id | figure | waits for |\n|---|---|---|\n"
  for p in pending do
    s := s ++ s!"| {p.id} | {cell p.what} | {cell p.needs} |\n"
  s := s ++ "\n## Reproducible now, not yet in the gallery\n\n" ++
    "* The rest of the Fatou wiki gallery (`docs/port-notes/fatou.md` §6.4: about 40 Newton, Julia-set " ++
    "and orbit images; four are above) and the 176² default-keyword sets: the Fatou port computes them " ++
    "(`Tests/Fatou/Catalog.lean`); maps with `exp`/`log`/complex powers need REDUCE's Newton forms " ++
    "written out.\n" ++
    "* `planes`, `spaces`, `planesbundle`, `spacesbundle` of frames are in `GrassmannPlot.Arrows`, but " ++
    "Cartan 0.4.16's `planes`/`scaledplanes` return `nothing` after drawing every parallelogram in a " ++
    "figure of its own, and `planesbundle` reads an undefined `M` (B4), so there is no Julia render " ++
    "to compare with.\n"
  s := s ++ "\nVideos (21 YouTube talks) and LaTeX formula images (Fatou basins, Dendriform) are " ++
    "out of scope (`plot-inventory.md` §1).\n"
  return s

end Gallery.Index
