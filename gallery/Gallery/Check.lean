import Gallery

/-!
# The gallery's test suite (`lake test` in `gallery/`)

`Gallery.Check.run` rebuilds the data of every figure (no rendering), runs its comparisons with
the committed Julia dumps (`oracle/gallery/data/`), and adds a few spot values from the Julia
docs that need no dump (`notes/grassmann-docs-goldens/readme_plot_goldens.json`). It returns
`(passed, failed)`.
-/

namespace Gallery.Check

open Gallery.Fields Grassmann

/-- Spot values of the README curves and fields (Julia 0.8.46): exact where Julia's
closed-form `exp` applies, within Julia's Taylor truncation (≈2e-9) otherwise. -/
def spots : Array Check :=
  let close (label : String) (got want : Array Float) (tol : Float) : Check :=
    let d := maxAbsDiff ⟨got⟩ ⟨want⟩
    { label, ok := got.size == want.size && d ≤ tol, detail := s!"max |Δ| = {sci d} (tol {sci tol})" }
  let c3 (c : Grassmann.Chain Inf3.V 1 Float) : Array Float := #[getD c.v 1, getD c.v 2, getD c.v 3]
  let h := helix (2 * pi)
  let (ox, oy, oz) := sphereField orbVersor 1 2 3 0.5 0.5 0.5
  let (px, py) := planeFieldOf 3 (-1.5) (-1.5)
  let (qx, qy) := planeFieldOf 5 (-1.5) (-1.5)
  #[close "torus(0) = (1, 1, 1)" (c3 (torus 0)) #[1, 1, 1] 1e-12,
    close "torus(2π)" (c3 (torus (2 * pi))) #[-1.0481768353996013, 0.4756012331663304, -0.9647624460121627] 1e-12,
    close "helix(2π)" #[getD h.v 2, getD h.v 3, getD h.v 4] #[-1.2878427202669922, 0.5843467530972623, 40.47841755597899] 1e-10,
    close "orbit-2(0) = (1, 1, -1)" (c3 (orbit2 0)) #[1, 1, -1] 1e-12,
    close "orbit-4(2π)" (c3 (orbit4 (2 * pi))) #[1.3635882823689522, 0.5278320450125441, -1.0715495013497132] 1e-12,
    close "orb field at (½, ½, ½) = (-4/11, 4/11, -1/11)" #[ox, oy, oz] #[-4 / 11, 4 / 11, -1 / 11] 5e-9,
    close "plane-3 field at (-1.5, -1.5)" #[px, py] #[1.1102230246251565e-16, -2.1213203435596424] 1e-15,
    close "plane-5 field at (-1.5, -1.5)" #[qx, qy] #[-2.221459005734865, -2.221459005734865] 1e-15,
    eqCheck "points range length" pointsRange.size 125664]

/-- Run every figure's data checks and the spot values; print failures; `(passed, failed)`. -/
def run (root : System.FilePath := "..") : IO (Nat × Nat) := do
  let mut pass := 0
  let mut fail := 0
  for c in spots do
    if c.ok then pass := pass + 1 else fail := fail + 1; IO.println s!"FAIL spot {c.label}: {c.detail}"
  for e in Gallery.registry do
    let dataPath := root / "oracle" / "gallery" / "data" / s!"{e.name}.json"
    if !(← dataPath.pathExists) then
      fail := fail + 1; IO.println s!"FAIL {e.name}: no Julia dump at {dataPath}"; continue
    match Lean.Json.parse (← IO.FS.readFile dataPath) with
    | .error err => fail := fail + 1; IO.println s!"FAIL {e.name}: {err}"
    | .ok j =>
      let out ← e.build (some j)
      for c in out.checks do
        if c.ok then pass := pass + 1 else fail := fail + 1; IO.println s!"FAIL {e.name} {c.label}: {c.detail}"
  return (pass, fail)

end Gallery.Check
