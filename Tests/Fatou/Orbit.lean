import Tests.Fatou.Harness

/-!
Cobweb data and orbit-plot strings against `oracle/golden/fatou/orbits.json`
(port-notes/fatou.md G10): the README orbit, a Newton orbit, the wiki's basilica, quadratic
and doubling-map orbits (bit for bit), and two transcendental maps (within a few ulps).
-/

namespace Tests.Fatou.Orbit

open _root_.Fatou Tests.Fatou

/-- The Lean definitions of the orbit cases, with the real maps Julia evaluates. -/
def cases : List (String × Define) := [
  ("readme_orbit", juliafill (fun z _ => z ^ 2 - (0.67 : Float))
    { bounds := .interval (-1.25) 1.5, x0 := some 1.25, orbit := 17, depth := 3, n := 147,
      label := "z ^ 2 - 0.67" }),
  ("noorbit", juliafill (fun z _ => z ^ 2 - (0.67 : Float))
    { bounds := .interval (-1.25) 1.5, label := "z ^ 2 - 0.67" }),
  ("newton_orbit", newton (fun z _ => z ^ 3 - (1 : Float)) (fun z _ => (3 : Float) * z ^ 2)
    { bounds := .interval 0.4 2.5, x0 := some 2.1, orbit := 4, depth := 2, n := 42, label := "z ^ 3 - 1" }
    -- REDUCE's `(2 * z ^ 3 + 1) / (3 * z ^ 2)` in real arithmetic
    (real := some fun x => (2 * (x * x * x) + 1) / (3 * (x * x)))),
  ("basilica_orbit", juliafill (fun z _ => z ^ 2 - (1 : Float))
    { bounds := .interval (-2) 2, x0 := some 0, orbit := 10, depth := 5, label := "z ^ 2 - 1" }),
  ("quadratic_orbit", juliafill (fun z _ => (-1.5 : Float) * z ^ 2 + ((5 : Float) * z) / (2 : Float) + (1 : Float))
    { bounds := .interval (-0.7) 2.5, x0 := some 0.001, orbit := 37, depth := 3,
      label := "(-3 / 2) * z ^ 2 + (5z) / 2 + 1" }
    (real := some fun x => -1.5 * (x * x) + (5 * x) / 2 + 1)),
  ("doubling_orbit", juliafill (fun z _ => (2 : Float) * z)
    { bounds := .interval 0 1, x0 := some 0.3, orbit := 70, depth := 3, label := "(2z) % 1" }
    (real := some fun x => JuliaBase.F64.rem (2 * x) 1)),
  ("hump_orbit", juliafill (fun z _ => z * C64.exp ((1.5 : Float) * ((1 : Float) - z ^ 2 / (50 : Float))))
    { bounds := .interval 0 15, x0 := some 1, orbit := 24, label := "z * exp(1.5 * (1 - z ^ 2 / 50))" }
    (real := some fun x => x * (1.5 * (1 - (x * x) / 50)).exp)),
  ("cos_orbit", juliafill (fun z _ => C64.cos z)
    { bounds := .interval 0 2, x0 := some 1.7, orbit := 17, depth := 3, label := "cos(z)" }
    (real := some Float.cos))
]

/-- Compare two float sequences (bit for bit, or within `n` ulps). -/
def checkFloats (lbl : String) (got : FloatArray) (exp : Array Float) (exact : Bool) : TestM Unit := do
  let ok := got.size == exp.size &&
    (got.toList.zip exp.toList).all fun (a, e) => if exact then sameF a e else closeF a e 8 1e-15
  check lbl ok fun _ =>
    let bad := (got.toList.zip exp.toList).zipIdx.find? fun ((a, e), _) =>
      !(if exact then sameF a e else closeF a e 8 1e-15)
    s!"sizes {got.size}/{exp.size}, first difference {bad.map fun ((a, e), i) => (i, a, e)}"

/-- Run the suite. -/
def run : TestM Unit := do
  let j ← readJson "orbits.json"
  for o in ← gArr j "orbits" do
    let name ← gStr o "name"
    let exact := (← gStr o "tier") == "exact"
    match cases.find? (·.1 == name) with
    | none => check s!"{name} in the Lean cases" false
    | some (_, K) =>
      let K := { K with latex := ← gStr o "latex" }
      let d := K.realOrbit
      checkFloats s!"{name} x" d.x (← gFs o "x") true
      let comps ← gArr o "comps"
      checkEq s!"{name} compositions" d.comps.size comps.size
      for t in [0:min d.comps.size comps.size] do
        checkFloats s!"{name} N[:,{t + 1}]" d.comps[t]! (← (← arr comps[t]!).mapM (fun x => (hexF x : IO Float))) exact
      checkFloats s!"{name} N2" d.orbit (← gFs o "N2") exact
      checkFloats s!"{name} cobweb x" d.cobwebX (← gFs o "cobx") exact
      checkFloats s!"{name} cobweb y" d.cobwebY (← gFs o "coby") exact
      let bis ← gFs o "bis"
      check s!"{name} bis" (sameF d.bis.1 bis[0]! && sameF d.bis.2.1 bis[1]! && sameF d.bis.2.2 bis[2]!)
      let yl ← gFs o "ylim"
      let (lo, hi) := d.ylim
      check s!"{name} ylim" (if exact then sameF lo yl[0]! && sameF hi yl[1]! else closeF lo yl[0]! 8 && closeF hi yl[1]! 8)
        fun _ => s!"got ({lo}, {hi}) expected {yl}"
      if K.spec.orbit != 0 then checkFloats s!"{name} time axis" d.orbitXs (← gFs o "tseries") true
      checkEq s!"{name} UnicodePlots title" K.orbitTitle (← gStr o "unicode_title")
      checkEq s!"{name} PyPlot title" K.orbitLatexTitle (← gStr o "latex_title")
      checkEq s!"{name} PyPlot legend" K.orbitLatexLegend ((← gArr o "latex_legend").map fun s => s.getStr?.toOption.getD "")
      -- cobweb shape: (x_k, x_k), (x_k, x_{k+1}), (x_{k+1}, x_{k+1})
      checkEq s!"{name} cobweb size" d.cobwebX.size (3 * K.spec.orbit)

end Tests.Fatou.Orbit
