import Tests.Fatou.Catalog

/-!
The symbolic layer against the oracle (`oracle/fatou/symbolic.jl`, `symbolic.json`): every Julia
expression of the Fatou README and wiki.

* `string(E)`: `JExpr.parse` and the printer reproduce Julia's text of every expression.
* Newton maps: `Fatou.CAS` produces REDUCE's `Expr` text exactly for the forms REDUCE leaves in
  its expanded normal form (`exactF`); for every map, the CAS's rational function equals
  REDUCE's (both evaluated with Julia's semantics at 64 points agree to rounding).
* LaTeX: REDUCE's `latex(E)` (titles) and the basin body `nL(E, m, 1)` / `jL(E, 1)` exactly for
  the forms listed; `Define.basinOf 1` then reproduces Julia's `basin(K, 1)`.
* The elaborated maps: `newton! "z^3 - 1"` iterates bit for bit like the hand-written
  REDUCE map, and `Symbolic.ofString` (interpreted) like the elaborated one.

Julia's REDUCE runs with `off exp` (Reduce.jl), so a product built during `newton_raphson` can
stay unexpanded; those golden forms are the same functions written differently and are
reported, not required (see `Fatou.CAS`). `default_juliafill`'s title in `sets.json` comes from a
Reduce.jl conversion defect (`RExpr(::Complex)` doubles an interpolated complex constant:
`(67 i+50 z^{2}-6)/50` for `z^2 + (-0.06 + 0.67im)`); the CAS gives the correct
`(67 i+100 z^{2}-6)/100`, which is also REDUCE's title for the same map written `z^2 - 0.06 +
0.67im`.
-/

namespace Tests.Fatou.Symbolic

open _root_.Fatou Tests.Fatou Wilkinson

/-- Newton maps whose golden `Expr` text the CAS reproduces exactly. -/
def exactF : List String :=
  ["readme_newton", "newton_m2", "newton_mhalf", "newton_quartic", "newton_cubic_factor",
   "newton_cubic5", "newton_z2m1", "newton_octic", "newton_octic_c", "newton_sin", "newton_golden"]

/-- Expressions whose golden `latex(E)` the CAS reproduces exactly. -/
def exactLatex : List String :=
  ["readme_newton", "newton_m2", "newton_mhalf", "newton_quartic", "newton_cubic_factor",
   "newton_cubic5", "readme_gen_newton", "newton_z2m1", "newton_zim", "newton_octic",
   "newton_octic_c", "newton_sin", "newton_sextic", "newton_cos_a", "newton_cos_b", "newton_cos",
   "newton_log", "newton_cpow", "newton_exp", "newton_golden", "readme_mandelbrot",
   "cubic_mandelbrot", "readme_orbit", "default_juliafill", "hump", "hump_linear", "basilica",
   "float_one", "cos", "sin", "golden", "quadratic", "chebyshev", "cubic", "sqrt", "plus_one",
   "sin2", "affine", "cubic_minus_one", "exp_plus_one", "cpow", "sin_minus_one"]

/-- Basin bodies (`j = 1`) the CAS reproduces exactly. -/
def exactBody1 : List String :=
  ["readme_newton", "newton_m2", "newton_mhalf", "newton_quartic", "newton_cubic_factor",
   "newton_cubic5", "newton_octic", "newton_sin", "newton_golden", "readme_mandelbrot",
   "cubic_mandelbrot", "readme_orbit", "default_juliafill", "hump", "hump_linear", "basilica",
   "float_one", "cos", "sin", "golden", "quadratic", "chebyshev", "cubic", "sqrt", "plus_one",
   "sin2", "affine", "cubic_minus_one", "exp_plus_one", "cpow", "sin_minus_one"]

/-- Evaluation points in the unit square around the origin (away from the poles at `0`). -/
def points : Array C64 := (Array.range 64).map fun k =>
  let t := Float.ofNat k
  ⟨0.9 * (t * 0.61803398875).sin + 0.35, 0.8 * (t * 1.3247179572).cos - 0.2⟩

/-- Relative closeness, `NaN`s and infinities excepted. -/
def near (a b : C64) : Bool :=
  let d := (a.re - b.re).abs + (a.im - b.im).abs
  let s := a.re.abs + a.im.abs + b.re.abs + b.im.abs
  !(a.re.isFinite && a.im.isFinite && b.re.isFinite && b.im.isFinite) || d ≤ 1e-9 * (1 + s)

/-- The map of a Julia expression text (Julia-typed, interpreted). -/
def mapOf (s : String) : Except String (C64 → C64 → C64) := do
  return (← Sym.lower (← JExpr.parse s)).map

/-- Strip REDUCE's line breaks. -/
def flat (s : String) : String := s.replace "\n" ""

/-- One golden case. -/
def runCase (c : Lean.Json) (counts : IO.Ref (Nat × Nat × Nat)) : TestM Unit := do
  let name ← gStr c "name"
  let kind ← gStr c "kind"
  let src ← gStr c "E"
  let E ← match JExpr.parse src with
    | .ok e => pure e
    | .error e => check s!"{name} parse" false (fun _ => e); return
  checkEq s!"{name} string(E)" E.toJulia src
  -- the title LaTeX
  let latex := match CAS.simp E with
    | .ok r => CAS.latexOf r
    | .error e => s!"<{e}>"
  let gl := flat (← gStr c "latex")
  if exactLatex.contains name then checkEq s!"{name} latex(E)" latex gl
  else if latex != gl then note s!"{name}: latex(E) {latex} (REDUCE {gl})"
  if kind == "newton" then
    let mS ← gStr c "m"
    let m := match Sym.constOf mS with
      | .ok v => v.toNumber
      | .error _ => .int 1
    let gF ← gStr c "F"
    match Symbolic.derive E true m with
    | .error e => check s!"{name} newton_raphson" false fun _ => e
    | .ok (F, _) =>
      if exactF.contains name then
        checkEq s!"{name} newton_raphson" F.toJulia gF
        counts.modify fun (a, b, c) => (a + 1, b, c)
      else
        note s!"{name}: CAS {F.toJulia}"
        note s!"{name}: REDUCE {gF}"
        counts.modify fun (a, b, c) => (a, b + 1, c)
      -- the same rational function: evaluate both with Julia's semantics
      match mapOf F.toJulia, mapOf gF with
      | .ok f, .ok g =>
        let bad := points.foldl (fun k z => if near (f z ⟨0, 0⟩) (g z ⟨0, 0⟩) then k else k + 1) 0
        check s!"{name} CAS map = REDUCE map" (bad == 0) fun _ => s!"{bad} of 64 points differ"
      | .error e, _ | _, .error e => check s!"{name} maps compile" false fun _ => e
    -- the basin body and `basin(K, 1)`
    let K := match Symbolic.ofString src true mS with
      | .ok S => S.newton
      | .error _ => newton (fun z _ => z) (fun _ _ => ⟨1, 0⟩)
    match K.basinOf 1 with
    | .ok b =>
      if exactBody1.contains name then checkEq s!"{name} basin(K, 1)" b (flat (← gStr c "basin1"))
      else note s!"{name}: basin body differs from REDUCE's (off exp form)"
    | .error e => check s!"{name} basin(K, 1)" false fun _ => e
  else
    let K := match Symbolic.ofString src with
      | .ok S => S.juliafill
      | .error _ => juliafill (fun z _ => z)
    match K.basinOf 1 with
    | .ok b =>
      if exactBody1.contains name then checkEq s!"{name} basin(K, 1)" b (flat (← gStr c "basin1"))
      else note s!"{name}: basin body {b}"
    | .error e => check s!"{name} basin(K, 1)" false fun _ => e
  checkEq s!"{name} basin(K, 0)" (basin (kind == "newton") 0 "") (← gStr c "basin0")
  counts.modify fun (a, b, c) => (a, b, c + 1)

/-- The options of the README generalized Newton fractal at 41 columns. -/
def genNewtonOpts : Options :=
  { bounds := ⟨-2 * pi / 3, -pi / 3, -pi / 6, pi / 6⟩, n := 41, N := 33, iter := true,
    ϵ := some 0.05, cmap := "cubehelix" }

/-- The elaborated maps against the hand-written ones and the interpreted ones. -/
def runMaps : TestM Unit := do
  let a := fatou (newton! "z^3 - 1" { n := 41 })
  let b := fatou (newton (fun z _ => z ^ 3 - (1 : Float)) (fun z _ => (3 : Float) * z ^ 2) { n := 41 }
    (map := some Catalog.newtonCubic))
  check "newton! = hand-written REDUCE map" (a.iter == b.iter &&
    (a.zre.toList.zip b.zre.toList).all (fun (x, y) => sameF x y) &&
    (a.mix.toList.zip b.mix.toList).all (fun (x, y) => sameF x y))
  -- the interpreted maps agree bit for bit with the compiled ones (a rational map; with
  -- `sin`/`cos` inside, clang may fuse the libm calls of the compiled map into `sincos`, a
  -- libm-tier difference)
  match Symbolic.ofString "z^8 - 15z^4 - 16" true "1.5" with
  | .ok S =>
    let o : Options := { bounds := ⟨-2 * pi / 3, 0, -pi / 3, pi / 3⟩, n := 41, N := 17 }
    let r := fatou (S.newton o)
    let e := fatou (newton! "z^8 - 15z^4 - 16" (m := "1.5")
      { bounds := ⟨-2 * pi / 3, 0, -pi / 3, pi / 3⟩, n := 41, N := 17 })
    check "Symbolic.ofString (interpreted) = newton! (compiled)" (r.iter == e.iter &&
      (r.zre.toList.zip e.zre.toList).all (fun (x, y) => sameF x y) &&
      (r.mix.toList.zip e.mix.toList).all (fun (x, y) => sameF x y))
  | .error err => check "Symbolic.ofString" false fun _ => err
  let reduceSin := "((sin(z) - 1) * (im - 1) + cos(z) * z) / cos(z)"
  match Symbolic.ofString "sin(z) - 1" true "1 - 1im" (some reduceSin) with
  | .ok S =>
    let K := S.newton genNewtonOpts
    let r := fatou K
    let e := fatou (Catalog.readmeGenNewton 41)
    let diff := (List.range (41 * 41)).foldl (fun k i => if r.iterFlat i == e.iterFlat i then k else k + 1) 0
    check "Symbolic.ofString ≈ newton! (sin, libm tier)" (diff * 100 ≤ 41 * 41) fun _ =>
      s!"{diff} counts differ"
    checkEq "m keeps Julia's type" (toString K.spec.m) "1 - 1im"
  | .error err => check "Symbolic.ofString" false fun _ => err
  -- titles from the expression alone
  checkEq "newton! title" (Catalog.readmeNewton 41).title "f : z ↦ z ^ 3 - 1, m = 1, iter."
  checkEq "mandelbrot! title" (Catalog.readmeMandelbrot 41).title "f : z ↦ z ^ 2 + c, limit"
  checkEq "mandelbrot! LaTeX" (Catalog.readmeMandelbrot 41).latexTitle "$f:z\\mapsto c+z^{2},\\,$limit"
  -- `mandelbrot(E; m ≠ 0)` switches to Newton mode (`src/Fatou.jl:269`)
  let mn := mandelbrot! "z^3 - 1" (m := "1") { n := 41 }
  check "mandelbrot! with m is Newton mode" (mn.spec.newt && mn.spec.mandel)

/-- Run the suite. -/
def run : TestM Unit := do
  let j ← readJson "symbolic.json"
  let counts ← IO.mkRef (0, 0, 0)
  for c in ← gArr j "cases" do runCase c counts
  let (exact, other, total) ← counts.get
  note s!"symbolic: {total} expressions; Newton maps: {exact} exactly REDUCE's text, {other} REDUCE's off-exp form (same function)"
  runMaps

end Tests.Fatou.Symbolic
