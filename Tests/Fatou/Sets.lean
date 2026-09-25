import Tests.Fatou.Catalog

/-!
Rasters, titles and the per-pixel kernel against the oracle (port-notes/fatou.md G5, G6, G9):

* `sets.json` + `<name>.{iter.u16,mix.f64,zre.f64,zim.f64}`: every catalog set at reduced
  resolution. Exact tier (rational maps): iteration counts and final iterates bit for bit,
  `mix` within a few ulps (it goes through `atan2`/`exp`). Transcendental tier (libm inside
  the map): at most a small fraction of pixels may differ in their count.
* the full-resolution README rasters (1501×1001, 800², 800², 500²) and the 176² defaults:
  iteration histograms and the FNV-1a hash of the counts, recomputed here.
* titles (`String(K)`, the PyPlot LaTeX title and y-label), `typeplot`, `basin`.
* `points.json`: `Define.orbit` at ~160 points per map, random and special.
* chaining (`fatou(K2, fatou(K1))`) and re-running a set (`fatou(fatou(K))`).
-/

namespace Tests.Fatou.Sets

open _root_.Fatou Tests.Fatou Tests.Fatou.Catalog

/-- Ulp budget for `mix` (Julia's own `atan`/`exp` against libm's). -/
def mixUlps : Nat := 4

/-- Iteration-count histogram and summary of a set (as `stats` in `gen.jl`). -/
structure Stats where
  /-- histogram of counts `0 … N` -/
  hist : Array Nat
  /-- FNV-1a of the little-endian `UInt16` counts -/
  fnv : String
  /-- number of NaN `mix` values -/
  mixNaN : Nat

/-- Compute `Stats` of a set. -/
def stats {r c : Nat} (Z : FilledSet r c) : Stats :=
  { hist := Z.iterHistogram, fnv := fnv1a Z.iter,
    mixNaN := Z.mix.foldl (fun k v => if v.isNaN then k + 1 else k) 0 }

/-- Compare `Stats` with a `stats` JSON object; exact tier requires equal histograms and
hashes, the transcendental tier a histogram within `slack` total variation. -/
def checkStats (lbl : String) (s : Stats) (j : Lean.Json) (exact : Bool) (slack : Nat) : TestM Unit := do
  let hist : Array Nat ← (← gArr j "hist").mapM (fun x => (nat x : IO Nat))
  let fnv ← gStr j "fnv"
  let nan ← gNat j "mixnan"
  if exact then
    checkEq s!"{lbl} histogram" s.hist hist
    checkEq s!"{lbl} fnv" s.fnv fnv
  else
    let tv := (s.hist.zip hist).foldl (fun a (x, y) => a + (if x ≥ y then x - y else y - x)) 0
    check s!"{lbl} histogram ~" (s.hist.size == hist.size && tv ≤ slack) fun _ =>
      s!"total variation {tv} > {slack}: {s.hist} vs {hist}"
    note s!"{lbl}: histogram total variation {tv} (of {2 * hist.foldl (· + ·) 0})"
  check s!"{lbl} mix NaN count" (if exact then s.mixNaN == nan else (s.mixNaN : Int) - nan ≤ 2 ∧ (nan : Int) - s.mixNaN ≤ 2)
    fun _ => s!"got {s.mixNaN}, expected {nan}"

/-- Compare a raster with its dump. -/
def checkRaster {r c : Nat} (name : String) (Z : FilledSet r c) (exact : Bool) : TestM Unit := do
  let it ← readU16 s!"{name}.iter.u16"
  let mix ← readF64 s!"{name}.mix.f64"
  let zre ← readF64 s!"{name}.zre.f64"
  let zim ← readF64 s!"{name}.zim.f64"
  let total := r * c
  checkEq s!"{name} dump size" it.size (2 * total)
  let mut iterBad := 0
  let mut zBad := 0
  let mut mixBad := 0
  let mut mixWorst := 0
  for i in [0:total] do
    let ok := Z.iterFlat i == (getU16 it i).toNat
    if !ok then iterBad := iterBad + 1
    else
      let zg : C64 := ⟨Z.zre[i]!, Z.zim[i]!⟩
      let ze : C64 := ⟨zre[i]!, zim[i]!⟩
      if !(if exact then sameC zg ze else closeC zg ze 64 1e-9) then zBad := zBad + 1
      let d := ulps Z.mix[i]! mix[i]!
      if d < 1000000 then mixWorst := max mixWorst d
      -- exact tier: `mix` differs only by the libm `atan2`/`exp` ulps; transcendental tier:
      -- the final iterates carry libm rounding amplified by the orbit
      if !(d ≤ mixUlps || closeF Z.mix[i]! mix[i]! 64 (if exact then 1e-14 else 1e-9)) then
        mixBad := mixBad + 1
  if exact then
    check s!"{name} iteration counts" (iterBad == 0) fun _ => s!"{iterBad} of {total} pixels differ"
    check s!"{name} final iterates" (zBad == 0) fun _ => s!"{zBad} of {total} pixels differ"
    check s!"{name} iteration bytes" (Z.iter == it) fun _ => "byte arrays differ"
  else
    check s!"{name} iteration counts ~" (iterBad * 100 ≤ total) fun _ => s!"{iterBad} of {total} pixels differ"
    check s!"{name} final iterates ~" (zBad * 100 ≤ total) fun _ => s!"{zBad} of {total} pixels differ"
    note s!"{name}: {iterBad} of {total} counts differ (libm transcendental tier)"
  check s!"{name} mix" (mixBad == 0) fun _ => s!"{mixBad} of {total} pixels beyond {mixUlps} ulps"
  if mixWorst > mixUlps then note s!"{name}: worst mix distance {mixWorst} ulps"

/-- Check titles and the other strings of a set. -/
def checkStrings {r c : Nat} (name : String) (K : Define) (Z : FilledSet r c) (j : Lean.Json) :
    TestM Unit := do
  checkEq s!"{name} title" Z.title (← gStr j "title")
  checkEq s!"{name} typeplot" Z.typeplot (← gStr j "typeplot")
  let K' := { K with latex := ← gStr j "latex" }
  checkEq s!"{name} PyPlot title" K'.latexTitle (← gStr j "pytitle")
  checkEq s!"{name} y-label" (K.latexYLabel.getD "") (← gStr j "ylabel")
  checkEq s!"{name} basin 0" (basin K.spec.newt 0 "") (← gStr j "basin0")
  checkEq s!"{name} basin 1" (basin K.spec.newt 1 (← gStr j "basin1body")) (← gStr j "basin1")
  checkEq s!"{name} m" (toString K.spec.m) (← gStr j "m")
  checkEq s!"{name} rows" r (← gNat j "rows")
  checkEq s!"{name} cols" c (← gNat j "cols")
  let b ← gFs j "bounds"
  check s!"{name} bounds" (Z.bounds.toArray.zip b |>.all fun (x, y) => sameF x y) fun _ =>
    s!"{Z.bounds.toArray} vs {b}"

/-- The full-resolution README rasters, with specialized kernels (each call site sees its
map). -/
def fullStats (name : String) : Option Stats :=
  match name with
  | "readme_filled_julia" => some (stats (fatou (readmeFilledJulia 1501)))
  | "readme_mandelbrot" => some (stats (fatou (readmeMandelbrot 800)))
  | "readme_newton" => some (stats (fatou (readmeNewton 800)))
  | "readme_gen_newton" => some (stats (fatou (readmeGenNewton 500)))
  | "default_newton" => some (stats (fatou (defaultNewton 176)))
  | "default_mandelbrot" => some (stats (fatou (defaultMandelbrot 176)))
  | "default_juliafill" => some (stats (fatou (defaultJuliafill 176)))
  | _ => none

/-- Every set of `sets.json`. -/
def runSets : TestM Unit := do
  let j ← readJson "sets.json"
  for s in ← gArr j "sets" do
    let name ← gStr s "name"
    let exact := (← gStr s "tier") == "exact"
    let n ← gNat s "n"
    match name with
    | "chain" =>
      let Z := FilledSet.chain chainSecond (fatou chainFirst)
      checkRaster name Z true
      checkStrings name chainSecond Z s
      checkStats name (stats Z) (← field s "stats") true 0
    | "refatou" =>
      let Z := (fatou chainFirst).refatou
      checkRaster name Z true
      checkStrings name chainFirst Z s
      checkStats name (stats Z) (← field s "stats") true 0
    | _ =>
      match find? name with
      | none => check s!"{name} in the Lean catalog" false
      | some mk =>
        let K := mk n
        let Z := fatou K
        checkRaster name Z exact
        checkStrings name K Z s
        checkStats name (stats Z) (← field s "stats") exact 0
        -- the sequential kernel and the reference semantics agree with the parallel one
        let Zs := fatou K (par := false)
        check s!"{name} sequential = parallel" (Zs.iter == Z.iter &&
          (Zs.mix.toList.zip Z.mix.toList).all fun (a, b) => sameF a b)
        let xs := K.spec.rect.xs
        let ys := K.spec.rect.ys
        let cols := K.spec.rect.cols
        let R : FilledSet K.spec.rect.rows K.spec.rect.cols :=
          FilledSet.reference K K.spec.rect.bounds fun i => ⟨xs[i % cols]!, ys[i / cols]!⟩
        check s!"{name} kernel = Define.orbit" (R.iter == Z.iter &&
          (R.zre.toList.zip Z.zre.toList).all (fun (a, b) => sameF a b) &&
          (R.zim.toList.zip Z.zim.toList).all (fun (a, b) => sameF a b))
        if let .ok full := s.getObjVal? "full" then
          match fullStats name with
          | some st =>
            let fr ← gNat full "rows"
            checkStats s!"{name} full {fr}×{← gNat full "cols"}" st full exact 400
          | none => check s!"{name} full-resolution builder" false

/-- The per-pixel kernel at random and special points. -/
def runPoints : TestM Unit := do
  let j ← readJson "points.json"
  let mut total := 0
  for m in ← gArr j "maps" do
    let name ← gStr m "name"
    let exact := (← gStr m "tier") == "exact"
    let some mk := find? name | check s!"{name} in the Lean catalog" false; continue
    -- the reduced size of the catalog; only the parameters matter here
    let K := mk 41
    let mut bad := 0
    let pts ← gArr m "points"
    for p in pts do
      let z0 ← gC p "z0"
      let (n, z) := K.orbit z0
      let en ← gNat p "n"
      let ez ← gC p "z"
      let emix ← gF p "mix"
      let ok := n == en && (if exact then sameC z ez else closeC z ez 64 1e-9) &&
        closeF (K.mixOf n z) emix mixUlps (if exact then 1e-14 else 1e-9)
      if !ok then
        bad := bad + 1
        if exact then
          check s!"{name} orbit({z0.re}, {z0.im})" false fun _ =>
            s!"got ({n}, {z.re}, {z.im}, {K.mixOf n z}) expected ({en}, {ez.re}, {ez.im}, {emix})"
      total := total + 1
    if exact then check s!"{name} points" (bad == 0)
    else
      check s!"{name} points ~" (bad * 20 ≤ pts.size) fun _ => s!"{bad} of {pts.size} differ"
      note s!"{name}: {bad} of {pts.size} points differ (transcendental tier)"
  note s!"points: {total} kernel evaluations"

/-- Lean's own Newton map `z - m·f/f'` against REDUCE's factored form: same basins, counts
equal on most pixels (they round differently). -/
def runGenericNewton : TestM Unit := do
  let K := readmeNewton 100
  let G := newton (fun z _ => z ^ 3 - (1 : Float)) (fun z _ => (3 : Float) * z ^ 2)
    { n := 100, ϵ := some 0.1, N := 25, iter := true, label := "z ^ 3 - 1" }
  let a := fatou K
  let b := fatou G
  let total := K.spec.rect.rows * K.spec.rect.cols
  let diff := (List.range total).foldl (fun k i => if a.iterFlat i == b.iterFlat i then k else k + 1) 0
  check "generic Newton map vs REDUCE form" (diff * 50 ≤ total) fun _ => s!"{diff} of {total} counts differ"
  note s!"generic Newton map: {diff} of {total} counts differ from REDUCE's factored map"

/-- Generalized units (port-notes/fatou.md §4.10): the hyperbolic Mandelbrot set
`mandelbrot(:(z^2+c), B = Λ(S"+-").v12, n = 40, N = 20)` has the histogram Julia gives with
the extension's intended return value (`t8.jl`); with `B² = -1` it is the ordinary set. -/
def runCouple : TestM Unit := do
  let split := fatou (mandelbrot (fun z c => Couple.sq 1 z + c) { n := 40, N := 20, label := "z ^ 2 + c" }
    (Q := fun z _ => Couple.abs2 1 z))
  checkEq "hyperbolic Mandelbrot histogram" split.iterHistogram
    #[0, 0, 184, 194, 116, 80, 94, 52, 39, 7, 202, 135, 52, 35, 15, 11, 3, 0, 0, 9, 372]
  let cx := fatou (mandelbrot (fun z c => Couple.sq (-1) z + c) { n := 40, N := 20 }
    (Q := fun z _ => Couple.abs2 (-1) z))
  let plain := fatou (mandelbrot (fun z c => z ^ 2 + c) { n := 40, N := 20 })
  check "Couple with B² = -1 is the complex plane" (cx.iter == plain.iter &&
    (cx.zre.toList.zip plain.zre.toList).all (fun (a, b) => sameF a b) &&
    (cx.zim.toList.zip plain.zim.toList).all (fun (a, b) => sameF a b))

/-- `(misclassified, converged)`: converged pixels whose basin index is not the root in the
angular sector of their final iterate. -/
def basinMismatches {r c : Nat} (Z : FilledSet r c) (b : ByteArray) : Nat × Nat :=
  (List.range (r * c)).foldl (init := (0, 0)) fun (bad, conv) i =>
    if Z.iterFlat i < Z.define.spec.N.toNat then
      let a := C64.angle ⟨Z.zre[i]!, Z.zim[i]!⟩
      let sector : Nat := if a.abs < pi / 3 then 1 else if a > 0 then 2 else 3
      (if b[i]!.toNat != sector then bad + 1 else bad, conv + 1)
    else (bad, conv)

/-- Basin indices (a Lean extension): every converged pixel of the README Newton fractal lies
near one of the cube roots of unity, the one in its angular sector. -/
def runBasins : TestM Unit := do
  -- (the loop lives in `basinMismatches`: a closed `FilledSet` used inside a `for` body can be
  -- copied into the specialized loop and recomputed per iteration, docs/PERF.md)
  let Z := fatou (readmeNewton 100)
  let s3 := (3 : Float).sqrt / 2
  let roots : Array C64 := #[⟨1, 0⟩, ⟨-0.5, s3⟩, ⟨-0.5, -s3⟩]
  let b := Z.basinIndex roots 0.05
  let total := 100 * 100
  checkEq "basin index size" b.size total
  let (bad, converged) := basinMismatches Z b
  check "converged pixels lie in their root's basin" (bad == 0 && converged > total / 2) fun _ =>
    s!"{bad} of {converged} converged pixels misclassified"
  -- a bare raster gets Julia's pixel extent
  let W := (readmeNewton 100).onPlane Z.set
  check "onPlane default extent" (W.bounds == Plane.pixelBounds 100 100)

/-- Run the suite. -/
def run : TestM Unit := do
  runSets
  runPoints
  runGenericNewton
  runCouple
  runBasins

end Tests.Fatou.Sets
