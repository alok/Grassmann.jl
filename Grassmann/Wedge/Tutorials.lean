import Grassmann.Scene.Types
import Grassmann.Scene.Json
import Grassmann.Wedge.Types

/-!
# Canonical Wedge Tutorial Cards (T1–T6) & Deterministic Procedural Challenge Generator

Strictly `Init`-only (`Grassmann.Scene.*` + `Grassmann.Wedge.Types` — zero `Lean.*`,
zero `Std.*`, zero external deps) so it compiles straight into both the tiny standalone
C ABI dylib and the Lean 4.36 → C → Emscripten WASM bundle.

Provides:
1. **The 6 Canonical Interactive Tutorial Cards** faithfully adapted from Steven De Keninck's
   (`enkimute`) `enkimute/ganja.js/examples/example_game_wedge.html` plus T6 for spatial 3D:
   - `T1`: Points & Lines (White givens, Red targets, Ghosted hints)
   - `T2`: Join by Pulling Apart (`A & B`)
   - `T3`: Meet by Pushing Together (`a ^ b`)
   - `T4`: Midpoint & Bisector Add (`A + B` and `c + b`)
   - `T5`: Orthogonal Dot Projection (`a << B`)
   - `T6`: Spatial Two-Hand Wedge 3D (`PGA3 = Cl(3,0,1)` for Web 3D & visionOS!)
   Each card carries structured text, algebraic formula, a playable mini `WedgeLevel`,
   and an animated `SceneFrame` (`GSIR` v1) demonstrating the gesture visually.
2. **Deterministic Procedural Challenge Generator** (`generateChallenge seed dim difficulty`):
   Infinite reproducible 2D (`PGA2`) and 3D (`PGA3`) geometric puzzles with guaranteed
   non-degeneracy checks (non-collinear triangles in 2D, non-coplanar tetrahedra in 3D)
   spanning Easy, Medium, and Hard (Orthocenter, Circumcenter, Centroid, Nine-Point Center,
   Euler Line, Tetrahedron Altitude, Foot of Altitude, Tetrahedron Circumcenter, 3D Monge Point).

Credits: Steven De Keninck (`enkimute` / `ganja.js`) & Michael Reed (`chakravala` / `Grassmann.jl`).
-/

namespace Grassmann.Wedge.Tutorials

open Grassmann.Scene Grassmann.Wedge

/-! ## Exact PGA Helpers (Strictly `Init`-Only via `PgaElem`) -/

private def p2 (x y : Float) : PgaElem := .pt2 x y
private def l2 (a b c : Float) : PgaElem := (PgaElem.mkLine2 a b c).getD (.line2 1.0 0.0 0.0)
private def p3 (x y z : Float) : PgaElem := .pt3 ⟨x, y, z⟩
private def pl3 (nx ny nz d : Float) : PgaElem :=
  (PgaElem.mkPlane3 ⟨nx, ny, nz⟩ d).getD (.plane3 ⟨0.0, 1.0, 0.0⟩ 0.0)
private def joinE (a b : PgaElem) : PgaElem := (PgaElem.join a b).getD a
private def meetE (a b : PgaElem) : PgaElem := (PgaElem.meet a b).getD a
private def addE  (a b : PgaElem) : PgaElem := (PgaElem.addSameGrade a b).getD a
private def dotE  (a b : PgaElem) : PgaElem := (PgaElem.dotProject a b).getD a

/-! ## 1. The 6 Canonical Tutorial Cards (T1–T6) -/

/-- Structured Wedge tutorial card with pedagogical copy, gesture glyph, playable
mini-level setup, and live visual demonstration metadata. -/
structure TutorialCard where
  id           : String
  index        : Nat
  dim          : WedgeDim
  title        : String
  headline     : String
  body         : String
  gestureGlyph : String -- "intro" | "pull-apart" | "push-together" | "add" | "hold-drag" | "spatial-two-hand"
  formula      : String
  miniLevel    : WedgeLevel
  deriving Repr, Inhabited

/-- All 6 canonical interactive Wedge tutorial cards (T1–T5 from enkimute's
`example_game_wedge.html`, plus T6 extending the gesture grammar to 3D `PGA3`). -/
def tutorialCards : Array TutorialCard :=
  let A0 := p2 (-1.0) 0.0
  let B0 := p2 1.0 0.5
  let a0 := l2 0.0 1.0 0.0
  let b0 := l2 1.0 (-0.5) 0.0
  let c0 := l2 1.0 0.5 0.0
  let AB0 := joinE A0 B0
  let a5 := l2 1.0 0.0 0.0
  let B5 := p2 0.0 1.0
  -- 3D tutorial tetrahedron apex + base
  let A3 := p3 (-1.0) (-0.4) 0.6
  let B3 := p3 1.0 (-0.4) 0.6
  let C3 := p3 0.0 (-0.4) (-1.0)
  let D3 := p3 0.15 1.15 0.1
  let basePl := joinE (joinE A3 B3) C3
  let alt3 := dotE basePl D3
  #[
    { id := "T1", index := 1, dim := .dim2D
      title := "T1 · Points & Lines"
      headline := "Wedge — The math game free of charge and coordinates."
      body := "Play Wedge by dragging WHITE points and lines to reconstruct every RED target element. GHOSTED elements are optional scaffolding hints. Try to solve each puzzle in as few moves and seconds as possible!"
      gestureGlyph := "intro"
      formula := "PGA2 = Cl(2, 0, 1): Points (e12) & Lines (e1, e2, e0)"
      miniLevel :=
        { number := 101, dim := .dim2D
          title := "T1 · Meet the Board"
          goal := "Pull the two white points apart to build the red line."
          tutorialText := "White = interactive, Red = target, Ghosted = hint."
          hintText := "Drag A left and B right to Join them (A & B)."
          givens := #[(A0, "A"), (B0, "B")]
          targets := #[(AB0, "A&B")] } },

    { id := "T2", index := 2, dim := .dim2D
      title := "T2 · Join by Pulling Apart"
      headline := "Drag points apart to JOIN them into a line."
      body := "In Projective Geometric Algebra, two points span a unique connecting line via the regressive Join operator (A & B). Grab two white points and pull them AWAY from each other."
      gestureGlyph := "pull-apart"
      formula := "L = A & B"
      miniLevel :=
        { number := 102, dim := .dim2D
          title := "T2 · Join Practice"
          goal := "Drag A and B apart to Join them into the red line."
          tutorialText := "Pulling two points apart computes their regressive Join (A & B)."
          hintText := "Drag A away from B and B away from A."
          givens := #[(A0, "A"), (B0, "B")]
          targets := #[(AB0, "A&B")] } },

    { id := "T3", index := 3, dim := .dim2D
      title := "T3 · Meet by Pushing Together"
      headline := "Drag lines together to MEET them in a point."
      body := "Dual to Join, two lines intersect via the exterior Wedge / Meet product (a ^ b). Grab two white lines and push them TOWARD each other to spawn their intersection point."
      gestureGlyph := "push-together"
      formula := "P = a ^ b"
      miniLevel :=
        { number := 103, dim := .dim2D
          title := "T3 · Meet Practice"
          goal := "Drag lines a and b together to Meet them in the red point."
          tutorialText := "Pushing two lines together computes their exterior Meet (a ^ b)."
          hintText := "Drag line a and line b toward one another."
          givens := #[(a0, "a"), (AB0, "b")]
          targets := #[(meetE a0 AB0, "a^b")] } },

    { id := "T4", index := 4, dim := .dim2D
      title := "T4 · Midpoint & Bisector Add"
      headline := "Drag points together (or lines apart) to ADD them."
      body := "You cannot Meet two points or Join two lines in 2D PGA — if you try, Wedge automatically upgrades the gesture to projective Addition (+)! Adding two normalized points gives their exact MIDPOINT (A + B); adding two lines gives their ANGLE BISECTOR (c + b)."
      gestureGlyph := "add"
      formula := "M = A + B  |  bis = c + b"
      miniLevel :=
        { number := 104, dim := .dim2D
          title := "T4 · Add Practice (Midpoint & Bisector)"
          goal := "Push points A & B together for their midpoint, and pull lines c & b apart for their angle bisector."
          tutorialText := "Same-grade Add (+) gives midpoints of points and angle bisectors of lines."
          hintText := "Push A & B toward each other → A + B; pull c & b apart → c + b."
          givens := #[(A0, "A"), (B0, "B"), (c0, "c"), (b0, "b")]
          targets := #[(addE A0 B0, "A+B"), (addE c0 b0, "c+b")] } },

    { id := "T5", index := 5, dim := .dim2D
      title := "T5 · Orthogonal Dot Projection"
      headline := "Hold a point in place and drag a line to it to DOT them."
      body := "Left contraction (a << B) constructs the unique line through point B perpendicular to line a! Lock point B (zero drag / hold gesture) and drag line a toward B."
      gestureGlyph := "hold-drag"
      formula := "L⊥ = a << B"
      miniLevel :=
        { number := 105, dim := .dim2D
          title := "T5 · Orthogonal Projection Practice"
          goal := "Hold point B fixed and drag line a toward B to create the perpendicular line."
          tutorialText := "Hold one element stationary and drag the other toward it to compute Dot (a << B)."
          hintText := "Lock B in place and drag line a toward B."
          givens := #[(a5, "a"), (B5, "B")]
          targets := #[(dotE a5 B5, "a<<B")] } },

    { id := "T6", index := 6, dim := .dim3D
      title := "T6 · Spatial Two-Hand Wedge 3D"
      headline := "Extend Join, Meet, Add & Dot seamlessly into 3D space!"
      body := "In 3D PGA = Cl(3, 0, 1), the exact same four gestures work on Points, Lines, and Planes — native to Web 3D drag and visionOS two-hand pinch! Pull apart (&): Point & Point → Line, Line & Point → Plane. Push together (^): Plane ^ Plane → Line, Plane ^ Line → Point. Hold + Drag (<<): Plane << Point → Altitude Line, Line << Point → Orthogonal Plane!"
      gestureGlyph := "spatial-two-hand"
      formula := "alt = (A & B & C) << D"
      miniLevel :=
        { number := 106, dim := .dim3D
          title := "T6 · 3D Spatial Altitude Practice"
          goal := "Hold apex D and drag the base plane toward D to drop the 3D perpendicular altitude."
          tutorialText := "In 3D PGA, holding point D and dragging plane P toward D computes P << D (the exact 3D altitude line!)."
          hintText := "Hold D stationary and drag plane ABC toward D."
          givens := #[(basePl, "ABC"), (D3, "D")]
          hints := #[(A3, "A"), (B3, "B"), (C3, "C")]
          targets := #[(alt3, "ABC<<D")] } }
  ]

/-- Look up a tutorial card by 0-based index (clamped). -/
def getTutorialCard (idx : Nat) : TutorialCard :=
  tutorialCards.getD (min idx (tutorialCards.size - 1)) tutorialCards[0]!

/-- Serialize all 6 tutorial cards to `Init`-only JSON for Web 3D & visionOS UI overlays. -/
def tutorialCardsJson : String :=
  Json.arrJson (tutorialCards.map fun c => Json.objJson #[
    ("id", Json.quote c.id),
    ("index", toString c.index),
    ("is3D", if c.dim == .dim3D then "true" else "false"),
    ("title", Json.quote c.title),
    ("headline", Json.quote c.headline),
    ("body", Json.quote c.body),
    ("gestureGlyph", Json.quote c.gestureGlyph),
    ("formula", Json.quote c.formula),
    ("goal", Json.quote c.miniLevel.goal),
    ("hint", Json.quote c.miniLevel.hintText)
  ])

/-! ## 2. Render Any `WedgeLevel` or `TutorialCard` Directly to an 8B-Aligned `SceneFrame` -/

private def pga2AlgebraMeta : AlgebraMeta :=
  { name := "PGA2", p := 2, q := 0, r := 1, conformalWitt := false
    basisNames := #["1", "e0", "e1", "e2", "e01", "e02", "e12", "e012"]
    basisMetric := #[1, 0, 1, 1, 0, 0, -1, 0] }

private def pga3AlgebraMeta : AlgebraMeta :=
  { name := "PGA3", p := 3, q := 0, r := 1, conformalWitt := false
    basisNames := #["1", "e0", "e1", "e2", "e3", "e01", "e02", "e03",
                    "e12", "e13", "e23", "e012", "e013", "e023", "e123", "e0123"]
    basisMetric := #[1, 0, 1, 1, 1, 0, 0, 0, -1, -1, -1, 0, 0, 0, -1, 0] }

/-- Construct an orthonormal tangent frame `(u, v)` perpendicular to unit normal `n`. -/
private def planeBasis (n : Vec3) : Vec3 × Vec3 :=
  let up : Vec3 := if Float.abs n.y < 0.9 then ⟨0.0, 1.0, 0.0⟩ else ⟨1.0, 0.0, 0.0⟩
  let u := Vec3.normalize (Vec3.cross up n)
  let v := Vec3.cross n u
  (u, v)

/-- Emit a canonical `SceneFrame` (`GSIR` v1) for any `WedgeLevel` (tutorial mini-level or
procedurally generated challenge), strictly `Init`-only! -/
def levelToSceneFrame (lvl : WedgeLevel) (seq : UInt64 := 0) (t : Float := 0.0)
    (extraGestureArrows : Array SegmentPrim := #[]) : SceneFrame := Id.run do
  let is2D := lvl.dim == .dim2D
  let mut pts : Array PointPrim := #[]
  let mut lines : Array LinePrim := #[]
  let mut planes : Array PlanePrim := #[]
  let segs : Array SegmentPrim := extraGestureArrows
  let mut insp : Array InspectEntry := #[]
  let mut nextId : UInt32 := 1
  let addElem (elem : PgaElem) (lbl : String) (role : WedgeRole)
      (pts : Array PointPrim) (lines : Array LinePrim) (planes : Array PlanePrim)
      (insp : Array InspectEntry) (hid : UInt32) :
      Array PointPrim × Array LinePrim × Array PlanePrim × Array InspectEntry :=
    let col : RGBA :=
      match role with
      | .given | .constructed => RGBA.white
      | .target => RGBA.coral
      | .hint   => RGBA.ghost
    let draggable := role == .given || role == .constructed
    let rp : RoleFlags :=
      { draggable, target := role == .target, hint := role == .hint }
    let st := insp.push { idx := hid, name := lbl, grade := UInt32.ofNat elem.grade,
                          formatted := elem.format, editable := false }
    match elem with
    | .pt2 x y =>
      (pts.push { handleId := hid, pos := ⟨x, y, 0.0⟩, radius := if role == .target then 0.09 else 0.075,
                  color := col, role := rp, label := lbl }, lines, planes, st)
    | .line2 a b c =>
      let orig : Vec3 := ⟨-c * a, -c * b, 0.0⟩
      let dir  : Vec3 := ⟨-b, a, 0.0⟩
      (pts, lines.push { handleId := hid, origin := orig, dir, clip := 4.5,
                         width := if role == .target then 3.0 else 2.2,
                         color := col, role := rp, label := lbl }, planes, st)
    | .pt3 p =>
      (pts.push { handleId := hid, pos := p, radius := if role == .target then 0.095 else 0.08,
                  color := col, role := rp, label := lbl }, lines, planes, st)
    | .line3 dir mom =>
      let orig := PgaElem.line3Origin dir mom
      (pts, lines.push { handleId := hid, origin := orig, dir, clip := 3.2,
                         width := if role == .target then 3.0 else 2.2,
                         color := col, role := rp, label := lbl }, planes, st)
    | .plane3 n d =>
      let orig := Vec3.scale (-d) n
      let (pu, pv) := planeBasis n
      let pCol : RGBA := { col with a := if role == .hint then 0.14 else if role == .target then 0.38 else 0.24 }
      (pts, lines, planes.push { handleId := hid, center := orig, u := pu, v := pv, extent := 1.45,
                                 color := pCol, role := rp, label := lbl }, st)
  for (e, lbl) in lvl.hints do
    let (p', l', pl', s') := addElem e lbl .hint pts lines planes insp nextId
    pts := p'; lines := l'; planes := pl'; insp := s'; nextId := nextId + 1
  for (e, lbl) in lvl.targets do
    let (p', l', pl', s') := addElem e lbl .target pts lines planes insp nextId
    pts := p'; lines := l'; planes := pl'; insp := s'; nextId := nextId + 1
  for (e, lbl) in lvl.givens do
    let (p', l', pl', s') := addElem e lbl .given pts lines planes insp nextId
    pts := p'; lines := l'; planes := pl'; insp := s'; nextId := nextId + 1
  { frameSeq := seq, simTime := t,
    mode := if is2D then .wedge2D else .wedge3D,
    is2D, gridEnabled := true, darkTheme := true, gridSize := 2.4,
    algebra := if is2D then pga2AlgebraMeta else pga3AlgebraMeta,
    presetId := if is2D then "wedge_2d" else "wedge_3d",
    title := lvl.title,
    camera :=
      if is2D then { motor := Motor3.translator 0.0 0.0 (-4.2), orthoScale := 1.0, isOrtho := true }
      else { motor := Motor3.orbitCamera (0.52 + 0.12 * Float.sin (t * 0.4)) (-0.34) 5.0, fovDeg := 45.0, distance := 5.0 },
    points := pts, lines := lines, planes := planes, segments := segs, inspect := insp,
    wedgeHud := some {
      level := lvl.number, totalLevels := 17, moves := 0, score := 1000,
      is3D := !is2D, solved := false,
      title := lvl.title, goal := lvl.goal,
      hintText := lvl.hintText, tutorialText := lvl.tutorialText
    } }

/-- Emit an animated demonstration `SceneFrame` for a `TutorialCard` (including animated
green gesture indicator segments showing pull-apart / push-together / hold-drag vectors!). -/
def tutorialToSceneFrame (card : TutorialCard) (seq : UInt64 := 0) (t : Float := 0.0) : SceneFrame :=
  let pulse := 0.15 + 0.35 * (0.5 + 0.5 * Float.sin (t * 2.4))
  let arrowRole : RoleFlags := { arrow := true }
  let arrows : Array SegmentPrim :=
    if card.miniLevel.givens.size ≥ 2 then
      let a := (card.miniLevel.givens[0]!.1).anchor
      let b := (card.miniLevel.givens[1]!.1).anchor
      let diff := Vec3.sub b a
      let axis := if Vec3.norm diff > 1e-4 then Vec3.normalize diff else ⟨1.0, 0.0, 0.0⟩
      match card.gestureGlyph with
      | "pull-apart" | "intro" =>
        #[ { a := a, b := Vec3.sub a (Vec3.scale pulse axis), width := 3.0, color := RGBA.green, role := arrowRole }
         , { a := b, b := Vec3.add b (Vec3.scale pulse axis), width := 3.0, color := RGBA.green, role := arrowRole } ]
      | "push-together" =>
        #[ { a := a, b := Vec3.add a (Vec3.scale pulse axis), width := 3.0, color := RGBA.green, role := arrowRole }
         , { a := b, b := Vec3.sub b (Vec3.scale pulse axis), width := 3.0, color := RGBA.green, role := arrowRole } ]
      | "hold-drag" | "spatial-two-hand" =>
        #[ { a := a, b := Vec3.add a (Vec3.scale (pulse * 1.1) axis), width := 3.2, color := RGBA.green, role := arrowRole } ]
      | _ =>
        #[ { a := a, b := Vec3.lerp a b (0.35 * pulse), width := 3.0, color := RGBA.green, role := arrowRole }
         , { a := b, b := Vec3.lerp b a (0.35 * pulse), width := 3.0, color := RGBA.green, role := arrowRole } ]
    else #[]
  let f := levelToSceneFrame card.miniLevel seq t arrows
  { f with
    title := card.title
    wedgeHud := f.wedgeHud.map fun h =>
      { h with tutorialText := s!"{card.headline} — {card.body}", goal := card.miniLevel.goal } }

/-! ## 3. Deterministic SplitMix64 Procedural Challenge Generator (2D & 3D) -/

/-- Pure deterministic SplitMix64 PRNG step returning `(nextSeed, rawUInt64)`. -/
private def splitmix64 (s : UInt64) : UInt64 × UInt64 :=
  let s1 := s + 0x9E3779B97F4A7C15
  let z1 := (s1 ^^^ (s1 >>> 30)) * 0xBF58476D1CE4E5B9
  let z2 := (z1 ^^^ (z1 >>> 27)) * 0x94D049BB133111EB
  let z3 := z2 ^^^ (z2 >>> 31)
  (s1, z3)

/-- Deterministic uniform `Float` in `[lo, hi]`. -/
private def randRange (s : UInt64) (lo hi : Float) : UInt64 × Float :=
  let (s1, r) := splitmix64 s
  -- Use upper 24 bits for exact IEEE-754 float mantissa mapping in [0, 1)
  let u := Float.ofNat ((r >>> 40).toNat) / 16777216.0
  (s1, lo + (hi - lo) * u)

/-- Sample a well-conditioned non-collinear 2D triangle `(A, B, C)` inside `[-1.5, 1.5]²`
with signed area `≥ 0.45` (guaranteed non-degenerate!). -/
private def sampleTriangle2D (seed : UInt64) : UInt64 × PgaElem × PgaElem × PgaElem := Id.run do
  let mut s := seed
  for _ in [:16] do
    let (s1, rA) := randRange s 0.9 1.55
    let (s2, thA) := randRange s1 0.0 6.283185307179586
    let (s3, dTh1) := randRange s2 1.45 2.45
    let (s4, dTh2) := randRange s3 1.45 2.45
    let (s5, rB) := randRange s4 0.85 1.55
    let (s6, rC) := randRange s5 0.85 1.55
    let (s7, ox) := randRange s6 (-0.25) 0.25
    let (s8, oy) := randRange s7 (-0.25) 0.25
    s := s8
    let ax := ox + rA * Float.cos thA; let ay := oy + rA * Float.sin thA
    let bx := ox + rB * Float.cos (thA + dTh1); let by_ := oy + rB * Float.sin (thA + dTh1)
    let cx := ox + rC * Float.cos (thA + dTh1 + dTh2); let cy := oy + rC * Float.sin (thA + dTh1 + dTh2)
    let area2 := Float.abs ((bx - ax) * (cy - ay) - (by_ - ay) * (cx - ax))
    if area2 > 0.9 then
      return (s, p2 ax ay, p2 bx by_, p2 cx cy)
  return (s, p2 (-0.9) (-0.8), p2 1.2 (-0.5), p2 0.1 1.2)

/-- Sample a well-conditioned non-coplanar 3D tetrahedron `(A, B, C, D)` inside `[-1.4, 1.4]³`
with `|det(B-A, C-A, D-A)| > 0.9` (guaranteed well-conditioned circumcenter & Monge point!). -/
private def sampleTetra3D (seed : UInt64) : UInt64 × PgaElem × PgaElem × PgaElem × PgaElem := Id.run do
  let mut s := seed
  -- Start from regular tetrahedron vertices and perturb deterministically
  let base : Array Vec3 :=
    #[ ⟨0.95, 0.85, 0.75⟩, ⟨-0.95, 0.65, 0.80⟩, ⟨0.35, -0.95, 0.70⟩, ⟨-0.25, -0.25, -1.15⟩ ]
  for _ in [:12] do
    let mut pts : Array Vec3 := #[]
    for v in base do
      let (s1, dx) := randRange s (-0.32) 0.32
      let (s2, dy) := randRange s1 (-0.32) 0.32
      let (s3, dz) := randRange s2 (-0.32) 0.32
      s := s3
      pts := pts.push ⟨v.x + dx, v.y + dy, v.z + dz⟩
    let a := pts[0]!; let b := pts[1]!; let c := pts[2]!; let d := pts[3]!
    let vol6 := Float.abs (Vec3.dot (Vec3.sub b a) (Vec3.cross (Vec3.sub c a) (Vec3.sub d a)))
    if vol6 > 0.9 then
      return (s, .pt3 a, .pt3 b, .pt3 c, .pt3 d)
  return (s, p3 1.0 0.8 0.6, p3 (-1.0) 0.6 0.8, p3 0.4 (-1.0) 0.6, p3 (-0.2) (-0.2) (-1.2))

/-- Generate an infinite stream of deterministic, guaranteed-solvable Wedge 2D or 3D
procedural puzzles from `(seed, dim, difficulty)` (`difficulty`: `0`=Easy, `1`=Medium, `2`=Hard). -/
def generateChallenge (seed : UInt64) (dim : WedgeDim := .dim2D) (difficulty : Nat := 1) :
    WedgeLevel :=
  let (s1, variantRaw) := splitmix64 (seed ^^^ 0x517CC1B727220A95)
  let variant := (variantRaw % 4).toNat
  let seedTag : UInt32 := (seed % 1000).toUInt32
  match dim with
  | .dim2D =>
    let (s2, A, B, C) := sampleTriangle2D s1
    let (_, dX) := randRange s2 (-1.2) 1.2
    let D := p2 dX (-1.05)
    let eAB := joinE A B
    let eBC := joinE B C
    let eCA := joinE C A
    let midAB := addE A B
    let midBC := addE B C
    let altC := dotE eAB C
    let altA := dotE eBC A
    let ortho := meetE altC altA
    let bisAB := dotE eAB midAB
    let bisBC := dotE eBC midBC
    let circum := meetE bisAB bisBC
    match difficulty with
    | 0 =>
      match variant % 2 with
      | 0 =>
        let medC := joinE midAB C
        { number := 200 + seedTag, dim := .dim2D
          title := s!"Challenge 2D #{seedTag} · Triangle Median"
          goal := "Construct the median from vertex C to the midpoint of AB."
          tutorialText := "Procedural Easy (2 moves): Add A & B for their midpoint, then Join it with C."
          hintText := "Push A & B together → A+B; pull (A+B) & C apart → (A+B)&C."
          givens := #[(A, "A"), (B, "B"), (C, "C")]
          hints := #[(midAB, "A+B")]
          targets := #[(medC, "(A+B)&C")] }
      | _ =>
        let chord1 := joinE A C
        let chord2 := joinE B D
        let xPt := meetE chord1 chord2
        { number := 200 + seedTag, dim := .dim2D
          title := s!"Challenge 2D #{seedTag} · Diagonal Meet"
          goal := "Join diagonals AC and BD, then Meet them at the red intersection point."
          tutorialText := "Procedural Easy (3 moves): Two Joins followed by one Meet."
          hintText := "Pull A&C apart, pull B&D apart, then push both lines together!"
          givens := #[(A, "A"), (B, "B"), (C, "C"), (D, "D")]
          hints := #[(chord1, "A&C")]
          targets := #[(xPt, "(A&C)^(B&D)")] }
    | 1 =>
      match variant % 3 with
      | 0 =>
        let foot := meetE eAB altC
        { number := 300 + seedTag, dim := .dim2D
          title := s!"Challenge 2D #{seedTag} · Foot of Altitude"
          goal := "Drop the perpendicular from C onto line AB and find its foot on AB."
          tutorialText := "Procedural Medium (3 moves): Join A&B, Dot with C, then Meet with A&B."
          hintText := "A&B → (A&B)<<C → ((A&B)<<C)^(A&B)."
          givens := #[(A, "A"), (B, "B"), (C, "C")]
          hints := #[(eAB, "A&B"), (altC, "(A&B)<<C")]
          targets := #[(foot, "foot")] }
      | 1 =>
        { number := 300 + seedTag, dim := .dim2D
          title := s!"Challenge 2D #{seedTag} · Perpendicular Bisector"
          goal := "Construct the perpendicular bisector of segment AB."
          tutorialText := "Procedural Medium (3 moves): Join A&B, Add A+B, then Dot (A&B)<<(A+B)."
          hintText := "Pull A&B apart, push A&B together, hold A+B and drag A&B to it."
          givens := #[(A, "A"), (B, "B")]
          hints := #[(midAB, "A+B")]
          targets := #[(bisAB, "(A&B)<<(A+B)")] }
      | _ =>
        let centroid := meetE (joinE midAB C) (joinE midBC A)
        { number := 300 + seedTag, dim := .dim2D
          title := s!"Challenge 2D #{seedTag} · Centroid"
          goal := "Construct the Centroid (center of mass) of triangle ABC."
          tutorialText := "Procedural Medium (5 moves): Meet two medians (A+B)&C and (B+C)&A."
          hintText := "Build midpoints A+B and B+C, join to opposite vertices, and meet them."
          givens := #[(A, "A"), (B, "B"), (C, "C")]
          hints := #[(midAB, "A+B"), (joinE midAB C, "medC")]
          targets := #[(centroid, "G")] }
    | _ =>
      match variant % 3 with
      | 0 =>
        { number := 400 + seedTag, dim := .dim2D
          title := s!"Challenge 2D #{seedTag} · Random Orthocenter"
          goal := "Construct the Orthocenter of this randomized triangle ABC."
          tutorialText := "Procedural Hard (5 moves): Meet two altitudes ((A&B)<<C) ^ ((B&C)<<A)."
          hintText := "Join two sides, dot each with its opposite vertex, and meet the two altitudes."
          givens := #[(A, "A"), (B, "B"), (C, "C")]
          hints := #[(eAB, "A&B"), (altC, "altC")]
          targets := #[(ortho, "H")] }
      | 1 =>
        let ninePt := addE ortho circum
        { number := 400 + seedTag, dim := .dim2D
          title := s!"Challenge 2D #{seedTag} · Nine-Point Center"
          goal := "Construct the Nine-Point Center N = H + O (midpoint of Orthocenter & Circumcenter)!"
          tutorialText := "Procedural Hard: Build Orthocenter H and Circumcenter O, then push H & O together to Add them!"
          hintText := "N is the exact projective sum H + O on Euler's line!"
          givens := #[(A, "A"), (B, "B"), (C, "C")]
          hints := #[(ortho, "H"), (circum, "O"), (eCA, "C&A")]
          targets := #[(ninePt, "N=H+O")] }
      | _ =>
        let euler := joinE ortho circum
        { number := 400 + seedTag, dim := .dim2D
          title := s!"Challenge 2D #{seedTag} · Random Euler's Line"
          goal := "Construct Euler's Line joining the Orthocenter and Circumcenter of ABC."
          tutorialText := "Procedural Hard: Pull Orthocenter H and Circumcenter O apart to reveal Euler's Line!"
          hintText := "Build H and O, then Join H & O."
          givens := #[(A, "A"), (B, "B"), (C, "C")]
          hints := #[(ortho, "H"), (circum, "O")]
          targets := #[(euler, "Euler")] }
  | .dim3D =>
    let (_, A, B, C, D) := sampleTetra3D s1
    let lAB := joinE A B
    let lAC := joinE A C
    let lAD := joinE A D
    let lCD := joinE C D
    let lBD := joinE B D
    let basePl := joinE lAB C
    let altD := dotE basePl D
    let pbAB := dotE lAB (addE A B)
    let pbAC := dotE lAC (addE A C)
    let pbAD := dotE lAD (addE A D)
    match difficulty with
    | 0 =>
      match variant % 2 with
      | 0 =>
        { number := 500 + seedTag, dim := .dim3D
          title := s!"Challenge 3D #{seedTag} · Span Plane"
          goal := "Join three spatial points A, B, C into the red plane ABC."
          tutorialText := "Procedural 3D Easy (2 moves): Pull A & B apart → line, then pull line & C apart → plane."
          hintText := "(A & B) & C."
          givens := #[(A, "A"), (B, "B"), (C, "C")]
          hints := #[(lAB, "A&B")]
          targets := #[(basePl, "A&B&C")] }
      | _ =>
        let pA := pl3 1.0 0.15 (-0.1) (-0.35)
        let pB := pl3 (-0.1) 1.0 0.2 (-0.25)
        let pC := pl3 0.2 (-0.15) 1.0 (-0.45)
        let vtx := meetE (meetE pA pB) pC
        { number := 500 + seedTag, dim := .dim3D
          title := s!"Challenge 3D #{seedTag} · Trihedral Vertex"
          goal := "Meet the three planes P1, P2, P3 to pinpoint their 3D vertex."
          tutorialText := "Procedural 3D Easy (2 moves): Push P1 & P2 together → crease line, then push with P3 → point."
          hintText := "(P1 ^ P2) ^ P3."
          givens := #[(pA, "P1"), (pB, "P2"), (pC, "P3")]
          hints := #[(meetE pA pB, "P1^P2")]
          targets := #[(vtx, "V")] }
    | 1 =>
      match variant % 2 with
      | 0 =>
        let foot3 := meetE basePl altD
        { number := 600 + seedTag, dim := .dim3D
          title := s!"Challenge 3D #{seedTag} · 3D Foot of Altitude"
          goal := "Drop the altitude from D onto plane ABC and find its foot on the base plane."
          tutorialText := "Procedural 3D Medium (4 moves): Build base plane A&B&C, Dot with D, then Meet altitude with base."
          hintText := "((A&B&C)<<D) ^ (A&B&C)."
          givens := #[(A, "A"), (B, "B"), (C, "C"), (D, "D")]
          hints := #[(basePl, "ABC"), (altD, "altD")]
          targets := #[(foot3, "Foot3D")] }
      | _ =>
        { number := 600 + seedTag, dim := .dim3D
          title := s!"Challenge 3D #{seedTag} · 3D Bisector Plane"
          goal := "Construct the perpendicular bisector plane of spatial points A and B."
          tutorialText := "Procedural 3D Medium (3 moves): Join A&B, Add A+B, then Dot (A&B) << (A+B)."
          hintText := "Hold midpoint A+B and drag line A&B toward it."
          givens := #[(A, "A"), (B, "B")]
          hints := #[(lAB, "A&B"), (addE A B, "A+B")]
          targets := #[(pbAB, "PerpBis")] }
    | _ =>
      match variant % 2 with
      | 0 =>
        let circum3 := meetE (meetE pbAB pbAC) pbAD
        { number := 700 + seedTag, dim := .dim3D
          title := s!"Challenge 3D #{seedTag} · Random Tet Circumcenter"
          goal := "Construct the 3D Circumcenter of this randomized tetrahedron ABCD."
          tutorialText := "Procedural 3D Hard: Meet three perpendicular bisector planes of edges AB, AC, AD."
          hintText := "Build perp-bisector planes pbAB, pbAC, pbAD and meet all three!"
          givens := #[(A, "A"), (B, "B"), (C, "C"), (D, "D")]
          hints := #[(pbAB, "pbAB")]
          targets := #[(circum3, "O3D")] }
      | _ =>
        let mp1 := dotE lCD (addE A B)
        let mp2 := dotE lBD (addE A C)
        let mp3 := dotE lAB (addE C D)
        let monge3 := meetE (meetE mp1 mp2) mp3
        { number := 700 + seedTag, dim := .dim3D
          title := s!"Challenge 3D #{seedTag} · Random 3D Monge Point"
          goal := "Construct the 3D Monge Point where all 6 opposite-edge midpoint orthogonal planes concur!"
          tutorialText := "Procedural 3D Hard: Meet three Monge planes (CD<<(A+B)), (BD<<(A+C)), (AB<<(C+D))."
          hintText := "Hold midpoint of an edge and drag the opposite edge line to it!"
          givens := #[(A, "A"), (B, "B"), (C, "C"), (D, "D")]
          hints := #[(mp1, "M1")]
          targets := #[(monge3, "Monge3D")] }

end Grassmann.Wedge.Tutorials
