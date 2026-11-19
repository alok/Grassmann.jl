import Grassmann.Wedge.Types
import Grassmann.Wedge.Levels2D
import Grassmann.Wedge.Levels3D
import Grassmann.Wedge.Tutorials
import Grassmann.Eval.Engine

/-!
# Pure-Lean Wedge Game State Machine, Gesture Classifier & `SceneIR` Emitter

Implements the exact coordinate-free 2-element drag gesture grammar from
`example_game_wedge.html` lifted uniformly to both 2D PGA (`Cl(2,0,1)`) and
3D PGA (`Cl(3,0,1)`), with:
- Lean-derived `hold` threshold (`‖dir‖ < 0.1` OR explicit spatial hold bit)
- Live `isPreview` ghost computation without mutating `moves` or `items`
- Projective win detection (`PgaElem.approxEq`)
- Scoring (`max 0 (1000 - elapsedSec - moves * 10)`), undo stack, hints, and full `SceneFrame` output!
-/

namespace Grassmann.Wedge

open Grassmann.Scene Grassmann.Eval

/-- Populate a playable `WedgeState` from any `WedgeLevel` (campaign, tutorial card, or
procedural challenge). -/
def loadCustomLevel (lvl : WedgeLevel) (levelIdx : Nat := 0) (isCustom : Bool := true)
    (tutorialGlyph : String := "") (tutorialCopy : String := "") : WedgeState :=
  let rec pushList (xs : Array (PgaElem × String)) (role : WedgeRole)
      (nextId : UInt32) (acc : Array BoardItem) : Array BoardItem × UInt32 :=
    xs.foldl (init := (acc, nextId)) fun (a, nid) (el, lbl) =>
      (a.push { id := nid, role, elem := el, label := lbl }, nid + 1)
  let (it1, id1) := pushList lvl.targets .target 1 #[]
  let (it2, id2) := pushList lvl.hints .hint id1 it1
  let (it3, id3) := pushList lvl.givens .given id2 it2
  { dim := lvl.dim, levelIdx,
    customLevel := if isCustom then some lvl else none,
    tutorialGlyph, tutorialCopy,
    items := it3, nextId := id3,
    moves := 0, elapsedSec := 0.0, timerStarted := false,
    lastOp := "", previewOp := "", previewElem := none,
    selectedIds := #[], showHints := true, solved := false, undoStack := #[] }

/-- Load a specific level index (0-based into `allLevels`, clamped). -/
def loadLevel (idx : Nat) : WedgeState :=
  let clamped := if allLevels.isEmpty then 0 else min idx (allLevels.size - 1)
  loadCustomLevel allLevels[clamped]! clamped false

/-- Load one of the 6 canonical Wedge tutorial cards (`"T1"`..`"T6"`) as a playable board
with animated green gesture indicator arrows. -/
def loadTutorial (id : String) : WedgeState :=
  let card :=
    (Tutorials.tutorialCards.find? fun c => c.id == id).getD (Tutorials.getTutorialCard 0)
  let copy := s!"{card.headline} — {card.body}"
  loadCustomLevel card.miniLevel 0 true card.gestureGlyph copy

/-- Generate and load a deterministic SplitMix64 procedural 2D or 3D Wedge challenge. -/
def loadRandomChallenge (is3D : Bool) (difficulty : Nat) (seed : UInt64) : WedgeState :=
  let dim : WedgeDim := if is3D then .dim3D else .dim2D
  let lvl := Tutorials.generateChallenge seed dim (min 2 difficulty)
  loadCustomLevel lvl 0 true

/-- Initial state for Wedge 2D (Level 1) or Wedge 3D (Level 10). -/
def initState (start3D : Bool := false) : WedgeState :=
  loadLevel (if start3D then levels2D.size else 0)

/-- Canonical separation axis pointing from `elB` toward `elA`.
Uses `anchorA - anchorB` when anchors are distinct, falling back to the normal difference
`nA - nB` when two lines/planes share the same anchor (e.g. passing through the origin). -/
def separationAxis (elA elB : PgaElem) : Vec3 :=
  let ab := Vec3.sub elA.anchor elB.anchor
  let abLen := Vec3.norm ab
  if abLen ≥ 1e-6 then Vec3.scale (1.0 / abLen) ab
  else
    let normalOf : PgaElem → Vec3
      | .line2 a b _  => ⟨a, b, 0.0⟩
      | .plane3 n _   => n
      | .line3 d _    => d
      | _             => ⟨1.0, 0.0, 0.0⟩
    let dn := Vec3.sub (normalOf elA) (normalOf elB)
    if Vec3.norm dn ≥ 1e-6 then Vec3.normalize dn else ⟨1.0, 0.0, 0.0⟩

/-- Classify a 2-element gesture strictly in Lean (matching `example_game_wedge.html:114-133`
and lifting seamlessly to 3D PGA).
Returns `some (opName, resultingElem)` or `none` if invalid/ambiguous. -/
def classifyGesture (elA elB : PgaElem) (dirA dirB : Vec3)
    (holdHintA holdHintB : Bool) : Option (String × PgaElem) :=
  let lenA := Vec3.norm dirA
  let lenB := Vec3.norm dirB
  -- Lean owns the hold threshold (`< 0.1`), honoring explicit spatial pinch-hold too
  let holdA := holdHintA || lenA < 0.1
  let holdB := holdHintB || lenB < 0.1
  let uAB := separationAxis elA elB
  let cosA := if holdA then 0.0 else Vec3.dot (Vec3.neg uAB) (Vec3.scale (1.0 / lenA) dirA)
  let cosB := if holdB then 0.0 else Vec3.dot uAB (Vec3.scale (1.0 / lenB) dirB)
  let aOut := !holdA && cosA < 0.0
  let bOut := !holdB && cosB < 0.0
  let aIn  := !holdA && cosA > 0.0
  let bIn  := !holdB && cosB > 0.0
  if aOut && bOut then
    match PgaElem.join elA elB with
    | some r => some ("join", r)
    | none   => (PgaElem.addSameGrade elA elB).map fun r => ("add", r)
  else if aIn && bIn then
    match PgaElem.meet elA elB with
    | some r => some ("wedge", r)
    | none   => (PgaElem.addSameGrade elA elB).map fun r => ("add", r)
  else if holdA && bIn then
    (PgaElem.dotProject elB elA).map fun r => ("dot", r)
  else if holdB && aIn then
    (PgaElem.dotProject elA elB).map fun r => ("dot", r)
  else
    none

/-- Check if all red target elements on the current board have been projectively reconstructed
by white player-created (or given) elements. -/
def checkSolved (items : Array BoardItem) : Bool :=
  let targets := items.filter fun it => it.role == .target
  let actives := items.filter fun it => it.role == .constructed
  !targets.isEmpty &&
    targets.all fun tgt => actives.any fun act => PgaElem.approxEq tgt.elem act.elem

/-- Compute current score `max 0 (1000 - floor(elapsed) - moves * 10)`. -/
def currentScore (st : WedgeState) : UInt32 :=
  let penalty := st.elapsedSec.toUInt32 + st.moves * 10
  if penalty ≥ 1000 then 0 else 1000 - penalty

/-- Find an interactive (white) board element by `handleId`. -/
private def findActive? (items : Array BoardItem) (id : UInt32) : Option BoardItem :=
  items.find? fun it => it.id == id && (it.role == .given || it.role == .constructed)

/-- Advance simulation clock during active play. -/
def stepTick (st : WedgeState) (dt : Float) : WedgeState :=
  if st.timerStarted && !st.solved then
    { st with elapsedSec := st.elapsedSec + max 0.0 (min 0.25 dt) }
  else st

/-- Apply a 2-element gesture (either `isPreview = true` for live non-mutating ghost feedback,
or `isPreview = false` to commit the move). -/
def stepGesture (st : WedgeState) (idA idB : UInt32) (dirA dirB : Vec3)
    (holdA holdB isPreview : Bool) : WedgeState :=
  if idA == idB then
    { st with previewOp := "", previewElem := none, selectedIds := #[idA] }
  else
    match findActive? st.items idA, findActive? st.items idB with
    | some itemA, some itemB =>
      match classifyGesture itemA.elem itemB.elem dirA dirB holdA holdB with
      | none =>
        if isPreview then
          { st with previewOp := "", previewElem := none, selectedIds := #[idA, idB] }
        else
          { st with lastOp := "invalid", previewOp := "", previewElem := none, selectedIds := #[] }
      | some (opName, resultElem) =>
        if isPreview then
          { st with previewOp := opName, previewElem := some resultElem, selectedIds := #[idA, idB] }
        else
          let newItem : BoardItem :=
            { id := st.nextId, role := .constructed, elem := resultElem,
              label := s!"{opName}#{st.moves + 1}" }
          let nextItems := st.items.push newItem
          let solvedNow := checkSolved nextItems
          { st with
            undoStack    := st.undoStack.push (st.items, st.moves)
            items        := nextItems
            nextId       := st.nextId + 1
            moves        := st.moves + 1
            timerStarted := true
            lastOp       := if solvedNow then "win" else opName
            previewOp    := ""
            previewElem  := none
            selectedIds  := #[]
            solved       := solvedNow }
    | _, _ =>
      { st with previewOp := "", previewElem := none, selectedIds := #[] }

/-- Apply a Wedge UI control action (`undo`, `reset`, `next`, `prev`, `toggle3D`, `hint`, `gotoLevel`). -/
def stepAction (st : WedgeState) (act : WedgeActionKind) (arg : UInt32 := 0) : WedgeState :=
  match act with
  | .undo =>
    if h : 0 < st.undoStack.size then
      let (prevItems, prevMoves) := st.undoStack[st.undoStack.size - 1]
      { st with
        items := prevItems, moves := prevMoves,
        undoStack := st.undoStack.pop,
        solved := checkSolved prevItems, lastOp := "undo",
        previewOp := "", previewElem := none, selectedIds := #[] }
    else st
  | .reset =>
    match st.customLevel with
    | some lvl => loadCustomLevel lvl st.levelIdx true st.tutorialGlyph st.tutorialCopy
    | none     => loadLevel st.levelIdx
  | .next  => loadLevel (min (allLevels.size - 1) (st.levelIdx + 1))
  | .prev  => loadLevel (if st.levelIdx > 0 then st.levelIdx - 1 else 0)
  | .toggle3D =>
    if st.dim == .dim2D then loadLevel levels2D.size else loadLevel 0
  | .hint => { st with showHints := !st.showHints }
  | .gotoLevel =>
    let idx := if arg > 0 then (arg - 1).toNat else 0
    loadLevel idx

/-! ## `SceneFrame` Projection (Pure-Lean Rendering Output) -/

private def roleColor (role : WedgeRole) (isSelected : Bool) : RGBA :=
  if isSelected then RGBA.green
  else match role with
  | .given       => RGBA.white
  | .constructed => ⟨0.88, 0.96, 1.0, 1.0⟩
  | .target      => RGBA.coral
  | .hint        => RGBA.ghost

private def pushElemToFrame (f : SceneFrame) (id : UInt32) (role : WedgeRole)
    (isSelected isPreviewGhost : Bool) (label : String) (el : PgaElem) : SceneFrame :=
  let col := if isPreviewGhost then ⟨0.32, 0.95, 0.62, 0.65⟩ else roleColor role isSelected
  let rf : RoleFlags :=
    { draggable := !isPreviewGhost && (role == .given || role == .constructed)
      selected  := isSelected
      target    := role == .target
      hint      := role == .hint || isPreviewGhost
      dashed    := role == .hint || isPreviewGhost }
  match el with
  | .pt2 x y =>
    { f with points := f.points.push {
        handleId := id, pos := ⟨x, y, 0.0⟩,
        radius := if role == .target then 0.11 else 0.095,
        color := col, role := rf, label } }
  | .line2 a b c =>
    let orig : Vec3 := ⟨-c * a, -c * b, 0.0⟩
    let dir : Vec3 := ⟨-b, a, 0.0⟩
    { f with lines := f.lines.push {
        origin := orig, dir, clip := 3.6,
        width := if role == .target then 3.2 else 2.4,
        color := col, handleId := id, role := rf, label } }
  | .pt3 p =>
    { f with points := f.points.push {
        handleId := id, pos := p,
        radius := if role == .target then 0.11 else 0.09,
        color := col, role := rf, label } }
  | .line3 dir mom =>
    let orig := PgaElem.line3Origin dir mom
    { f with lines := f.lines.push {
        origin := orig, dir, clip := 3.2,
        width := if role == .target then 3.2 else 2.4,
        color := col, handleId := id, role := rf, label } }
  | .plane3 n d =>
    let center := Vec3.scale (-d) n
    let (u, v) := Vec3.orthonormalBasis n
    let alpha := if isPreviewGhost then 0.28 else if role == .target then 0.34 else if role == .hint then 0.12 else 0.22
    { f with planes := f.planes.push {
        center, u, v, extent := 1.9,
        color := ⟨col.r, col.g, col.b, alpha⟩,
        gridLines := true, handleId := id, role := rf, label } }

/-- Crisp KaTeX `formula` and 1-sentence `summary` for every Wedge 2D/3D campaign level,
tutorial card, and procedural challenge. -/
private def wedgeMathMeta (lvl : WedgeLevel) (is3D : Bool) : String × String :=
  match lvl.number.toNat with
  | 1  => ("L = A \\vee B \\in \\mathrm{Cl}_{2,0,1}",
           "Regressive join (pull apart) spans the unique 2D PGA line passing through points A and B.")
  | 2  => ("P = a \\wedge b \\in \\mathrm{Cl}_{2,0,1}",
           "Exterior meet (push together) computes the exact projective intersection point of two 2D lines.")
  | 3  => ("M = \\frac{A + B}{\\|A + B\\|} \\in \\mathrm{Cl}_{2,0,1}",
           "Normalized projective addition of two same-weight PGA points yields their exact Euclidean midpoint.")
  | 4  => ("\\ell = \\frac{c + b}{\\|c + b\\|} \\in \\mathrm{Cl}_{2,0,1}",
           "Normalized addition of two unit 2D PGA lines constructs their exact Euclidean angle bisector.")
  | 5  => ("\\ell_\\perp = a \\rfloor B \\in \\mathrm{Cl}_{2,0,1}",
           "Left contraction (hold B, drag a toward B) drops the line through B orthogonal to line a.")
  | 6  => ("\\ell_\\perp = a \\rfloor B,\\qquad \\ell_{45^\\circ} = a + (a \\rfloor B)",
           "Combines orthogonal contraction and projective line addition to construct a 45-degree bisector without coordinates.")
  | 7  => ("H = ((A \\vee B) \\rfloor C) \\wedge ((B \\vee C) \\rfloor A)",
           "Constructs the triangle orthocenter as the exterior meet of two coordinate-free PGA altitudes.")
  | 8  => ("O = ((A \\vee B) \\rfloor (A+B)) \\wedge ((B \\vee C) \\rfloor (B+C))",
           "Constructs the circumcenter as the meet of perpendicular bisectors built from midpoints and contractions.")
  | 9  => ("\\ell_{\\text{Euler}} = H \\vee O",
           "Proves Euler's theorem in 2D PGA by joining the orthocenter and circumcenter into Euler's line.")
  | 10 => ("\\Pi = (A \\vee B) \\vee C \\in \\mathrm{Cl}_{3,0,1}",
           "3D regressive join lifts two points to a Plücker line and joins a third point to span their plane.")
  | 11 => ("P = (\\Pi_1 \\wedge \\Pi_2) \\wedge \\Pi_3 \\in \\mathrm{Cl}_{3,0,1}",
           "3D exterior meet intersects two planes into a line and meets a third plane to find their corner vertex.")
  | 12 => ("\\Pi_{\\text{bis}} = \\frac{\\Pi_1 + \\Pi_2}{\\|\\Pi_1 + \\Pi_2\\|}",
           "Same-grade addition of two normalized 3D PGA planes yields their exact dihedral angle bisector plane.")
  | 13 => ("\\Pi_{\\perp} = (A \\vee B) \\rfloor (A + B)",
           "Contracts the joining line onto the midpoint to construct the 3D perpendicular bisector plane of segment AB.")
  | 14 => ("L_{\\perp} = (A \\vee B \\vee C) \\rfloor D",
           "Drops the exact 3D altitude line from apex D orthogonal to the base plane spanned by A, B, and C.")
  | 15 => ("O = \\Pi_{\\perp}(AB) \\wedge \\Pi_{\\perp}(AC) \\wedge \\Pi_{\\perp}(AD)",
           "Finds the tetrahedron circumcenter as the triple meet of three perpendicular bisector planes in PGA3.")
  | 16 => ("M = ((C \\vee D)\\rfloor(A+B)) \\wedge ((B \\vee D)\\rfloor(A+C)) \\wedge ((A \\vee B)\\rfloor(C+D))",
           "Constructs the 3D Monge point where planes through edge midpoints perpendicular to opposite edges concur.")
  | _  =>
    if is3D then
      ("A \\vee B,\\quad \\Pi_1 \\wedge \\Pi_2,\\quad X \\rfloor Y \\in \\mathrm{Cl}_{3,0,1}",
       if lvl.goal.isEmpty then "Coordinate-free 3D PGA construction using join, meet, addition, and orthogonal contraction." else lvl.goal)
    else
      ("A \\vee B,\\quad a \\wedge b,\\quad a \\rfloor B \\in \\mathrm{Cl}_{2,0,1}",
       if lvl.goal.isEmpty then "Coordinate-free 2D PGA construction using join, meet, addition, and orthogonal contraction." else lvl.goal)

/-- Emit the complete `SceneFrame` + `WedgeHudState` for the current Wedge board
(supporting campaign levels 1–16, animated tutorial cards T1–T6, and procedural challenges). -/
def toSceneFrame (st : WedgeState) (frameSeq : UInt64 := 0) (simTime : Float := 0.0) :
    SceneFrame := Id.run do
  let lvl := st.customLevel.getD (allLevels[min st.levelIdx (allLevels.size - 1)]!)
  let is3D := st.dim == .dim3D
  let (algName, V, p, q, r, witt) := resolveAlgebra (if is3D then "PGA3" else "PGA2")
  let (wFormula, wSummary) := wedgeMathMeta lvl is3D
  let mut f : SceneFrame :=
    { frameSeq, simTime,
      mode := if is3D then .wedge3D else .wedge2D,
      is2D := !is3D,
      gridEnabled := true,
      darkTheme := true,
      gridSize := 2.4,
      algebra := algebraMetaOf algName V p q r witt,
      presetId := s!"wedge_level_{lvl.number}",
      title := lvl.title,
      formula := wFormula,
      summary := wSummary,
      camera :=
        if is3D then { motor := Motor3.orbitCamera 0.55 (-0.34) 5.4, fovDeg := 45.0, distance := 5.4 }
        else { motor := Motor3.translator 0.0 0.0 (-4.2), orthoScale := 1.0, isOrtho := true } }
  -- Animated green gesture indicator arrows for Tutorial Cards (while untouched)
  if !st.tutorialGlyph.isEmpty && st.moves == 0 && !st.solved && lvl.givens.size ≥ 2 then
    let pulse := 0.15 + 0.35 * (0.5 + 0.5 * Float.sin (simTime * 2.4))
    let arrowRole : RoleFlags := { arrow := true }
    let a := (lvl.givens[0]!.1).anchor
    let b := (lvl.givens[1]!.1).anchor
    let diff := Vec3.sub b a
    let axis := if Vec3.norm diff > 1e-4 then Vec3.normalize diff else ⟨1.0, 0.0, 0.0⟩
    let arrows : Array SegmentPrim :=
      match st.tutorialGlyph with
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
    f := { f with segments := f.segments ++ arrows }
  let mut inspectIdx : UInt32 := 0
  for it in st.items do
    if it.role != .hint || st.showHints then
      let isSel := st.selectedIds.contains it.id
      f := pushElemToFrame f it.id it.role isSel false it.label it.elem
      if it.role != .hint then
        f := { f with inspect := f.inspect.push {
          idx := inspectIdx, name := if it.label.isEmpty then s!"#{it.id}" else it.label,
          grade := it.elem.grade.toUInt32, formatted := it.elem.format, editable := false } }
        inspectIdx := inspectIdx + 1
  if let some ghost := st.previewElem then
    f := pushElemToFrame f 0 .hint false true s!"preview:{st.previewOp}" ghost
  let tutText := if st.tutorialCopy.isEmpty then lvl.tutorialText else st.tutorialCopy
  let hud : WedgeHudState :=
    { is3D, level := lvl.number, totalLevels := allLevels.size.toUInt32,
      title := lvl.title, goal := lvl.goal, tutorialText := tutText,
      moves := st.moves, score := currentScore st,
      elapsedMs := (st.elapsedSec * 1000.0).toUInt32,
      lastOp := st.lastOp, previewOp := st.previewOp,
      hintText := lvl.hintText, solved := st.solved,
      canUndo := !st.undoStack.isEmpty }
  return { f with wedgeHud := some hud }

end Grassmann.Wedge
