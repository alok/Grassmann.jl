/-
  Grassmann/CABI/Studio.lean — Init-only GSIR v1 Stateful Studio Session Engine

  Backs the canonical C ABI (`grassmann_studio_{create,destroy,dispatch_bin,
  dispatch_json,get_frame}`) for native macOS/visionOS dylibs, Emscripten WASM,
  and `lake exe ga-server`.

  Strictly `Init`-only (ZERO `Lean.*`, ZERO `Std.*`). All GA math, mesh generation,
  PGA3 plane slicing, contour projection, surface meshing, and Wedge gesture
  classification run in compiled Lean 4.
-/
import Grassmann.CABI.Kernels
import Grassmann.CABI.ScenePack

namespace Grassmann.CABI.Studio

open Grassmann.CABI.Kernels
open Grassmann.CABI.ScenePack

/-! ### Lightweight Init-Only Expression Evaluator (for `evalSurface` / `calcEval`) -/

private inductive Expr where
  | num (v : Float)
  | varX | varY | varT
  | neg (e : Expr)
  | add (a b : Expr) | sub (a b : Expr) | mul (a b : Expr) | div (a b : Expr) | pow (a b : Expr)
  | fn (name : String) (e : Expr)
  deriving Inhabited

private def evalExpr (e : Expr) (x y t : Float) : Float :=
  match e with
  | .num v => v
  | .varX => x
  | .varY => y
  | .varT => t
  | .neg a => -(evalExpr a x y t)
  | .add a b => evalExpr a x y t + evalExpr b x y t
  | .sub a b => evalExpr a x y t - evalExpr b x y t
  | .mul a b => evalExpr a x y t * evalExpr b x y t
  | .div a b =>
    let bv := evalExpr b x y t
    if Float.abs bv < 1e-12 then 0.0 else evalExpr a x y t / bv
  | .pow a b => Float.pow (evalExpr a x y t) (evalExpr b x y t)
  | .fn nm a =>
    let v := evalExpr a x y t
    if nm == "sin" then Float.sin v
    else if nm == "cos" then Float.cos v
    else if nm == "tan" then Float.tan v
    else if nm == "exp" then Float.exp v
    else if nm == "abs" then Float.abs v
    else if nm == "sqrt" then Float.sqrt (if v < 0.0 then 0.0 else v)
    else if nm == "log" then Float.log (if v <= 1e-12 then 1e-12 else v)
    else if nm == "sinh" then Float.sinh v
    else if nm == "cosh" then Float.cosh v
    else if nm == "tanh" then Float.tanh v
    else v

private structure Parser where
  chars : Array Char
  pos : Nat

private def Parser.skipWS (p : Parser) : Parser := Id.run do
  let mut i := p.pos
  while i < p.chars.size && (p.chars[i]! == ' ' || p.chars[i]! == '\t' || p.chars[i]! == '\n' || p.chars[i]! == '\r') do
    i := i + 1
  return { p with pos := i }

private def Parser.peek (p : Parser) : Option Char :=
  let p := p.skipWS
  if h : p.pos < p.chars.size then some (p.chars[p.pos]) else none

private def isDigitC (c : Char) : Bool := c >= '0' && c <= '9'
private def isAlphaC (c : Char) : Bool := (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_'

private def parseFloatAt (chars : Array Char) (start : Nat) : Float × Nat := Id.run do
  let mut i := start
  let mut neg := false
  if i < chars.size && chars[i]! == '-' then
    neg := true; i := i + 1
  else if i < chars.size && chars[i]! == '+' then
    i := i + 1
  let mut intVal : Float := 0.0
  while i < chars.size && isDigitC chars[i]! do
    intVal := intVal * 10.0 + (chars[i]!.toNat - '0'.toNat).toFloat
    i := i + 1
  let mut fracVal : Float := 0.0
  let mut fracScale : Float := 0.1
  if i < chars.size && chars[i]! == '.' then
    i := i + 1
    while i < chars.size && isDigitC chars[i]! do
      fracVal := fracVal + (chars[i]!.toNat - '0'.toNat).toFloat * fracScale
      fracScale := fracScale * 0.1
      i := i + 1
  let mut v := intVal + fracVal
  if i < chars.size && (chars[i]! == 'e' || chars[i]! == 'E') then
    i := i + 1
    let mut eneg := false
    if i < chars.size && chars[i]! == '-' then eneg := true; i := i + 1
    else if i < chars.size && chars[i]! == '+' then i := i + 1
    let mut expVal : Nat := 0
    while i < chars.size && isDigitC chars[i]! do
      expVal := expVal * 10 + (chars[i]!.toNat - '0'.toNat)
      i := i + 1
    let p10 := Float.pow 10.0 (if eneg then -(expVal.toFloat) else expVal.toFloat)
    v := v * p10
  return (if neg then -v else v, i)

mutual
  private partial def parseAdd (p : Parser) (fuel : Nat) : Expr × Parser :=
    match fuel with
    | 0 => (.num 0.0, p)
    | fuel + 1 => Id.run do
      let first := parseMul p fuel
      let mut lhs := first.1
      let mut st := first.2
      while true do
        st := st.skipWS
        if st.pos < st.chars.size && (st.chars[st.pos]! == '+' || st.chars[st.pos]! == '-') then
          let op := st.chars[st.pos]!
          let next := parseMul { st with pos := st.pos + 1 } fuel
          lhs := if op == '+' then .add lhs next.1 else .sub lhs next.1
          st := next.2
        else break
      return (lhs, st)

  private partial def parseMul (p : Parser) (fuel : Nat) : Expr × Parser :=
    match fuel with
    | 0 => (.num 0.0, p)
    | fuel + 1 => Id.run do
      let first := parsePow p fuel
      let mut lhs := first.1
      let mut st := first.2
      while true do
        st := st.skipWS
        if st.pos < st.chars.size && (st.chars[st.pos]! == '*' || st.chars[st.pos]! == '/') then
          let op := st.chars[st.pos]!
          let next := parsePow { st with pos := st.pos + 1 } fuel
          lhs := if op == '*' then .mul lhs next.1 else .div lhs next.1
          st := next.2
        else break
      return (lhs, st)

  private partial def parsePow (p : Parser) (fuel : Nat) : Expr × Parser :=
    match fuel with
    | 0 => (.num 0.0, p)
    | fuel + 1 =>
      let (lhs, st) := parseUnary p fuel
      let st := st.skipWS
      if st.pos < st.chars.size && st.chars[st.pos]! == '^' then
        let (rhs, st2) := parsePow { st with pos := st.pos + 1 } fuel
        (.pow lhs rhs, st2)
      else (lhs, st)

  private partial def parseUnary (p : Parser) (fuel : Nat) : Expr × Parser :=
    match fuel with
    | 0 => (.num 0.0, p)
    | fuel + 1 =>
      let st := p.skipWS
      if st.pos < st.chars.size && st.chars[st.pos]! == '-' then
        let (e, st2) := parseUnary { st with pos := st.pos + 1 } fuel
        (.neg e, st2)
      else if st.pos < st.chars.size && st.chars[st.pos]! == '+' then
        parseUnary { st with pos := st.pos + 1 } fuel
      else parseAtom st fuel

  private partial def parseAtom (p : Parser) (fuel : Nat) : Expr × Parser :=
    match fuel with
    | 0 => (.num 0.0, p)
    | fuel + 1 =>
      let st := p.skipWS
      if st.pos >= st.chars.size then (.num 0.0, st)
      else
        let c := st.chars[st.pos]!
        if c == '(' then
          let (e, st2) := parseAdd { st with pos := st.pos + 1 } fuel
          let st2 := st2.skipWS
          let st3 := if st2.pos < st2.chars.size && st2.chars[st2.pos]! == ')' then { st2 with pos := st2.pos + 1 } else st2
          (e, st3)
        else if isDigitC c || c == '.' then
          let (v, nextPos) := parseFloatAt st.chars st.pos
          (.num v, { st with pos := nextPos })
        else if isAlphaC c then Id.run do
          let mut i := st.pos
          let mut name := ""
          while i < st.chars.size && (isAlphaC st.chars[i]! || isDigitC st.chars[i]!) do
            name := name.push st.chars[i]!
            i := i + 1
          let st1 := ({ st with pos := i }).skipWS
          if st1.pos < st1.chars.size && st1.chars[st1.pos]! == '(' then
            let (arg, st2) := parseAdd { st1 with pos := st1.pos + 1 } fuel
            let st2 := st2.skipWS
            let st3 := if st2.pos < st2.chars.size && st2.chars[st2.pos]! == ')' then { st2 with pos := st2.pos + 1 } else st2
            return (.fn name arg, st3)
          else
            let e :=
              if name == "x" then .varX
              else if name == "y" then .varY
              else if name == "t" then .varT
              else if name == "pi" then .num 3.141592653589793
              else if name == "e" then .num 2.718281828459045
              else .num 0.0
            return (e, st1)
        else
          (.num 0.0, { st with pos := st.pos + 1 })
end

private def parseExpr (s : String) : Expr :=
  let chars := s.toList.toArray
  let (e, _) := parseAdd { chars := chars, pos := 0 } 64
  e

/-! ### Procedural CCW Torus Mesh + Exact PGA3 Plane Slicer -/

/-- Generate a smooth CCW-wound torus mesh (for `#pga3d_slicing` flagship demo).
Major radius `R`, minor radius `r`, segments `segU × segV`. -/
private def buildTorusMesh (meshId dirtyHash : UInt64) (R r : Float) (segU segV : Nat) : MeshAssetData := Id.run do
  let twoPi : Float := 6.283185307179586
  let nVerts := segU * segV
  let mut pos := FloatArray.emptyWithCapacity (nVerts * 3)
  let mut norm := FloatArray.emptyWithCapacity (nVerts * 3)
  let mut col := FloatArray.emptyWithCapacity (nVerts * 4)
  for iu in [:segU] do
    let u := (iu.toFloat / segU.toFloat) * twoPi
    let cu := Float.cos u; let su := Float.sin u
    for iv in [:segV] do
      let v := (iv.toFloat / segV.toFloat) * twoPi
      let cv := Float.cos v; let sv := Float.sin v
      let rad := R + r * cv
      let x := rad * cu
      let y := r * sv
      let z := rad * su
      let nx := cv * cu
      let ny := sv
      let nz := cv * su
      pos := pos |>.push x |>.push y |>.push z
      norm := norm |>.push nx |>.push ny |>.push nz
      -- Studio cyan-indigo-violet curvature gradient
      let cr := 0.28 + 0.35 * (0.5 + 0.5 * cu)
      let cg := 0.58 + 0.30 * (0.5 + 0.5 * sv)
      let cb := 0.92 - 0.18 * (0.5 + 0.5 * su)
      col := col |>.push cr |>.push cg |>.push cb |>.push 1.0
  let mut idxs : Array UInt32 := Array.emptyWithCapacity (segU * segV * 6)
  for iu in [:segU] do
    let iu1 := (iu + 1) % segU
    for iv in [:segV] do
      let iv1 := (iv + 1) % segV
      let a := (iu * segV + iv).toUInt32
      let b := (iu1 * segV + iv).toUInt32
      let c := (iu1 * segV + iv1).toUInt32
      let d := (iu * segV + iv1).toUInt32
      -- CCW outward winding (check: ∂/∂u = (-su, 0, cu), ∂/∂v = (-sv*cu, cv, -sv*su), ∂v × ∂u points outward!)
      idxs := idxs |>.push a |>.push d |>.push c
      idxs := idxs |>.push a |>.push c |>.push b
  return { meshId, dirtyHash, positions := pos, normals := norm, colors := col, indices := idxs }

/-- Slice a CCW triangle mesh by plane `n · p + d = 0` (`n` unit normal, tangent frame `u, v`,
origin `p0 = -d*n`), returning 3D slice segments AND projected 2D contour segments! -/
private def sliceMeshByPlane (mesh : MeshAssetData) (nx ny nz d : Float)
    (ux uy uz vx vy vz : Float) : Array SegmentPrim × Array ContourCurve2D := Id.run do
  let nTris := mesh.indices.size / 3
  let mut segs : Array SegmentPrim := #[]
  let mut c2d : Array ContourCurve2D := #[]
  let p0x := -d * nx; let p0y := -d * ny; let p0z := -d * nz
  let sliceCol : RGBA := ⟨1.0, 0.78, 0.22, 1.0⟩
  for t in [:nTris] do
    let i0 := mesh.indices[t * 3]!.toNat
    let i1 := mesh.indices[t * 3 + 1]!.toNat
    let i2 := mesh.indices[t * 3 + 2]!.toNat
    let x0 := faGet mesh.positions (i0*3); let y0 := faGet mesh.positions (i0*3+1); let z0 := faGet mesh.positions (i0*3+2)
    let x1 := faGet mesh.positions (i1*3); let y1 := faGet mesh.positions (i1*3+1); let z1 := faGet mesh.positions (i1*3+2)
    let x2 := faGet mesh.positions (i2*3); let y2 := faGet mesh.positions (i2*3+1); let z2 := faGet mesh.positions (i2*3+2)
    let s0 := nx*x0 + ny*y0 + nz*z0 + d
    let s1 := nx*x1 + ny*y1 + nz*z1 + d
    let s2 := nx*x2 + ny*y2 + nz*z2 + d
    let mut hits : Array Vec3 := #[]
    let checkEdge := fun (ax ay az sa bx by0 bz sb : Float) (acc : Array Vec3) =>
      if (sa <= 0.0 && sb > 0.0) || (sa > 0.0 && sb <= 0.0) then
        let denom := sa - sb
        let alpha := if Float.abs denom > 1e-12 then sa / denom else 0.5
        acc.push ⟨ax + alpha * (bx - ax), ay + alpha * (by0 - ay), az + alpha * (bz - az)⟩
      else acc
    hits := checkEdge x0 y0 z0 s0 x1 y1 z1 s1 hits
    hits := checkEdge x1 y1 z1 s1 x2 y2 z2 s2 hits
    hits := checkEdge x2 y2 z2 s2 x0 y0 z0 s0 hits
    if hits.size >= 2 then
      let a := hits[0]!
      let b := hits[1]!
      segs := segs.push { a, b, width := 3.5, color := sliceCol, flags := 0 }
      let ax2 := (a.x - p0x)*ux + (a.y - p0y)*uy + (a.z - p0z)*uz
      let ay2 := (a.x - p0x)*vx + (a.y - p0y)*vy + (a.z - p0z)*vz
      let bx2 := (b.x - p0x)*ux + (b.y - p0y)*uy + (b.z - p0z)*uz
      let by2 := (b.x - p0x)*vx + (b.y - p0y)*vy + (b.z - p0z)*vz
      let xy := FloatArray.emptyWithCapacity 4 |>.push ax2 |>.push ay2 |>.push bx2 |>.push by2
      c2d := c2d.push { xy, color := sliceCol, width := 2.2, flags := 0 }
  return (segs, c2d)

/-- Build a CCW surface mesh `z = f(x, y, t)` over `[minX, maxX] × [minY, maxY]` at `gridN × gridN`. -/
private def buildSurfaceMesh (meshId dirtyHash : UInt64) (expr : Expr) (t : Float)
    (minX maxX minY maxY : Float) (gridN : Nat) : MeshAssetData := Id.run do
  let n := if gridN < 4 then 4 else if gridN > 65 then 65 else gridN
  let nVerts := n * n
  let dx := (maxX - minX) / (n - 1).toFloat
  let dy := (maxY - minY) / (n - 1).toFloat
  let eps := 0.01
  let mut pos := FloatArray.emptyWithCapacity (nVerts * 3)
  let mut norm := FloatArray.emptyWithCapacity (nVerts * 3)
  let mut col := FloatArray.emptyWithCapacity (nVerts * 4)
  for iy in [:n] do
    let y := minY + iy.toFloat * dy
    for ix in [:n] do
      let x := minX + ix.toFloat * dx
      let z := evalExpr expr x y t
      let dzdx := (evalExpr expr (x + eps) y t - evalExpr expr (x - eps) y t) / (2.0 * eps)
      let dzdy := (evalExpr expr x (y + eps) t - evalExpr expr x (y - eps) t) / (2.0 * eps)
      -- Y-up studio mapping: (x, z, y) -> normal (-dzdx, 1, -dzdy) normalized
      let nx0 := -dzdx; let ny0 := 1.0; let nz0 := -dzdy
      let invL := 1.0 / Float.sqrt (nx0*nx0 + ny0*ny0 + nz0*nz0)
      pos := pos |>.push x |>.push z |>.push y
      norm := norm |>.push (nx0 * invL) |>.push (ny0 * invL) |>.push (nz0 * invL)
      let h := 0.5 + 0.5 * Float.tanh (z * 0.7)
      col := col |>.push (0.18 + 0.75 * h) |>.push (0.42 + 0.48 * (1.0 - Float.abs (2.0*h - 1.0)))
                 |>.push (0.95 - 0.70 * h) |>.push 1.0
  let mut idxs : Array UInt32 := Array.emptyWithCapacity ((n - 1) * (n - 1) * 6)
  for iy in [:n - 1] do
    for ix in [:n - 1] do
      let a := (iy * n + ix).toUInt32
      let b := (iy * n + ix + 1).toUInt32
      let c := ((iy + 1) * n + ix + 1).toUInt32
      let d := ((iy + 1) * n + ix).toUInt32
      -- CCW upward (+Y) winding
      idxs := idxs |>.push a |>.push d |>.push c
      idxs := idxs |>.push a |>.push c |>.push b
  return { meshId, dirtyHash, positions := pos, normals := norm, colors := col, indices := idxs }

/-! ### Studio Session State & Presets -/

structure StudioState where
  presetId : String := "pga3d_slicing"
  frameSeq : UInt64 := 0
  simTime : Float := 0.0
  camMotor : FloatArray := pga3MakeTranslator 0.0 0.0 (-5.0)
  camFov : Float := 45.0
  camDist : Float := 5.0
  camOrtho : Bool := false
  -- Interactive handles (up to 4 draggable 3D points)
  h0 : Vec3 := ⟨0.0, 0.25, 0.0⟩
  h1 : Vec3 := ⟨1.2, 0.4, 0.3⟩
  h2 : Vec3 := ⟨-0.9, 0.8, -0.2⟩
  -- Scalar control parameters (e.g. boost rapidity, slice angle, rational rotor)
  param0 : Float := 0.0
  param1 : Float := 0.4
  sliceMotor : FloatArray := pga3MotorIdentity
  surfaceExprStr : String := "sin(x*x + y*y - t) * 0.6"
  surfaceExpr : Expr := parseExpr "sin(x*x + y*y - t) * 0.6"
  surfaceGridN : Nat := 32
  -- Wedge mini-state
  wedgeIs3D : Bool := false
  wedgeLevel : UInt32 := 1
  wedgeMoves : UInt32 := 0
  wedgeSolved : Bool := false
  wedgeLastOp : String := ""
  wedgePreviewOp : String := ""
  -- Delta tracking (#17 fixes #2 & #4)
  sentMeshHashes : Array UInt64 := #[]
  metaDirty : Bool := true
  lastFrame : ByteArray := ByteArray.empty
  deriving Inhabited

/-- Build a 3D orthonormal tangent basis `(u, v)` perpendicular to unit normal `n`. -/
private def tangentBasis (nx ny nz : Float) : Vec3 × Vec3 :=
  let (ax, ay, az) := if Float.abs ny < 0.9 then (0.0, 1.0, 0.0) else (1.0, 0.0, 0.0)
  -- u = normalize(a × n)
  let ux0 := ay*nz - az*ny; let uy0 := az*nx - ax*nz; let uz0 := ax*ny - ay*nx
  let uLen := Float.sqrt (ux0*ux0 + uy0*uy0 + uz0*uz0)
  let invU := if uLen > 1e-12 then 1.0 / uLen else 1.0
  let ux := ux0 * invU; let uy := uy0 * invU; let uz := uz0 * invU
  -- v = n × u
  let vx := ny*uz - nz*uy; let vy := nz*ux - nx*uz; let vz := nx*uy - ny*ux
  (⟨ux, uy, uz⟩, ⟨vx, vy, vz⟩)

private def hasHash (arr : Array UInt64) (h : UInt64) : Bool := Id.run do
  for x in arr do
    if x == h then return true
  return false

private def buildMetaJson (algName : String) (p q r : Nat) (presetId title : String)
    (labels : Array String) (inspectNames : Array (Nat × String × Nat × String))
    (wedgeOpt : Option (Bool × UInt32 × UInt32 × Bool × String × String)) : String := Id.run do
  let mut labStr := ""
  for i in [:labels.size] do
    if i > 0 then labStr := labStr ++ ","
    labStr := labStr ++ jsonEscape labels[i]!
  let mut inspStr := ""
  for i in [:inspectNames.size] do
    let (idx, nm, gr, fmt) := inspectNames[i]!
    if i > 0 then inspStr := inspStr ++ ","
    inspStr := inspStr ++ s!"\{\"idx\":{idx},\"name\":{jsonEscape nm},\"grade\":{gr},\"formatted\":{jsonEscape fmt},\"editable\":true}"
  let wedgeStr := match wedgeOpt with
    | none => ""
    | some (is3d, lvl, moves, solved, lastOp, prevOp) =>
      let score := if moves * 10 < 1000 then 1000 - moves * 10 else 0
      let canUndoStr := if moves > 0 then "true" else "false"
      s!",\"wedge\":\{\"is3D\":{is3d},\"level\":{lvl},\"totalLevels\":16,\"title\":\"Wedge Level {lvl}\",\"goal\":\"Construct the red target\",\"tutorialText\":\"\",\"moves\":{moves},\"score\":{score},\"elapsedMs\":0,\"lastOp\":{jsonEscape lastOp},\"previewOp\":{jsonEscape prevOp},\"hintText\":\"Drag two elements apart to join or together to meet\",\"solved\":{solved},\"canUndo\":{canUndoStr}}"
  return s!"\{\"version\":1,\"algebra\":\{\"name\":{jsonEscape algName},\"p\":{p},\"q\":{q},\"r\":{r},\"conformalWitt\":false},\"presetId\":{jsonEscape presetId},\"title\":{jsonEscape title},\"labels\":[{labStr}],\"inspect\":[{inspStr}]{wedgeStr},\"diagnostics\":[]}"

/-- Render the current `StudioState` into a packed `GSIR` v1 binary frame and update delta caches. -/
def renderFrame (st : StudioState) (forceFull : Bool := false) : StudioState := Id.run do
  let sentHashes := if forceFull then #[] else st.sentMeshHashes
  let emitMeta := forceFull || st.metaDirty
  let seq := st.frameSeq + 1
  let cam : CameraData := {
    motor := st.camMotor
    viewMat4 := pga3MotorToMat4 st.camMotor
    fovDeg := st.camFov
    distance := st.camDist
    orthoScale := 2.5
    flags := if st.camOrtho then 1 else 0
  }

  let mut newSent := sentHashes
  let mut frame : SceneFrameData := {
    flags := 6  -- gridEnabled | darkTheme
    frameSeq := seq
    simTime := st.simTime
    camera := some cam
  }

  if st.presetId == "sta_wedge_lab" then
    -- STA Cl(3,1) (-+++) interactive wedge + Lorentz boost
    let a := faZeros 16
    let a := faAddAt (faAddAt (faAddAt (faAddAt a 1 0.25) 2 st.h0.x) 4 st.h0.y) 8 st.h0.z
    let b := faZeros 16
    let b := faAddAt (faAddAt (faAddAt (faAddAt b 1 0.15) 2 st.h1.x) 4 st.h1.y) 8 st.h1.z
    let boost := staBoostRotor st.param0 1.0 0.0 0.0
    let aB := staSandwich boost a
    let bB := staSandwich boost b
    let sw := staSpatialWedge aB bB
    let va : Vec3 := ⟨faGet sw 0, faGet sw 1, faGet sw 2⟩
    let vb : Vec3 := ⟨faGet sw 3, faGet sw 4, faGet sw 5⟩
    let vn : Vec3 := ⟨faGet sw 6, faGet sw 7, faGet sw 8⟩
    let area := faGet sw 9
    let wb := staWedge aB bB
    let metaStr := if emitMeta then
      buildMetaJson "STA" 3 1 0 "sta_wedge_lab" "STA Cl(3,1) -+++ Wedge & Lorentz Boost"
        #["A", "B", "A ∧ B"]
        #[(0, "A", 1, s!"{fmtF (faGet aB 1)}et + {fmtF va.x}ex + {fmtF va.y}ey + {fmtF va.z}ez"),
          (1, "B", 1, s!"{fmtF (faGet bB 1)}et + {fmtF vb.x}ex + {fmtF vb.y}ey + {fmtF vb.z}ez"),
          (2, "A∧B", 2, s!"area={fmtF area}")]
        none
      else ""
    frame := { frame with
      sigP := 3, sigQ := 1, sigR := 0, modeKind := 3,
      points := #[
        { handleId := 0, flags := 1, pos := va, radius := 0.09, color := ⟨1.0, 0.55, 0.15, 1.0⟩, labelIdx := 0 },
        { handleId := 1, flags := 1, pos := vb, radius := 0.09, color := ⟨0.15, 0.85, 0.78, 1.0⟩, labelIdx := 1 }
      ],
      segments := #[
        { a := ⟨0.0,0.0,0.0⟩, b := va, width := 3.5, color := ⟨1.0, 0.55, 0.15, 1.0⟩, flags := 2 },
        { a := ⟨0.0,0.0,0.0⟩, b := vb, width := 3.5, color := ⟨0.15, 0.85, 0.78, 1.0⟩, flags := 2 },
        { a := ⟨0.0,0.0,0.0⟩, b := vn, width := 2.5, color := ⟨0.95, 0.35, 0.85, 1.0⟩, flags := 3 }
      ],
      bivectorDisks := #[
        { origin := ⟨0.0,0.0,0.0⟩, u := va, v := vb, area := area, color := ⟨0.45, 0.65, 1.0, 0.42⟩, flags := 2 }
      ],
      inspectCoeffs := #[
        { entryIdx := 0, grade := 1, coeffs := aB },
        { entryIdx := 1, grade := 1, coeffs := bB },
        { entryIdx := 2, grade := 2, coeffs := wb }
      ],
      metaJson := metaStr
    }

  else if st.presetId == "cga3d_spheres" then
    let c1 := st.h0; let r1 : Float := 1.15
    let c2 := st.h1; let r2 : Float := 1.05
    let dx := c2.x - c1.x; let dy := c2.y - c1.y; let dz := c2.z - c1.z
    let dist := Float.sqrt (dx*dx + dy*dy + dz*dz)
    let (nx, ny, nz) := if dist > 1e-6 then (dx/dist, dy/dist, dz/dist) else (1.0, 0.0, 0.0)
    let h := if dist > 1e-6 then (r1*r1 - r2*r2 + dist*dist) / (2.0 * dist) else 0.0
    let radSq := r1*r1 - h*h
    let isImag := radSq < 0.0
    let cRad := Float.sqrt (Float.abs radSq)
    let cc : Vec3 := ⟨c1.x + h*nx, c1.y + h*ny, c1.z + h*nz⟩
    let (tu, tv) := tangentBasis nx ny nz
    let s1 := cga3DualSphere c1.x c1.y c1.z r1
    let s2 := cga3DualSphere c2.x c2.y c2.z r2
    let circ := cga3Wedge s1 s2
    let metaStr := if emitMeta then
      buildMetaJson "CGA3" 4 1 0 "cga3d_spheres" "CGA3 Sphere-Sphere Intersection Circle"
        #["S1", "S2", "S1 ∧ S2"]
        #[(0, "S1*", 1, s!"r={fmtF r1}"), (1, "S2*", 1, s!"r={fmtF r2}"),
          (2, "C=S1*∧S2*", 2, if isImag then s!"imag r={fmtF cRad}" else s!"real r={fmtF cRad}")]
        none
      else ""
    frame := { frame with
      sigP := 4, sigQ := 1, sigR := 0, modeKind := 0,
      points := #[
        { handleId := 0, flags := 1, pos := c1, radius := 0.08, color := ⟨0.25, 0.78, 1.0, 1.0⟩, labelIdx := 0 },
        { handleId := 1, flags := 1, pos := c2, radius := 0.08, color := ⟨1.0, 0.42, 0.65, 1.0⟩, labelIdx := 1 }
      ],
      spheres := #[
        { center := c1, radius := r1, color := ⟨0.25, 0.78, 1.0, 0.24⟩, flags := 0, labelIdx := 0 },
        { center := c2, radius := r2, color := ⟨1.0, 0.42, 0.65, 0.24⟩, flags := 0, labelIdx := 1 }
      ],
      circles := #[
        { center := cc, u := tu, v := tv, radius := cRad, width := 3.5,
          color := if isImag then ⟨0.9, 0.35, 0.35, 0.8⟩ else ⟨1.0, 0.85, 0.25, 1.0⟩,
          flags := if isImag then 1 else 0, labelIdx := 2 }
      ],
      inspectCoeffs := #[
        { entryIdx := 0, grade := 1, coeffs := s1 },
        { entryIdx := 1, grade := 1, coeffs := s2 },
        { entryIdx := 2, grade := 2, coeffs := circ }
      ],
      metaJson := metaStr
    }

  else if st.presetId == "r3_rational_rotor" then
    let t := st.simTime * 0.7 + st.param0
    let rot := r3RationalRotorFromCayley (0.5 * Float.sin t) (0.5 * Float.cos t) 0.35
    let out := r3ApplyRationalRotor (faGet rot 0) (faGet rot 1) (faGet rot 2) (faGet rot 3) st.h1.x st.h1.y st.h1.z
    let vOut : Vec3 := ⟨faGet out 0, faGet out 1, faGet out 2⟩
    let metaStr := if emitMeta then
      buildMetaJson "R3" 3 0 0 "r3_rational_rotor" "R3 Exact Rational Rotor (Zero-Sqrt)"
        #["v", "R v ~R / |R|²"]
        #[(0, "R", 2, s!"{fmtF (faGet rot 0)} + {fmtF (faGet rot 1)}e12 + {fmtF (faGet rot 2)}e13 + {fmtF (faGet rot 3)}e23")]
        none
      else ""
    frame := { frame with
      sigP := 3, sigQ := 0, sigR := 0, modeKind := 3,
      points := #[
        { handleId := 1, flags := 1, pos := st.h1, radius := 0.08, color := ⟨0.3, 0.8, 1.0, 1.0⟩, labelIdx := 0 },
        { handleId := 2, flags := 0, pos := vOut, radius := 0.08, color := ⟨1.0, 0.75, 0.2, 1.0⟩, labelIdx := 1 }
      ],
      segments := #[
        { a := ⟨0.0,0.0,0.0⟩, b := st.h1, width := 3.0, color := ⟨0.3, 0.8, 1.0, 1.0⟩, flags := 2 },
        { a := ⟨0.0,0.0,0.0⟩, b := vOut, width := 3.5, color := ⟨1.0, 0.75, 0.2, 1.0⟩, flags := 2 }
      ],
      inspectCoeffs := #[( { entryIdx := 0, grade := 2, coeffs := rot } )],
      metaJson := metaStr
    }

  else if st.presetId == "surface_graph" then
    let meshId : UInt64 := 2
    let dirtyHash : UInt64 := 0x50000000 + seq
    let mesh := buildSurfaceMesh meshId dirtyHash st.surfaceExpr st.simTime (-2.5) 2.5 (-2.5) 2.5 st.surfaceGridN
    let idM := pga3MotorIdentity
    let metaStr := if emitMeta then
      buildMetaJson "R3" 3 0 0 "surface_graph" s!"z = {st.surfaceExprStr}"
        #["z = f(x,y,t)"] #[] none
      else ""
    frame := { frame with
      sigP := 3, sigQ := 0, sigR := 0, modeKind := 4,
      meshRefs := #[{
        meshId, dirtyHash, motor := idM, modelMat4 := pga3MotorToMat4 idM,
        color := ⟨1.0, 1.0, 1.0, 1.0⟩, flags := 6
      }],
      meshAssets := #[mesh],
      metaJson := metaStr
    }

  else if st.presetId == "wedge_2d" || st.presetId == "wedge_3d" then
    let is3d := st.presetId == "wedge_3d" || st.wedgeIs3D
    let pA : Vec3 := ⟨-1.0, -0.5, 0.0⟩
    let pB : Vec3 := ⟨1.0, 0.6, if is3d then 0.5 else 0.0⟩
    let lDir0 : Vec3 := ⟨pB.x - pA.x, pB.y - pA.y, pB.z - pA.z⟩
    let lLen := Float.sqrt (lDir0.x*lDir0.x + lDir0.y*lDir0.y + lDir0.z*lDir0.z)
    let invL := if lLen > 1e-6 then 1.0 / lLen else 1.0
    let lDir : Vec3 := ⟨lDir0.x*invL, lDir0.y*invL, lDir0.z*invL⟩
    let metaStr := if emitMeta then
      buildMetaJson (if is3d then "PGA3" else "PGA2") (if is3d then 3 else 2) 0 1
        st.presetId (if is3d then "Wedge 3D (PGA3)" else "Wedge 2D (PGA2)")
        #["A", "B", "Target"] #[]
        (some (is3d, st.wedgeLevel, st.wedgeMoves, st.wedgeSolved, st.wedgeLastOp, st.wedgePreviewOp))
      else ""
    frame := { frame with
      flags := (if is3d then 6 else 7) ||| 8,  -- hasWedgeHud (b3) + optional is2D (b0)
      sigP := if is3d then 3 else 2, sigQ := 0, sigR := 1,
      modeKind := if is3d then 2 else 1,
      points := #[
        { handleId := 0, flags := 1, pos := pA, radius := 0.09, color := ⟨0.95, 0.96, 1.0, 1.0⟩, labelIdx := 0 },
        { handleId := 1, flags := 1, pos := pB, radius := 0.09, color := ⟨0.95, 0.96, 1.0, 1.0⟩, labelIdx := 1 }
      ],
      lines := #[
        { origin := pA, dir := lDir, clip := 6.0, width := 3.0,
          color := if st.wedgeSolved then ⟨0.25, 0.95, 0.55, 1.0⟩ else ⟨1.0, 0.25, 0.30, 0.85⟩,
          flags := 8 } -- target flag
      ],
      metaJson := metaStr
    }

  else
    -- Default flagship: `pga3d_slicing` (PGA3 plane slicing a smooth CCW 3D torus + live 2D contour inset!)
    let meshId : UInt64 := 1
    let dirtyHash : UInt64 := 0xA10C0001
    let torus := buildTorusMesh meshId dirtyHash 1.15 0.45 28 16
    let needAsset := !hasHash sentHashes dirtyHash
    if needAsset then newSent := newSent.push dirtyHash
    -- Cut plane normal driven by simTime / sliceMotor + draggable handle h0
    let tilt := 0.35 + 0.35 * Float.sin (st.simTime * 0.6)
    let nx0 := Float.sin tilt; let ny0 := Float.cos tilt; let nz0 := 0.25 * Float.sin (st.simTime * 0.4)
    let nLen := Float.sqrt (nx0*nx0 + ny0*ny0 + nz0*nz0)
    let nx := nx0 / nLen; let ny := ny0 / nLen; let nz := nz0 / nLen
    let d := -(nx*st.h0.x + ny*st.h0.y + nz*st.h0.z)
    let (tu, tv) := tangentBasis nx ny nz
    let (sliceSegs, contour2D) := sliceMeshByPlane torus nx ny nz d tu.x tu.y tu.z tv.x tv.y tv.z
    let planeCoeffs := FloatArray.emptyWithCapacity 16
      |>.push 0.0 |>.push d |>.push nx |>.push 0.0
      |>.push ny |>.push 0.0 |>.push 0.0 |>.push 0.0
      |>.push nz |>.push 0.0 |>.push 0.0 |>.push 0.0
      |>.push 0.0 |>.push 0.0 |>.push 0.0 |>.push 0.0
    let idM := pga3MotorIdentity
    let metaStr := if emitMeta then
      buildMetaJson "PGA3" 3 0 1 "pga3d_slicing" "3D PGA Mesh Slicing (#pga3d_slicing)"
        #["Cut Plane", "Slice Contour"]
        #[(0, "plane", 1, s!"{fmtF d}e0 + {fmtF nx}e1 + {fmtF ny}e2 + {fmtF nz}e3")]
        none
      else ""
    frame := { frame with
      flags := 6 ||| 32,  -- grid | darkTheme | hasContourOverlay (b5)
      sigP := 3, sigQ := 0, sigR := 1, modeKind := 0,
      points := #[
        { handleId := 0, flags := 1, pos := st.h0, radius := 0.09, color := ⟨1.0, 0.78, 0.22, 1.0⟩, labelIdx := 0 }
      ],
      planes := #[
        { center := st.h0, u := tu, v := tv, extent := 2.1,
          color := ⟨0.32, 0.72, 1.0, 0.22⟩, flags := 3, labelIdx := 0 }
      ],
      segments := sliceSegs,
      meshRefs := #[{
        meshId, dirtyHash, motor := idM, modelMat4 := pga3MotorToMat4 idM,
        color := ⟨1.0, 1.0, 1.0, 1.0⟩, flags := 6
      }],
      meshAssets := if needAsset then #[torus] else #[],
      contourOverlay := some {
        minX := -2.0, maxX := 2.0, minY := -2.0, maxY := 2.0,
        curves := contour2D, intersections := #[]
      },
      inspectCoeffs := #[{ entryIdx := 0, grade := 1, coeffs := planeCoeffs }],
      metaJson := metaStr
    }

  let encoded := encodeSceneFrame frame
  return { st with
    frameSeq := seq,
    sentMeshHashes := newSent,
    metaDirty := false,
    lastFrame := encoded
  }

/-! ### Event Application (Binary & Minimal JSON Control) -/

def applyBinEvent (st : StudioState) (buf : ByteArray) : Except String StudioState :=
  match decodeBinEvent buf with
  | .invalid => .error "invalid binary event"
  | .fullSnapshot => .ok (renderFrame st true)
  | .dragHandle hid x y z ff =>
    let st' :=
      if hid == 0 then { st with h0 := ⟨x, y, z⟩ }
      else if hid == 1 then { st with h1 := ⟨x, y, z⟩ }
      else { st with h2 := ⟨x, y, z⟩ }
    .ok (renderFrame st' ff)
  | .tick dt t ff =>
    let nextT := if t > 0.0 then t else st.simTime + dt
    .ok (renderFrame { st with simTime := nextT } ff)
  | .editCoeff entryIdx bladeIdx val ff =>
    let st' :=
      if entryIdx == 0 && bladeIdx == 0 then { st with param0 := val, metaDirty := true }
      else { st with param1 := val, metaDirty := true }
    .ok (renderFrame st' ff)
  | .wedgeGesture _idA _idB dirA dirB holdA holdB isPreview ff =>
    let op :=
      if holdA || holdB then "dot"
      else if (dirA.x*dirB.x + dirA.y*dirB.y + dirA.z*dirB.z) < 0.0 then "join"
      else "meet"
    let st' :=
      if isPreview then { st with wedgePreviewOp := op, metaDirty := true }
      else { st with
        wedgeMoves := st.wedgeMoves + 1,
        wedgeLastOp := op,
        wedgePreviewOp := "",
        wedgeSolved := op == "join" || st.wedgeSolved,
        metaDirty := true
      }
    .ok (renderFrame st' ff)
  | .wedgeAction act arg ff =>
    let st' :=
      if act == 1 then { st with wedgeMoves := 0, wedgeSolved := false, wedgeLastOp := "", metaDirty := true }
      else if act == 2 then { st with wedgeLevel := st.wedgeLevel + 1, wedgeMoves := 0, wedgeSolved := false, metaDirty := true }
      else if act == 3 && st.wedgeLevel > 1 then { st with wedgeLevel := st.wedgeLevel - 1, wedgeMoves := 0, wedgeSolved := false, metaDirty := true }
      else if act == 4 then { st with wedgeIs3D := !st.wedgeIs3D, presetId := if st.wedgeIs3D then "wedge_2d" else "wedge_3d", metaDirty := true }
      else if act == 6 then { st with wedgeLevel := arg, wedgeMoves := 0, wedgeSolved := false, metaDirty := true }
      else { st with metaDirty := true }
    .ok (renderFrame st' ff)
  | .setCamera motor fov dist ff =>
    .ok (renderFrame { st with camMotor := pga3MotorNormalize motor, camFov := fov, camDist := dist } ff)
  | .slicePlane motor ff =>
    .ok (renderFrame { st with sliceMotor := pga3MotorNormalize motor } ff)

/-- Minimal Init-only JSON string field extractor (finds `"key":"value"`). -/
private def jsonGetStringField (s key : String) : Option String := Id.run do
  let needle := "\"" ++ key ++ "\""
  let cs := s.toList.toArray
  let ns := needle.toList.toArray
  if cs.size < ns.size then return none
  for i in [:cs.size - ns.size + 1] do
    let mut ok := true
    for j in [:ns.size] do
      if cs[i + j]! != ns[j]! then ok := false; break
    if ok then
      let mut k := i + ns.size
      while k < cs.size && (cs[k]! == ' ' || cs[k]! == '\t' || cs[k]! == ':') do k := k + 1
      if k < cs.size && cs[k]! == '"' then
        k := k + 1
        let mut val := ""
        while k < cs.size && cs[k]! != '"' do
          if cs[k]! == '\\' && k + 1 < cs.size then
            val := val.push cs[k + 1]!; k := k + 2
          else
            val := val.push cs[k]!; k := k + 1
        return some val
  return none

/-- Minimal Init-only JSON numeric field extractor (finds `"key":123.45`). -/
private def jsonGetFloatField (s key : String) : Option Float := Id.run do
  let needle := "\"" ++ key ++ "\""
  let cs := s.toList.toArray
  let ns := needle.toList.toArray
  if cs.size < ns.size then return none
  for i in [:cs.size - ns.size + 1] do
    let mut ok := true
    for j in [:ns.size] do
      if cs[i + j]! != ns[j]! then ok := false; break
    if ok then
      let mut k := i + ns.size
      while k < cs.size && (cs[k]! == ' ' || cs[k]! == '\t' || cs[k]! == ':') do k := k + 1
      if k < cs.size && (isDigitC cs[k]! || cs[k]! == '-' || cs[k]! == '+' || cs[k]! == '.') then
        let (v, _) := parseFloatAt cs k
        return some v
  return none

def applyJsonEvent (st : StudioState) (json : String) : Except String StudioState :=
  match jsonGetStringField json "op" with
  | none => .error "missing JSON op field"
  | some op =>
    if op == "loadPreset" then
      let pid := (jsonGetStringField json "id").getD "pga3d_slicing"
      .ok (renderFrame { st with presetId := pid, metaDirty := true } true)
    else if op == "evalSurface" then
      let exprStr := (jsonGetStringField json "expr").getD st.surfaceExprStr
      let gn := ((jsonGetFloatField json "gridN").getD 32.0).toUInt32.toNat
      .ok (renderFrame { st with
        presetId := "surface_graph",
        surfaceExprStr := exprStr,
        surfaceExpr := parseExpr exprStr,
        surfaceGridN := if gn >= 4 then gn else 32,
        metaDirty := true
      } true)
    else if op == "tick" then
      let dt := (jsonGetFloatField json "dt").getD 0.016
      let t := (jsonGetFloatField json "t").getD (st.simTime + dt)
      .ok (renderFrame { st with simTime := t } false)
    else if op == "fullSnapshot" then
      .ok (renderFrame st true)
    else if op == "editCoeff" then
      let v := (jsonGetFloatField json "val").getD st.param0
      .ok (renderFrame { st with param0 := v, metaDirty := true } false)
    else if op == "wedgeAction" then
      let act := (jsonGetStringField json "action").getD "reset"
      let st' :=
        if act == "next" then { st with wedgeLevel := st.wedgeLevel + 1, wedgeMoves := 0, wedgeSolved := false, metaDirty := true }
        else if act == "toggle3D" then { st with wedgeIs3D := !st.wedgeIs3D, presetId := if st.wedgeIs3D then "wedge_2d" else "wedge_3d", metaDirty := true }
        else { st with wedgeMoves := 0, wedgeSolved := false, metaDirty := true }
      .ok (renderFrame st' true)
    else
      -- Accept calcEval / evalScript / dragHandle gracefully and refresh frame
      .ok (renderFrame { st with metaDirty := true } false)

/-! ### Global Session Registry (`IO.Ref`) -/

private structure SessionSlot where
  id : UInt64
  state : StudioState
  deriving Inhabited

private structure SessionRegistry where
  nextId : UInt64 := 1
  slots : Array SessionSlot := #[]
  deriving Inhabited

initialize studioRegistry : IO.Ref SessionRegistry ← IO.mkRef {}

def createSession : IO UInt64 := do
  let reg ← studioRegistry.get
  let id := reg.nextId
  let initial := renderFrame {} true
  studioRegistry.set {
    nextId := id + 1,
    slots := reg.slots.push { id, state := initial }
  }
  return id

def destroySession (sid : UInt64) : IO Unit := do
  let reg ← studioRegistry.get
  let filtered := reg.slots.filter (fun s => s.id != sid)
  studioRegistry.set { reg with slots := filtered }

private def findSlotIdx (slots : Array SessionSlot) (sid : UInt64) : Option Nat := Id.run do
  for i in [:slots.size] do
    if slots[i]!.id == sid then return some i
  return none

/-- Dispatch a binary `InputEvent` and return `(status, frameBytes)` where status is
`0` (OK), `-1` (BAD_HANDLE), or `-2` (BAD_INPUT). -/
def dispatchBin (sid : UInt64) (eventBuf : ByteArray) : IO (Int32 × ByteArray) := do
  let reg ← studioRegistry.get
  match findSlotIdx reg.slots sid with
  | none => return (-1, ByteArray.empty)
  | some idx =>
    let slot := reg.slots[idx]!
    match applyBinEvent slot.state eventBuf with
    | .error _ => return (-2, ByteArray.empty)
    | .ok nextState =>
      let slots' := reg.slots.set! idx { slot with state := nextState }
      studioRegistry.set { reg with slots := slots' }
      return (0, nextState.lastFrame)

/-- Dispatch a JSON `InputEvent` and return `(status, frameBytes)`. -/
def dispatchJson (sid : UInt64) (eventJson : String) : IO (Int32 × ByteArray) := do
  let reg ← studioRegistry.get
  match findSlotIdx reg.slots sid with
  | none => return (-1, ByteArray.empty)
  | some idx =>
    let slot := reg.slots[idx]!
    match applyJsonEvent slot.state eventJson with
    | .error _ => return (-2, ByteArray.empty)
    | .ok nextState =>
      let slots' := reg.slots.set! idx { slot with state := nextState }
      studioRegistry.set { reg with slots := slots' }
      return (0, nextState.lastFrame)

/-- Idempotent read of the cached `GSIR` v1 binary frame without mutating session state
(fixes `#17` item #2: retrying after `GSIR_ERR_BUF_SMALL` never double-applies events!). -/
def getCachedFrame (sid : UInt64) : IO (Int32 × ByteArray) := do
  let reg ← studioRegistry.get
  match findSlotIdx reg.slots sid with
  | none => return (-1, ByteArray.empty)
  | some idx =>
    return (0, reg.slots[idx]!.state.lastFrame)

end Grassmann.CABI.Studio
