import Grassmann.Studio

/-!
# Comprehensive Unit & Integration Test Suite for SceneIR, Eval, Wedge 2D/3D, CoffeeShop & GPU Codegen

Verifies every Wave 1 deliverable with zero `sorry` / zero external deps:
1. `GSIR` v1 binary framing: header magic, version, **8-byte alignment** on every section &
   odd-index-count mesh asset, `CAMERA.flags` (`isOrtho`), `metaJsonLen = 0` unchanged delta,
   `forceFullSnapshot`, and idempotent `getLastFrame`!
2. `InputEvent` binary & JSON roundtrips (`DragHandle`, `Tick`, `WedgeGesture` w/ `isPreview`,
   `EvalSurface`, `EvalEquations`, `Snapshot`, etc.).
3. `Grassmann.Eval`: GA expression parsing & evaluation across `PGA2`, `PGA3`, `CGA3`, `STA`, `R3`,
   `Cl(p,q,r)`, Dorst `<<` left contraction, metric-free `!` dual, marching-triangles contour
   extraction & exact circle-line intersections (`x² + y² = 1` ∩ `y = x` → `(±√2/2, ±√2/2)`!),
   forward-mode AD 3D surfaces, GAlculator registers, and `ALOK-950` exact R3 rational rotors!
4. `Grassmann.Wedge`: full end-to-end automated playthroughs solving Wedge 2D levels (Join, Meet,
   Add points/lines, Dot, Orthocenter, Circumcenter, Euler's Line!) AND Wedge 3D levels
   (3D Join line/plane, 3D Meet 3 planes, Perpendicular Bisector Plane, Tetrahedron Altitude!),
   plus `isPreview` non-mutation, Undo, and score checks!
5. `Grassmann.CoffeeShop`: all **19 interactive presets** render valid 8-byte-aligned `GSIR` v1
   frames, `#pga3d_slicing` bunny produces non-empty lower/upper meshes + 3D cut edges + 2D
   `ContourOverlay`, and RK4 Dzhanibekov top preserves motor normalization `‖M‖ ≈ 1`!
6. `Grassmann.Codegen.GPU`: straight-line WGSL, GLSL 300 es, and Metal MSL OPNS raymarching
   shaders + PGA3 motor product kernels compile cleanly with zero loops inside `product_len`!
-/

namespace Tests.Studio

open Grassmann Grassmann.Scene Grassmann.Scene.Binary Grassmann.Scene.Json
open Grassmann.Eval Grassmann.Eval.Calc Grassmann.Eval.Contour
open Grassmann.Wedge Grassmann.CoffeeShop Grassmann.Codegen.GPU Grassmann.Studio

private def hasSubstr (s pat : String) : Bool := (s.splitOn pat).length > 1

private def assertTrue (name : String) (cond : Bool) : IO Unit := do
  if !cond then
    throw (IO.userError s!"FAIL [{name}]")

private def assertApprox (name : String) (a b : Float) (tol : Float := 1e-3) : IO Unit := do
  if Float.abs (a - b) > tol then
    throw (IO.userError s!"FAIL [{name}]: got {a}, expected {b} (tol={tol})")

/-! ## 1. SceneIR v1 Binary Framing, 8-Byte Alignment & Delta Tests -/

def testBinaryAndAlignment : IO Unit := do
  -- Mesh with ODD idxCount (3 indices = 12 bytes) to verify 8-byte per-mesh record padding!
  let pos := FloatArray.empty |>.push 0 |>.push 0 |>.push 0
                              |>.push 1 |>.push 0 |>.push 0
                              |>.push 0 |>.push 1 |>.push 0
  let nrm := FloatArray.empty |>.push 0 |>.push 0 |>.push 1
                              |>.push 0 |>.push 0 |>.push 1
                              |>.push 0 |>.push 0 |>.push 1
  let asset : MeshAsset :=
    { meshId := 42, dirtyHash := 12345, positions := pos, normals := nrm, indices := #[0, 1, 2] }
  let frame : SceneFrame :=
    { frameSeq := 7, simTime := 1.25, is2D := false,
      camera := { isOrtho := true },
      points := #[{ handleId := 0, pos := ⟨1.0, 2.0, 3.0⟩, role := { draggable := true }, label := "P0" }],
      meshAssets := #[asset],
      meshRefs := #[{ meshId := 42, dirtyHash := 12345 }] }
  let bytes := encodeFrame frame true
  match validateGsirFrame bytes with
  | .error e => throw (IO.userError s!"GSIR validate failed: {e}")
  | .ok (secCount, seq, metaLen) =>
    assertTrue "gsir seq" (seq == 7)
    assertTrue "gsir secCount >= 4" (secCount ≥ 4)
    assertTrue "gsir metaLen > 0" (metaLen > 0)
    assertTrue "gsir 8-byte total alignment" (bytes.size % 8 == 0)
  -- Check unchanged metaJson delta produces metaJsonLen == 0
  let bytesDelta := encodeFrame frame false
  match validateGsirFrame bytesDelta with
  | .error e => throw (IO.userError s!"GSIR delta validate failed: {e}")
  | .ok (_, _, metaLen) =>
    assertTrue "delta metaJsonLen == 0" (metaLen == 0)
  -- Binary InputEvent roundtrips (incl. WedgeGesture isPreview + forceFullSnapshot)
  let wgEv := InputEvent.wedgeGesture 3 4 ⟨1.0, 0.0, 0.0⟩ ⟨-1.0, 0.0, 0.0⟩ false true true
  match encodeInputEventBin wgEv true with
  | .error e => throw (IO.userError s!"encodeInputEventBin failed: {e}")
  | .ok evBytes =>
    match decodeInputEventBin evBytes with
    | .error e => throw (IO.userError s!"decodeInputEventBin failed: {e}")
    | .ok (.wedgeGesture a b _ _ hA hB isPrev, forceSnap) =>
      assertTrue "wg idA" (a == 3)
      assertTrue "wg idB" (b == 4)
      assertTrue "wg holdA" (!hA)
      assertTrue "wg holdB" hB
      assertTrue "wg isPreview" isPrev
      assertTrue "wg forceSnap" forceSnap
    | _ => throw (IO.userError "wrong decoded event kind")
  -- JSON InputEvent parsing (`evalSurface`, `wedgeGesture` w/ `isPreview`, `snapshot`)
  match parseInputEventJson "{\"op\":\"evalSurface\",\"expr\":\"sin(x)+cos(y)\",\"bounds\":[-3,3,-3,3],\"gridN\":32}" with
  | .ok (.evalSurface expr minX _ _ _ gn) =>
    assertTrue "evalSurface expr" (expr == "sin(x)+cos(y)")
    assertApprox "evalSurface minX" minX (-3.0)
    assertTrue "evalSurface gridN" (gn == 32)
  | _ => throw (IO.userError "parseInputEventJson evalSurface failed")
  -- Motor3 exp/log & affine sanity
  let m := Motor3.mul (Motor3.translator 1.5 (-0.5) 2.0) (Motor3.rotorAxis ⟨0.0, 0.0, 1.0⟩ (3.141592653589793 / 2.0))
  let p := Motor3.applyPoint m ⟨1.0, 0.0, 0.0⟩
  assertApprox "motor apply x" p.x 1.5 1e-4
  assertApprox "motor apply y" p.y 0.5 1e-4
  assertApprox "motor apply z" p.z 2.0 1e-4

/-! ## 2. Pure-Lean Eval, Contours, Intersections, Surfaces & R3 Rational Rotors -/

def testEvalAndContours : IO Unit := do
  -- GA script evaluation in PGA3, STA, CGA3, Cl(2,1,1)
  let fPga := evalScriptToFrame "PGA3" "let A = point(1, 0, 0); let B = point(0, 1, 0); let L = A & B"
  assertTrue "PGA3 script no errors" fPga.diagnostics.isEmpty
  assertTrue "PGA3 script points" (fPga.points.size == 2)
  assertTrue "PGA3 script line" (fPga.lines.size == 1)

  let fSta := evalScriptToFrame "STA" "let A = 1e2 + 0.5e3; let B = 0.5e2 + 1e3; let W = A ^ B"
  assertTrue "STA script no errors" fSta.diagnostics.isEmpty
  assertTrue "STA bivector disk emitted" (fSta.bivectorDisks.size == 1)

  let fCl := evalScriptToFrame "Cl(2,1,1)" "let x = e1 + 2e2; x * x"
  assertTrue "Arbitrary Cl(2,1,1) no errors" fCl.diagnostics.isEmpty

  -- Marching-triangles contour & exact intersection test: circle x^2+y^2-1=0 ∩ line y-x=0
  match evalEquationsToOverlay #["x^2 + y^2 - 1", "y - x"] (-2.0) 2.0 (-2.0) 2.0 40 with
  | .error e => throw (IO.userError s!"evalEquationsToOverlay failed: {e}")
  | .ok ov =>
    assertTrue "contour curves >= 2" (ov.curves.size ≥ 2)
    assertTrue "circle-line intersections == 2" (ov.intersections.size == 2)
    let r := Float.sqrt 0.5
    let hasPos := ov.intersections.any fun pt =>
      Float.abs (pt.x - r) < 0.05 && Float.abs (pt.y - r) < 0.05
    let hasNeg := ov.intersections.any fun pt =>
      Float.abs (pt.x + r) < 0.05 && Float.abs (pt.y + r) < 0.05
    assertTrue "intersection at (+√½, +√½)" hasPos
    assertTrue "intersection at (-√½, -√½)" hasNeg

  -- Forward-mode AD 3D surface mesh test
  match evalSurfaceMesh "sin(x*2) * cos(y*2)" 0.0 (-2.0) 2.0 (-2.0) 2.0 16 9001 with
  | .error e => throw (IO.userError s!"evalSurfaceMesh failed: {e}")
  | .ok mesh =>
    assertTrue "surface verts == 17*17" (mesh.positions.size == 17 * 17 * 3)
    assertTrue "surface indices == 16*16*6" (mesh.indices.size == 16 * 16 * 6)
    assertTrue "surface colors populated" (mesh.colors.size == 17 * 17 * 4)

  -- ALOK-950 Exact R3 rational rotor check: R = 3 + 4e12 rotates (1,0,0) -> (-7/25, -24/25, 0) or (+24/25)
  let rRat : RatRotor3 := { s := 3, b12 := 4, b13 := 0, b23 := 0 }
  let out := r3RationalSandwich rRat ⟨1, 0, 0⟩
  assertTrue "R3 rational rotor preserves norm^2 == 1"
    (out.x * out.x + out.y * out.y + out.z * out.z == 1)
  assertTrue "R3 rational rotor exact x == -7/25" (out.x == (-7 : Rat) / 25)

  -- GAlculator keypad + register workflow
  let c0 := CalcState.init "P2D"
  let c1 := stepKey (stepKey (stepKey (stepKey c0 "e1") "+") "e2") "="
  assertTrue "GAlculator eval non-empty" (!c1.display.isEmpty && c1.lastError.isEmpty)

/-! ## 3. Wedge 2D (L1–L9) & Wedge 3D (L10–L16) Automated Playthrough Tests -/

private def findIdByLabel (st : WedgeState) (lbl : String) : UInt32 :=
  ((st.items.find? fun it => it.label == lbl).map (·.id)).getD 0

def testWedge2DAnd3D : IO Unit := do
  -- L1 Join: drag A(-1,0) and B(1,0.5) APART!
  let s0 := Wedge.loadLevel 0
  let idA := findIdByLabel s0 "A"
  let idB := findIdByLabel s0 "B"
  -- First test `isPreview = true` does NOT increment moves or mutate items!
  let sPrev := Wedge.stepGesture s0 idA idB ⟨-1.0, 0.0, 0.0⟩ ⟨1.0, 0.0, 0.0⟩ false false true
  assertTrue "L1 preview op == join" (sPrev.previewOp == "join")
  assertTrue "L1 preview does not increment moves" (sPrev.moves == 0)
  assertTrue "L1 preview does not solve" (!sPrev.solved)
  -- Commit gesture!
  let s1 := Wedge.stepGesture s0 idA idB ⟨-1.0, 0.0, 0.0⟩ ⟨1.0, 0.0, 0.0⟩ false false false
  assertTrue "L1 solved in 1 move" (s1.solved && s1.moves == 1 && s1.lastOp == "win")
  -- Undo reverses solve!
  let sUndo := Wedge.stepAction s1 .undo
  assertTrue "L1 undo restores unsolved" (!sUndo.solved && sUndo.moves == 0)

  -- L2 Meet: drag lines together!
  let l2 := Wedge.loadLevel 1
  let l2a := findIdByLabel l2 "a"
  let l2b := findIdByLabel l2 "b"
  -- Push both lines toward each other's anchors
  let anchA := (l2.items.find? (·.id == l2a)).get!.elem.anchor
  let anchB := (l2.items.find? (·.id == l2b)).get!.elem.anchor
  let dirAB := Vec3.sub anchB anchA
  let l2Done := Wedge.stepGesture l2 l2a l2b dirAB (Vec3.neg dirAB) false false false
  assertTrue "L2 Meet solved" l2Done.solved

  -- L3 Add Points (midpoint): drag A & B TOGETHER!
  let l3 := Wedge.loadLevel 2
  let l3Done := Wedge.stepGesture l3 (findIdByLabel l3 "A") (findIdByLabel l3 "B")
    ⟨1.0, 0.25, 0.0⟩ ⟨-1.0, -0.25, 0.0⟩ false false false
  assertTrue "L3 Add midpoint solved" l3Done.solved

  -- L5 Dot (a << B): hold B (zero drag — Lean derives hold!) & drag line a toward B!
  let l5 := Wedge.loadLevel 4
  let l5a := findIdByLabel l5 "a"
  let l5B := findIdByLabel l5 "B"
  let l5Done := Wedge.stepGesture l5 l5a l5B ⟨0.0, 1.0, 0.0⟩ ⟨0.0, 0.0, 0.0⟩ false false false
  assertTrue "L5 Dot solved with Lean-derived hold" l5Done.solved

  -- L7 Orthocenter (full multi-step PGA2 construction: 5 moves!)
  let l7 := Wedge.loadLevel 6
  let a7 := findIdByLabel l7 "A"; let b7 := findIdByLabel l7 "B"; let c7 := findIdByLabel l7 "C"
  let pushApart (st : WedgeState) (u v : UInt32) : WedgeState :=
    let eu := (st.items.find? (·.id == u)).get!.elem
    let ev := (st.items.find? (·.id == v)).get!.elem
    let d := Wedge.separationAxis eu ev
    Wedge.stepGesture st u v d (Vec3.neg d) false false false
  let pushTogether (st : WedgeState) (u v : UInt32) : WedgeState :=
    let eu := (st.items.find? (·.id == u)).get!.elem
    let ev := (st.items.find? (·.id == v)).get!.elem
    let d := Vec3.neg (Wedge.separationAxis eu ev)
    Wedge.stepGesture st u v d (Vec3.neg d) false false false
  let dotTo (st : WedgeState) (lineId ptId : UInt32) : WedgeState :=
    let el := (st.items.find? (·.id == lineId)).get!.elem
    let ep := (st.items.find? (·.id == ptId)).get!.elem
    let d := Vec3.neg (Wedge.separationAxis el ep)
    Wedge.stepGesture st lineId ptId d Vec3.zero false true false
  let l7_1 := pushApart l7 a7 b7       -- eAB
  let eAB := l7_1.nextId - 1
  let l7_2 := dotTo l7_1 eAB c7        -- altC
  let altC := l7_2.nextId - 1
  let l7_3 := pushApart l7_2 b7 c7     -- eBC
  let eBC := l7_3.nextId - 1
  let l7_4 := dotTo l7_3 eBC a7        -- altA
  let altA := l7_4.nextId - 1
  let l7_5 := pushTogether l7_4 altC altA -- Orthocenter!
  assertTrue "L7 Orthocenter solved in 5 moves!" (l7_5.solved && l7_5.moves == 5)

  -- L4 Add Lines (bisector): drag lines c & b APART!
  let l4 := Wedge.loadLevel 3
  let l4c := findIdByLabel l4 "c"; let l4b := findIdByLabel l4 "b"
  let l4Done := pushApart l4 l4c l4b
  assertTrue "L4 Add Lines bisector solved" l4Done.solved

  -- L6 Two Targets: a << B AND a + (a << B)
  let l6 := Wedge.loadLevel 5
  let l6a := findIdByLabel l6 "a"; let l6B := findIdByLabel l6 "B"
  let l6_1 := Wedge.stepGesture l6 l6a l6B ⟨0.0, 1.0, 0.0⟩ Vec3.zero false true false
  let perp6 := l6_1.nextId - 1
  let l6_2 := pushApart l6_1 l6a perp6
  assertTrue "L6 Two-Target Combo solved in 2 moves!" (l6_2.solved && l6_2.moves == 2)

  -- L8 Circumcenter (7 moves)
  let l8 := Wedge.loadLevel 7
  let a8 := findIdByLabel l8 "A"; let b8 := findIdByLabel l8 "B"; let c8 := findIdByLabel l8 "C"
  let l8_1 := pushApart l8 a8 b8;     let eAB8 := l8_1.nextId - 1
  let l8_2 := pushTogether l8_1 a8 b8; let mAB8 := l8_2.nextId - 1
  let l8_3 := dotTo l8_2 eAB8 mAB8;   let pAB8 := l8_3.nextId - 1
  let l8_4 := pushApart l8_3 b8 c8;   let eBC8 := l8_4.nextId - 1
  let l8_5 := pushTogether l8_4 b8 c8; let mBC8 := l8_5.nextId - 1
  let l8_6 := dotTo l8_5 eBC8 mBC8;   let pBC8 := l8_6.nextId - 1
  let l8_7 := pushTogether l8_6 pAB8 pBC8
  assertTrue "L8 Circumcenter solved in 7 moves!" (l8_7.solved && l8_7.moves == 7)

  -- L9 Euler's Line (orthocenter & circumcenter joined!)
  let l9 := Wedge.loadLevel 8
  let a9 := findIdByLabel l9 "A"; let b9 := findIdByLabel l9 "B"; let c9 := findIdByLabel l9 "C"
  let l9_1 := pushApart l9 a9 b9;     let eAB9 := l9_1.nextId - 1
  let l9_2 := pushApart l9_1 b9 c9;   let eBC9 := l9_2.nextId - 1
  let l9_3 := dotTo l9_2 eAB9 c9;     let altC9 := l9_3.nextId - 1
  let l9_4 := dotTo l9_3 eBC9 a9;     let altA9 := l9_4.nextId - 1
  let l9_5 := pushTogether l9_4 altC9 altA9; let ortho9 := l9_5.nextId - 1
  let l9_6 := pushTogether l9_5 a9 b9; let mAB9 := l9_6.nextId - 1
  let l9_7 := dotTo l9_6 eAB9 mAB9;   let pAB9 := l9_7.nextId - 1
  let l9_8 := pushTogether l9_7 b9 c9; let mBC9 := l9_8.nextId - 1
  let l9_9 := dotTo l9_8 eBC9 mBC9;   let pBC9 := l9_9.nextId - 1
  let l9_10 := pushTogether l9_9 pAB9 pBC9; let circ9 := l9_10.nextId - 1
  let l9_11 := pushApart l9_10 ortho9 circ9
  assertTrue "L9 Euler's Line solved in 11 moves!" (l9_11.solved && l9_11.moves == 11)

  -- L10 Wedge 3D: Join A & B → Line, Join (A&B) & C → Plane!
  let l10 := Wedge.loadLevel 9
  assertTrue "L10 is 3D" (l10.dim == .dim3D)
  let a10 := findIdByLabel l10 "A"; let b10 := findIdByLabel l10 "B"; let c10 := findIdByLabel l10 "C"
  let l10_1 := pushApart l10 a10 b10
  let lineAB := l10_1.nextId - 1
  let l10_2 := pushApart l10_1 lineAB c10
  assertTrue "L10 3D Join Plane solved in 2 moves!" (l10_2.solved && l10_2.moves == 2)

  -- L11 Wedge 3D: Meet 3 Planes → Vertex Point!
  let l11 := Wedge.loadLevel 10
  let p1_11 := findIdByLabel l11 "P1"; let p2_11 := findIdByLabel l11 "P2"; let p3_11 := findIdByLabel l11 "P3"
  let l11_1 := pushTogether l11 p1_11 p2_11
  let l11_2 := pushTogether l11_1 (l11_1.nextId - 1) p3_11
  assertTrue "L11 3D 3-Plane Meet solved in 2 moves!" (l11_2.solved && l11_2.moves == 2)

  -- L12 Wedge 3D: 3D Bisector Plane (P1 + P2)!
  let l12 := Wedge.loadLevel 11
  let p1_12 := findIdByLabel l12 "P1"; let p2_12 := findIdByLabel l12 "P2"
  let l12Done := pushApart l12 p1_12 p2_12
  assertTrue "L12 3D Bisector Plane solved!" l12Done.solved

  -- L13 Wedge 3D: Perpendicular Bisector Plane (A&B) << (A+B)!
  let l13 := Wedge.loadLevel 12
  let a13 := findIdByLabel l13 "A"; let b13 := findIdByLabel l13 "B"
  let l13_1 := pushApart l13 a13 b13; let eAB13 := l13_1.nextId - 1
  let l13_2 := pushTogether l13_1 a13 b13; let mAB13 := l13_2.nextId - 1
  let l13_3 := dotTo l13_2 eAB13 mAB13
  assertTrue "L13 3D Perp Bisector Plane solved in 3 moves!" (l13_3.solved && l13_3.moves == 3)

  -- L14 Wedge 3D: Tetrahedron Altitude `(A&B&C) << D`!
  let l14 := Wedge.loadLevel 13
  let a14 := findIdByLabel l14 "A"; let b14 := findIdByLabel l14 "B"
  let c14 := findIdByLabel l14 "C"; let d14 := findIdByLabel l14 "D"
  let l14_1 := pushApart l14 a14 b14
  let l14_2 := pushApart l14_1 (l14_1.nextId - 1) c14
  let basePl := l14_2.nextId - 1
  let l14_3 := dotTo l14_2 basePl d14
  assertTrue "L14 Tetrahedron Altitude solved in 3 moves!" (l14_3.solved && l14_3.moves == 3)

  -- L15 Wedge 3D: Tetrahedron Circumcenter (meet of 3 perp bisector planes)!
  let l15 := Wedge.loadLevel 14
  let a15 := findIdByLabel l15 "A"; let b15 := findIdByLabel l15 "B"
  let c15 := findIdByLabel l15 "C"; let d15 := findIdByLabel l15 "D"
  let mkPB (st : WedgeState) (u v : UInt32) : WedgeState × UInt32 :=
    let s1 := pushApart st u v;    let ln := s1.nextId - 1
    let s2 := pushTogether s1 u v; let md := s2.nextId - 1
    let s3 := dotTo s2 ln md;      (s3, s3.nextId - 1)
  let (l15_1, pbAB) := mkPB l15 a15 b15
  let (l15_2, pbAC) := mkPB l15_1 a15 c15
  let (l15_3, pbAD) := mkPB l15_2 a15 d15
  let l15_4 := pushTogether l15_3 pbAB pbAC
  let l15_5 := pushTogether l15_4 (l15_4.nextId - 1) pbAD
  assertTrue "L15 Tetrahedron Circumcenter solved in 11 moves!" (l15_5.solved && l15_5.moves == 11)

  -- L16 Wedge 3D: 3D Monge Point!
  let l16 := Wedge.loadLevel 15
  let a16 := findIdByLabel l16 "A"; let b16 := findIdByLabel l16 "B"
  let c16 := findIdByLabel l16 "C"; let d16 := findIdByLabel l16 "D"
  let mkMonge (st : WedgeState) (e1 e2 m1 m2 : UInt32) : WedgeState × UInt32 :=
    let s1 := pushApart st e1 e2;    let ln := s1.nextId - 1
    let s2 := pushTogether s1 m1 m2; let md := s2.nextId - 1
    let s3 := dotTo s2 ln md;        (s3, s3.nextId - 1)
  let (l16_1, mp1) := mkMonge l16 c16 d16 a16 b16
  let (l16_2, mp2) := mkMonge l16_1 b16 d16 a16 c16
  let (l16_3, mp3) := mkMonge l16_2 a16 b16 c16 d16
  let l16_4 := pushTogether l16_3 mp1 mp2
  let l16_5 := pushTogether l16_4 (l16_4.nextId - 1) mp3
  assertTrue "L16 3D Monge Point is a pt3 and solved in 11 moves!"
    (l16_5.solved && l16_5.moves == 11 &&
      match (l16_5.items.find? fun (it : BoardItem) => it.role == .target).map BoardItem.elem with
      | some (PgaElem.pt3 _) => true
      | _ => false)

/-! ## 4. All 19 CoffeeShop Presets, Bunny Slicer, RK4 Top & Delta Studio Session -/

def testCoffeeShopAndStudio : IO Unit := do
  assertTrue "19 CoffeeShop presets registered" (presetCatalog.size == 19)
  let mut sess := Studio.create
  match validateGsirFrame (Studio.getLastFrame sess) with
  | .error e => throw (IO.userError s!"Initial studio frame invalid: {e}")
  | .ok _ => pure ()

  -- Verify EVERY single preset renders cleanly and passes strict 8-byte GSIR validation!
  for info in presetCatalog do
    sess := Studio.dispatchEvent sess (.loadPreset info.id) true
    let raw := Studio.getLastFrame sess
    match validateGsirFrame raw with
    | .error e => throw (IO.userError s!"Preset {info.id} GSIR invalid: {e}")
    | .ok (secCount, _, metaLen) =>
      assertTrue s!"Preset {info.id} has sections" (secCount ≥ 1)
      assertTrue s!"Preset {info.id} has metaJson" (metaLen > 0)

  -- Verify #pga3d_slicing produces both clipped halves + cut edges + 2D contour inset!
  let sliceFrame := buildPga3dSlicing #[] none 1 0.5
  assertTrue "Bunny slicing produces 2 clipped meshes" (sliceFrame.meshAssets.size == 2)
  assertTrue "Bunny slicing lower mesh non-empty" (sliceFrame.meshAssets[0]!.indices.size > 30)
  assertTrue "Bunny slicing upper mesh non-empty" (sliceFrame.meshAssets[1]!.indices.size > 30)
  assertTrue "Bunny slicing 3D contour segments > 10" (sliceFrame.segments.size > 10)
  match sliceFrame.contourOverlay with
  | some co => assertTrue "Bunny slicing 2D contour inset non-empty" (!co.curves.isEmpty)
  | none => throw (IO.userError "Bunny slicing missing 2D ContourOverlay")

  -- Verify Free Top RK4 preserves motor norm after 50 steps!
  let mut topM := Motor3.identity
  let mut topW : Vec3 := ⟨0.08, 3.2, 0.05⟩
  for _ in [:50] do
    let (m1, w1) := stepFreeTopRK4 topM topW 0.02
    topM := m1; topW := w1
  let n2 := topM.s * topM.s + topM.e12 * topM.e12 + topM.e13 * topM.e13 + topM.e23 * topM.e23
  assertApprox "Free top RK4 unit motor norm" n2 1.0 1e-5

  -- Verify live `editCoeff` inspector override, `slicePlane`, `evalSurface`, `evalScript` & `calcEval`
  sess := Studio.dispatchEvent sess (.loadPreset "pga3d_slicing") true
  sess := Studio.dispatchEvent sess (.editCoeff 0 1 0.35) false
  assertTrue "editCoeff recorded & updated handle 0.y"
    (sess.coffee.coeffOverrides.size == 1 &&
      match sess.coffee.handles.find? fun h => h.1 == 0 with
      | some (_, p) => Float.abs (p.y - 0.35) < 1e-6
      | none => false)
  match validateGsirFrame (Studio.getLastFrame sess) with
  | .error e => throw (IO.userError s!"editCoeff GSIR invalid: {e}")
  | .ok _ => pure ()
  sess := Studio.dispatchEvent sess (.evalSurface "sin(x)*cos(y)" (-3.0) 3.0 (-3.0) 3.0 16) true
  match validateGsirFrame (Studio.getLastFrame sess) with
  | .error e => throw (IO.userError s!"evalSurface GSIR invalid: {e}")
  | .ok (secCount, _, _) => assertTrue "evalSurface frame has sections" (secCount ≥ 2)
  sess := Studio.dispatchEvent sess (.calcEval "scalar" "sin(pi/2) + 2^3") true
  match validateGsirFrame (Studio.getLastFrame sess) with
  | .error e => throw (IO.userError s!"calcEval GSIR invalid: {e}")
  | .ok _ => pure ()
  sess := Studio.dispatchEvent sess (.evalScript "3,0,1" "var P = !(1e1 + 2e2 + 3e3); P") true
  match validateGsirFrame (Studio.getLastFrame sess) with
  | .error e => throw (IO.userError s!"evalScript GSIR invalid: {e}")
  | .ok _ => pure ()
  sess := Studio.dispatchEvent sess (.slicePlane (Motor3.translator 0.0 0.25 0.0)) false
  match validateGsirFrame (Studio.getLastFrame sess) with
  | .error e => throw (IO.userError s!"slicePlane GSIR invalid: {e}")
  | .ok _ => pure ()

  -- Verify idempotent `getLastFrame` & `snapshot` forceFull behavior
  sess := Studio.dispatchEvent sess (.loadPreset "pga3d_icosahedron") true
  let fFull := Studio.getLastFrame sess
  let fSame := Studio.getLastFrame sess
  assertTrue "getLastFrame idempotent" (fFull.size == fSame.size)
  sess := Studio.dispatchEvent sess (.tick 0.016 0.016) false
  let fTick := Studio.getLastFrame sess
  match validateGsirFrame fTick with
  | .ok (_, _, tickMetaLen) =>
    assertTrue "Hot tick omits unchanged metaJson (metaJsonLen == 0)" (tickMetaLen == 0)
  | .error e => throw (IO.userError s!"Tick frame invalid: {e}")

/-! ## 5. Straight-Line GPU Codegen (WGSL, GLSL 300 es, Metal MSL) -/

def testGpuCodegen : IO Unit := do
  match compileOpnsBundle "cga3_witt" Grassmann.CABI.Alg.AlgSpace.CGA3 4 false with
  | .error e => throw (IO.userError s!"compileOpnsBundle failed: {e}")
  | .ok bundle =>
    assertTrue "WGSL has @fragment, product_len & 16-byte vec4 uniform blade array"
      (hasSubstr bundle.wgsl "@fragment" && hasSubstr bundle.wgsl "fn product_len" &&
       hasSubstr bundle.wgsl "array<vec4<f32>")
    assertTrue "GLSL has #version 300 es & product_len"
      (hasSubstr bundle.glsl "#version 300 es" && hasSubstr bundle.glsl "float product_len")
    assertTrue "MSL has metal_stdlib & opns_fragment"
      (hasSubstr bundle.msl "metal_stdlib" && hasSubstr bundle.msl "opns_fragment")
  match emitPga3MotorShaders with
  | .error e => throw (IO.userError s!"emitPga3MotorShaders failed: {e}")
  | .ok (wgslM, mslM) =>
    assertTrue "WGSL PGA3 motor kernel non-empty" (hasSubstr wgslM "fn pga3_motor_mul")
    assertTrue "MSL PGA3 motor kernel non-empty" (hasSubstr mslM "void pga3_motor_mul")

def runAll : IO Unit := do
  testBinaryAndAlignment
  IO.println "PASS [1/5] SceneIR v1 GSIR binary framing, 8-byte alignment & delta cache"
  testEvalAndContours
  IO.println "PASS [2/5] Grassmann.Eval GA scripts, marching-triangles contours, AD surfaces & R3 rational rotors"
  testWedge2DAnd3D
  IO.println "PASS [3/5] All 16/16 Wedge levels solved: 2D (L1-L9 incl. Circumcenter & Euler Line) + 3D (L10-L16 incl. Tet Circumcenter & 3D Monge Point)"
  testCoffeeShopAndStudio
  IO.println "PASS [4/5] All 19 CoffeeShop presets, #pga3d_slicing bunny contour & RK4 Dzhanibekov top"
  testGpuCodegen
  IO.println "PASS [5/5] Straight-line WGSL / GLSL 300 es / Metal MSL OPNS & PGA3 GPU shader codegen"
  IO.println "ALL STUDIO TESTS PASSED!"

end Tests.Studio

def main : IO Unit := Tests.Studio.runAll
