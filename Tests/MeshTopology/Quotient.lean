import Tests.MeshTopology.Util

/-!
QuotientTopology goldens: `quotient.json` (every named topology in 1-5 dimensions) and
`cross.json` (products). Checks the Julia tables, summaries, ghost lookups over whole padded
grids and random samples, slices, resize/resample, node identification and multilinear cells.
-/

open Lean MeshTopology Tests.Small

namespace Tests.MeshTopology.Quotient

/-- Every lookup `m[Val(K), idx…]` for `idx ∈ (0:n+1)^N`, column-major (`ghostgrid`). -/
def ghostGrid {N : Nat} (m : QuotientTopology N) (K : Nat) : Array Json :=
  let pad := m.size.map (· + 2)
  (Array.range (gridLength pad)).map fun k =>
    let idx := (cartesianIndex pad (k + 1)).map fun (i : Nat) => (i : Int) - 1
    jvec (m.ghost K idx)

/-- Check the ghost grids and samples of a case. -/
def checkGhosts {N : Nat} (lbl : String) (m : QuotientTopology N) (c : Json) : TestM Unit := do
  if let .ok gs := (c.getObjVal? "ghosts") then
    for g in ← jArr gs do
      let K ← gNat g "K"
      checkJ s!"{lbl} ghosts K={K}" (Json.arr (ghostGrid m K)) (← jField g "grid")
  if let .ok ss := (c.getObjVal? "ghostsamples") then
    for smp in ← jArr ss do
      let K ← gNat smp "K"
      let idx ← intsOf (← jField smp "idx")
      let v ← vecOf idx N
      let out ← jField smp "out"
      checkJ s!"{lbl} ghost K={K} {idx}" (jvec (m.ghost K v)) out
      -- the upstream value, where it differs, is Q11
      if let .ok u := out.getObjVal? "julia" then
        checkJ s!"{lbl} ghost (Q11 upstream) K={K} {idx}" (jvec (m.ghost K v (q11 := true))) u

/-- Tables, summary and flags. -/
def checkTable {N : Nat} (lbl : String) (m : QuotientTopology N) (c : Json) : TestM Unit := do
  checkJ s!"{lbl} table" (jquotient m) (← jField c "table")
  checkJ s!"{lbl} summary" (jstr m.summary) (← jField c "summary")

/-- A column-major grid of naturals. -/
def jgridN {N : Nat} (s : Vector Nat N) (a : Array Nat) : Json := jgrid s.toList (a.map jnat)

/-- Node identification, cells and the bilinear topology of a case. -/
def checkGrid {N : Nat} (name : String) (m : QuotientTopology N) (c : Json) : TestM Unit := do
  checkJ s!"{name} elementfuns" (jgridN m.size m.elementfuns) (← jField c "elementfuns")
  checkJ s!"{name} vertices" (jgridN m.size m.vertices) (← jField c "vertices")
  let vinv := if m.isOpen then (Array.range m.length).map (· + 1) else m.verticesInv
  checkJ s!"{name} verticesinv" (jnats vinv) (← jField c "verticesinv")
  checkJ s!"{name} duplicates" (jnats m.duplicates) (← jField c "duplicates")
  checkJ s!"{name} duplicatemap" (Json.arr (m.duplicateMap.map fun (a, b) => jpair a b))
    (← jField c "duplicatemap")
  checkJ s!"{name} uniquemap" (Json.arr (m.uniqueMap.map fun (a, b) => jpair a b))
    (← jField c "uniquemap")
  checkJ s!"{name} linearelements"
    (jgrid (m.size.toList.map (· - 1)) (m.linearElements.map jnats)) (← jField c "linearelements")
  if h : N = 2 then
    let b := BilinearTopology.ofQuotient (h ▸ m)
    checkJ s!"{name} bilinear" (Json.mkObj [
      ("q", Json.arr (b.quads.map fun v => jnats v.toArray)),
      ("t", Json.arr (b.tris.map fun v => jnats v.toArray)),
      ("iq", jnats b.quadIds), ("it", jnats b.triIds),
      ("split", Json.arr (b.split.map fun (a, k) => jpair a k)),
      ("v", jnats b.verticesInv), ("i", jgridN b.top.size b.vertices), ("nodes", jnat b.nodes)])
      (← jField c "bilinear")
  -- In one and two dimensions the transitive closure is exactly Julia's single-step
  -- identification whenever the gluing maps are involutions that Julia's `min` rule resolves in
  -- one step. It is not for Möbius and Hopf (the corner rule, an elementwise `min` of two
  -- resolved multi-indices, merges inequivalent corners), Klein (chains through two gluings
  -- stay split) and half-turns of even length (not involutions): Q7.
  let even (k : Nat) := m.size.toList[k]?.getD 1 % 2 == 0
  let skip := name.startsWith "Mobius" || name.startsWith "Hopf" || name.startsWith "Klein" ||
    (name.startsWith "Cone" && even 1) || (name.startsWith "Geographic" && even 0)
  if N ≤ 2 && !skip then
    checkJ s!"{name} elementfunsClosed" (jgridN m.size m.elementfunsClosed) (← jField c "elementfuns")

/-- One `quotient.json` case. -/
def checkCase (c : Json) : TestM Unit := do
  let name ← gStr c "name"
  let some (fam, sizes) := parseName name | throw <| IO.userError s!"bad name {name}"
  let ⟨N, m⟩ ← namedTopology fam sizes
  checkTable name m c
  checkJ s!"{name} display" (jstr m.displayString) (← jField c "display")
  checkJ s!"{name} print" (jstr m.printString) (← jField c "print")
  checkJ s!"{name} isopen" (jbool m.isOpen) (← jField c "isopen")
  checkJ s!"{name} iscompact" (jbool m.isCompact) (← jField c "iscompact")
  checkGhosts name m c
  let vals ← gArr c "subtopology_val"
  for h : a in [0:N] do
    checkJ s!"{name} subtopology Val({a + 1})" (jquotient (m.axisTopology ⟨a, h.2.1⟩)) vals[a]!
  for sl in ← gArr c "slices" do
    let colons ← natsOf (← jField sl "colons")
    let fixed ← intsOf (← jField sl "fixed")
    match m.sliceAt? colons.toList fixed with
    | some ⟨_, t⟩ => checkJ s!"{name} slice {colons} {fixed}" (jquotient t) (← jField sl "out")
    | none => check s!"{name} slice {colons}" false
  checkOptJ s!"{name} resize 7" ((m.resize? 7).map jquotient) (← jField c "resize")
  checkOptJ s!"{name} resample" ((m.resample? (m.size.map (· + 1))).map jquotient)
    (← jField c "resample")
  checkJ s!"{name} OpenTopology" (jquotient m.toOpen) (← jField c "open")
  checkGrid name m c


/-- Julia names of the default-size constructors in `quotient.json`. -/
def defaultTopology : String → Option SomeQuotient
  | "Hopf()" => some ⟨3, .hopfDefault⟩
  | "Open()" => some ⟨2, .openTop #v[61, 61]⟩
  | "Mirror()" => some ⟨2, .mirror #v[61, 61]⟩
  | "Clamped()" => some ⟨2, .clamped #v[61, 61]⟩
  | "Torus()" => some ⟨2, .torusDefault⟩
  | "Cylinder()" => some ⟨2, .cylinderDefault⟩
  | "Wing()" => some ⟨2, .wing #v[61, 20]⟩
  | "Mobius()" => some ⟨2, .mobius #v[61, 20]⟩
  | "Klein()" => some ⟨2, .kleinDefault⟩
  | "Cone()" => some ⟨2, .coneDefault⟩
  | "Cone(5)" => some ⟨2, .coneDefault 5⟩
  | "Geographic()" => some ⟨2, .geographicDefault⟩
  | "Geographic(9)" => some ⟨2, .geographicDefault 9⟩
  | "Tube()" => some ⟨2, .tubeDefault⟩
  | "Ball()" => some ⟨2, .ballDefault⟩
  | "Sphere()" => some ⟨2, .sphereDefault⟩
  | "Polar(4,5)" => some ⟨2, .ball #v[4, 5]⟩
  | "Revolved(4,5)" => some ⟨2, .tube2 #v[4, 5]⟩
  | "Torus((3,4))" => some ⟨2, .torus #v[3, 4]⟩
  | "Cylinder(9)" => some ⟨2, .cylinderDefault 9⟩
  | _ => none

/-- The products in `cross.json`, by name. -/
def crossTopology (name : String) : Option SomeQuotient :=
  let T1 (n : Nat) : QuotientTopology 1 := .torus #v[n]
  let T2 (a b : Nat) : QuotientTopology 2 := .torus #v[a, b]
  let T3 (a b c : Nat) : QuotientTopology 3 := .torus #v[a, b, c]
  let O1 (n : Nat) : QuotientTopology 1 := .openTop #v[n]
  let M1 (n : Nat) : QuotientTopology 1 := .mirror #v[n]
  match name with
  | "Open(3)×Open(4)" => some ⟨2, (O1 3).cross (O1 4)⟩
  | "Open(3,4)×Open(5)" => some ⟨3, (QuotientTopology.openTop #v[3, 4]).cross (O1 5)⟩
  | "Open(3)×Open(4,5)" => some ⟨3, (O1 3).cross (.openTop #v[4, 5])⟩
  | "Open(2,3)×Open(4,5)" => some ⟨4, (QuotientTopology.openTop #v[2, 3]).cross (.openTop #v[4, 5])⟩
  | "Open(3)×Open(2,3,4)" => some ⟨4, (O1 3).cross (.openTop #v[2, 3, 4])⟩
  | "Open(2,3,4)×Open(3)" => some ⟨4, (QuotientTopology.openTop #v[2, 3, 4]).cross (O1 3)⟩
  | "Open(3,4)×6" => some ⟨3, (QuotientTopology.openTop #v[3, 4]).crossInt 6⟩
  | "Open(3)×6" => some ⟨2, (O1 3).crossInt 6⟩
  | "6×Open(3,4)" => some ⟨3, QuotientTopology.intCross 6 (.openTop #v[3, 4])⟩
  | "6×Open(3)" => some ⟨2, QuotientTopology.intCross 6 (O1 3)⟩
  | "Torus(4)×5" => some ⟨2, (T1 4).crossInt 5⟩
  | "Mirror(4)×5" => some ⟨2, (M1 4).crossInt 5⟩
  | "Torus(3,4)×5" => some ⟨3, (T2 3 4).crossInt 5⟩
  | "Mobius(4,5)×3" => some ⟨3, (QuotientTopology.mobius #v[4, 5]).crossInt 3⟩
  | "Sphere(4,5)×3" => some ⟨3, (QuotientTopology.sphere #v[4, 5]).crossInt 3⟩
  | "Hopf(3,4,5)×3" => some ⟨4, (QuotientTopology.hopf3 #v[3, 4, 5]).crossInt 3⟩
  | "5×Torus(4)" => some ⟨2, QuotientTopology.intCross 5 (T1 4)⟩
  | "5×Mirror(4)" => some ⟨2, QuotientTopology.intCross 5 (M1 4)⟩
  | "5×Torus(3,4)" => some ⟨3, QuotientTopology.intCross 5 (T2 3 4)⟩
  | "5×Mobius(4,5)" => some ⟨3, QuotientTopology.intCross 5 (.mobius #v[4, 5])⟩
  | "Torus(4)×Torus(5)" => some ⟨2, (T1 4).cross (T1 5)⟩
  | "Torus(4)×Open(5)" => some ⟨2, (T1 4).cross (O1 5)⟩
  | "Mirror(4)×Torus(5)" => some ⟨2, (M1 4).cross (T1 5)⟩
  | "Clamped(4)×Mirror(5)" => some ⟨2, (QuotientTopology.clamped #v[4]).cross (M1 5)⟩
  | "Torus(3)×Torus(4,5)" => some ⟨3, (T1 3).cross (T2 4 5)⟩
  | "Mirror(3)×Mobius(4,5)" => some ⟨3, (M1 3).cross (.mobius #v[4, 5])⟩
  | "Torus(4,5)×Torus(3)" => some ⟨3, (T2 4 5).cross (T1 3)⟩
  | "Mobius(4,5)×Torus(3)" => some ⟨3, (QuotientTopology.mobius #v[4, 5]).cross (T1 3)⟩
  | "Sphere(4,5)×Mirror(3)" => some ⟨3, (QuotientTopology.sphere #v[4, 5]).cross (M1 3)⟩
  | "Torus(3)×Torus(3,4,5)" => some ⟨4, (T1 3).cross (T3 3 4 5)⟩
  | "Torus(3,4,5)×Torus(3)" => some ⟨4, (T3 3 4 5).cross (T1 3)⟩
  | "Torus(3)×Torus(2,3,4,5)" => some ⟨5, (T1 3).cross (.torus #v[2, 3, 4, 5])⟩
  | "Torus(2,3,4,5)×Torus(3)" => some ⟨5, (QuotientTopology.torus #v[2, 3, 4, 5]).cross (T1 3)⟩
  | "Torus(3,4)×Torus(5,6)" => some ⟨4, (T2 3 4).cross (T2 5 6)⟩
  | "Klein(4,5)×Mirror(3,4)" => some ⟨4, (QuotientTopology.klein #v[4, 5]).cross (.mirror #v[3, 4])⟩
  | "Torus(3,4)×Torus(3,4,5)" => some ⟨5, (T2 3 4).cross (T3 3 4 5)⟩
  | "Torus(3,4,5)×Torus(3,4)" => some ⟨5, (T3 3 4 5).cross (T2 3 4)⟩
  | "cross_sphere(Torus(4),Torus(5))" => some ⟨2, QuotientTopology.crossSphere (T1 4) (T1 5)⟩
  | "cross_sphere(Torus(4),Mirror(5))" => some ⟨2, QuotientTopology.crossSphere (T1 4) (M1 5)⟩
  | "cross_sector(Torus(4),Torus(5))" => some ⟨2, QuotientTopology.crossSector (T1 4) (T1 5)⟩
  | "cross_sector(Torus(4),Mirror(5))" => some ⟨2, QuotientTopology.crossSector (T1 4) (M1 5)⟩
  | "cross_sector(Torus(4),Torus(3,5))" => some ⟨3, QuotientTopology.crossSector (T1 4) (T2 3 5)⟩
  | "cross_sector(Torus(4),Mirror(3,5))" =>
    some ⟨3, QuotientTopology.crossSector (T1 4) (.mirror #v[3, 5])⟩
  | "cross_sector(Torus(4),Torus(3,4,5))" => some ⟨4, QuotientTopology.crossSector (T1 4) (T3 3 4 5)⟩
  | "cross_sector(Torus(4),Torus(3,3,4,5))" =>
    some ⟨5, QuotientTopology.crossSector (T1 4) (.torus #v[3, 3, 4, 5])⟩
  | _ => none

/-- Run `quotient.json` and `cross.json`. -/
def run : TestM Unit := do
  let j ← readJson "oracle/golden/meshtopology/quotient.json"
  for c in ← gArr j "cases" do
    checkCase c
  for c in ← gArr j "random" do
    let name ← gStr c "name"
    let some (fam, sizes) := parseName name | throw <| IO.userError s!"bad name {name}"
    let ⟨_, m⟩ ← namedTopology fam sizes
    checkJ s!"{name} table" (jquotient m) (← jField c "table")
    checkGhosts name m c
    checkJ s!"{name} elementfuns" (jgridN m.size m.elementfuns) (← jField c "elementfuns")
  for c in ← gArr j "defaults" do
    let name ← gStr c "name"
    match defaultTopology name with
    | some ⟨_, m⟩ => checkTable name m c
    | none => check s!"default {name}" false
  let x ← readJson "oracle/golden/meshtopology/cross.json"
  for c in ← gArr x "cases" do
    let name ← gStr c "name"
    match crossTopology name with
    | some ⟨_, m⟩ =>
      checkTable name m c
      checkGhosts name m c
    | none => check s!"cross {name}" false

end Tests.MeshTopology.Quotient
