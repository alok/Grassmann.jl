import MeshTopology.Obj
import Tests.MeshTopology.Util

/-! New authored OBJ profile fixtures, kept separate from pinned Julia oracle goldens. -/

namespace Tests.MeshTopology.Obj

open Tests.Small Lean _root_.MeshTopology _root_.MeshTopology.Obj StaticVectors

private def kindName : ErrorKind → String
  | .syntax => "syntax"
  | .unsupportedRecord => "unsupportedRecord"
  | .unsupportedIndex => "unsupportedIndex"
  | .unsupportedVertex => "unsupportedVertex"
  | .unsupportedFace => "unsupportedFace"
  | .unsupportedContinuation => "unsupportedContinuation"
  | .nonAscii => "nonAscii"
  | .coordinate => "coordinate"
  | .coordinateRange => "coordinateRange"
  | .indexRange => "indexRange"
  | .degenerate => "degenerate"
  | .nonPlanarQuad => "nonPlanarQuad"
  | .nonConvexQuad => "nonConvexQuad"
  | .emptyMesh => "emptyMesh"
  | .connectivity => "connectivity"

private def pointJson (p : Point) : Json := Json.arr (p.toArray.map fun q =>
  Json.mkObj [("num", toJson (toString q.num)), ("den", toJson (toString q.den))])

private def ids : Corners → Array Nat
  | .triangle v => v.toArray
  | .quad v => v.toArray

/-- A consumer obtains bounded node ids for every accepted triangle without another check. -/
theorem acceptedNodeBounds (m : Mesh) (e : Fin m.top.totalElements) (k : Fin 3) :
    (m.top.vertexFin m.connectivity e k).1 < m.vertices.size := by
  rw [← m.nodes_match]
  exact (m.top.vertexFin m.connectivity e k).2

/-- A huge original integer cannot wrap to an existing node. -/
theorem hugeOriginalRejected : resolveIndex? 3 18446744073709551617 = none := by decide

/-- Zero is not an OBJ node id, including at an empty vertex list. -/
theorem zeroRejected (count : Nat) : resolveIndex? count 0 = none := by
  simp [resolveIndex?]

private def originVertices : Array Vertex :=
  #[⟨Values.ofFn fun _ => (0 : Rat), #v["0", "0", "0"], 1⟩]

private def repeatedTop : SimplexTopology 3 :=
  .ofElements #[#v[1, 1, 1]] (p := some 1)

-- A geometrically valid empty topology still cannot be directly constructed externally.
example : True := by
  fail_if_success
    have : Mesh := {
      source := ""
      vertices := #[]
      faces := #[]
      top := SimplexTopology.ofElements #[] (p := some 0)
      nodes_match := rfl
      connectivity := by decide +kernel
      geometry_checked := by decide +kernel
      triangles_checked := by decide +kernel }
  trivial

example : True := by
  fail_if_success
    have : Mesh := Mesh.mk "" #[] #[] (.ofElements #[] (p := some 0))
      rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
  trivial

example : True := by
  fail_if_success
    have : Mesh := ⟨"", #[], #[], .ofElements #[] (p := some 0),
      rfl, by decide +kernel, by decide +kernel, by decide +kernel⟩
  trivial

-- Bounds and the old face certificate still hold for the reviewer's repeated triangle.
example : repeatedTop.valid = true := by decide +kernel
example : (#[] : Array Face).all (fun f => geometryValid originVertices f.corners) = true := by
  decide +kernel

-- The newly required actual-triangle certificate cannot hold, even with empty faces.
example : repeatedTop.fulltopology.all
    (fun t => geometryValid originVertices (.triangle t)) = false := by decide +kernel

/-- A bounds-valid repeated topology cannot inhabit the strengthened mesh type. -/
theorem repeatedTopologyImpossible (m : Mesh) (hv : m.vertices = originVertices)
    (ht : m.top.fulltopology = repeatedTop.fulltopology) : False := by
  have h := m.triangles_checked
  rw [hv, ht] at h
  have bad : repeatedTop.fulltopology.all
      (fun t => geometryValid originVertices (.triangle t)) = false := by decide +kernel
  rw [bad] at h
  cases h

private def squareVertices : Array Vertex :=
  #[⟨Values.ofFn fun _ => 0, #v["0", "0", "0"], 1⟩,
    ⟨Values.ofFn fun i => if i.1 == 0 then 1 else 0, #v["1", "0", "0"], 2⟩,
    ⟨Values.ofFn fun i => if i.1 == 2 then 0 else 1, #v["1", "1", "0"], 3⟩,
    ⟨Values.ofFn fun i => if i.1 == 1 then 1 else 0, #v["0", "1", "0"], 4⟩]

/-- The exact positive triangle still satisfies the topology geometry predicate. -/
theorem triangleStillChecked : geometryValid squareVertices (.triangle #v[1, 2, 3]) = true := by
  decide +kernel

/-- Both emitted triangles from a positive quad pass the strengthened predicate. -/
theorem quadSplitStillChecked : (SimplexTopology.ofElements
    (triangles (.quad #v[1, 2, 3, 4])) (p := some 4)).fulltopology.all
    (fun t => geometryValid squareVertices (.triangle t)) = true := by decide +kernel

/-- Repeated vertex ids fail the exact triangle predicate. -/
theorem repeatedTriangleRejected :
    geometryValid originVertices (.triangle #v[1, 1, 1]) = false := by decide +kernel

/-- Run file-backed exact fixtures plus a signed-index sweep and proof consumers. -/
def run : TestM Unit := do
  let packet ← readJson "docs/fixtures/obj/manifest.json"
  for fixture in ← gArr packet "cases" do
    let file ← gStr fixture "file"
    let source ← IO.FS.readFile s!"docs/fixtures/obj/{file}"
    let good ← gBool fixture "valid"
    match _root_.MeshTopology.Obj.parse source with
    | .error error =>
      check s!"{file} rejected" (!good)
      if !good then
        checkEq s!"{file} category" (kindName error.kind) (← gStr fixture "error_kind")
        checkEq s!"{file} line" error.line (← gNat fixture "error_line")
        check s!"{file} detail" (!error.detail.isEmpty || file == "empty.obj")
    | .ok mesh =>
      check s!"{file} accepted" good
      if good then
        checkEq s!"{file} original source" mesh.source source
        checkEq s!"{file} node count" mesh.top.totalNodes mesh.vertices.size
        check s!"{file} connectivity" mesh.top.valid
        check s!"{file} exact geometry predicate"
          (mesh.faces.all fun f => geometryValid mesh.vertices f.corners)
        check s!"{file} actual topology triangles"
          (mesh.top.fulltopology.all fun t => geometryValid mesh.vertices (.triangle t))
        let vertices ← gArr fixture "vertices"
        let faces ← gArr fixture "faces"
        checkEq s!"{file} vertex count" mesh.vertices.size vertices.size
        checkEq s!"{file} face count" mesh.faces.size faces.size
        checkJ s!"{file} triangle winding"
          (toJson (mesh.top.fulltopology.map (·.toArray))) (← jField fixture "triangles")
        for (v, expected) in mesh.vertices.zip vertices do
          let i := v.line
          checkJ s!"{file} vertex {i} exact" (pointJson v.point) (← jField expected "point")
          checkJ s!"{file} vertex {i} tokens" (toJson v.tokens.toArray)
            (← jField expected "tokens")
          checkEq s!"{file} vertex {i} line" v.line (← gNat expected "line")
        for (f, expected) in mesh.faces.zip faces do
          let i := f.line
          checkJ s!"{file} face {i} ids" (toJson (ids f.corners)) (← jField expected "ids")
          checkJ s!"{file} face {i} tokens" (toJson f.tokens) (← jField expected "tokens")
          checkEq s!"{file} face {i} line" f.line (← gNat expected "line")
        for e in Array.finRange mesh.top.totalElements do
          for k in Array.finRange 3 do
            let i := mesh.top.vertexFin mesh.connectivity e k
            checkJ s!"{file} proof-bounded gather {e.1}/{k.1}" (pointJson (mesh.corner e k))
              (← jField vertices[i.1]! "point")
  for count in [:8] do
    for offset in [:25] do
      let raw : Int := (offset : Int) - 12
      let resolved := if raw > 0 then raw else (count : Int) + raw + 1
      let expected := if raw != 0 && resolved > 0 && resolved ≤ (count : Int)
        then some resolved.toNat else none
      check s!"index {count}/{raw}" (resolveIndex? count raw == expected)

end Tests.MeshTopology.Obj
