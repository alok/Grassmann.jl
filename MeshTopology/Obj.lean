import MeshTopology.Simplex
import StaticVectors.Values
import JuliaBase.Parse

/-!
Exact, deliberately narrow Wavefront OBJ ingress. See `docs/guides/obj-mesh-ingress.md`.
The format source is Wavefront's Advanced Visualizer manual, appendix B1 (original
text mirrored at https://www.martinreddy.net/gfx/3d/OBJ.spec). This is a new import
boundary, not a port of a Julia mesh importer or a solid-validity certificate.
-/

namespace MeshTopology.Obj

open StaticVectors

/-- Exact Cartesian coordinates; no rounding or coordinate-system conversion. -/
abbrev Point := Values Rat 3

/-- Stable categories for the first rejected physical record. -/
inductive ErrorKind where
  | syntax | unsupportedRecord | unsupportedIndex | unsupportedVertex
  | unsupportedFace | unsupportedContinuation | nonAscii | coordinate | coordinateRange
  | indexRange | degenerate | nonPlanarQuad | nonConvexQuad | emptyMesh | connectivity
  deriving BEq, Repr

/-- A 1-based physical line, stable category and original token or diagnostic detail. -/
structure Error where
  /-- Physical line of the first error (1-based). -/
  line : Nat
  /-- Stable rejection category. -/
  kind : ErrorKind
  /-- Original offending token or diagnostic detail. -/
  detail : String
  deriving BEq, Repr

/-- An exact point with its three original coordinate tokens and physical line. -/
structure Vertex where
  /-- Exact Cartesian coordinates. -/
  point : Point
  /-- Original spellings, including signed zero and exponent syntax. -/
  tokens : Vector String 3
  /-- Physical vertex line (1-based). -/
  line : Nat

/-- Original triangle or quad winding, represented by existing fixed-length vectors. -/
inductive Corners where
  /-- Three resolved ids in original winding. -/
  | triangle (ids : Vector Nat 3)
  /-- Four resolved ids in original winding, before the documented split. -/
  | quad (ids : Vector Nat 4)

/-- Original face tokens and line, with resolved 1-based ids before triangulation. -/
structure Face where
  /-- Resolved original face, before triangulation. -/
  corners : Corners
  /-- Original signed index tokens. -/
  tokens : Array String
  /-- Physical face line (1-based). -/
  line : Nat

/-- Preserve triangle winding; split a quad on its first-to-third diagonal. -/
def triangles : Corners → Array (Vector Nat 3)
  | .triangle ids => #[ids]
  | .quad ids => #[#v[ids[0], ids[1], ids[2]], #v[ids[0], ids[2], ids[3]]]

/-- Check the original arbitrary-precision signed index, then resolve to a 1-based Nat.
Negative indices refer to the vertex count at the face record, not the final count. -/
def resolveIndex? (count : Nat) (raw : Int) : Option Nat :=
  let resolved := if raw > 0 then raw else (count : Int) + raw + 1
  if raw ≠ 0 ∧ 0 < resolved ∧ resolved ≤ (count : Int) then some resolved.toNat else none

/-- Successful index ingress preserves the signed-index interpretation and node bounds. -/
theorem resolveIndex?_sound {count : Nat} {raw : Int} {id : Nat}
    (h : resolveIndex? count raw = some id) :
    raw ≠ 0 ∧ 0 < id ∧ id ≤ count ∧
      (id : Int) = (if raw > 0 then raw else (count : Int) + raw + 1) := by
  unfold resolveIndex? at h
  generalize he : (if raw > 0 then raw else (count : Int) + raw + 1) = resolved at h ⊢
  dsimp only at h
  split at h
  next hr =>
    simp only [Option.some.injEq] at h
    subst id
    rcases hr with ⟨hz, hp, hb⟩
    have he := Int.toNat_of_nonneg (Int.le_of_lt hp)
    exact ⟨hz, by omega, by omega, he⟩
  next => simp at h

private def sub (a b : Point) : Point := Values.ofFn fun i => a[i.1] - b[i.1]

private def cross (a b : Point) : Point := Values.ofFn fun i =>
  match i.1 with
  | 0 => a[1] * b[2] - a[2] * b[1]
  | 1 => a[2] * b[0] - a[0] * b[2]
  | _ => a[0] * b[1] - a[1] * b[0]

private def dot (a b : Point) : Rat := a[0] * b[0] + a[1] * b[1] + a[2] * b[2]

private def point? (vs : Array Vertex) (id : Nat) : Option Point := do
  if id == 0 then none else return (← vs[id - 1]?).point

private def faceStatus (vs : Array Vertex) (cs : Corners) : Option ErrorKind :=
  let ids := match cs with
    | .triangle is => is.toArray
    | .quad is => is.toArray
  match ids.mapM (point? vs) with
  | none => some .indexRange
  | some ps =>
    let a := ps[0]!
    let b := ps[1]!
    let c := ps[2]!
    let n := cross (sub b a) (sub c a)
    if dot n n == 0 then some .degenerate
    else match cs with
      | .triangle _ => none
      | .quad _ =>
        let d := ps[3]!
        if dot n (sub d a) != 0 then some .nonPlanarQuad
        else if dot n (cross (sub c b) (sub d c)) > 0 &&
            dot n (cross (sub d c) (sub a d)) > 0 &&
            dot n (cross (sub a d) (sub b a)) > 0 then none
        else some .nonConvexQuad

/-- Exact cross/dot-product screening: nonzero triangle normal, or planar quad with
strictly consistent corner turns. This predicate carries no global mesh/solid claim. -/
def geometryValid (vs : Array Vertex) (cs : Corners) : Bool := (faceStatus vs cs).isNone

/-- Exact import data and an existing triangle topology with checked gather bounds.
The fields certify the stated executable checks, not a closed or manifold solid. -/
structure Mesh where
  private mk ::
  /-- Complete original input text. -/
  source : String
  /-- All original points, including unused points. -/
  vertices : Array Vertex
  /-- All original faces and their source positions. -/
  faces : Array Face
  /-- Existing simplex connectivity after the explicit quad split. -/
  top : SimplexTopology 3
  /-- Gather bounds refer to this exact coordinate array. -/
  nodes_match : top.totalNodes = vertices.size
  /-- Every stored node id lies in 1..vertices.size. -/
  connectivity : top.valid = true
  /-- Every original face passed the documented exact predicate. -/
  geometry_checked : faces.all (fun f => geometryValid vertices f.corners) = true
  /-- Every actual topology triangle passed the exact predicate, independently of faces. -/
  triangles_checked : top.fulltopology.all (fun t => geometryValid vertices (.triangle t)) = true

/-- Every actual topology triangle passes the exact geometry screen for any mesh value. -/
theorem Mesh.triangle_checked (m : Mesh) (e : Fin m.top.totalElements) :
    geometryValid m.vertices (.triangle (m.top.fullElem e)) = true := by
  have h := (Array.all_eq_true.mp m.triangles_checked) e.1
    (by simp [SimplexTopology.fulltopology])
  simpa [SimplexTopology.fulltopology] using h

/-- Gather an exact original vertex through the existing proof-bounded topology API. -/
def Mesh.corner (m : Mesh) (e : Fin m.top.totalElements) (k : Fin 3) : Point :=
  let i := m.top.vertexFin m.connectivity e k
  (m.vertices[i.1]'(m.nodes_match ▸ i.2)).point

private def signedDigits (s : String) : Bool :=
  let cs := s.toList
  let body := match cs with | '+' :: tl | '-' :: tl => tl | _ => cs
  !body.isEmpty && body.all Char.isDigit

private def coordinate (line : Nat) (s : String) : Except Error Rat := do
  let cs := s.toList
  let (neg, body) := match cs with
    | '-' :: tl => (true, tl)
    | '+' :: tl => (false, tl)
    | _ => (false, cs)
  let (mant, nd, frac, rest) := JuliaBase.IEEEFloat.scanMantissa body 0 0 0 false
  let some e := JuliaBase.IEEEFloat.scanExponent rest
    | throw ⟨line, .coordinate, s⟩
  if nd == 0 then throw ⟨line, .coordinate, s⟩
  let power := e - (frac : Int)
  if power.natAbs > 4096 then throw ⟨line, .coordinateRange, s⟩
  let numerator : Int := if neg then -(mant : Int) else mant
  return if power ≥ 0 then Rat.ofInt (numerator * (10 ^ power.toNat : Nat))
    else mkRat numerator (10 ^ (-power).toNat)

private def index (line count : Nat) (s : String) : Except Error Nat := do
  if s.contains '/' then throw ⟨line, .unsupportedIndex, s⟩
  if !signedDigits s then throw ⟨line, .syntax, s⟩
  let body := if s.startsWith "+" then (s.drop 1).toString else s
  let some raw := body.toInt? | throw ⟨line, .syntax, s⟩
  let some id := resolveIndex? count raw | throw ⟨line, .indexRange, s⟩
  return id

private structure State where
  vertices : Array Vertex := #[]
  faces : Array Face := #[]

private def record (line : Nat) (text : String) (st : State) : Except Error State := do
  let text := if text.endsWith "\r" then (text.dropEnd 1).toString else text
  if !text.toList.all (fun c => c == '\t' || (32 ≤ c.toNat && c.toNat ≤ 126)) then
    throw ⟨line, .nonAscii, text⟩
  let body := (text.splitOn "#").head!
  if body.contains '\\' then throw ⟨line, .unsupportedContinuation, body⟩
  let words := (body.splitToList (fun c => c == ' ' || c == '\t')).filter (· != "")
  match words with
  | [] => return st
  | "v" :: args =>
    match args with
    | [x, y, z] =>
      let a ← coordinate line x
      let b ← coordinate line y
      let c ← coordinate line z
      let point : Point := Values.ofFn fun i => if i.1 == 0 then a else if i.1 == 1 then b else c
      return { st with vertices := st.vertices.push ⟨point, #v[x, y, z], line⟩ }
    | _ => throw ⟨line, .unsupportedVertex, body⟩
  | "f" :: args =>
    let ids ← args.toArray.mapM (index line st.vertices.size)
    let corners ← if h : ids.size = 3 then pure (Corners.triangle ⟨ids, h⟩)
      else if h : ids.size = 4 then pure (Corners.quad ⟨ids, h⟩)
      else throw ⟨line, .unsupportedFace, body⟩
    if let some kind := faceStatus st.vertices corners then throw ⟨line, kind, body⟩
    return { st with faces := st.faces.push ⟨corners, args.toArray, line⟩ }
  | keyword :: _ => throw ⟨line, .unsupportedRecord, keyword⟩

private def records : List String → Nat → State → Except Error State
  | [], _, st => .ok st
  | text :: rest, line, st => do records rest (line + 1) (← record line text st)

/-- Parse the documented untextured triangle/convex-planar-quad OBJ profile exactly.
Reject unsupported records and the first error, without repairing or dropping geometry.
Positive and relative indices are checked before conversion; source text is retained. -/
def parse (source : String) : Except Error Mesh := do
  let st ← records (source.splitOn "\n") 1 {}
  if st.vertices.isEmpty || st.faces.isEmpty then throw ⟨1, .emptyMesh, "vertices/faces"⟩
  let top := SimplexTopology.ofElements (st.faces.flatMap fun f => triangles f.corners)
    (p := some st.vertices.size)
  if hc : top.valid = true then
    if hg : st.faces.all (fun f => geometryValid st.vertices f.corners) = true then
      if ht : top.fulltopology.all
          (fun t => geometryValid st.vertices (.triangle t)) = true then
        return ⟨source, st.vertices, st.faces, top, rfl, hc, hg, ht⟩
      else throw ⟨1, .degenerate, "final triangle check"⟩
    else throw ⟨1, .degenerate, "final geometry check"⟩
  else throw ⟨1, .connectivity, "final topology check"⟩

end MeshTopology.Obj
