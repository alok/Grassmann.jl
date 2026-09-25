import MeshTopology.Lagrange
import MeshTopology.Grid

/-!
# The rest of the Julia API

Small accessors and forwarders of MeshTopology.jl that the main modules do not need themselves:
simplex numbers, node-count updates, the Lagrange forwarders to the corner topology, single
multilinear cells, and the `text/plain` display of simplex topologies.
-/

namespace MeshTopology

/-- Julia `trinum(n) = simplexnumber(2, n)`, the `n`-th triangular number (LG:22). -/
def trinum (n : Nat) : Nat := simplexNumber 2 n

/-- Julia `tetnum(n) = simplexnumber(3, n)`, the `n`-th tetrahedral number (LG:23). -/
def tetnum (n : Nat) : Nat := simplexNumber 3 n

namespace SimplexTopology

variable {N : Nat}

/-- Julia `sdims(t) = N` (MT:90): vertices per simplex. -/
@[inline] def sdims (_ : SimplexTopology N) : Nat := N

/-- Julia `totalnodes!(m, p)` (MT:308). Julia mutates the node count shared by every view of the
mesh; here the updated topology is returned. -/
def withTotalNodes (m : SimplexTopology N) (p : Nat) : SimplexTopology N := { m with totalNodes := p }

/-- Julia `isdiscontinuous(m)` (MT:546): `false` for a continuous topology. -/
@[inline] def isDiscontinuous (_ : SimplexTopology N) : Bool := false

/-- Julia `isdisconnected(m)` (MT:554): `false` for a continuous topology. -/
@[inline] def isDisconnected (_ : SimplexTopology N) : Bool := false

/-- Julia `pointset = vertices` (element.jl:33). -/
@[inline] def pointset (m : SimplexTopology N) : IdxVec := m.verts

/-- Julia `facesindices(t)` (element.jl:342): `edgesindices` of a triangle mesh. -/
def facesIndices (m : SimplexTopology 3) : SimplexTopology 3 := m.edgesIndices

/-- Julia `print(t)`: `Values{3, Int64}[[1, 2, 3], [2, 4, 3]]`. -/
def printString (m : SimplexTopology N) : String :=
  s!"Values\{{N}, Int64}[" ++ ", ".intercalate (m.topology.toList.map fun e => showInts (e.toList.map Int.ofNat)) ++ "]"

/-- Julia `show(stdout, MIME"text/plain"(), t)` (MT:704-714): the summary, `:`, then one element
per line. -/
def displayString (m : SimplexTopology N) : String :=
  m.summary ++ ":" ++ String.join (m.topology.toList.map fun e => "\n " ++ showInts (e.toList.map Int.ofNat))

end SimplexTopology

namespace DiscontinuousTopology

variable {N : Nat}

/-- Julia `isdiscontinuous(d) = true` (MT:547). -/
@[inline] def isDiscontinuous (_ : DiscontinuousTopology N) : Bool := true

/-- Julia `SimplexTopology(d)` (MT:518). -/
@[inline] def toSimplex (d : DiscontinuousTopology N) : SimplexTopology N := d.t

/-- Julia `show(stdout, MIME"text/plain"(), d)`. -/
def displayString (d : DiscontinuousTopology N) : String :=
  d.summary ++ ":" ++ String.join (d.topology.toList.map fun e => "\n " ++ showInts (e.toList.map Int.ofNat))

end DiscontinuousTopology

/-! ## Lagrange forwarders (LG:27-67) -/

namespace LagrangeTriangles

variable {M : Nat}

/-- Julia `cornertopology(m)`. -/
@[inline] def cornerTopology (m : LagrangeTriangles M) : SimplexTopology 3 := m.t
/-- Julia `edges(m)`. -/
@[inline] def edges (m : LagrangeTriangles M) : SimplexTopology 2 := m.e
/-- Julia `edgesindices(m)`. -/
@[inline] def edgesIndices (m : LagrangeTriangles M) : SimplexTopology 3 := m.ei
/-- Julia `facets(m)` (the edges of a triangle mesh). -/
@[inline] def facets (m : LagrangeTriangles M) : SimplexTopology 2 := m.e
/-- Julia `facetsindices(m)`. -/
@[inline] def facetsIndices (m : LagrangeTriangles M) : SimplexTopology 3 := m.ei
/-- Julia `totalelements(m)`. -/
@[inline] def totalElements (m : LagrangeTriangles M) : Nat := m.t.totalElements
/-- Julia `elements(m)`. -/
@[inline] def elements (m : LagrangeTriangles M) : Nat := m.t.elements
/-- Julia `subelements(m)`. -/
@[inline] def subelements (m : LagrangeTriangles M) : IdxVec := m.t.sub
/-- Julia `istotal(m)`. -/
@[inline] def isTotal (m : LagrangeTriangles M) : Bool := m.t.isTotal
/-- Julia `isfull(m)`. -/
@[inline] def isFull (m : LagrangeTriangles M) : Bool := m.t.isFull
/-- Julia `iscover(m)`. -/
@[inline] def isCover (m : LagrangeTriangles M) : Bool := m.t.isCover
/-- Julia `getfacet(m, i)`. -/
@[inline] def getFacet (m : LagrangeTriangles M) (i : Nat) : Nat := m.t.getFacet i
/-- Julia `getimage(m, i)` (LG:60-61). -/
@[inline] def getImage (m : LagrangeTriangles M) (i : Nat) : Nat :=
  if m.verts.isOneTo || m.isCover then i else m.verts.get1 i
/-- Julia `getedge(m, i)` (LG:252-254): the interior nodes of edge `i` (from its smaller vertex). -/
def getEdge (m : LagrangeTriangles M) (i : Nat) : Array Nat :=
  edgesIndex #[m.e.getFacet i] m.t.totalNodes M
/-- Julia `lagrangesimplex(m)`: nodes per element. -/
@[inline] def lagrangeSimplex (_ : LagrangeTriangles M) : Nat := MeshTopology.lagrangeSimplex 3 M
/-- Julia `show(stdout, MIME"text/plain"(), m)`. -/
def displayString (m : LagrangeTriangles M) : String :=
  m.summary ++ ":" ++ String.join (m.topology.toList.map fun e => "\n " ++ showInts (e.toList.map Int.ofNat))

end LagrangeTriangles

namespace LagrangeTetrahedra

variable {M : Nat}

/-- Julia `cornertopology(m)`. -/
@[inline] def cornerTopology (m : LagrangeTetrahedra M) : SimplexTopology 4 := m.t
/-- Julia `edges(m)`. -/
@[inline] def edges (m : LagrangeTetrahedra M) : SimplexTopology 2 := m.e
/-- Julia `edgesindices(m)`. -/
@[inline] def edgesIndices (m : LagrangeTetrahedra M) : SimplexTopology 6 := m.ei
/-- Julia `facets(m)`. -/
@[inline] def facets (m : LagrangeTetrahedra M) : SimplexTopology 3 := m.f
/-- Julia `facetsindices(m)`. -/
@[inline] def facetsIndices (m : LagrangeTetrahedra M) : SimplexTopology 4 := m.fi
/-- Julia `totalelements(m)`. -/
@[inline] def totalElements (m : LagrangeTetrahedra M) : Nat := m.t.totalElements
/-- Julia `elements(m)`. -/
@[inline] def elements (m : LagrangeTetrahedra M) : Nat := m.t.elements
/-- Julia `subelements(m)`. -/
@[inline] def subelements (m : LagrangeTetrahedra M) : IdxVec := m.t.sub
/-- Julia `iscover(m)`. -/
@[inline] def isCover (m : LagrangeTetrahedra M) : Bool := m.t.isCover
/-- Julia `getfacet(m, i)`. -/
@[inline] def getFacet (m : LagrangeTetrahedra M) (i : Nat) : Nat := m.t.getFacet i
/-- Julia `getimage(m, i)`. -/
@[inline] def getImage (m : LagrangeTetrahedra M) (i : Nat) : Nat :=
  if m.verts.isOneTo || m.isCover then i else m.verts.get1 i
/-- Julia `getedge(m, i)`. -/
def getEdge (m : LagrangeTetrahedra M) (i : Nat) : Array Nat :=
  edgesIndex #[m.e.getFacet i] m.t.totalNodes M
/-- Julia `show(stdout, MIME"text/plain"(), m)`. -/
def displayString (m : LagrangeTetrahedra M) : String :=
  m.summary ++ ":" ++ String.join (m.topology.toList.map fun e => "\n " ++ showInts (e.toList.map Int.ofNat))

end LagrangeTetrahedra

/-- Julia `show(stdout, MIME"text/plain"(), m)` of Lagrange edges. -/
def LagrangeEdges.displayString {M : Nat} (m : LagrangeEdges M) : String :=
  m.summary ++ ":" ++ String.join (m.topology.toList.map fun e => "\n " ++ showInts (e.toList.map Int.ofNat))

/-! ## Single multilinear cells -/

/-- Julia `linearelement(l, i…)` (GR:21-50): the corner values of the cell with lowest corner
`base` (1-based) of a column-major grid array `vals` of sizes `s`. -/
def linearElement {N : Nat} (s : Vector Nat N) (vals : Array Nat) (base : Vector Nat N) : Array Nat :=
  ((cornerOffsets N).map fun o =>
    vals[(linearIndex s (Vector.ofFn fun k => ((base[k] + o[k.1]! : Nat) : Int))).toNat - 1]!).toArray

/-- Julia `linearelement(m::QuotientTopology, ij…)` (GR:60-90): a cell with `elementfun` values. -/
def QuotientTopology.linearElement {N : Nat} (m : QuotientTopology N) (base : Vector Nat N) :
    Array Nat :=
  MeshTopology.linearElement m.size m.elementfuns base

end MeshTopology
