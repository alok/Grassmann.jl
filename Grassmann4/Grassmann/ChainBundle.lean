/-
  Grassmann/ChainBundle.lean - Simplicial complexes and mesh support

  Port of Grassmann.jl's chain bundle and mesh operations.

  A ChainBundle provides:
  - Simplices: vertices (0-simplices), edges (1-simplices), faces (2-simplices), etc.
  - Chains: formal sums of simplices with coefficients
  - Boundary operator: ∂ maps k-chains to (k-1)-chains
  - Support for mesh processing and discrete exterior calculus
-/
import Grassmann.Multivector
import Grassmann.LinearAlgebra

namespace Grassmann

/-! ## Simplex Types

A k-simplex is defined by k+1 vertices.
0-simplex = vertex, 1-simplex = edge, 2-simplex = triangle, 3-simplex = tetrahedron
-/

/-- A vertex index in the mesh -/
abbrev VertexId := Nat

/-- A k-simplex represented by its k+1 vertex indices (in sorted order) -/
structure Simplex (k : Nat) where
  /-- The k+1 vertices defining this simplex (sorted) -/
  vertices : Array VertexId
  /-- Proof that we have exactly k+1 vertices -/
  hsize : vertices.size = k + 1 := by rfl
  deriving Repr

namespace Simplex

/-- Create a 0-simplex (vertex) -/
def vertex (v : VertexId) : Simplex 0 := ⟨#[v], rfl⟩

/-- Create a 1-simplex (edge) from two vertices -/
def edge (v0 v1 : VertexId) : Simplex 1 := ⟨#[v0, v1], rfl⟩

/-- Create a 2-simplex (triangle) from three vertices -/
def triangle (v0 v1 v2 : VertexId) : Simplex 2 :=
  ⟨#[v0, v1, v2], rfl⟩  -- Store unsorted for simplicity

/-- Create a 3-simplex (tetrahedron) from four vertices -/
def tetrahedron (v0 v1 v2 v3 : VertexId) : Simplex 3 :=
  ⟨#[v0, v1, v2, v3], rfl⟩  -- Store unsorted for simplicity

/-- Get the i-th face (subsimplex) of a k-simplex by removing vertex i.
    Returns the simplex with vertex i omitted. -/
def face (s : Simplex (k + 1)) (i : Nat) (hi : i < k + 2) : Simplex k :=
  -- Build result by erasing the i-th vertex
  let arr := s.vertices
  have hiBound : i < arr.size := by rw [s.hsize]; omega
  -- Use Array.eraseIdx which removes exactly one element
  let result := arr.eraseIdx i hiBound
  ⟨result, by rw [Array.size_eraseIdx, s.hsize]; omega⟩

/-- Dimension of the simplex -/
def dim (_s : Simplex k) : Nat := k

/-- Check if two simplices are equal (same vertices) -/
instance : BEq (Simplex k) := ⟨fun a b => a.vertices == b.vertices⟩

/-- Hash for simplex (for use in hash maps) -/
instance : Hashable (Simplex k) := ⟨fun s => hash s.vertices⟩

end Simplex

/-! ## Chains

A k-chain is a formal sum of k-simplices with coefficients.
Chain{k,R} = Σᵢ cᵢ σᵢ where σᵢ are k-simplices and cᵢ ∈ R

Note: For full simplicial chain support with HashMap, import Std.Data.HashMap.
Here we provide a simple list-based implementation for basic usage.
-/

/-- A simplicial chain is a weighted sum of simplices (list-based implementation) -/
structure SimplicialChain (k : Nat) (R : Type*) where
  /-- List of (simplex, coefficient) pairs -/
  terms : List (Simplex k × R)
  deriving Repr

namespace SimplicialChain

variable {k : Nat} {R : Type*} [Ring R]

/-- The zero chain -/
def zero : SimplicialChain k R := ⟨[]⟩

/-- Create a chain from a single simplex with coefficient 1 -/
def single [One R] (s : Simplex k) : SimplicialChain k R := ⟨[(s, 1)]⟩

/-- Create a chain from a single simplex with given coefficient -/
def singleton (s : Simplex k) (c : R) : SimplicialChain k R := ⟨[(s, c)]⟩

/-- Add two chains (concatenation; simplification done elsewhere) -/
def add (a b : SimplicialChain k R) : SimplicialChain k R := ⟨a.terms ++ b.terms⟩

/-- Negate a chain -/
def neg (a : SimplicialChain k R) : SimplicialChain k R :=
  ⟨a.terms.map fun (s, c) => (s, -c)⟩

/-- Scale a chain -/
def smul (r : R) (a : SimplicialChain k R) : SimplicialChain k R :=
  ⟨a.terms.map fun (s, c) => (s, r * c)⟩

/-- Number of terms (may include duplicates) -/
def numTerms (a : SimplicialChain k R) : Nat := a.terms.length

instance : Zero (SimplicialChain k R) := ⟨zero⟩
instance : Add (SimplicialChain k R) := ⟨add⟩
instance : Neg (SimplicialChain k R) := ⟨neg⟩
instance : SMul R (SimplicialChain k R) := ⟨smul⟩

end SimplicialChain

/-! ## Boundary Operator

The boundary operator ∂ maps k-chains to (k-1)-chains.
For a k-simplex [v₀, v₁, ..., vₖ]:
  ∂σ = Σᵢ (-1)ⁱ [v₀, ..., v̂ᵢ, ..., vₖ]
where v̂ᵢ means vertex i is omitted.

Key property: ∂∂ = 0 (boundary of a boundary is zero)
-/

namespace Boundary

variable {R : Type*} [Ring R]

/-- Sign factor (-1)^i -/
def sign (i : Nat) : Int := if i % 2 == 0 then 1 else -1

/-- Boundary of a single k-simplex, returning a (k-1)-chain.
    ∂σ = Σᵢ (-1)ⁱ face(σ, i) -/
def simplexBoundary (s : Simplex (k + 1)) : SimplicialChain k R :=
  let faces := (List.range (k + 2)).filterMap fun i =>
    if hi : i < k + 2 then
      let coeff : R := if i % 2 == 0 then 1 else -1
      some (s.face i hi, coeff)
    else none
  ⟨faces⟩

/-- Boundary operator on chains: ∂(Σ cᵢσᵢ) = Σ cᵢ(∂σᵢ) -/
def boundary (c : SimplicialChain (k + 1) R) : SimplicialChain k R :=
  let allTerms := c.terms.flatMap fun (s, coeff) =>
    let bs := simplexBoundary (R := R) s
    bs.terms.map fun (face, faceCoeff) => (face, coeff * faceCoeff)
  ⟨allTerms⟩

/-- Unicode notation for boundary -/
scoped prefix:max "∂" => boundary

end Boundary

/-- Verify ∂∂ = 0 for a specific triangle -/
def verifyBoundarySquaredZero' (v0 v1 v2 : VertexId) : Bool :=
  -- Create the triangle
  let tri := Simplex.triangle v0 v1 v2
  -- Compute ∂(triangle) - a chain of edges
  let btri : SimplicialChain 1 Int := Boundary.simplexBoundary tri
  -- Compute ∂∂(triangle) - a chain of vertices
  let bbtri : SimplicialChain 0 Int := Boundary.boundary btri
  -- Sum up coefficients for each vertex to check cancellation
  -- Collect all (vertex, coeff) pairs and group by vertex
  let init : Array (Nat × Int) := #[(0, 0)]
  let vertexCoeffs := bbtri.terms.foldl (init := init)
    fun acc (simplex, coeff) =>
      let v := simplex.vertices[0]!
      -- Find and update or add
      let found := acc.findIdx? (fun (vid, _) => vid == v)
      match found with
      | some idx => acc.modify idx (fun (vid, c) => (vid, c + coeff))
      | none => acc.push (v, coeff)
  -- Check all coefficients sum to zero
  vertexCoeffs.all fun (_, c) => c == 0

/-! ## Point Cloud and Mesh

A PointCloud stores vertex positions.
A Mesh combines a point cloud with simplicial structure.
-/

/-- A point cloud stores vertex positions as multivectors -/
structure PointCloud (sig : Signature n) (F : Type*) where
  /-- Array of vertex positions -/
  positions : Array (Multivector sig F)

namespace PointCloud

variable {n : ℕ} {sig : Signature n} {F : Type*}

/-- Create empty point cloud -/
def empty : PointCloud sig F := ⟨#[]⟩

/-- Number of points -/
def size (pc : PointCloud sig F) : Nat := pc.positions.size

/-- Add a point -/
def addPoint (pc : PointCloud sig F) (p : Multivector sig F) : PointCloud sig F :=
  ⟨pc.positions.push p⟩

/-- Get point by index -/
def getPoint (pc : PointCloud sig F) (i : Nat) : Option (Multivector sig F) :=
  if h : i < pc.positions.size then some pc.positions[i] else none

/-- Create from array of positions -/
def ofArray (arr : Array (Multivector sig F)) : PointCloud sig F := ⟨arr⟩

/-- Convert to array -/
def toArray (pc : PointCloud sig F) : Array (Multivector sig F) := pc.positions

end PointCloud

/-- A simplicial mesh with vertices and k-simplices -/
structure Mesh (sig : Signature n) (F : Type*) (maxDim : Nat) where
  /-- Vertex positions -/
  vertices : PointCloud sig F
  /-- Simplices of each dimension (0 = vertices, 1 = edges, etc.) -/
  simplices : (d : Nat) → (h : d ≤ maxDim) → Array (Simplex d)

namespace Mesh

variable {n : ℕ} {sig : Signature n} {F : Type*} {maxDim : Nat}

/-- Create an empty mesh -/
def empty : Mesh sig F maxDim :=
  { vertices := PointCloud.empty
    simplices := fun _ _ => #[] }

/-- Number of vertices -/
def numVertices (m : Mesh sig F maxDim) : Nat := m.vertices.size

/-- Number of k-simplices -/
def numSimplices (m : Mesh sig F maxDim) (k : Nat) (h : k ≤ maxDim) : Nat :=
  (m.simplices k h).size

/-- Add a vertex and return its index -/
def addVertex (m : Mesh sig F maxDim) (p : Multivector sig F) : Mesh sig F maxDim × VertexId :=
  let idx := m.vertices.size
  ({ m with vertices := m.vertices.addPoint p }, idx)

end Mesh

/-! ## Triangle Mesh (2D surfaces in 3D)

Specialized mesh type for triangle meshes, common in graphics.
-/

/-- A triangle mesh in R3 -/
structure TriangleMesh where
  /-- Vertex positions as (x, y, z) -/
  vertices : Array (Float × Float × Float)
  /-- Triangle faces as (v0, v1, v2) indices -/
  faces : Array (Nat × Nat × Nat)
  deriving Repr

namespace TriangleMesh

/-- Create an empty triangle mesh -/
def empty : TriangleMesh := ⟨#[], #[]⟩

/-- Number of vertices -/
def numVertices (m : TriangleMesh) : Nat := m.vertices.size

/-- Number of faces -/
def numFaces (m : TriangleMesh) : Nat := m.faces.size

/-- Add a vertex, returns its index -/
def addVertex (m : TriangleMesh) (x y z : Float) : TriangleMesh × Nat :=
  (⟨m.vertices.push (x, y, z), m.faces⟩, m.vertices.size)

/-- Add a triangle face -/
def addFace (m : TriangleMesh) (v0 v1 v2 : Nat) : TriangleMesh :=
  ⟨m.vertices, m.faces.push (v0, v1, v2)⟩

/-- Get vertex position -/
def getVertex (m : TriangleMesh) (i : Nat) : Option (Float × Float × Float) :=
  if h : i < m.vertices.size then some (m.vertices[i]) else none

/-- Get face vertex indices -/
def getFace (m : TriangleMesh) (i : Nat) : Option (Nat × Nat × Nat) :=
  if h : i < m.faces.size then some (m.faces[i]) else none

/-- Compute face normal (unnormalized) -/
def faceNormal (m : TriangleMesh) (faceIdx : Nat) : Option (Float × Float × Float) := do
  let (i, j, k) ← m.getFace faceIdx
  let (x0, y0, z0) ← m.getVertex i
  let (x1, y1, z1) ← m.getVertex j
  let (x2, y2, z2) ← m.getVertex k
  -- Edge vectors
  let (e1x, e1y, e1z) := (x1 - x0, y1 - y0, z1 - z0)
  let (e2x, e2y, e2z) := (x2 - x0, y2 - y0, z2 - z0)
  -- Cross product
  let nx := e1y * e2z - e1z * e2y
  let ny := e1z * e2x - e1x * e2z
  let nz := e1x * e2y - e1y * e2x
  return (nx, ny, nz)

/-- Compute face area -/
def faceArea (m : TriangleMesh) (faceIdx : Nat) : Float :=
  match m.faceNormal faceIdx with
  | some (nx, ny, nz) => Float.sqrt (nx*nx + ny*ny + nz*nz) / 2.0
  | none => 0.0

/-- Total surface area -/
def surfaceArea (m : TriangleMesh) : Float :=
  (List.range m.numFaces).foldl (init := 0.0) fun acc i =>
    acc + m.faceArea i

/-- Compute vertex normal (average of adjacent face normals) -/
def vertexNormal (m : TriangleMesh) (vertIdx : Nat) : (Float × Float × Float) :=
  let init := (0.0, 0.0, 0.0, 0)
  let (sumX, sumY, sumZ, count) := m.faces.foldl (init := init)
    fun (sx, sy, sz, c) (v0, v1, v2) =>
      if v0 = vertIdx || v1 = vertIdx || v2 = vertIdx then
        match m.faceNormal c with
        | some (nx, ny, nz) => (sx + nx, sy + ny, sz + nz, c + 1)
        | none => (sx, sy, sz, c + 1)
      else
        (sx, sy, sz, c)
  if count > 0 then
    let invCount := 1.0 / count.toFloat
    (sumX * invCount, sumY * invCount, sumZ * invCount)
  else
    (0.0, 0.0, 1.0)  -- Default up

/-- Convert to GA PointCloud in R3 -/
def toPointCloud (m : TriangleMesh) : PointCloud R3 Float :=
  PointCloud.ofArray (m.vertices.map fun (x, y, z) =>
    let ex : Multivector R3 Float := Multivector.ofBlade (e1 : Blade R3)
    let ey : Multivector R3 Float := Multivector.ofBlade (e2 : Blade R3)
    let ez : Multivector R3 Float := Multivector.ofBlade (e3 : Blade R3)
    (ex.smul x).add ((ey.smul y).add (ez.smul z)))

/-- Create a unit cube mesh -/
def unitCube : TriangleMesh :=
  let verts : Array (Float × Float × Float) := #[
    (0, 0, 0), (1, 0, 0), (1, 1, 0), (0, 1, 0),  -- Bottom face
    (0, 0, 1), (1, 0, 1), (1, 1, 1), (0, 1, 1)   -- Top face
  ]
  let faces : Array (Nat × Nat × Nat) := #[
    -- Bottom (z=0)
    (0, 2, 1), (0, 3, 2),
    -- Top (z=1)
    (4, 5, 6), (4, 6, 7),
    -- Front (y=0)
    (0, 1, 5), (0, 5, 4),
    -- Back (y=1)
    (2, 3, 7), (2, 7, 6),
    -- Left (x=0)
    (0, 4, 7), (0, 7, 3),
    -- Right (x=1)
    (1, 2, 6), (1, 6, 5)
  ]
  ⟨verts, faces⟩

/-- Create a tetrahedron mesh -/
def tetrahedron : TriangleMesh :=
  let verts : Array (Float × Float × Float) := #[
    (0, 0, 0),
    (1, 0, 0),
    (0.5, Float.sqrt 0.75, 0),
    (0.5, Float.sqrt 0.75 / 3, Float.sqrt (2.0/3.0))
  ]
  let faces : Array (Nat × Nat × Nat) := #[
    (0, 1, 2),  -- Base
    (0, 1, 3),  -- Front
    (1, 2, 3),  -- Right
    (2, 0, 3)   -- Left
  ]
  ⟨verts, faces⟩

end TriangleMesh

/-! ## Betti Numbers and Euler Characteristic

Topological invariants computed from simplicial complexes.

For a simplicial complex K:
- β_k = dim(H_k) = dim(ker ∂_k) - dim(im ∂_{k+1})
- χ = Σ (-1)^k β_k = Σ (-1)^k |K_k| (Euler characteristic)

For common shapes:
- Sphere S²: β = (1, 0, 1), χ = 2
- Torus T²: β = (1, 2, 1), χ = 0
- Klein bottle: β = (1, 1, 0), χ = 0
-/

/-- Count simplices at each dimension in a mesh -/
def countSimplices (m : TriangleMesh) : List Nat :=
  [m.numVertices,     -- 0-simplices (vertices)
   3 * m.numFaces,    -- 1-simplices (edges) - upper bound, may have duplicates
   m.numFaces]        -- 2-simplices (faces)

/-- Euler characteristic: χ = V - E + F for a surface -/
def eulerCharacteristic (m : TriangleMesh) : Int :=
  let v := m.numVertices
  let f := m.numFaces
  -- For a closed triangle mesh, E = 3F/2 (each edge shared by 2 faces)
  -- For open mesh, E ≤ 3F/2
  -- Using Euler formula: χ = V - E + F
  -- For closed surface: E = 3F/2, so χ = V - 3F/2 + F = V - F/2
  v - (3 * f / 2) + f

/-- Euler characteristic (alias using χ symbol) -/
abbrev χ (m : TriangleMesh) : Int := eulerCharacteristic m

/-- Simplified Betti numbers for a triangle mesh (2D surface).
    Returns [β₀, β₁, β₂] where:
    - β₀ = number of connected components
    - β₁ = number of "holes" (1-dimensional cycles)
    - β₂ = number of enclosed volumes

    Note: Full computation requires boundary matrix rank calculation.
    This simplified version assumes a connected, closed surface. -/
def betti (m : TriangleMesh) : List Int :=
  -- For a connected surface: β₀ = 1
  -- From Euler formula: χ = β₀ - β₁ + β₂
  -- For closed orientable surface of genus g: β₀ = 1, β₁ = 2g, β₂ = 1
  let chi := eulerCharacteristic m
  -- Assume connected (β₀ = 1) and closed (β₂ = 1)
  let beta0 : Int := 1
  let beta2 : Int := 1
  -- β₁ = β₀ + β₂ - χ = 2 - χ
  let beta1 := beta0 + beta2 - chi
  [beta0, beta1, beta2]

/-- Genus of a closed orientable surface: g = (2 - χ) / 2 -/
def genus (m : TriangleMesh) : Int :=
  (2 - eulerCharacteristic m) / 2

/-! ## Grade Dimension Counting

For a graded algebra or simplicial complex, count elements at each grade.
-/

/-- Count elements at each grade in a simplicial complex.
    Returns array where result[k] = number of k-simplices. -/
def countGdims (simplices : List (Nat × List VertexId)) : Array Nat :=
  let maxDim := simplices.foldl (init := 0) fun acc (k, _) => max acc k
  let init := Array.replicate (maxDim + 1) 0
  simplices.foldl (init := init) fun arr (k, _) =>
    arr.modify k (· + 1)

/-- Alternating sum: Σ (-1)^k d_k
    Used for Euler characteristic computation. -/
def alternatingSum (dims : List Nat) : Int :=
  (dims.zip (List.range dims.length)).foldl (init := 0) fun acc (d, k) =>
    if k % 2 == 0 then acc + d else acc - d

/-! ## Boundary Operator (Partial Implementation)

The boundary operator ∂_k : C_k → C_{k-1} maps k-chains to (k-1)-chains.
∂(σ) = Σᵢ (-1)ⁱ σ̂ᵢ where σ̂ᵢ omits vertex i.

Full implementation requires careful handling of orientations and
sparse matrix representation for efficiency.
-/

/-- Boundary of a triangle (2-simplex) as a list of oriented edges.
    Returns [(sign, edge)] pairs. -/
def triangleBoundary (v0 v1 v2 : VertexId) : List (Int × Simplex 1) :=
  [(1, Simplex.edge v1 v2),   -- +[v1, v2] (omit v0)
   (-1, Simplex.edge v0 v2),  -- -[v0, v2] (omit v1)
   (1, Simplex.edge v0 v1)]   -- +[v0, v1] (omit v2)

/-- Boundary of an edge (1-simplex) as a list of oriented vertices.
    Returns [(sign, vertex)] pairs. -/
def edgeBoundary (v0 v1 : VertexId) : List (Int × Simplex 0) :=
  [(1, Simplex.vertex v1),    -- +v1 (omit v0)
   (-1, Simplex.vertex v0)]   -- -v0 (omit v1)

/-- Check if ∂∂ = 0 for a triangle using the actual boundary operator -/
def checkBoundarySquared (v0 v1 v2 : VertexId) : Bool :=
  verifyBoundarySquaredZero' v0 v1 v2

/-! ## Tests -/

section Tests

open Simplex SimplicialChain in

-- Simplex tests
#eval! Simplex.vertex 0
#eval! Simplex.edge 1 2
#eval! Simplex.triangle 0 1 2
#eval! Simplex.tetrahedron 0 1 2 3

-- Boundary operator tests
-- Test face extraction
#eval! (Simplex.triangle 0 1 2).face 0 (by omega)  -- Should be edge [1, 2]
#eval! (Simplex.triangle 0 1 2).face 1 (by omega)  -- Should be edge [0, 2]
#eval! (Simplex.triangle 0 1 2).face 2 (by omega)  -- Should be edge [0, 1]

-- Test boundary of a triangle (returns 3 edges with signs)
#eval! (Boundary.simplexBoundary (R := Int) (Simplex.triangle 0 1 2)).numTerms  -- 3

-- Test ∂∂ = 0 (fundamental property)
#eval! verifyBoundarySquaredZero' 0 1 2  -- Should be true
#eval! verifyBoundarySquaredZero' 5 10 15  -- Should be true (any vertices)

-- Triangle mesh tests
#eval! TriangleMesh.unitCube.numVertices  -- 8
#eval! TriangleMesh.unitCube.numFaces     -- 12
#eval! TriangleMesh.unitCube.surfaceArea  -- 6.0 (unit cube)

#eval! TriangleMesh.tetrahedron.numVertices  -- 4
#eval! TriangleMesh.tetrahedron.numFaces     -- 4

-- Test face normal
#eval! TriangleMesh.unitCube.faceNormal 0  -- First face normal

-- Euler characteristic tests
-- Cube: V=8, F=12, E=18, χ = 8 - 18 + 12 = 2
#eval! eulerCharacteristic TriangleMesh.unitCube  -- Should be 2

-- Tetrahedron: V=4, F=4, E=6, χ = 4 - 6 + 4 = 2
#eval! eulerCharacteristic TriangleMesh.tetrahedron  -- Should be 2

-- Betti numbers for cube (sphere-like): [1, 0, 1]
#eval! betti TriangleMesh.unitCube

-- Test boundary squared is zero
#eval! checkBoundarySquared 0 1 2  -- Should be true

end Tests

end Grassmann
