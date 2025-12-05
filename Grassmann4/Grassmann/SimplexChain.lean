/-
  Grassmann/SimplexChain.lean - Port of Grassmann.jl's Simplex/Chain types

  This module documents and implements the type hierarchy from Grassmann.jl:
  - Blade: Basis blades (e₁, e₁₂, e₁₂₃, etc.)
  - Single/Simplex: Blade × scalar coefficient
  - Chain: Grade-homogeneous multivector (binomial(n,G) coefficients)
  - ChainBundle: Collection of simplices for meshes

  The main Multivector type is in Multivector.lean; this provides
  the additional Chain type for grade-homogeneous operations.
-/

import Grassmann.Manifold
import Grassmann.Blade

namespace Grassmann.SimplexChain

open Grassmann

/-! ## Single (Simplex in Julia)

Note: The `Single` type is already defined in `Grassmann.Blade` as:
  `structure Single (sig : Signature n) (F : Type*) where coeff : F; blade : Blade sig`

This corresponds to `Simplex{V,G,B,T}` in Grassmann.jl.
We re-export it here for convenience.
-/

-- Re-export Single from Blade.lean
export Grassmann (Single)

/-! ## Chain (Grade-Homogeneous Multivector)

A Chain contains all blades of a single grade G.
Storage size is binomial(n, G) = n choose G.

In Julia: `Chain{V,G,T} <: TensorGraded{V,G}`
-/

/-- Number of blades of grade G in dimension n -/
def numBladesOfGrade (n G : Nat) : Nat := Nat.choose n G

/-- A grade-G multivector with exactly C(n,G) coefficients.
    This is Julia's `Chain{V,G,T}` type.

    Uses function storage like Multivector for uniformity. -/
structure Chain (sig : Signature n) (G : Nat) (F : Type*) where
  /-- Coefficients indexed by position within grade -/
  coeffs : Fin (numBladesOfGrade n G) → F

-- Custom Repr for Chain (can't derive for function types)
instance {n : Nat} {sig : Signature n} {G : Nat} [Repr F] : Repr (Chain sig G F) where
  reprPrec c _ :=
    let size := numBladesOfGrade n G
    let coeffList := (List.finRange size).map (fun i => repr (c.coeffs i))
    .text "Chain[" ++ .group (.nest 2 (.joinSep coeffList (.text ", "))) ++ .text "]"

namespace Chain

variable {n : Nat} {sig : Signature n} {G : Nat} {F : Type*}

/-- Zero chain -/
def zero [Zero F] : Chain sig G F := ⟨fun _ => 0⟩

/-- Get coefficient at index -/
def coeff (c : Chain sig G F) (i : Fin (numBladesOfGrade n G)) : F := c.coeffs i

/-- Set coefficient at index -/
def setCoeff (c : Chain sig G F) (i : Fin (numBladesOfGrade n G)) (v : F) : Chain sig G F :=
  ⟨fun j => if i = j then v else c.coeffs j⟩

/-- Add two chains of the same grade -/
def add [Add F] (a b : Chain sig G F) : Chain sig G F :=
  ⟨fun i => a.coeffs i + b.coeffs i⟩

/-- Scale a chain -/
def smul [Mul F] (c : F) (chain : Chain sig G F) : Chain sig G F :=
  ⟨fun i => c * chain.coeffs i⟩

/-- Negate a chain -/
def neg [Neg F] (c : Chain sig G F) : Chain sig G F :=
  ⟨fun i => -c.coeffs i⟩

instance [Add F] : Add (Chain sig G F) := ⟨Chain.add⟩
instance [Neg F] : Neg (Chain sig G F) := ⟨Chain.neg⟩

end Chain

/-! ## ChainBundle (for mesh operations)

A collection of simplices (chains), used for point clouds and meshes.
This is Julia's `ChainBundle{V,G,T,Points}` type.
-/

/-- A bundle of grade-G chains (for mesh representation) -/
structure ChainBundle (sig : Signature n) (G : Nat) (F : Type*) where
  chains : Array (Chain sig G F)
  deriving Repr

namespace ChainBundle

variable {n : Nat} {sig : Signature n} {G : Nat} {F : Type*}

/-- Empty bundle -/
def empty : ChainBundle sig G F := ⟨#[]⟩

/-- Add a chain to the bundle -/
def push (bundle : ChainBundle sig G F) (c : Chain sig G F) : ChainBundle sig G F :=
  ⟨bundle.chains.push c⟩

/-- Number of simplices -/
def size (bundle : ChainBundle sig G F) : Nat := bundle.chains.size

/-- Get chain by index -/
def get? (bundle : ChainBundle sig G F) (i : Nat) : Option (Chain sig G F) :=
  if h : i < bundle.chains.size then
    some (bundle.chains[i])
  else
    none

/-! ### Mesh Operations

From Grassmann.jl: boundary, skeleton, edges, facets operations for computational topology.
Simplified implementation that avoids external dependencies.
-/

/-- Indices type: references into point array -/
abbrev PointIndex := Nat

/-- A simplex represented by vertex indices (for mesh connectivity).
    We use a simple array representation without size proof for easier use. -/
structure IndexSimplex where
  /-- Vertex indices defining the simplex -/
  vertices : Array PointIndex
  /-- Grade (dimension) of the simplex: 0=point, 1=edge, 2=triangle, etc. -/
  grade : Nat
  deriving Repr, BEq

namespace IndexSimplex

/-- Create a 0-simplex (point) -/
def point (i : PointIndex) : IndexSimplex := ⟨#[i], 0⟩

/-- Create a 1-simplex (edge) -/
def edge (i j : PointIndex) : IndexSimplex := ⟨#[i, j], 1⟩

/-- Create a 2-simplex (triangle) -/
def triangle (i j k : PointIndex) : IndexSimplex := ⟨#[i, j, k], 2⟩

/-- Create a 3-simplex (tetrahedron) -/
def tetrahedron (i j k l : PointIndex) : IndexSimplex := ⟨#[i, j, k, l], 3⟩

/-- Number of vertices -/
def numVertices (s : IndexSimplex) : Nat := s.vertices.size

/-- Get vertex by index -/
def getVertex (s : IndexSimplex) (i : Nat) : Option PointIndex :=
  if h : i < s.vertices.size then some s.vertices[i] else none

end IndexSimplex

/-- A mesh bundle: points + connectivity -/
structure Mesh (sig : Signature n) (F : Type*) where
  /-- Point coordinates as grade-1 chains -/
  points : Array (Chain sig 1 F)
  /-- Connectivity: array of simplices (can be mixed grades) -/
  simplices : Array IndexSimplex
  deriving Repr

namespace Mesh

variable {n : Nat} {sig : Signature n} {F : Type*}

/-- Empty mesh -/
def empty : Mesh sig F := ⟨#[], #[]⟩

/-- Number of points -/
def numPoints (m : Mesh sig F) : Nat := m.points.size

/-- Number of simplices -/
def numSimplices (m : Mesh sig F) : Nat := m.simplices.size

/-- Add a point, return its index -/
def addPoint (m : Mesh sig F) (p : Chain sig 1 F) : Mesh sig F × PointIndex :=
  (⟨m.points.push p, m.simplices⟩, m.points.size)

/-- Add a simplex -/
def addSimplex (m : Mesh sig F) (s : IndexSimplex) : Mesh sig F :=
  ⟨m.points, m.simplices.push s⟩

/-- Get simplices of a specific grade -/
def simplicesOfGrade (m : Mesh sig F) (g : Nat) : Array IndexSimplex :=
  m.simplices.filter (·.grade == g)

/-- Get triangles (grade-2 simplices) -/
def triangles (m : Mesh sig F) : Array IndexSimplex := m.simplicesOfGrade 2

/-- Get edges (grade-1 simplices) -/
def edges (m : Mesh sig F) : Array IndexSimplex := m.simplicesOfGrade 1

end Mesh

/-- Extract all edges from triangles in a mesh -/
def extractEdgesFromTriangles (m : Mesh sig F) : Array IndexSimplex :=
  let tris := m.triangles
  let edgeList := tris.foldl (init := #[]) fun acc tri =>
    match tri.getVertex 0, tri.getVertex 1, tri.getVertex 2 with
    | some v0, some v1, some v2 =>
      acc.push (IndexSimplex.edge v0 v1)
         |>.push (IndexSimplex.edge v1 v2)
         |>.push (IndexSimplex.edge v0 v2)
    | _, _, _ => acc
  -- Remove duplicates (simple approach: keep if not already present)
  edgeList.foldl (init := #[]) fun acc e =>
    let normalized := if (e.vertices[0]? |>.getD 0) ≤ (e.vertices[1]? |>.getD 0)
                      then e
                      else IndexSimplex.edge (e.vertices[1]? |>.getD 0) (e.vertices[0]? |>.getD 0)
    if acc.any (· == normalized) then acc
    else acc.push normalized

/-- Boundary faces of a simplex (one grade lower).
    ∂[v₀,...,vₖ] = Σᵢ (-1)ⁱ [v₀,...,v̂ᵢ,...,vₖ] -/
def simplexBoundaryFaces (s : IndexSimplex) : Array (Int × IndexSimplex) :=
  if s.grade == 0 then #[]
  else
    (Array.range s.vertices.size).filterMap fun i =>
      if h : i < s.vertices.size then
        let sign : Int := if i % 2 == 0 then 1 else -1
        -- Build face by excluding vertex i
        let faceVerts := (Array.range s.vertices.size).filterMap fun j =>
          if j ≠ i then s.vertices[j]? else none
        some (sign, ⟨faceVerts, s.grade - 1⟩)
      else none

/-- Euler characteristic: V - E + F for a triangle mesh -/
def eulerCharacteristic (m : Mesh sig F) : Int :=
  let V : Int := m.numPoints
  let E : Int := (extractEdgesFromTriangles m).size
  let F : Int := m.triangles.size
  V - E + F

end ChainBundle

/-! ## Index Computations

These match Leibniz.jl's bladeindex, basisindex, indexbasis functions.
-/

/-- Cumulative sum of binomial coefficients up to grade G-1.
    This gives the starting index for grade-G blades in a full multivector. -/
def binomsum (n G : Nat) : Nat :=
  (List.range G).foldl (fun acc k => acc + Nat.choose n k) 0

/-- Popcount for Nat (count set bits) -/
partial def popcount (x : Nat) : Nat :=
  if x == 0 then 0
  else (x &&& 1) + popcount (x >>> 1)

/-! ## Blade Index Mapping

In a full multivector, blades are ordered by grade then by lexicographic order
within each grade. These functions convert between bitmask and index.
-/

/-- All blade bitmasks of grade G in dimension n.
    Returns them in lexicographic order. -/
partial def indexbasis (n G : Nat) : List Nat :=
  if G > n then []
  else if G == 0 then [0]
  else
    -- Generate all G-element subsets of {0, ..., n-1}
    let rec go (start : Nat) (remaining : Nat) (current : Nat) : List Nat :=
      if remaining == 0 then [current]
      else if start >= n then []
      else
        let with_start := go (start + 1) (remaining - 1) (current ||| (1 <<< start))
        let without_start := go (start + 1) remaining current
        with_start ++ without_start
    go 0 G 0

/-- Find index of element in list -/
def listFindIndex (p : α → Bool) (l : List α) : Option Nat :=
  let rec go (l : List α) (idx : Nat) : Option Nat :=
    match l with
    | [] => none
    | x :: xs => if p x then some idx else go xs (idx + 1)
  go l 0

/-- Index of blade within its grade -/
def bladeindex (n : Nat) (bits : Nat) : Nat :=
  let G := popcount bits
  let blades := indexbasis n G
  listFindIndex (· == bits) blades |>.getD 0

/-- Overall index of blade in multivector array -/
def basisindex (n : Nat) (bits : Nat) : Nat :=
  let G := popcount bits
  binomsum n G + bladeindex n bits

/-! ## Parity/Sign Computations -/

/-- Reverse parity: sign of (v₁∧v₂∧...∧vₖ)† = (-1)^(k(k-1)/2) -/
def parityReverse (grade : Nat) : Bool :=
  ((grade * (grade - 1)) / 2) % 2 == 1

/-- Involute parity: sign of grade involution = (-1)^grade -/
def parityInvolute (grade : Nat) : Bool :=
  grade % 2 == 1

/-- Clifford conjugation parity -/
def parityClifford (grade : Nat) : Bool :=
  parityReverse grade != parityInvolute grade

/-! ## Tests -/

section Tests

-- Test binomsum
#eval binomsum 3 0   -- 0 (no grades before 0)
#eval binomsum 3 1   -- 1 (just the scalar)
#eval binomsum 3 2   -- 4 (scalar + 3 vectors)
#eval binomsum 3 3   -- 7 (scalar + 3 vectors + 3 bivectors)

-- Test indexbasis - all bitmasks of grade G
#eval indexbasis 3 0  -- [0]
#eval indexbasis 3 1  -- [1, 2, 4] = [e₁, e₂, e₃]
#eval indexbasis 3 2  -- [3, 5, 6] = [e₁₂, e₁₃, e₂₃]
#eval indexbasis 3 3  -- [7] = [e₁₂₃]

-- Test bladeindex
#eval bladeindex 3 0b001  -- 0 (e₁ is first grade-1 blade)
#eval bladeindex 3 0b010  -- 1 (e₂ is second grade-1 blade)
#eval bladeindex 3 0b011  -- 0 (e₁₂ is first grade-2 blade)
#eval bladeindex 3 0b111  -- 0 (e₁₂₃ is only grade-3 blade)

-- Test basisindex (overall index in 2^n array)
#eval basisindex 3 0b000  -- 0 (scalar)
#eval basisindex 3 0b001  -- 1 (e₁)
#eval basisindex 3 0b010  -- 2 (e₂)
#eval basisindex 3 0b100  -- 3 (e₃)
#eval basisindex 3 0b011  -- 4 (e₁₂)
#eval basisindex 3 0b101  -- 5 (e₁₃)
#eval basisindex 3 0b110  -- 6 (e₂₃)
#eval basisindex 3 0b111  -- 7 (e₁₂₃)

-- Test parity functions
#eval parityReverse 0  -- false (grade 0: (-1)^0 = 1)
#eval parityReverse 1  -- false (grade 1: (-1)^0 = 1)
#eval parityReverse 2  -- true  (grade 2: (-1)^1 = -1)
#eval parityReverse 3  -- true  (grade 3: (-1)^3 = -1)
#eval parityReverse 4  -- false (grade 4: (-1)^6 = 1)

#eval parityInvolute 0  -- false (even grade)
#eval parityInvolute 1  -- true  (odd grade)
#eval parityInvolute 2  -- false (even grade)
#eval parityInvolute 3  -- true  (odd grade)

-- Test Chain construction
#eval numBladesOfGrade 3 0  -- 1 (scalar)
#eval numBladesOfGrade 3 1  -- 3 (vectors)
#eval numBladesOfGrade 3 2  -- 3 (bivectors)
#eval numBladesOfGrade 3 3  -- 1 (pseudoscalar)
#eval numBladesOfGrade 4 2  -- 6 (bivectors in 4D)

-- Test Chain type (grade-1 chain in R3 = 3D vector)
-- Use function-based construction
def testVector : Chain R3 1 Float :=
  ⟨fun i => match i.val with
    | 0 => 1.0
    | 1 => 2.0
    | 2 => 3.0
    | _ => 0.0⟩

#eval testVector.coeffs ⟨0, by decide⟩  -- 1.0
#eval testVector.coeffs ⟨1, by decide⟩  -- 2.0
#eval testVector.coeffs ⟨2, by decide⟩  -- 3.0

-- Test Chain operations
def v1' : Chain R3 1 Float :=
  ⟨fun i => if i.val == 0 then 1.0 else 0.0⟩
def v2' : Chain R3 1 Float :=
  ⟨fun i => if i.val == 1 then 1.0 else 0.0⟩
def v3' : Chain R3 1 Float := v1'.add v2'

#eval v3'.coeffs ⟨0, by decide⟩  -- 1.0
#eval v3'.coeffs ⟨1, by decide⟩  -- 1.0
#eval v3'.coeffs ⟨2, by decide⟩  -- 0.0

-- Test ChainBundle
def bundle' : ChainBundle R3 1 Float := ChainBundle.empty
  |>.push v1'
  |>.push v2'

#eval bundle'.size  -- 2

-- Test Mesh and IndexSimplex
def tri1' : ChainBundle.IndexSimplex := ChainBundle.IndexSimplex.triangle 0 1 2
def tri2' : ChainBundle.IndexSimplex := ChainBundle.IndexSimplex.triangle 1 2 3

#eval tri1'.grade  -- 2
#eval tri1'.numVertices  -- 3

-- Test boundary faces
#eval (ChainBundle.simplexBoundaryFaces tri1').size  -- 3 (three edges)

end Tests

/-! ## Type Hierarchy Summary

Julia Type Hierarchy (from Grassmann.jl):

```
TensorAlgebra{V}
├── TensorGraded{V,G}
│   ├── TensorTerm{V,G}
│   │   ├── Simplex{V,G,B,T}  ← Single
│   │   └── SubManifold{V,G,B} ← Blade
│   └── Chain{V,G,T}          ← Chain
└── TensorMixed{V}
    ├── Multivector{V,T}      ← Multivector
    └── AbstractSpinor{V}
        ├── Spinor{V,T}       ← Spinor
        └── Couple{V,B,T}
```

Manifold Hierarchy:
```
Manifold{N}
└── TensorBundle{N,Opts,Metric,Vars,Diff,Name}
    ├── Signature{...}        ← Signature
    ├── DiagonalForm{...}
    └── SubManifold{V,G,B}    ← Blade
```

Key correspondences:
- `Simplex{V,G,B,T}` → `Single sig F`
- `SubManifold{V,G,B}` → `Blade sig`
- `Chain{V,G,T}` → `Chain sig G F`
- `Multivector{V,T}` → `Multivector sig F`
- `ChainBundle{V,G,T,P}` → `ChainBundle sig G F`
-/

end Grassmann.SimplexChain
