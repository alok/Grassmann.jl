# Grassmann.jl Type Hierarchy Analysis

## Overview

Grassmann.jl uses a three-layer package architecture:
1. **AbstractTensors** - Base abstract types (TensorAlgebra, TensorGraded, TensorTerm)
2. **Leibniz** - Manifold utilities, indexing, differentiation
3. **DirectSum** - Manifold types (Signature, SubManifold, Simplex)
4. **Grassmann** - Multivector types (Chain, Multivector, Spinor)

## Type Hierarchy Diagram

```
                            TensorAlgebra{V}
                                   │
              ┌────────────────────┴────────────────────┐
              │                                         │
       TensorGraded{V,G}                         TensorMixed{V}
              │                                         │
    ┌─────────┴─────────┐                    ┌──────────┴──────────┐
    │                   │                    │                     │
TensorTerm{V,G}    Chain{V,G,T}      Multivector{V,T}     AbstractSpinor{V}
    │                                                            │
    ├── Simplex{V,G,B,T}                              ┌──────────┴──────────┐
    │                                                 │                     │
    └── SubManifold{V,G,B}                     Spinor{V,T}          Couple{V,B,T}
             │
        (also acts as Blade/Basis)
```

## Manifold Types (DirectSum)

```
                         Manifold{N}
                              │
                    TensorBundle{N,Opts,Metric,Vars,Diff,Name}
                              │
         ┌────────────────────┼────────────────────┐
         │                    │                    │
   Signature{...}      DiagonalForm{...}     SubManifold{V,G,B}
```

### Signature{N,M,S,F,D,L}

The primary manifold type for Euclidean/Minkowski/Clifford algebras.

```julia
struct Signature{Indices,Options,Signatures,Vars,Diff,Name} <: TensorBundle{...}
```

**Type Parameters:**
- `Indices` (N): Dimension of the space
- `Options` (M): Byte-encoded options (infinity, origin, dyadic mode)
- `Signatures` (S): UInt bitmask where bit i=1 means e_i^2 = -1
- `Vars` (F): Number of tangent variables
- `Diff` (D): Differential mode
- `Name` (L): Index into name cache

**Examples:**
```julia
Signature(3)           # ℝ³ - 3D Euclidean
Signature(3,0,1)       # ℝ³,₀,₁ - PGA (3 positive, 0 negative, 1 zero)
Signature(4,1,0)       # ℝ⁴,₁ - CGA (4 positive, 1 negative)
Signature("+++")       # Explicit: e₁²=e₂²=e₃²=+1
Signature("+++-")      # Minkowski: e₁²=e₂²=e₃²=+1, e₄²=-1
V"+++"                 # String macro shorthand
```

### DiagonalForm{N,M,S,F,D,L}

For non-standard metrics (e.g., e₁² = 2, e₂² = 3).

```julia
struct DiagonalForm{Indices,Options,Signatures,Vars,Diff,Name} <: TensorBundle{...}
    # S is index into diagonalform_cache containing the actual Values
```

### SubManifold{V,G,B}

A basis blade within a manifold. Used both as a type for manifold subspaces AND as a blade.

```julia
struct SubManifold{V,n,Indices} <: TensorTerm{V,n}
    # V: Parent manifold
    # n: Grade (number of basis vectors wedged together)
    # Indices (B): UInt bitmask indicating which basis vectors
```

**Key Insight:** `SubManifold` is the "blade" type - it represents e₁, e₁₂, e₁₂₃, etc.

**Examples:**
```julia
SubManifold{V,1}(0b001)  # e₁
SubManifold{V,1}(0b010)  # e₂
SubManifold{V,2}(0b011)  # e₁₂ = e₁∧e₂
SubManifold{V,3}(0b111)  # e₁₂₃ = e₁∧e₂∧e₃
```

## Blade/Term Types (DirectSum)

### Simplex{V,G,B,T}

A single blade times a scalar coefficient.

```julia
struct Simplex{V,G,B,T} <: TensorTerm{V,G}
    v::T  # The scalar coefficient
end
```

**Type Parameters:**
- `V`: Manifold (Signature or SubManifold)
- `G`: Grade
- `B`: The basis blade (SubManifold{V,G})
- `T`: Scalar type (Float64, Int, etc.)

**Example:**
```julia
3.5 * e₁₂  # Simplex{V,2,e₁₂,Float64} with v=3.5
```

## Multivector Types (Grassmann)

### Chain{V,G,T}

Grade-homogeneous multivector (all terms have same grade).

```julia
@computed struct Chain{V,G,T} <: TensorGraded{V,G}
    v::Values{binomial(mdims(V),G),T}  # Exactly C(n,G) coefficients
end
```

**Size:** Stores `binomial(n,G)` coefficients where n = dimension.

**Examples:**
```julia
Chain{V,1,Float64}  # Vector in V (grade 1), n coefficients
Chain{V,2,Float64}  # Bivector in V (grade 2), C(n,2) coefficients
Chain{V,0,Float64}  # Scalar (grade 0), 1 coefficient
```

### Multivector{V,T}

Full multivector with all grades.

```julia
@computed struct Multivector{V,T} <: TensorMixed{V}
    v::Values{1<<mdims(V),T}  # 2^n coefficients
end
```

**Size:** Stores `2^n` coefficients (one per basis blade).

### Spinor{V,T}

Even-grade multivector (grades 0, 2, 4, ...).

```julia
@computed struct Spinor{V,T} <: AbstractSpinor{V}
    v::Values{1<<(mdims(V)-1),T}  # 2^(n-1) coefficients
end
```

**Size:** Stores `2^(n-1)` coefficients (half of Multivector).

### Couple{V,B,T}

A scalar + single blade (like Complex but for any blade).

```julia
struct Couple{V,B,T} <: AbstractSpinor{V}
    v::Complex{T}  # real = scalar, imag = B coefficient
end
```

## Index Computation (Leibniz)

### Key Functions

```julia
# Bitmask to indices
indices(b::UInt, N::Int) -> Vector{Int}
# e.g., indices(0b101, 3) = [1, 3]

# Index within grade
bladeindex(N, B::UInt) -> Int
# Position of blade B among all grade-G blades

# Overall index
basisindex(N, B::UInt) -> Int
# = binomsum(N,G) + bladeindex(N,B)

# Get all basis blades of grade G
indexbasis(N::Int, G::Int) -> Vector{UInt}
# e.g., indexbasis(3, 2) = [0b011, 0b101, 0b110]
```

### binomsum - Cumulative Blade Count

```julia
binomsum(n, G) = sum of binomial(n,0) + ... + binomial(n,G-1)
```

This gives the starting index for grade-G blades in the coefficient array.

## Blade Indexing Example

For 3D (n=3):
```
Grade 0: binomsum(3,0)=0, blades: [scalar]     indices: 1
Grade 1: binomsum(3,1)=1, blades: e₁,e₂,e₃     indices: 2,3,4
Grade 2: binomsum(3,2)=4, blades: e₁₂,e₁₃,e₂₃  indices: 5,6,7
Grade 3: binomsum(3,3)=7, blades: e₁₂₃         indices: 8
```

Multivector coefficient array layout:
```
[scalar, e₁, e₂, e₃, e₁₂, e₁₃, e₂₃, e₁₂₃]
   0      1   2   3    4    5    6     7
```

## Parity and Sign Computation

### parityreverse(G)
```julia
parityreverse(G) = isodd(Int((G-1)*G/2))
```
Sign change under reversion: `(-1)^(G*(G-1)/2)`

### parityinvolute(G)
```julia
parityinvolute(G) = isodd(G)
```
Sign change under grade involution: `(-1)^G`

### parityclifford(G)
```julia
parityclifford(G) = parityreverse(G) ⊻ parityinvolute(G)
```
Sign change under Clifford conjugation.

## Options Encoding

The `options` byte encodes special manifold properties:

```julia
doc2m(d,o,c=0,C=0) = (1<<(d-1))|(1<<(2*o-1))|(c<0 ? 8 : (1<<(3*c-1)))|(1<<(5*C-1))
```

- Bit 0: Has infinity point (conformal)
- Bit 1: Has origin point (conformal)
- Bits 2-3: Dyadic mode
- Bits 4+: Other options

Check functions:
```julia
hasinf(V)      # Has ∞ point
hasorigin(V)   # Has o point
hasconformal(V) = hasinf(V) && hasorigin(V)
isdyadic(V)    # Dyadic mode
```

## Lean 4 Port Strategy

### Direct Mappings

| Julia Type | Lean 4 Type |
|------------|-------------|
| `Signature{N,M,S,F,D,L}` | `Signature (n : Nat) where signs : BitVec n` |
| `SubManifold{V,G,B}` | `Blade (sig : Signature n) where bits : BitVec n` |
| `Simplex{V,G,B,T}` | `Single (sig) (blade : Blade sig) (coeff : F)` |
| `Chain{V,G,T}` | `Chain (sig) (grade : Fin (n+1)) (coeffs : Fin (n.choose grade) → F)` |
| `Multivector{V,T}` | `Multivector (sig : Signature n) (F : Type) where coeffs : Fin (2^n) → F` |
| `Spinor{V,T}` | `Spinor (sig) (F) where coeffs : Fin (2^(n-1)) → F` |

### Key Differences for Lean

1. **Grade in Type**: Julia's `G` parameter is often erased at runtime. In Lean, make it a dependent parameter for stronger guarantees.

2. **Bitmask**: Use `BitVec n` instead of `UInt` for compile-time dimension checking.

3. **Coefficient Storage**: Use `Fin (2^n) → F` or `Array F (2^n)` depending on computability needs.

4. **Options**: Encode as separate booleans or a structure rather than bit-packed byte.

### Suggested Lean Structure

```lean
/-- Metric signature: which basis vectors square to -1 -/
structure Signature (n : Nat) where
  signs : BitVec n  -- bit i = true means e_i² = -1
  hasInf : Bool := false
  hasOrigin : Bool := false

/-- A basis blade -/
structure Blade (sig : Signature n) where
  bits : BitVec n
  deriving DecidableEq, Repr

/-- Grade of a blade (number of basis vectors) -/
def Blade.grade (b : Blade sig) : Fin (n + 1) :=
  ⟨b.bits.popCount, by omega⟩

/-- Grade-homogeneous multivector -/
structure Chain (sig : Signature n) (grade : Nat) (F : Type*) where
  coeffs : Fin (Nat.choose n grade) → F

/-- Full multivector -/
structure Multivector (sig : Signature n) (F : Type*) where
  coeffs : Fin (2^n) → F

/-- Single blade × coefficient -/
structure Single (sig : Signature n) (F : Type*) where
  blade : Blade sig
  coeff : F
```

## ChainBundle (Mesh/Point Cloud)

For geometric applications, Grassmann.jl has:

```julia
struct ChainBundle{V,G,T,Points} <: Manifold{V}
    # Points is index into bundle_cache containing Vector{Chain{V,G,T}}
end
```

This represents a collection of simplices (triangles, tetrahedra, etc.) for mesh operations.

## Type Aliases

```julia
const Quaternion{V,T} = Spinor{V,T,4}
const GaussianInteger{V,B,T<:Integer} = Couple{V,B,T}
const PointCloud{T<:Chain{V,1}} = AbstractVector{T}
const ElementMesh{T<:Chain{V,1,<:Integer}} = AbstractVector{T}
```
