# Grassmann

A Lean 4 port of [Grassmann.jl](https://github.com/chakravala/Grassmann.jl) - a Clifford/Geometric Algebra library.

**3400+ lines** across **15 modules** implementing geometric algebra for arbitrary dimensions and signatures.

## Features

- **Compile-time dimension checking**: Uses `BitVec n` for basis blade representation
- **Arbitrary metric signatures**: Euclidean, Minkowski, conformal, projective, and custom signatures
- **All fundamental products**: Geometric, wedge, dot, contractions, regressive
- **Involutions**: Reverse (†), involute (ˆ), conjugate (‡), Hodge dual (⋆)
- **Geometric models**: Conformal (CGA) and Projective (PGA) geometric algebras
- **Spinors/Rotors**: Efficient rotation representation with slerp
- **Linear algebra**: Generic determinants, linear maps, Cramer's rule, outermorphism
- **Calculus**: Gradient, divergence, curl, Laplacian via finite differences
- **Unicode notation**: Clean syntax with operators like `⋀`, `⊛`, `⌋`
- **Computable**: All definitions work with `#eval` and Float arithmetic

## Quick Start

```lean
import Grassmann

open Grassmann

-- Euclidean 3-space basis
#check (e1 : Blade R3)  -- grade 1 vector
#check (e12 : Blade R3) -- grade 2 bivector
#check (e123 : Blade R3) -- grade 3 pseudoscalar

-- Products
#eval (e1 : Blade R3) ⋀ (e2 : Blade R3)  -- wedge: e12
#eval (e1 : Blade R3) ⊛ (e1 : Blade R3)  -- geometric: scalar 1
#eval (e1 : Blade R3) ⌋ (e12 : Blade R3) -- contraction: e2

-- Multivector operations
#eval let v := (Multivector.ofBlade (e1 : Blade R3) : Multivector R3 Int)
      let w := (Multivector.ofBlade (e2 : Blade R3))
      (v * w).coeff e12  -- 1 (anticommutative)

-- Rotations via spinors
#eval let R := rotorZ (3.14159 / 2)  -- 90° around z
      let e1v : Multivector R3 Float := Multivector.ofBlade (e1 : Blade R3)
      R.rotate e1v  -- rotates e1 towards e2
```

## Modules

| Module | Lines | Description |
|--------|-------|-------------|
| `BitMask` | 218 | BitVec utilities: popcount, grade, indices |
| `Manifold` | 144 | Metric signatures: R1-R4, STA, CGA3, PGA3, Cl(p,q) |
| `Blade` | 184 | Basis blades with BitVec representation |
| `Parity` | 166 | Sign computation via parityjoin algorithm |
| `Products` | 198 | Geometric, wedge, dot, contraction for blades |
| `Notation` | 111 | Unicode operators: `⋀`, `⊛`, `⌋`, `⌊`, `⋁` |
| `Multivector` | 426 | Full 2^n multivector type with all products |
| `Versor` | 173 | Exponential, rotor construction, sandwich product |
| `Spinor` | 213 | Even-grade multivectors, slerp, axis-angle rotors |
| `CGA` | 190 | Conformal GA: points, lines, circles, spheres, meet |
| `PGA` | 233 | Projective GA: points, lines, planes, motors |
| `LinearAlgebra` | 266 | Generic determinant, linear maps, Cramer's rule |
| `Calculus` | 205 | Gradient, divergence, curl, Laplacian |
| `Tests` | 310 | Comprehensive algebraic identity tests |
| `OracleTests` | 371 | Tests comparing against Grassmann.jl |

## Signatures

```lean
-- Standard Euclidean spaces
R1, R2, R3, R4 : Signature n

-- Complex numbers as Cl(0,1)
ℂ_sig : Signature 1

-- Quaternions as Cl(0,2)
ℍ_sig : Signature 2

-- Spacetime algebra Cl(1,3)
STA : Signature 4

-- Conformal geometric algebra Cl(4,1)
CGA3 : Signature 5

-- Projective geometric algebra Cl(3,1)
PGA3 : Signature 4

-- Custom signatures
Signature.cl p q  -- Cl(p,q) with p positive, q negative
```

## Products

| Operator | Name | Description |
|----------|------|-------------|
| `⋀` / `⋀ᵐ` | Wedge | Antisymmetric, grade-increasing |
| `⊛` / `*` | Geometric | Full Clifford product |
| `⌋` / `⌋ᵐ` | Left contraction | Projects a into b |
| `⌊` / `⌊ᵐ` | Right contraction | Projects b into a |
| `⋁` | Regressive | Dual to wedge (meet) |
| `⋅ᵐ` | Fat dot | Left + right contraction |

## Involutions

| Notation | Name | Grade k factor |
|----------|------|----------------|
| `†` | Reverse | (-1)^(k(k-1)/2) |
| `ˆ` | Involute | (-1)^k |
| `‡` | Conjugate | (-1)^(k(k+1)/2) |
| `⋆ᵐ` | Hodge dual | Maps grade k to n-k |

## Conformal Geometric Algebra (CGA)

```lean
open Grassmann.CGA

-- Embed 3D point into CGA
let p := point (1 : Float) 2 3

-- Geometric objects as blades
let l := line p1 p2           -- grade-3 line
let c := circle p1 p2 p3      -- grade-3 circle
let π := plane p1 p2 p3       -- grade-4 plane
let s := sphere p1 p2 p3 p4   -- grade-4 sphere

-- Intersections via meet
let intersection := meet obj1 obj2
```

## Projective Geometric Algebra (PGA)

```lean
open Grassmann.PGA

-- Points, lines, planes as blades
let p := point (1 : Float) 2 3    -- grade-3 trivector
let π := plane 1 0 0 5            -- grade-1 (x = 5)
let l := joinPoints p1 p2         -- line through two points

-- Intersections
let pt := meetPlaneLine π l       -- point where line meets plane

-- Rigid transformations via motors
let T := translator 1 0 0         -- translate by (1,0,0)
let R := rotor 0 0 1 (π/2)        -- rotate 90° around z
let p' := applyMotor (T * R) p    -- combined transform
```

## Spinors and Rotations

```lean
-- Create rotor from axis-angle
let R := Spinor.fromAxisAngle bivector angle

-- Convenient R3 rotors
let Rx := rotorX angle
let Ry := rotorY angle
let Rz := rotorZ angle
let R := rotorFromEuler roll pitch yaw

-- Apply rotation
let v' := R.rotate v

-- Interpolate rotations
let Rmid := Spinor.slerp R1 R2 0.5
```

## Linear Algebra via GA

```lean
open Grassmann.LinearAlgebra

-- Generic determinant (works for any dimension!)
let d := det [v1, v2, v3]  -- R3
let d := det [v1, v2, v3, v4]  -- R4

-- Linear maps
let L : LinearMap R3 Float := LinearMap.id
let v' := L.apply v
let d := L.det

-- Solve systems via Cramer's rule
let x := cramer L b
```

## Calculus

```lean
open Grassmann.Calculus

-- Numerical derivatives
let grad := gradient f x h        -- ∇f
let div := divergence F x h       -- ∇·F
let rot := curl F x h             -- ∇×F (⋆(∇∧F))
let lap := laplacian f x h        -- ∇²f

-- Geometric measurements
let v := volume [v1, v2, v3]      -- parallelepiped volume
let a := signedArea2D v1 v2       -- 2D signed area
```

## Building

```bash
lake build
```

## Testing Against Grassmann.jl

The `OracleTests` module contains tests designed to be verified against Grassmann.jl:

```julia
using Grassmann
@basis V"+++"  # R3 Euclidean

# Verify: e1*e1 = 1, e1*e2 = e12, e12*e12 = -1
v1 * v1        # 1
v1 * v2        # v12
v12 * v12      # -1

# Rotations
R = 1 + v12    # unnormalized 45° rotor
R * v1 * ~R    # rotates e1
```

## References

- David Hestenes, *New Foundations for Classical Mechanics*
- Alan Macdonald, *Linear and Geometric Algebra*
- Leo Dorst et al., *Geometric Algebra for Computer Science*
- [Grassmann.jl](https://grassmann.crucialflow.com/)

## License

MIT
