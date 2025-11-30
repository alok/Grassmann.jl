# Grassmann

A Lean 4 port of [Grassmann.jl](https://github.com/chakravala/Grassmann.jl) - a Clifford/Geometric Algebra library.

## Features

- **Compile-time dimension checking**: Uses `BitVec n` for basis blade representation
- **Arbitrary metric signatures**: Euclidean, Minkowski, conformal, and custom signatures
- **All fundamental products**: Geometric, wedge, dot, contractions, regressive
- **Unicode notation**: Clean syntax with operators like `⋀`, `⊛`, `⌋`
- **Computable**: All definitions work with `#eval` and can be used in programs

## Quick Start

```lean
import Grassmann

open Grassmann

-- Euclidean 3-space
#check R3  -- Signature 3

-- Basis vectors
#check (e1 : Blade R3)  -- grade 1
#check (e2 : Blade R3)
#check (e3 : Blade R3)

-- Bivectors
#check (e12 : Blade R3)  -- e₁ ∧ e₂
#check (e23 : Blade R3)  -- e₂ ∧ e₃

-- Products
#eval (e1 : Blade R3) ⋀ (e2 : Blade R3)  -- wedge: e12
#eval (e1 : Blade R3) ⊛ (e1 : Blade R3)  -- geometric: scalar (e₁² = 1)
#eval (e1 : Blade R3) ⌋ (e12 : Blade R3) -- contraction: e2
```

## Modules

| Module | Description |
|--------|-------------|
| `BitMask` | BitVec utilities: popcount, grade, indices |
| `Manifold` | Metric signatures: Euclidean, Minkowski, Cl(p,q) |
| `Blade` | Basis blades and scaled blades (Single) |
| `Parity` | Sign computation via parityjoin algorithm |
| `Products` | Geometric, wedge, dot, contraction products |
| `Notation` | Unicode operators: `⋀`, `⊛`, `⌋`, `⌊`, `⋁` |

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

-- Custom signatures
Signature.cl p q  -- Cl(p,q) with p positive, q negative
```

## Products

| Operator | Name | Description |
|----------|------|-------------|
| `⋀` | Wedge | Antisymmetric, grade-increasing |
| `⊛` | Geometric | Full Clifford product |
| `⌋` | Left contraction | Projects a into b |
| `⌊` | Right contraction | Projects b into a |
| `⋁` | Regressive | Dual to wedge (meet) |

## Sign Computation

The `parityjoin` algorithm efficiently computes signs from:
1. **Koszul sign**: Permutation parity from reordering basis vectors
2. **Metric sign**: Contribution from basis vectors squaring to -1

```lean
-- e₂ ∧ e₁ = -e₁₂ (one transposition)
#eval (e2 : Blade R3) ⋀ (e1 : Blade R3)  -- nonzero (-1) { bits := 0x3#3 }

-- e₁₂ · e₁₂ = e₁e₂e₁e₂ = -e₁e₁e₂e₂ = -1
#eval (e12 : Blade R3) ⊛ (e12 : Blade R3)  -- nonzero (-1) { bits := 0x0#3 }
```

## Building

```bash
lake build
```

## Documentation

Verso documentation is in `Manual/`. To enable, uncomment the verso
dependency in `lakefile.toml` and run `lake build manual`.

## References

- David Hestenes, *New Foundations for Classical Mechanics*
- Alan Macdonald, *Linear and Geometric Algebra*
- Leo Dorst et al., *Geometric Algebra for Computer Science*
- [Grassmann.jl](https://grassmann.crucialflow.com/)

## License

MIT
