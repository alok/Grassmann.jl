/-
  Manual/Basic.lean - Main documentation content

  This file contains the documentation for the Grassmann library
  using Verso's manual genre.
-/
import VersoManual
import Grassmann

-- This gets access to most of the manual genre
open Verso.Genre Manual

-- This gets access to Lean code in code blocks
open Verso.Genre.Manual.InlineLean

open Grassmann

set_option pp.rawOnError true

#doc (Manual) "Grassmann: A Lean 4 Clifford Algebra Library" =>
%%%
authors := ["Alok Singh"]
shortTitle := "Grassmann"
%%%

Grassmann is a Lean 4 port of [Grassmann.jl](https://github.com/chakravala/Grassmann.jl),
a Julia library for Clifford and Grassmann algebras. This port leverages Lean's dependent
types to provide compile-time dimension checking and provably correct implementations.

# Overview

Clifford algebra (also called geometric algebra) is a powerful mathematical framework
that unifies and generalizes complex numbers, quaternions, and exterior algebra.
Key operations include:

- **Geometric product**: The fundamental Clifford product `a ⊛ b`
- **Wedge product**: Antisymmetric exterior product `a ⋀ b`
- **Inner product**: Grade-lowering contraction `a ⌋ b`

# Signatures and Metrics

A **signature** determines the quadratic form of the algebra:

- `R3` is standard Euclidean 3-space where all basis vectors square to +1
- `STA` is spacetime algebra Cl(1,3) with one timelike and three spacelike dimensions
- `CGA3` is conformal geometric algebra Cl(4,1)

# Basis Blades

A **blade** is a wedge product of basis vectors, represented by a bitmask.
The grade of a blade is the number of basis vectors in the product.

- **Scalars**: grade 0
- **Vectors**: grade 1 (e.g., `e1`, `e2`, `e3`)
- **Bivectors**: grade 2 (e.g., `e12 = e1 ∧ e2`)
- **Trivectors**: grade 3 (e.g., `e123 = e1 ∧ e2 ∧ e3`)

# Products

## Wedge Product (∧)

The wedge product is antisymmetric and grade-increasing:
- `e1 ∧ e2 = e12`
- `e2 ∧ e1 = -e12` (anticommutativity)
- `e1 ∧ e1 = 0` (nilpotency)

## Geometric Product (·)

The geometric product is the fundamental operation:
- `e1 · e1 = 1` (in Euclidean space)
- `e1 · e2 = e12`
- `e2 · e1 = -e12`
- `e12 · e12 = -1`

## Left Contraction (⌋)

Left contraction projects one blade onto another:
- `e1 ⌋ e12 = e2`
- `e1 ⌋ e23 = 0` (e1 not in e23)

# Sign Computation

The sign of Clifford products comes from two sources:

1. **Koszul sign**: From reordering basis vectors to canonical form
2. **Metric sign**: From basis vectors that square to -1

This is computed efficiently using the `parityjoin` algorithm.

# References

- David Hestenes, *New Foundations for Classical Mechanics*
- Alan Macdonald, *Linear and Geometric Algebra*
- Leo Dorst, Daniel Fontijne, Stephen Mann, *Geometric Algebra for Computer Science*
- [Grassmann.jl documentation](https://grassmann.crucialflow.com/)
