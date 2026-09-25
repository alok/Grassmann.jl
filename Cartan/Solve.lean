import Cartan.Solve.Dense
import Cartan.Solve.Sparse
import Cartan.Solve.Iterative
import Cartan.Solve.Eigen

/-!
# `Cartan.Solve`: the linear algebra behind Cartan's elements and spectra

Julia's Cartan and Adapode lean on `LinearAlgebra`, `SparseArrays` (CHOLMOD, UMFPACK) and
KrylovKit for assembly and solves; the port has no dependencies, so this module provides them:

| module | Julia | contents |
|---|---|---|
| `Cartan.Solve.Dense` | `Matrix{Float64}`, `lu`, `\`, `cholesky`, `inv`, `det` | column-major dense matrices, LU with partial pivoting (`dgetf2`), Cholesky, triangular solves, the symmetric tridiagonal QL eigen-iteration |
| `Cartan.Solve.Sparse` | `SparseMatrixCSC`, `sparse(I,J,V,m,n)`, `*` | CSC matrices assembled from triplets (duplicates summed in Julia's order), products, transposes, reverse Cuthill–McKee, envelope Cholesky and LU |
| `Cartan.Solve.Iterative` | `A \ b` (CHOLMOD/UMFPACK), `cg`, `bicgstab` | Jacobi-preconditioned CG and BiCGSTAB, and the `\` dispatcher |
| `Cartan.Solve.Eigen` | `eigen(Symmetric(A), Symmetric(M))`, `geneigsolve` | Jacobi symmetric eigen, dense generalized eigen, shift-invert Lanczos for FEM modes |

Oracle: `oracle/cartan/element/solve.jl` → `oracle/golden/cartan/element/solve.json`
(`Tests/Cartan/Solve.lean`).
-/
