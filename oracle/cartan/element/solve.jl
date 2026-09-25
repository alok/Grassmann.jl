# Goldens for Cartan.Solve (sparse assembly, direct and iterative solves, dense LU, generalized
# symmetric eigenproblems): Julia's SparseArrays / LinearAlgebra (CHOLMOD, UMFPACK, LAPACK).
#
#   julia --startup-file=no --project=oracle oracle/cartan/element/solve.jl
#
# Writes oracle/golden/cartan/element/solve.json. Inputs are built from SplitMix64 streams
# (common.jl `randfloats`) or closed forms that the Lean test rebuilds identically.
include(joinpath(@__DIR__, "common.jl"))
using SparseArrays, LinearAlgebra

enc(A::SparseMatrixCSC) = Dict("m" => A.m, "n" => A.n, "colptr" => A.colptr .- 1,
    "rowval" => A.rowval .- 1, "nzval" => hxs(A.nzval))

out = Dict{String,Any}("meta" => Dict("julia" => string(VERSION)))

# 1. triplet assembly with duplicates (summation order) and products
let I = [0, 2, 1, 0, 2, 2, 1, 0, 3, 3, 0], J = [0, 0, 1, 0, 2, 0, 3, 0, 3, 1, 2],
    V = [0.1, 0.7, 0.2, 0.2, 1.5, 1e-17, -0.3, 0.3, 2.0, 0.0, 4.0]
    A = sparse(I .+ 1, J .+ 1, V, 4, 4)
    x = [1.0, -2.0, 0.5, 3.0]
    out["triplets"] = Dict("I" => I, "J" => J, "V" => hxs(V), "A" => enc(A),
        "Ax" => hxs(A * x), "At" => enc(sparse(transpose(A))))
end

# 2D 5-point Laplacian on an n×n interior grid (row-major node k = i + n j), and a
# convection-diffusion variant (first-order upwind in x, Péclet 20h)
function lap2d(n; conv = 0.0)
    I = Int[]; J = Int[]; V = Float64[]
    h = 1 / (n + 1)
    for j in 0:n-1, i in 0:n-1
        k = i + n * j
        push!(I, k); push!(J, k); push!(V, 4.0 + conv * h)
        i > 0 && (push!(I, k); push!(J, k - 1); push!(V, -1.0 - conv * h))
        i < n - 1 && (push!(I, k); push!(J, k + 1); push!(V, -1.0))
        j > 0 && (push!(I, k); push!(J, k - n); push!(V, -1.0))
        j < n - 1 && (push!(I, k); push!(J, k + n); push!(V, -1.0))
    end
    sparse(I .+ 1, J .+ 1, V, n * n, n * n)
end

# 2. sparse direct solves
let n = 30
    A = lap2d(n)
    b = randfloats(n * n, UInt64(0x5eed1), -1.0, 1.0)
    out["lap2d"] = Dict("n" => n, "b" => hxs(b), "x" => hxs(A \ b), "nnz" => nnz(A))
    C = lap2d(n; conv = 20.0)
    out["conv2d"] = Dict("n" => n, "b" => hxs(b), "x" => hxs(C \ b), "nnz" => nnz(C))
end

# 3. dense LU, solve, det, inv (random 7×7 from the stream 0xde45e)
let n = 7
    a = randfloats(n * n, UInt64(0xde45e), -1.0, 1.0)
    A = reshape(a, n, n)
    F = lu(A)
    b = randfloats(n, UInt64(0xb0b), -1.0, 1.0)
    out["dense"] = Dict("n" => n, "A" => hxs(A), "L" => hxs(F.L), "U" => hxs(F.U), "p" => F.p .- 1,
        "b" => hxs(b), "x" => hxs(A \ b), "det" => hx(det(A)), "inv" => hxs(inv(A)))
    S = A * A' + n * I
    out["dense"]["chol"] = hxs(cholesky(Symmetric(S)).L)
    out["dense"]["symeig"] = hxs(eigvals(Symmetric(S)))
end

# 4. generalized eigenproblem of the P1 finite-element Laplacian on [0,1] (N interior nodes,
#    uniform h): stiffness tridiag(-1,2,-1)/h, consistent mass h·tridiag(1,4,1)/6
let N = 60
    h = 1 / (N + 1)
    Kd = diagm(0 => fill(2 / h, N), 1 => fill(-1 / h, N - 1), -1 => fill(-1 / h, N - 1))
    Md = diagm(0 => fill(4h / 6, N), 1 => fill(h / 6, N - 1), -1 => fill(h / 6, N - 1))
    E = eigen(Symmetric(Kd), Symmetric(Md))
    out["geneig1d"] = Dict("N" => N, "vals" => hxs(E.values[1:8]))
    # 2-D: 5-point Laplacian with a lumped mass diag(1 + x_k) (x_k the node's x)
    n = 12
    A = Matrix(lap2d(n))
    Mm = Diagonal([1 + (i + 1) / (n + 1) for j in 0:n-1 for i in 0:n-1])
    E2 = eigen(Symmetric(A), Symmetric(Matrix(Mm)))
    out["geneig2d"] = Dict("n" => n, "vals" => hxs(E2.values[1:6]))
end

save("solve", out)
