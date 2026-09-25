# Julia twin of Bench/Forms.lean (`forms` suite): TensorOperators of ℝⁿ (n = 3…6) built from the
# same SplitMix64 entries (column-major, +3 on the diagonal; `exp` on entries in [-1/2, 1/2)),
# a ring of K = 64 per case, every coefficient of every result summed into the checksum; and the
# documented Cramer solve `A\b` (docs/src/tutorials/dyadic-tensors.md:54-75).
isdefined(Main, :BenchHarness) || include(joinpath(@__DIR__, "harness.jl"))
using .BenchHarness
using Grassmann, LinearAlgebra

const FK = 64

frm_tot(x::Real) = Float64(x)
frm_tot(x::Chain) = sum(value(x))
frm_tot(x::Multivector) = sum(value(x))
frm_tot(x::TensorOperator) = sum(Matrix(x))
frm_tot(x::Outermorphism) = sum(sum(Matrix(TensorOperator(b))) for b in value(x))
frm_tot(x::Values) = sum(real, x) + sum(imag, x)
frm_tot(x::Grassmann.Projector) = sum(real, value(x.λ)) + sum(imag, value(x.λ)) + sum(abs, Matrix(TensorOperator(x.v)))

function frm_ops(n, xs, shift)
    V = Submanifold(n)
    [TensorOperator(Chain{V,1}(ntuple(j -> Chain{V,1}(ntuple(i -> begin
        x = xs[(k - 1) * n * n + (j - 1) * n + i]
        i == j ? x + shift : x
    end, n)...), n)...)) for k in 1:FK]
end
frm_vecs(n, xs) = [Chain{Submanifold(n),1}(ntuple(i -> xs[(k - 1) * n + i], n)...) for k in 1:FK]
frm_mvs(n, xs) = [Multivector{Submanifold(n)}(Values(ntuple(i -> xs[(k - 1) * (1 << n) + i], 1 << n)...)) for k in 1:FK]

function frm_sum1(f::F, as) where {F}
    acc = 0.0
    @inbounds for a in as
        acc += frm_tot(f(a))
    end
    acc
end
function frm_sum2(f::F, as, bs) where {F}
    acc = 0.0
    @inbounds for k in eachindex(as)
        acc += frm_tot(f(as[k], bs[k]))
    end
    acc
end

function frm_dim(ctx, n, seed)
    p = "K=$FK"
    Ts = frm_ops(n, randfloats(FK * n * n, UInt64(seed), -1.0, 1.0), 3.0)
    Us = frm_ops(n, randfloats(FK * n * n, UInt64(seed + 1), -1.0, 1.0), 3.0)
    Es = frm_ops(n, randfloats(FK * n * n, UInt64(seed + 2), -0.5, 0.5), 0.0)
    xs = frm_vecs(n, randfloats(FK * n, UInt64(seed + 3), -1.0, 1.0))
    Ms = frm_mvs(n, randfloats(FK * (1 << n), UInt64(seed + 4), -1.0, 1.0))
    Os = [outermorphism(T) for T in Ts]
    key(s) = "n=$n/$s"
    bench!(i -> frm_sum2((T, x) -> T * x, blackbox(i, Ts), xs), ctx, key("T*x"); ops = FK, param = p)
    bench!(i -> frm_sum2((T, U) -> T * U, blackbox(i, Ts), Us), ctx, key("T*U"); ops = FK, param = p)
    bench!(i -> frm_sum1(T -> value(det(T))[1], blackbox(i, Ts)), ctx, key("det"); ops = FK, param = p)
    bench!(i -> frm_sum1(inv, blackbox(i, Ts)), ctx, key("inv"); ops = FK, param = p)
    bench!(i -> frm_sum1(exp, blackbox(i, Es)), ctx, key("exp"); ops = FK, param = p)
    bench!(i -> frm_sum1(Grassmann.adjugate, blackbox(i, Ts)), ctx, key("adjugate"); ops = FK, param = p)
    bench!(i -> frm_sum2((T, x) -> value(T) \ x, blackbox(i, Ts), xs), ctx, key("solve"); ops = FK, param = p)
    bench!(i -> frm_sum1(Grassmann.characteristic, blackbox(i, Ts)), ctx, key("characteristic"); ops = FK, param = p)
    bench!(i -> frm_sum1(T -> value(eigvals(T)), blackbox(i, Ts)), ctx, key("eigvals"); ops = FK, param = p)
    bench!(i -> frm_sum1(outermorphism, blackbox(i, Ts)), ctx, key("outermorphism"); ops = FK, param = p)
    bench!(i -> frm_sum2((O, M) -> O * M, blackbox(i, Os), Ms), ctx, key("O*M"); ops = FK, param = p)
    bench!(i -> frm_sum1(T -> compound(T, 2), blackbox(i, Ts)), ctx, key("compound2"); ops = FK, param = p)
    bench!(i -> frm_sum1(eigen, blackbox(i, Ts)), ctx, key("eigen"); ops = FK, param = p)
    bench!(i -> frm_sum1(T -> Grassmann.monicroots(value(Grassmann.characteristic(T))...), blackbox(i, Ts)),
        ctx, key("roots"); ops = FK, param = p)
    bench!(i -> frm_sum1(x -> Grassmann.vandermonde(value(x)), blackbox(i, xs)), ctx, key("vandermonde"); ops = FK, param = p)
    bench!(i -> frm_sum1(T -> abs(value(det(T))[1]) / factorial(n - 1), blackbox(i, Ts)), ctx, key("volume"); ops = FK, param = p)
end

function frm_dyadic(ctx)
    n = 5
    Ts = frm_ops(n, randfloats(FK * n * n, UInt64(0xD1AD), -1.0, 1.0), 3.0)
    b = Chain{Submanifold(5),1}(1.0, 2.0, 3.0, 4.0, 5.0)
    bench!(i -> frm_sum1(T -> value(T) \ b, blackbox(i, Ts)), ctx, "dyadic/A\\b"; ops = FK, param = "K=$FK")
    m = sized(ctx, 10000, 100)
    bundle = [Ts[(k - 1) % FK + 1] for k in 1:m]
    bench!(i -> frm_sum1(T -> value(T) \ b, blackbox(i, bundle)), ctx, "dyadic/bundle A\\b"; ops = m, param = "m=$m")
end

function suite_forms(ctx)
    frm_dim(ctx, 3, 0xF003)
    frm_dim(ctx, 4, 0xF004)
    frm_dim(ctx, 5, 0xF005)
    frm_dim(ctx, 6, 0xF006)
    frm_dyadic(ctx)
end

register!("forms", suite_forms)
(abspath(PROGRAM_FILE) == @__FILE__) && main_suites(["forms" => suite_forms])
