# Julia side of the Fatou benchmarks (docs/PERF.md; Lean side: Tests/Fatou/Bench.lean).
#
#   JULIA_NUM_THREADS=1  julia --startup-file=no --project=<env with Fatou> oracle/fatou/bench.jl
#   JULIA_NUM_THREADS=16 julia --startup-file=no --project=<env with Fatou> oracle/fatou/bench.jl
#
# For each case: `Fatou.fatou(K)` itself (its maps go through `invokelatest`), and a
# handwritten kernel with Fatou's exact grid and loop semantics (iteration counts checked
# equal to Fatou's), threaded over rows like `Fatou.Compute`.

using Fatou, Base.Threads

function kernel(F, Q, C, newt, ϵ, mandel, xs, ys, N)
    rows, cols = length(ys), length(xs)
    it = Matrix{UInt16}(undef, rows, cols); zf = Matrix{ComplexF64}(undef, rows, cols)
    mix = Matrix{Float64}(undef, rows, cols)
    @threads for j in 1:rows
        @inbounds for k in 1:cols
            c = complex(xs[k], ys[j]); z = mandel ? 0.0 + 0.0im : c; n = 0x0000
            while (newt ? Q(z, c) > ϵ : Q(z, c) < ϵ) && N > n
                z = F(z, c); n += 0x0001
            end
            it[j, k] = n; zf[j, k] = z; mix[j, k] = C(z, n / N)
        end
    end
    it, zf, mix
end

const c₀ = -0.06 + 0.67im
cases = [
    ("mandelbrot 1000x1000 N=100", mandelbrot(:(z^2 + c), n = 1000, N = 100, ∂ = [-2.0, 0.5, -1.25, 1.25]),
     (z, c) -> z^2 + c, (z, c) -> abs2(z), (z, n) -> exp(-abs(z)) * n^0.0),
    ("README filled Julia n=1501", juliafill(:(z^2 + $c₀), ∂ = [-1.5, 1.5, -1, 1], N = 80, n = 1501, iter = true),
     (z, c) -> z^2 + c₀, (z, c) -> abs2(z), (z, n) -> (angle(z) / (2π)) * n^0.0),
    ("README Newton n=800", newton(:(z^3 - 1), n = 800, ϵ = 0.1, N = 25, iter = true),
     (z, c) -> (2 * z^3 + 1) / (3 * z^2), (z, c) -> abs(z^3 - 1), (z, n) -> (angle(z) / (2π)) * n^0.0),
    ("README generalized Newton n=500", newton(:(sin(z) - 1), m = 1 - 1im, ∂ = [-2π / 3, -π / 3, -π / 6, π / 6],
                                              n = 500, N = 33, iter = true, ϵ = 0.05),
     (z, c) -> ((sin(z) - 1) * (im - 1) + cos(z) * z) / cos(z), (z, c) -> abs(sin(z) - 1),
     (z, n) -> (angle(z) / (2π)) * n^0.0),
]
for (name, K, F, Q, C) in cases
    G = Fatou.fatou(Fatou.Rectangle(K)).Ω
    xs = real.(G[1, :]); ys = imag.(G[:, 1])
    it, _, _ = kernel(F, Q, C, K.newt, K.ϵ, K.mandel, xs, ys, K.N)
    S = redirect_stdout(devnull) do; fatou(K); end
    @assert it == S.iter
    th = minimum(@elapsed(kernel(F, Q, C, K.newt, K.ϵ, K.mandel, xs, ys, K.N)) for _ in 1:7)
    tf = minimum(redirect_stdout(devnull) do; @elapsed(fatou(K)); end for _ in 1:3)
    println(rpad(name, 34), " threads=$(nthreads())  handwritten $(round(th * 1000, digits = 2)) ms",
            "  Fatou.jl $(round(tf * 1000, digits = 1)) ms  (iterations $(sum(Int, S.iter)))")
end
