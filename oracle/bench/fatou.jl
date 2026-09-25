# Julia twin of Bench/Fatou.lean (`fatou` suite). Run with every core (`--threads=auto`):
# `*_par` uses the threaded kernel, `*_seq` the same kernel on one thread, `*_fatoujl` is
# `Fatou.fatou` itself. The kernel has Fatou's exact grid and loop semantics (iteration counts
# checked equal to Fatou's), threaded over rows like `Fatou.Compute` (from oracle/fatou/bench.jl).
isdefined(Main, :BenchHarness) || include(joinpath(@__DIR__, "harness.jl"))
using .BenchHarness
using Fatou, Base.Threads

@inline function fatou_row!(it, zf, mix, F, Q, C, newt, ϵ, mandel, xs, ys, N, j)
    @inbounds for k in eachindex(xs)
        c = complex(xs[k], ys[j]); z = mandel ? 0.0 + 0.0im : c; n = 0x0000
        while (newt ? Q(z, c) > ϵ : Q(z, c) < ϵ) && N > n
            z = F(z, c); n += 0x0001
        end
        it[j, k] = n; zf[j, k] = z; mix[j, k] = C(z, n / N)
    end
end
function fatou_kernel(F, Q, C, newt, ϵ, mandel, xs, ys, N, par::Bool)
    rows, cols = length(ys), length(xs)
    it = Matrix{UInt16}(undef, rows, cols); zf = Matrix{ComplexF64}(undef, rows, cols)
    mix = Matrix{Float64}(undef, rows, cols)
    if par
        @threads for j in 1:rows
            fatou_row!(it, zf, mix, F, Q, C, newt, ϵ, mandel, xs, ys, N, j)
        end
    else
        for j in 1:rows
            fatou_row!(it, zf, mix, F, Q, C, newt, ϵ, mandel, xs, ys, N, j)
        end
    end
    it
end

const fatou_c₀ = -0.06 + 0.67im

function fatou_cases(ctx, tag, param, K, F, Q, C)
    G = redirect_stdout(devnull) do; Fatou.fatou(Fatou.Rectangle(K)).Ω; end
    xs = real.(G[1, :]); ys = imag.(G[:, 1])
    bench!(ctx, "$(tag)_seq"; param = param) do i
        sum(Int, fatou_kernel(F, Q, C, K.newt, K.ϵ, K.mandel, blackbox(i, xs), ys, K.N, false))
    end
    bench!(ctx, "$(tag)_par"; param = param) do i
        sum(Int, fatou_kernel(F, Q, C, K.newt, K.ϵ, K.mandel, blackbox(i, xs), ys, K.N, true))
    end
    bench!(ctx, "$(tag)_fatoujl"; param = param) do i
        S = redirect_stdout(devnull) do; fatou(blackbox(i, K)); end
        sum(Int, S.iter)
    end
end

function suite_fatou(ctx)
    n = sized(ctx, 1000, 100)
    fatou_cases(ctx, "mandelbrot", "$(n)² N=100",
        mandelbrot(:(z^2 + c), n = n, N = 100, ∂ = [-2.0, 0.5, -1.25, 1.25]),
        (z, c) -> z^2 + c, (z, c) -> abs2(z), (z, n) -> exp(-abs(z)) * n^0.0)
    m = sized(ctx, 1501, 151)
    fatou_cases(ctx, "filled_julia", "$(m)×$((2m + 2) ÷ 3) N=80",
        juliafill(:(z^2 + $fatou_c₀), ∂ = [-1.5, 1.5, -1, 1], N = 80, n = m, iter = true),
        (z, c) -> z^2 + fatou_c₀, (z, c) -> abs2(z), (z, n) -> (angle(z) / (2π)) * n^0.0)
    k = sized(ctx, 800, 100)
    fatou_cases(ctx, "newton", "$(k)² N=25",
        newton(:(z^3 - 1), n = k, ϵ = 0.1, N = 25, iter = true),
        (z, c) -> (2 * z^3 + 1) / (3 * z^2), (z, c) -> abs(z^3 - 1), (z, n) -> (angle(z) / (2π)) * n^0.0)
    g = k * 5 ÷ 8
    fatou_cases(ctx, "gen_newton", "$(g)² N=33",
        newton(:(sin(z) - 1), m = 1 - 1im, ∂ = [-2π / 3, -π / 3, -π / 6, π / 6], n = g, N = 33, iter = true, ϵ = 0.05),
        (z, c) -> ((sin(z) - 1) * (im - 1) + cos(z) * z) / cos(z), (z, c) -> abs(sin(z) - 1),
        (z, n) -> (angle(z) / (2π)) * n^0.0)
end

register!("fatou", suite_fatou)
(abspath(PROGRAM_FILE) == @__FILE__) && main_suites(["fatou" => suite_fatou])
