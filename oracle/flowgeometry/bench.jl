# Julia side of Tests/FlowGeometry/Bench.lean: time per call of FlowGeometry's constructors.
#
#   julia --startup-file=no --project=oracle oracle/flowgeometry/bench.jl [path/to/FlowGeometry.jl]
#
# Each case runs `n` calls in a loop whose results feed a global sink (so nothing is optimized
# away), best of 7 after a warm-up; inputs come from `Ref`s so they are not constants.
using Grassmann, Cartan, LinearAlgebra
const SRC = length(ARGS) ≥ 1 ? ARGS[1] : joinpath(homedir(), "chakravala", "FlowGeometry.jl")
include(joinpath(SRC, "src", "FlowGeometry.jl"))
using .FlowGeometry
const F = FlowGeometry
isdefined(F, :TorusTopology) || Core.eval(F, :(const TorusTopology = Cartan.TorusTopology))
const fib = Cartan.fiber

sink = Ref(0.0)
function timeit(name, n, f, x)
    f(x); f(x)
    best = Inf
    for _ in 1:7
        t = @elapsed for _ in 1:n
            sink[] += f(x)
        end
        best = min(best, t)
    end
    ns = best / n * 1e9
    s = ns < 1e4 ? string(round(ns, digits = 1), " ns") : ns < 1e7 ? string(round(ns / 1e3, digits = 1), " µs") :
        string(round(ns / 1e6, digits = 1), " ms")
    println("  ", name, ": ", s)
end

nacafun = getfield(F, Symbol("@NACA_str"))
parse_naca(s) = (a = nacafun(LineNumberNode(1), Main, s); Float64(typeof(a).parameters[end]))
timeit("NACA\"2412\" parse (macro body)", 10000, parse_naca, "2412")
timeit("NACA\"24012-34\" parse (macro body)", 10000, parse_naca, "24012-34")

field(p) = fib(profile(p))[end]
slopef(p) = fib(profileslope(p))[end]
for (name, p) in (("ClarkY{12,150}", ClarkY{12,150}()), ("Thickness{12,4,150}", Thickness{12,4,150}()),
        ("Modified{12,64,150}", Modified{12,64,150}()), ("NACA4{24,150}", NACA4{24,150}()),
        ("NACA5{230,150}", NACA5{230,150}()), ("NACA6{2,150}", NACA6{2,150}()), ("CircularArc{6,150}", CircularArc{6,150}()))
    timeit("profile($name)", 2000, field, Ref(p)[])
end
timeit("profileslope(ClarkY{12,150})", 2000, slopef, ClarkY{12,150}())

N = F.@NACA_str "2412"
up(N) = real(fib(upper(N))[2])
cx(N) = real(fib(complex(N))[2])
pts(N) = F.points(N)[2][2]
timeit("upper(NACA\"2412\")", 2000, up, N)
timeit("complex(NACA\"2412\")", 2000, cx, N)
timeit("points(NACA\"2412\")", 2000, pts, N)
timeit("complex(NACA\"0012-64\")", 2000, cx, F.@NACA_str "0012-64")
J = F.joukowski(1.1, 0.1, 0.1, 1.0, 75)
timeit("complex(Joukowski{1.1,0.1,0.1,1.0,75})", 2000, cx, J)

rak(P) = (r = F.initrakich(P); Float64(length(r[1])))
timeit("initrakich() (101×51)", 20, rak, CircularArc{6,61}())
wng(N) = fib(F.wing(N))[end][3]
timeit("wing(NACA\"6511\") (150×299)", 20, wng, F.@NACA_str "6511")
rnd(k) = ((k * 2654435761 + 12345) % 1000003) / 1000003 - 0.5
hullp = Cartan.PointCloud([Chain{Submanifold(ℝ^3),1}(1.0, rnd(2k), rnd(2k + 1)) for k in 0:24])
hull(p) = Float64(length(F.convhull(p)))
timeit("convhull (25 points)", 200, hull, hullp)
faces = [Values(1, 2, 3), Values(1, 7, 2), Values(1, 3, 9), Values(1, 5, 7), Values(1, 9, 5), Values(2, 8, 3),
    Values(2, 7, 6), Values(2, 6, 8), Values(3, 8, 4), Values(3, 4, 9), Values(4, 8, 10), Values(4, 11, 9),
    Values(4, 10, 11), Values(5, 12, 7), Values(5, 9, 11), Values(5, 11, 12), Values(6, 7, 12), Values(6, 10, 8),
    Values(6, 12, 10), Values(10, 12, 11)]
function sph(r)
    P = Cartan.PointCloud(F.sphere(r))   # a fresh cloud each call: `sphere` appends in place
    s = F.sphere(F.sphere(P(SimplexTopology(faces, 12)), r), r)
    Float64(length(Cartan.fullpoints(s)))
end
timeit("sphere subdivision ×2 (20 → 320 faces)", 200, sph, 1.0)

function evals(p, n)
    s = 0.0; x = 0.0; st = 1 / n
    for _ in 1:n
        s += p(x); x += st
    end
    s
end
for (name, p) in (("ClarkY{12}", ClarkY{12,150}()), ("Modified{12,64}", Modified{12,64,150}()), ("NACA6{2}", NACA6{2,150}()))
    evals(p, 10)
    best = Inf
    for _ in 1:7
        best = min(best, @elapsed(sink[] += evals(p, 10^6)))
    end
    println("  ", name, "(x) per point: ", round(best * 1e3, digits = 2), " ns")
end
println("  (sink ", sink[], ")")
