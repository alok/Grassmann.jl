# Julia timings for the Cartan field benchmarks (compare Tests/Cartan/Bench.lean).
#
#   julia --startup-file=no --project=oracle oracle/cartan/bench.jl
#
# Best of 7 wall times after a warm-up run, one thread. The fields match the Lean benchmark: a
# 1000×1000 grid `range(0,1,length=1000)²`, the interval `range(0,10,length=10^6)`.
using Grassmann, Cartan
const MT = Cartan.MeshTopology
for fun in (:Torus,)
    top = Symbol(fun, :Topology)
    @eval MT.$top(p::Cartan.ProductSpace) = MT.$top(Cartan.PointArray(p))
end

function best(f, reps = 7)
    f()
    b = Inf
    r = nothing
    for _ in 1:reps
        t = @elapsed (r = f())
        b = min(b, t)
    end
    b, r
end
fmt(t) = t < 1e-3 ? string(round(t * 1e6, digits = 1), " µs") : string(round(t * 1e3, digits = 1), " ms")
chk(x::TensorField) = sum(sum.(value.(fiber(x))))
chk(x) = x
report(name, (t, r)) = println(name, ": ", fmt(t), "  (checksum ", chk(r), ")")

n = 1000
g = TensorField(ProductSpace(range(0, 1, length = n), range(0, 1, length = n)))
report("tabulate Chain ℝ3 on $(n)×$(n)", best(() -> (x -> Chain(x[1], x[2], 1.0)).(g)))
v = (x -> Chain(x[1], x[2], 1.0)).(g)
report("tabulate w", best(() -> (x -> Chain(1.0, -x[2], x[1])).(g)))
w = (x -> Chain(1.0, -x[2], x[1])).(g)
report("tabulate scalar", best(() -> (x -> x[1] + 2x[2]).(g)))
a = (x -> x[1] + 2x[2]).(g)
report("identity field of range($(n*n))", best(() -> TensorField(range(0, 10, length = n * n))))
t = TensorField(range(0, 10, length = n * n))
report("sin(t)", best(() -> sin(t)))
s = sin(t)
report("exp(t)", best(() -> exp(t)))
report("t + s", best(() -> t + s))
report("s * 2", best(() -> s * 2))
report("s * t (field product)", best(() -> s * t))
report("v + w (Chain)", best(() -> v + w))
report("2v (Chain)", best(() -> 2v))
report("a * v (scalar field times Chain field)", best(() -> a * v))
report("v ∧ w", best(() -> v ∧ w))
report("v * w (geometric)", best(() -> v * w))
report("v ⋅ w", best(() -> v ⋅ w))
report("⋆v", best(() -> ⋆v))
report("norm(v)", best(() -> norm(v)))
report("sum(s)", best(() -> sum(s)))
report("supnorm(v)", best(() -> supnorm(v)))
T = TorusParameter(n, n)
torus(x) = (r = 3 + cos(x[2]); Chain(r * cos(x[1]), r * sin(x[1]), sin(x[2])))
report("torus.(TorusParameter(n,n))", best(() -> torus.(T)))
