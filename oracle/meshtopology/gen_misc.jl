# misc.json: CrossRange, simplex numbers, the Leibniz combinatorics MeshTopology borrows, and
# the Float range `resample` methods (MT:36-46).

misc = Dict{String,Any}()

misc["crossrange"] = [Dict("n" => n, "m" => F.crossrange(n), "vals" => J(collect(F.CrossRange(n))))
                      for n in 1:13]

misc["simplexnumber"] = [Dict("N" => N, "n" => n, "out" => both(M -> M.simplexnumber(N, n)))
                         for N in 1:5 for n in 0:7]
misc["lagrange_counts"] = [Dict("N" => N, "M" => m,
        "lagrangesimplex" => F.lagrangesimplex(N, m), "centersimplex" => F.centersimplex(N, m),
        "facetsimplex" => F.facetsimplex(N, m), "edgesimplex" => F.edgesimplex(N, m))
    for N in 2:4 for m in 1:7]

const L = Grassmann.Leibniz
misc["indexparity"] = [begin
        v = Values(p...)
        (odd, s) = L.indexparity!(v)
        Dict("in" => collect(p), "odd" => odd, "sorted" => J(s))
    end for p in ((3, 1, 2), (1, 2, 3), (2, 1), (4, 3, 2, 1), (2, 2, 1), (5, 1, 4, 2, 3), (1,), (3, 3, 1),
                  (7, 2, 9, 2, 5), (6, 5, 4, 3, 2, 1))]
misc["combinations"] = [Dict("v" => collect(v), "k" => k, "out" => J(collect(L.combinations(collect(v), k))))
    for (v, k) in (((5, 2, 7), 2), ((1, 2, 3, 4), 3), ((4, 3, 2, 1), 2), ((1, 2, 3, 4, 5), 4),
                   ((9, 8), 1), ((1, 2, 3), 3))]
misc["combo"] = [Dict("n" => n, "g" => g, "out" => J(Grassmann.combo(n, g))) for n in 1:5 for g in 1:n]
misc["boundary"] = [Dict("M" => m, "out" => J(collect(F.value(F.∂(F.Submanifold(m)(I)))))) for m in 2:5]

# Float range resampling: exact bits of every element, plus the result type.
rs(x) = Dict("type" => string(nameof(typeof(x))), "bits" => [string(reinterpret(UInt64, Float64(y))) for y in x])
misc["resample_ranges"] = [
    Dict("case" => "OneTo(5),9", "out" => rs(F.resample(Base.OneTo(5), 9))),
    Dict("case" => "2:6,5", "out" => rs(F.resample(2:6, 5))),
    Dict("case" => "1:2:9,3", "out" => rs(F.resample(1:2:9, 3))),
    Dict("case" => "9:-2:1,7", "out" => rs(F.resample(9:-2:1, 7))),
    Dict("case" => "LinRange(0,1,5),9", "out" => rs(F.resample(LinRange(0, 1, 5), 9))),
    Dict("case" => "LinRange(-pi,pi,7),13", "out" => rs(F.resample(LinRange(-π, π, 7), 13))),
    Dict("case" => "0.0:0.1:1.0,21", "out" => rs(F.resample(0.0:0.1:1.0, 21))),
    Dict("case" => "0.0:0.1:1.0,4", "out" => rs(F.resample(0.0:0.1:1.0, 4))),
    Dict("case" => "range(0,2pi,length=7),13", "out" => rs(F.resample(range(0, 2π, length = 7), 13))),
    Dict("case" => "range(-1,1,length=5),(9,)", "out" => rs(F.resample(range(-1, 1, length = 5), (9,)))),
    Dict("case" => "[1.0,2.0,4.0],5", "out" => rs(F.resample([1.0, 2.0, 4.0], 5))),
    Dict("case" => "[1.0,2.0,4.0]", "out" => rs(F.resample([1.0, 2.0, 4.0]))),
    Dict("case" => "[0.5,-3.0],(4,)", "out" => rs(F.resample([0.5, -3.0], (4,)))),
    Dict("case" => "1:5,(9,)", "out" => rs(F.resample(1:5, (9,)))),
]

writejson("misc.json", misc)
