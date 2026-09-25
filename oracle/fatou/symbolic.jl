# Oracle for Fatou's symbolic layer (port-notes/fatou.md §4.5, §5.2, §5.4; G7, G8):
# every Julia expression of the README and the wiki (`scratchpad/fatou/wiki`), with
#
#   E        string(E), the title label
#   latex    REDUCE's latex(E) (the PyPlot title), newlines removed
#   F        string(newton_raphson(E, m)) for the Newton maps (REDUCE `factor`, Reduce.jl parse)
#   body1/2  nL(E, m, j) / jL(E, j), the basin bodies for j = 1, 2 (newlines removed)
#   basin1   String(basin(K, 1)) of the front-end call
#
#   julia --startup-file=no --project=<env with Fatou 1.2.4 + JSON> oracle/fatou/symbolic.jl
#
# Writes oracle/golden/fatou/symbolic.json.

using Fatou, JSON

const OUT = joinpath(@__DIR__, "..", "golden", "fatou")
const R = Fatou.Reduce
nonl(s) = replace(String(s), "\n" => "")
latexE(E) = nonl(Fatou.rdpm(Fatou.Algebra.latex(E)))

# (name, E, m) for newton; m = nothing for juliafill/mandelbrot
newtons = [
    ("readme_newton", :(z^3 - 1), 1),
    ("newton_m2", :(z^3 - 1), 2),
    ("newton_mhalf", :(z^3 - 1), -0.5),
    ("newton_quartic", :(z^4 - 1), 1),
    ("newton_cubic_factor", :(z^3 - 2z + 2), 1),
    ("newton_cubic5", :(z^3 - 2z - 5), 1),
    ("readme_gen_newton", :(sin(z) - 1), 1 - 1im),
    ("newton_z2m1", :(z^2 - 1), 1 + 1im),
    ("newton_zim", :(z^2 - im), -0.5 + 2im),
    ("newton_octic", :(z^8 - 15z^4 - 16), 1.5),
    ("newton_octic_c", :(z^8 - 15z^4 - 16), -0.5 + 2im),
    ("newton_sin", :(sin(z)), 1),
    ("newton_sextic", :(z^6 + z^3 - 1), 1 - 0.4im),
    ("newton_cos_a", :(cos(z) - 1), -0.5 + 2im),
    ("newton_cos_b", :(cos(z) - 1), 0.5 - 2im),
    ("newton_cos", :(cos(z) - 1), 1),
    ("newton_quintic", :(z^5 - 3im * z^3 - (5 + 2im)z^2 + 3z + 1), 1 - 0.24im),
    ("newton_log", :(log(z)), 1 + 1im),
    ("newton_cpow", :(z^(4.0 + 3.0im) - 1), 2.1),
    ("newton_exp", :(exp(z) + 1), 1),
    ("newton_golden", :(z^2 - z - 4), 1),
]
maps = [
    ("readme_mandelbrot", :(z^2 + c)),
    ("cubic_mandelbrot", :(z^3 + c)),
    ("readme_orbit", :(z^2 - 0.67)),
    ("default_juliafill", :(z^2 - 0.06 + 0.67im)),
    ("hump", :(z * exp(1.5 * (1 - z^2 / 50)))),
    ("hump_linear", :(z * exp(1.5 * (1 - z / 50)))),
    ("basilica", :(z^2 - 1)),
    ("float_one", :(z^2 + 1.0)),
    ("cos", :(cos(z))),
    ("sin", :(sin(z))),
    ("golden", :(z^2 - z - 4)),
    ("quadratic", :((-3 / 2) * z^2 + 5z / 2 + 1)),
    ("chebyshev", :(z^2 - 2)),
    ("cubic", :(z^3)),
    ("sqrt", :(sqrt(z))),
    ("plus_one", :(z^2 + 1)),
    ("sin2", :(sin(2z))),
    ("affine", :(3z + 2)),
    ("cubic_minus_one", :(z^3 - 1)),
    ("exp_plus_one", :(exp(z) + 1)),
    ("cpow", :(z^(4.0 + 3.0im) - 1)),
    ("sin_minus_one", :(sin(z) - 1)),
]

cases = Any[]
for (name, E, m) in newtons
    K = newton(E, m = m, n = 3)
    push!(cases, Dict("name" => name, "kind" => "newton", "E" => string(E), "m" => string(m),
        "latex" => latexE(E), "F" => string(Fatou.newton_raphson(E, m)),
        "body1" => nonl(Fatou.nL(E, m, 1)), "body2" => nonl(Fatou.nL(E, m, 2)),
        "basin0" => String(basin(K, 0)), "basin1" => nonl(basin(K, 1))))
    println(name)
end
for (name, E) in maps
    K = juliafill(E, n = 3)
    push!(cases, Dict("name" => name, "kind" => "map", "E" => string(E), "latex" => latexE(E),
        "body1" => nonl(Fatou.jL(E, 1)), "body2" => nonl(Fatou.jL(E, 2)),
        "basin0" => String(basin(K, 0)), "basin1" => nonl(basin(K, 1))))
    println(name)
end
open(io -> JSON.print(io, Dict("cases" => cases)), joinpath(OUT, "symbolic.json"), "w")
println("symbolic.json: ", length(cases), " cases")
