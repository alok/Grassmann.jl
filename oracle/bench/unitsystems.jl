# Julia twin of Bench/UnitSystems.lean (`unitsystems` suite): UnitSystems conversion factors
# between runtime-selected systems and Similitude dimension-group products.
isdefined(Main, :BenchHarness) || include(joinpath(@__DIR__, "harness.jl"))
using .BenchHarness
using UnitSystems, Similitude
const us_US = UnitSystems
const us_FC = UnitSystems.FieldConstants

us_val(x) = x isa us_FC.Constant ? Float64(us_FC.constant(x)) : Float64(x)
function us_convertall(qs::Vector{Any}, ps::Vector{Any})
    acc = 0.0
    for q in qs, (U, S) in ps
        acc += us_val(q(U, S))
    end
    acc
end
function us_naturalall(qs::Vector{Any}, us::Vector{Any})
    acc = 0.0
    for q in qs, U in us
        acc += us_val(q(U))
    end
    acc
end
function us_dimproducts(ds::Vector{Any})
    acc = 0.0
    for a in ds, b in ds
        acc += Float64((a * b).v[3])
    end
    acc
end
# `energy(v, English, Metric)` with literal systems: Julia folds the factor.
function us_convlit(xs::Vector{Float64})
    acc = 0.0
    for v in xs
        acc += us_US.energy(v, us_US.English, us_US.Metric)
    end
    acc
end
# `energy(U, Metric)` with `U` chosen at run time (dynamic dispatch).
function us_convany(us::Vector{Any})
    acc = 0.0
    for U in us
        acc += us_val(us_US.energy(U, us_US.Metric))
    end
    acc
end

function suite_unitsystems(ctx)
    qs = Any[getfield(us_US, q) for q in us_US.Convert]
    ps = Any[(us_US.Metric, us_US.English), (us_US.English, us_US.Metric), (us_US.SI2019, us_US.Gauss),
             (us_US.Planck, us_US.Metric), (us_US.Hartree, us_US.SI2019), (us_US.IAU, us_US.Metric)]
    # Lean has three evaluation strategies for the same factors (chains on `Num`, per-pair
    # tables, unboxed chains); Julia's twin is the same runtime-dispatch loop for all three.
    for name in ("convert_pairs", "convert_pairs_sys", "convert_pairs_numf")
        bench!(i -> us_convertall(qs, blackbox(i, ps)), ctx, name;
               ops = length(qs) * length(ps), param = "$(length(qs))×$(length(ps))")
    end
    n = sized(ctx, 10000, 100)
    xs = [1.0 + i / n for i in 0:n-1]
    bench!(i -> us_convlit(blackbox(i, xs)), ctx, "convert_literal"; ops = n, param = "n=$n")
    ua = Any[us_US.English, us_US.Gauss, us_US.Planck, us_US.Hartree]
    bench!(i -> us_convany(blackbox(i, ua)), ctx, "convert_any"; ops = length(ua), param = "$(length(ua))")
    us = Any[us_US.Metric, us_US.English, us_US.Gauss, us_US.Planck, us_US.Hartree, us_US.IAU,
             us_US.Stoney, us_US.QCD]
    for name in ("natural_systems", "natural_systems_sys")
        bench!(i -> us_naturalall(qs, blackbox(i, us)), ctx, name;
               ops = length(qs) * length(us), param = "$(length(qs))×$(length(us))")
    end
    ds = Any[q in (:length, :time, :angle, :molarmass, :luminousefficacy) ? Similitude.evaldim(q) :
             getfield(Similitude, q) for q in us_US.Convert]
    bench!(i -> us_dimproducts(blackbox(i, ds)), ctx, "dim_products";
           ops = length(ds)^2, param = "$(length(ds))²")
end

register!("unitsystems", suite_unitsystems)
(abspath(PROGRAM_FILE) == @__FILE__) && main_suites(["unitsystems" => suite_unitsystems])
