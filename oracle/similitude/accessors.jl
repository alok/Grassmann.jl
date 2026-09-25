# Golden generator for Similitude's applied-units accessors:
# `dimensions`/`Dimension`/`quantity`/`unitsystem2` on `Quantity` and
# `dimensions`/`convertdim` on `ConvertUnit` (dimension.jl:230-231, 300-307).
#   julia --startup-file=no --project=oracle oracle/similitude/accessors.jl
# Writes oracle/golden/similitude/accessors.json.
using Similitude
const S = Similitude
const FA = S.FieldAlgebra
const US = S.UnitSystems
include(joinpath(@__DIR__, "..", "unitsystems", "jsonw.jl"))
const OUT = joinpath(@__DIR__, "..", "golden", "similitude")
mkpath(OUT)

ex(x::Integer) = string(x)
ex(x::Rational) = isone(denominator(x)) ? string(numerator(x)) : string(numerator(x), "/", denominator(x))
ex(x::AbstractFloat) = "0x" * string(reinterpret(UInt64, Float64(x)), base = 16, pad = 16)
ev(v) = join([ex(a) for a in v], " ")
showstr(x) = try sprint(show, x) catch; "ERROR" end

# The USQ group of a `Convert` name, reached through Similitude's dimension
# constants (Similitude.jl:166-170) rather than the UnitSystems function of the
# same name, which is callable and would recurse in `evaldim`.
# Some exported names are dimension groups, others are already SI2019 unit
# `Quantity`s (Similitude.jl:166-170 vs the derived-unit table); accept either.
function dimof(name::Symbol)
    x = getfield(S, name)
    x isa FA.Group ? x : S.dimensions(x)::FA.Group
end
# `convertdim` returns a `Constant{Group}`; unwrap to the group's exponents.
cdexps(c) = (g = S.dimension(S.convertdim(c)); g.v)

# Dimensions chosen so the 11 USQ slots are between them all exercised, and
# system pairs chosen so that `convertdim` both keeps everything (Metric ->
# English) and drops shared base dimensions (Metric -> SI2019, Metric -> Gauss).
const DIMS = [:energy, :force, :action, :angularmomentum, :power, :charge,
              :entropy, :molarmass, :luminousflux, :impedance, :photonintensity,
              :specificenergy, :pressure, :frequency]
const PAIRS = [(:Metric, :English), (:Metric, :SI2019), (:Metric, :Gauss),
               (:Metric, :Metric), (:English, :British), (:Metric, :Natural),
               (:SI2019, :CODATA), (:Metric, :IAU)]

rows = Any[]
for dn in DIMS
    d = dimof(dn)
    for (un, sn) in PAIRS
        U = getfield(S, un); Sy = getfield(S, sn)
        q = S.Quantity(U, 1.0, d)
        c = S.ConvertUnit{U,Sy}(d)
        # dimensions and Dimension are the same object (dimension.jl:303-304)
        S.dimensions(q) === S.Dimension(q) || error("dimensions !== Dimension for $dn")
        push!(rows, Any[
            string(un), string(sn), string(dn),
            ev(d.v),                      # 3: the dimension's USQ exponents
            ev(S.dimensions(q).v),        # 4: dimensions(q)
            ev(S.Dimension(q).v),         # 5: Dimension(q)
            showstr(S.dimensions(q)),     # 6: its printed form
            S.quantity(q),                # 7: quantity(q)
            string(S.unitname(S.unitsystem2(q))),  # 8: unitsystem2(q)
            ev(S.dimensions(c).v),        # 9: dimensions(c)
            ev(cdexps(c)),                # 10: convertdim(c)
            showstr(S.dimensions(c)),     # 11
        ])
    end
end
writejson(joinpath(OUT, "accessors.json"), rows)
println("wrote accessors (", length(rows), ")")
