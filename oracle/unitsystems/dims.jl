# Recover the exact exponents of every UnitSystems quantity over the eleven defining
# constants (kB, ħ, 𝘤, μ₀, mₑ, Mᵤ, Kcd, θ, λ, αL, g₀) by evaluating it on random
# synthetic unit systems and solving a log-linear least-squares problem, and map them to
# USQ dimensions (F M L T Q Θ N J A R C). Cross-checked against Similitude's `evaldim`.
#   julia --startup-file=no --project=oracle oracle/unitsystems/dims.jl [lean-snippet-path]
# Writes oracle/golden/unitsystems/dims.json (exponents stored doubled, as integers), and
# optionally the Lean source of `UnitSystems/DimTable.lean`.
using UnitSystems, Similitude, LinearAlgebra, Random
const US = UnitSystems
const FC = US.FieldConstants
include(joinpath(@__DIR__, "jsonw.jl"))
const OUT = joinpath(@__DIR__, "..", "golden", "unitsystems")
val(x) = x isa FC.Constant ? FC.constant(x) : x
Random.seed!(20260924)
const NK = 11
# USQ dims of each constant, basis order F M L T Q Θ N J A R C
const Dc = [
 1 0 1 0 0 -1 0 0 0 0 0;   # kB  = F L Θ⁻¹
 1 0 1 1 0 0 0 0 -1 0 0;   # ħ   = F L T A⁻¹
 0 0 1 -1 0 0 0 0 0 0 0;   # 𝘤   = L T⁻¹
 1 0 0 2 -2 0 0 0 0 -1 2;  # μ₀  = F T² Q⁻² R⁻¹ C²
 0 1 0 0 0 0 0 0 0 0 0;    # mₑ  = M
 0 1 0 0 0 0 -1 0 0 0 0;   # Mᵤ  = M N⁻¹
 -1 0 -1 1 0 0 0 1 0 0 0;  # Kcd = J T F⁻¹ L⁻¹
 0 0 0 0 0 0 0 0 1 0 0;    # θ   = A
 0 0 0 0 0 0 0 0 0 1 0;    # λ   = R
 0 0 0 0 0 0 0 0 0 0 -1;   # αL  = C⁻¹
 -1 1 1 -2 0 0 0 0 0 0 0]  # g₀  = M L T⁻² F⁻¹
@assert rank(Float64.(Dc)) == 11

const K = 30
rs() = exp(randn() * 2.0)
raw = [ntuple(_ -> rs(), NK) for _ in 1:K+1]
mk(p) = US.unitsystem(map(FC.Constant, p)...)
systems = [mk(p) for p in raw]
logc = [log.(collect(p)) for p in raw]
fitexp(y, X) = (e = X \ y; (e, norm(X * e - y) / max(1, norm(y))))
dbl(x) = round(Int, 2x)   # exponents are half-integers: store 2e
usqof(e2) = vec(sum(e2 .* Dc, dims = 1))   # doubled USQ exponents

conv = Any[]
for q in US.Convert
    fq = getfield(US, q)
    y = Float64[]; X = Matrix{Float64}(undef, K, NK)
    for i in 1:K
        push!(y, log(abs(Float64(val(fq(systems[1], systems[i+1]))))))
        X[i, :] = logc[i+1] .- logc[1]
    end
    e, r = fitexp(y, X)
    e2 = dbl.(e)
    @assert r < 1e-9 "$q not a monomial"
    sd = q in (:length, :time, :angle, :molarmass, :luminousefficacy) ? Similitude.evaldim(q) : getfield(Similitude, q)
    push!(conv, Dict("name" => string(q), "const2" => e2, "usq2" => usqof(e2),
                     "similitude" => [Int(x) for x in 2 .* sd.v]))
end

scal = Any[]
fl = unique(vcat(collect(US.Dimensionless), collect(US.Constants), collect(US.Physics), collect(US.Derived),
    [:amagat, :thermalconductivity_water]))
for f in fl
    isdefined(US, f) || continue
    fn = getfield(US, f)
    y = Float64[]; X = Matrix{Float64}(undef, K + 1, NK + 1)
    for i in 1:K+1
        v = Float64(val(fn(systems[i])))
        push!(y, log(abs(v)))
        X[i, 1] = 1.0
        X[i, 2:end] = logc[i]
    end
    e, r = fitexp(y, X)
    r < 1e-9 || continue   # not a monomial (sackurtetrode)
    e2 = dbl.(e[2:end])
    push!(scal, Dict("name" => string(f), "const2" => e2, "usq2" => usqof(e2)))
end
writejson(joinpath(OUT, "dims.json"), Dict("julia" => string(VERSION), "convert" => conv, "scalars" => scal,
    "Dc" => [Dc[i, :] for i in 1:11]))
println("wrote dims.json: ", length(conv), " quantities, ", length(scal), " functions")

# ---- optional: emit the Lean table of USQ dimensions of the 131 quantities ----
if length(ARGS) > 0
    names = ("F", "M", "L", "T", "Q", "Θ", "N", "J", "A", "R", "C")
    sup(n) = n == 1 ? "" : n < 0 ? "⁻" * join(("⁰¹²³⁴⁵⁶⁷⁸⁹"[nextind("⁰¹²³⁴⁵⁶⁷⁸⁹", 0, parse(Int, c) + 1)] for c in string(-n))) : join(("⁰¹²³⁴⁵⁶⁷⁸⁹"[nextind("⁰¹²³⁴⁵⁶⁷⁸⁹", 0, parse(Int, c) + 1)] for c in string(n)))
    pw(k, e) = "USQ.$(names[k])" * (e == 1 ? "" : " ^ $e")
    function lean(d2)
        d = d2 .÷ 2
        num = [pw(k, d[k]) for k in 1:11 if d[k] > 0]
        den = [pw(k, -d[k]) for k in 1:11 if d[k] < 0]
        n = isempty(num) ? "USQ.one" : join(num, " * ")
        isempty(den) ? n : n * " / " * (length(den) == 1 ? den[1] : "(" * join(den, " * ") * ")")
    end
    open(ARGS[1], "w") do io
        for c in conv
            println(io, "/-- `$(c["name"])`: `$(lean(c["usq2"]))` -/")
            println(io, "@[reducible] def $(c["name"]) : Dim := $(lean(c["usq2"]))")
        end
    end
end
