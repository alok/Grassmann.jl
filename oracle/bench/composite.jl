# Julia twin of Bench/Composite.lean (`composite` suite): composite functions of Grassmann
# elements, ↑/↓ and the README curves over the same grid of arguments, the same coefficient of
# every result summed into the checksum. The bases are `const` globals (with `@basis`'s
# non-constant globals every case is two orders of magnitude slower).
isdefined(Main, :BenchHarness) || include(joinpath(@__DIR__, "harness.jl"))
using .BenchHarness
using Grassmann
import Grassmann: Couple

const CW3 = Submanifold(S"+++")
const C3 = Λ(CW3)
const Cb1 = C3.v1
const Cb12 = C3.v12
const CWP = Submanifold(D"0,1,1,1")
const CWC = Submanifold(S"∞∅+++")
const CC = Λ(CWC)
const CWI = Submanifold(S"∞+++")
const CI = Λ(CWI)

"The sum of every coefficient of a result (so no output lane is dead code)."
cmp_sum(r::Real) = Float64(r)
cmp_sum(r) = sum(value(r))

function cmp_loop(f::F, xs) where {F}
    acc = 0.0
    @inbounds for x in xs
        acc += cmp_sum(f(x))
    end
    acc
end

cmp_biv(x) = Chain{CW3,2}(0.3x, 0.2x, 0.4x)
cmp_quat(x) = Spinor{CW3}(Values(1.0, 0.3x, 0.2x, 0.4x))
cmp_mv(x) = Multivector{CW3}(Values(ntuple(i -> (0.1x) * Float64(i), 8)))
cmp_mvq(x) = Multivector{CW3}(Values(1.0, 0.0, 0.0, 0.0, 0.3x, 0.2x, 0.4x, 0.0))
cmp_pga(x) = Chain{CWP,2}(x * 0.3, x * 0.2, x * 0.4, x * 0.1, x * 0.5, x * 0.6)
cmp_cga(x) = Chain{CWC,2}(0.0, x, 0.5x, -0.25x, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0)

# the README curves (README.md:287-316)
const Ctorus = (3 / 7) * CI.v12 + CI.v∞3
const Cp111 = CI.v1 + CI.v2 + CI.v3
const Cp11m = CI.v1 + CI.v2 - CI.v3
const Chelix = (3 / 7) * CC.v12 + CC.v∞3
const Cc111 = CC.v1 + CC.v2 + CC.v3
cmp_torus(t) = ↓(exp(π * t * Ctorus) >>> ↑(Cp111))
cmp_wobble(t) = sin(3t) * 3CI.v1 + cos(2t) * 7CI.v2 - sin(5t) * 4CI.v3
cmp_orbit2(t) = ↓(exp(t * CI.v∞ * cmp_wobble(t) / 2) >>> ↑(Cp11m))
cmp_orbit4(t) = ↓(exp(t * (CI.v12 + 0.07CI.v∞ * cmp_wobble(t) / 2)) >>> ↑(Cp11m))
cmp_helix(t) = ↓(exp(π * t * Chelix) >>> ↑(Cc111))
const Corb = chainfield(exp((π / 4) * (CI.v12 + CI.v∞3)), CWI(2, 3, 4))
const CW234 = CWI(2, 3, 4)

function suite_composite(ctx)
    n = sized(ctx, 1000, 20)
    p = "n=$n"
    d = 1.0 / n
    xs = [0.5 * d + Float64(i) * d for i in 0:n-1]
    b(name, f) = bench!(i -> cmp_loop(f, blackbox(i, xs)), ctx, name; ops = n, param = p)
    b("ℝ3/input_biv", x -> cmp_biv(x))
    b("ℝ3/input_quat", x -> cmp_quat(x))
    b("ℝ3/Couple.exp", x -> exp(Couple{CW3,Cb12}(0.1, x)))
    b("ℝ3/Single.exp", x -> exp(x * Cb12))
    b("ℝ3/Couple.log", x -> log(Couple{CW3,Cb12}(1.0, x)))
    b("ℝ3/Couple.sqrt", x -> sqrt(Couple{CW3,Cb12}(1.0, x)))
    b("ℝ3/Couple.cosh", x -> cosh(Couple{CW3,Cb1}(0.5, x)))
    b("ℝ3/Couple.logFast", x -> Grassmann.log_fast(Couple{CW3,Cb12}(1.0, x)))
    b("ℝ3/Couple.pow5", x -> Couple{CW3,Cb12}(1.0, x)^5)
    b("ℝ3/Phasor.complexify", x -> complexify(Phasor(2.0, x * Cb12)))
    b("ℝ3/Chain.exp", x -> exp(cmp_biv(x)))
    b("ℝ3/Chain.exp_mv", x -> exp(cmp_biv(x)))
    b("ℝ3/Chain.cos", x -> cos(cmp_biv(x)))
    b("ℝ3/Spinor.exp", x -> exp(cmp_quat(x)))
    b("ℝ3/Spinor.log", x -> log(cmp_quat(x)))
    b("ℝ3/Spinor.sqrt", x -> sqrt(cmp_quat(x)))
    b("ℝ3/Multivector.exp", x -> exp(cmp_mv(x)))
    b("ℝ3/Multivector.log", x -> log(cmp_mvq(x + 0.1)))
    b("ℝ3/Multivector.sqrt", x -> sqrt(cmp_mvq(x + 0.1)))
    b("ℝ3/Multivector.pow3", x -> cmp_mv(x)^3)
    b("ℝ3/Multivector.logFast", x -> Grassmann.log_fast(cmp_mvq(x + 0.1)))
    b("PGA3/Chain.exp", x -> exp(cmp_pga(x)))
    b("CGA3/Chain.exp", x -> exp(cmp_cga(x)))
    b("Inf3/up", x -> ↑(Chain{CWI,1}(0.0, x, 0.5, -x)))
    b("Inf3/down", x -> ↓(Chain{CWI,1}(0.25, x, 0.5, -x)))
    b("CGA3/up", x -> ↑(Chain{CWC,1}(0.0, 0.0, x, 0.5, -x)))
    b("CGA3/down", x -> ↓(Chain{CWC,1}(0.5 + x * x, 1.0, x, 0.5, -x)))
    b("Inf3/torus", t -> cmp_torus(t))
    b("Inf3/orbit2", t -> cmp_orbit2(t))
    b("Inf3/orbit4", t -> cmp_orbit4(t))
    b("CGA3/helix", t -> cmp_helix(t))
    b("Inf3/chainfield", x -> Corb(Chain{CW234,1}(x, 0.5, -x)))
end

register!("composite", suite_composite)
(abspath(PROGRAM_FILE) == @__FILE__) && main_suites(["composite" => suite_composite])
