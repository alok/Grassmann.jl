# Golden generator for the Cartan core (TensorField, bases, parameters, lifted algebra).
#
#   julia --startup-file=no --project=oracle oracle/cartan/gen.jl
#
# Writes oracle/golden/cartan/*.json. Floats are IEEE bit patterns ("0x…", bit-exact
# comparisons); a Julia exception is {"E": "<Type>: …"}. Arrays are column-major (`vec`), and a
# field's fibers are flattened point by point (a Chain contributes its coefficients in Grassmann's
# storage order, a Complex `re, im`), which is the Lean `FlatFiber` layout.
#
# Cartan 0.4.16 cannot build any multi-dimensional XParameter (docs/port-notes/cartan-core.md §8.6
# B1: the MeshTopology split dropped `XTopology(::ProductSpace)`); the shim below restores the
# pre-split method so the goldens record the intended values.
using Grassmann, Cartan, JSON
const MT = Cartan.MeshTopology

for fun in (:Open,:Cylinder,:Mobius,:Wing,:Mirror,:Clamped,:Torus,:Hopf,:Klein,:Cone,:Tube,:Ball,:Sphere,:Geographic)
    top = Symbol(fun,:Topology)
    @eval MT.$top(p::Cartan.ProductSpace) = MT.$top(Cartan.PointArray(p))
end

const OUT = joinpath(@__DIR__, "..", "golden", "cartan")
mkpath(OUT)
save(name, data) = (open(io -> JSON.print(io, data), joinpath(OUT, name * ".json"), "w");
    println("wrote ", name, " (", filesize(joinpath(OUT, name * ".json")), " bytes)"))

hx(x::Real) = "0x" * string(reinterpret(UInt64, Float64(x)), base = 16, pad = 16)
errstr(e) = (s = sprint(showerror, e); string(nameof(typeof(e)), ": ", first(s, 160)))
macro safe(ex)
    quote
        try
            $(esc(ex))
        catch e
            e isa InterruptException && rethrow()
            Dict("E" => errstr(e))
        end
    end
end

# flat float encodings (the Lean FlatFiber layout)
flat(x::Real) = [hx(x)]
flat(x::Complex) = [hx(real(x)), hx(imag(x))]
flat(x::Single) = [hx(value(x))]
flat(x::Coordinate) = flat(point(x))
flat(x::TensorAlgebra) = [hx(c) for c in value(x)]
flatall(xs) = reduce(vcat, [flat(x) for x in vec(collect(xs))]; init = String[])

isrange(x) = x isa AbstractRange
function encfield(t)
    Dict("size" => collect(size(t)), "fiber" => flatall(fiber(t)), "points" => flatall(points(t)),
        "isrange" => isrange(fiber(t)), "fibertype" => string(fibertype(t)))
end
encfieldsafe(f) = (r = @safe f(); r isa Dict ? r : encfield(r))

meta = Dict("julia" => string(VERSION), "cartan" => string(pkgversion(Cartan)),
    "grassmann" => string(pkgversion(Grassmann)), "meshtopology" => string(pkgversion(MT)))

# ---------- 1. range fields: Julia's lazy range arithmetic ----------
ranges = Dict{String,Any}("meta" => meta)
let cases = Dict{String,Any}()
    for (rn, r) in (("0:0.1:1", 0:0.1:1), ("0:0.25:2", 0:0.25:2), ("-1:0.3:2", -1:0.3:2),
                    ("range(0,1,length=7)", range(0, 1, length = 7)), ("LinRange(0,2π,7)", LinRange(0, 2π, 7)),
                    ("LinRange(-1,3,9)", LinRange(-1, 3, 9)))
        t = TensorField(r)
        t2 = TensorField(r, x -> 0.5x)
        ops = Dict{String,Any}()
        for (nm, f) in ("t" => () -> t, "3t" => () -> 3t, "t*3" => () -> t * 3, "2πt" => () -> 2π * t,
                        "t/3" => () -> t / 3, "-t" => () -> -t, "t+t" => () -> t + t, "t+3t" => () -> t + 3t,
                        "t-3t" => () -> t - 3t, "t/3+t*7" => () -> t / 3 + t * 7, "t+1" => () -> t + 1,
                        "1-t" => () -> 1 - t, "t*t" => () -> t * t, "t+t2" => () -> t + t2,
                        "-(t/3)" => () -> -(t / 3))
            ops[nm] = encfieldsafe(f)
        end
        ops["sum(t)"] = hx(sum(t)); ops["sum(3t)"] = hx(sum(3t)); ops["sum(t/3)"] = hx(sum(t / 3))
        ops["sum(t+1)"] = hx(sum(t + 1))
        cases[rn] = ops
    end
    ranges["cases"] = cases
end
save("ranges", ranges)

# ---------- 2. product spaces ----------
ps = Any[]
for (nm, rs) in (("0:0.1:1", (0:0.1:1,)), ("0:0.5:2 x 0:1.0:3", (0:0.5:2, 0:1.0:3)),
                 ("LinRange(0,2π,7) x LinRange(-1,1,4)", (LinRange(0, 2π, 7), LinRange(-1, 1, 4))),
                 ("0:0.25:1 x 1:-0.5:0 x 0:2.0:4", (0:0.25:1, 1:-0.5:0, 0:2.0:4)),
                 ("0:0.5:1 x 0:1.0:2", (0:0.5:1, 0:1.0:2)))
    p = ProductSpace(rs...)
    push!(ps, Dict("name" => nm, "size" => collect(size(p)), "points" => flatall(p),
        "linear5" => flat(p[5]), "show" => (@safe sprint(show, p)),
        "point5" => sprint(show, p[5]), "widths" => [hx(w) for w in Cartan.widths(p)]))
end
save("productspace", Dict("meta" => meta, "cases" => ps))

# ---------- 3. parameters ----------
params = Any[]
for (fun, ns) in ((:Open, [(5,), (3, 4), (2, 3, 2)]), (:Torus, [(5,), (4, 5), (3, 3, 4)]),
                  (:Mirror, [(5,), (4, 5)]), (:Clamped, [(5,), (4, 5)]), (:Sphere, [(5,), (5, 7), (3, 4, 5)]),
                  (:Ball, [(5,), (4, 6), (3, 4, 5)]), (:Cylinder, [(5, 4)]), (:Mobius, [(5, 4)]),
                  (:Wing, [(5, 4)]), (:Klein, [(5, 4)]), (:Cone, [(5, 4)]), (:Tube, [(5, 4), (3, 4, 5)]),
                  (:Geographic, [(6, 5)]), (:Hopf, [(3, 4, 5)]))
    P = getfield(Cartan, Symbol(fun, :Parameter))
    for n in ns
        tf = @safe P(n...)
        if tf isa Dict
            push!(params, Dict("param" => string(fun), "n" => collect(n), "error" => tf))
            continue
        end
        top = immersion(tf)
        push!(params, Dict("param" => string(fun), "n" => collect(n), "size" => collect(size(tf)),
            "points" => flatall(points(tf)), "fiber" => flatall(fiber(tf)),
            "fiberrange" => isrange(fiber(tf)),
            "p" => collect(top.p), "r" => collect(top.r), "c" => collect(top.c),
            "elem1" => sprint(show, tf[1]), "elemlast" => sprint(show, tf[end])))
    end
end
save("parameters", Dict("meta" => meta, "cases" => params))

# ---------- 4. field algebra on 2-D grids ----------
g2 = TensorField(ProductSpace(0:0.5:1.5, 0:0.25:1))
a = (x -> x[1] + 2x[2]).(g2)
b = (x -> 1 + x[1] * x[2]).(g2)
v = (x -> Chain(x[1], x[2], 1.0)).(g2)
w = (x -> Chain(1.0, -x[2], x[1])).(g2)
q = v * w
ops = Dict{String,Any}()
for (nm, f) in (
        "g2" => () -> g2, "a" => () -> a, "b" => () -> b, "v" => () -> v, "w" => () -> w,
        "a+b" => () -> a + b, "a-b" => () -> a - b, "a*b" => () -> a * b, "a/b" => () -> a / b,
        "2a" => () -> 2a, "a/3" => () -> a / 3, "-a" => () -> -a, "a+1" => () -> a + 1, "1-a" => () -> 1 - a,
        "sin(a)" => () -> sin(a), "cos(a)" => () -> cos(a), "exp(a)" => () -> exp(a), "log(b)" => () -> log(b),
        "sqrt(b)" => () -> sqrt(b), "b^0.5" => () -> b^0.5, "b^2" => () -> b^2, "b^-3" => () -> b^(-3),
        "cbrt(b)" => () -> cbrt(b), "tanh(a)" => () -> tanh(a), "atan(a)" => () -> atan(a),
        "inv(b)" => () -> inv(b), "abs(a-1)" => () -> abs(a - 1), "sign(a-1)" => () -> sign(a - 1),
        "max(a,1)" => () -> max(a, 1), "min(a,1)" => () -> min(a, 1), "mod(a,0.75)" => () -> mod(a, 0.75),
        "rem(a,0.75)" => () -> rem(a, 0.75), "round(a*1.3)" => () -> round(a * 1.3),
        "iszero(a)" => () -> iszero(a), "graph(a)" => () -> Cartan.graph(a),
        "v+w" => () -> v + w, "v-w" => () -> v - w, "2v" => () -> 2v, "v*2" => () -> v * 2, "v/2" => () -> v / 2,
        "-v" => () -> -v, "v∧w" => () -> v ∧ w, "v∨w" => () -> v ∨ w, "v*w" => () -> v * w, "v⋅w" => () -> v ⋅ w,
        "v×w" => () -> v × w, "⋆v" => () -> ⋆v, "!v" => () -> !v, "~(v*w)" => () -> ~(v * w),
        "a*v" => () -> a * v, "v*a" => () -> v * a, "v/b" => () -> v / b, "norm(v)" => () -> norm(v),
        "abs(v)" => () -> abs(v), "abs2(v)" => () -> abs2(v), "inv(v)" => () -> inv(v), "unit(v)" => () -> unit(v),
        "scalar(q)" => () -> scalar(q), "bivector(q)" => () -> bivector(q), "v<w" => () -> v < w,
        "q*q" => () -> q * q, "q+q" => () -> q + q, "v*q" => () -> v * q, "q*v" => () -> q * v,
        "v∧w∧v" => () -> (v ∧ w) ∧ v, "⋆(v∧w)" => () -> ⋆(v ∧ w), "(v∧w)⋅v" => () -> (v ∧ w) ⋅ v,
        "v⊘q" => () -> v ⊘ q, "clifford(q)" => () -> clifford(q),
        "v+q" => () -> v + q)
    ops[nm] = encfieldsafe(f)
end
ops["sum(a)"] = hx(sum(a)); ops["prod(b)"] = hx(prod(b)); ops["supnorm(v)"] = hx(supnorm(v))
ops["infnorm(v)"] = hx(Cartan.infnorm(v))
ops["sum(v)"] = flat(sum(v))
ops["findroot(a-1.1)"] = Dict("base" => flat(point(base(findroot(a - 1.1)))), "fiber" => hx(fiber(findroot(a - 1.1))))
ops["maximum(a)"] = Dict("base" => flat(point(base(maximum(a)))), "fiber" => hx(fiber(maximum(a))))
ops["split(v)"] = [flatall(fiber(c)) for c in split(v)]
save("field2d", Dict("meta" => meta, "ops" => ops))

# ---------- 5. complex and 1-D fields ----------
t = TensorField(0:0.25:2)
z = TensorField(0:0.25:2, x -> Complex(x, 1 - x))
z2 = TensorField(0:0.25:2, x -> Complex(1 + x, x / 2))
ops1 = Dict{String,Any}()
for (nm, f) in ("t" => () -> t, "sin(t)" => () -> sin(t), "t^2" => () -> t^2, "t^0.5" => () -> t^0.5,
                "sqrt(t)" => () -> sqrt(t), "exp(t)" => () -> exp(t), "log(t+1)" => () -> log(t + 1),
                "t/(t+1)" => () -> t / (t + 1), "cumsum(t)" => () -> cumsum(t), "cumprod(t+1)" => () -> cumprod(t + 1),
                "z" => () -> z, "z*z" => () -> z * z, "z+z2" => () -> z + z2, "z/z2" => () -> z / z2,
                "exp(z)" => () -> exp(z), "abs(z)" => () -> abs(z), "conj(z)" => () -> conj(z),
                "sqrt(z)" => () -> sqrt(z), "log(z2)" => () -> log(z2), "2z" => () -> 2z, "z*t" => () -> z * t,
                "t*z" => () -> t * z, "real(z)" => () -> real(z), "imag(z)" => () -> imag(z),
                "Chain.(t,t*t)" => () -> Chain.(t, t * t), "norm(Chain.(t,t*t))" => () -> norm(Chain.(t, t * t)))
    ops1[nm] = encfieldsafe(f)
end
ops1["findroot(t-1.1)"] = Dict("base" => hx(point(base(findroot(t - 1.1)))), "fiber" => hx(fiber(findroot(t - 1.1))))
ops1["sum(t)"] = hx(sum(t)); ops1["prod(t+1)"] = hx(prod(t + 1))
# pairwise reductions beyond 16 and 1024 elements
big = sin(TensorField(0:0.01:20))
ops1["sum(big)"] = hx(sum(big)); ops1["prod(1+big/100)"] = hx(prod(1 + big / 100))
mid = sin(TensorField(0:0.37:13))
ops1["sum(mid)"] = hx(sum(mid)); ops1["prod(1+mid/10)"] = hx(prod(1 + mid / 10))
ops1["mid"] = encfield(mid)
g5 = TensorField(ProductSpace(0:0.25:1, 0:0.25:1))
vbig = (x -> Chain(x[1], x[2] * x[1], 1.0 + x[2])).(g5)
ops1["sum(vbig)"] = flat(sum(vbig))
ops1["vbig"] = encfield(vbig)
save("field1d", Dict("meta" => meta, "ops" => ops1))

# ---------- 6. slices, leaves, boundary components ----------
sl = Dict{String,Any}()
aa = (x -> x[1] + 10x[2]).(TensorField(ProductSpace(0:1.0:3, 0:0.5:1)))
sl["aa"] = encfield(aa)
sl["leaf(aa,2)"] = encfield(Cartan.leaf(aa, 2)); sl["leaf(aa,2,1)"] = encfield(Cartan.leaf(aa, 2, 1))
sl["aa[:,2]"] = encfield(aa[:, 2]); sl["aa[3,:]"] = encfield(aa[3, :])
sl["boundarycomponents(aa)"] = [encfield(c) for c in boundarycomponents(aa)]
sl["boundarycomponents(aa,2)"] = [encfield(c) for c in boundarycomponents(aa, 2)]
a3 = (x -> x[1] + 10x[2] + 100x[3]).(TensorField(ProductSpace(0:1.0:2, 0:1.0:3, 0:1.0:1)))
sl["a3"] = encfield(a3)
sl["leaf(a3,2)"] = encfield(Cartan.leaf(a3, 2))
sl["boundarycomponents(a3)"] = [encfield(c) for c in boundarycomponents(a3)]
sl["a3[2,:,:]"] = encfield(a3[2, :, :]); sl["a3[:,3,:]"] = encfield(a3[:, 3, :]); sl["a3[:,:,1]"] = encfield(a3[:, :, 1])
sl["a3[:,2,1]"] = encfield(a3[:, 2, 1])
ex = extract(aa, 2)
sl["extract(aa,2)"] = Dict("base" => hx(base(ex)), "fiber" => encfield(fiber(ex)))
enctop(m) = Dict("size" => collect(size(m)), "p" => collect(m.p), "r" => collect(m.r), "c" => collect(m.c))
tops = Dict{String,Any}()
M = MobiusParameter(5, 7)
S = SphereParameter(5, 7)
B = BallParameter(5, 7)
T3 = TorusParameter(3, 4, 5)
for (nm, f) in ("M[:,4]" => () -> M[:, 4], "M[:,1]" => () -> M[:, 1], "M[2,:]" => () -> M[2, :],
                "S[:,3]" => () -> S[:, 3], "S[2,:]" => () -> S[2, :], "B[:,3]" => () -> B[:, 3],
                "B[3,:]" => () -> B[3, :], "T3[:,:,2]" => () -> T3[:, :, 2], "T3[2,:,:]" => () -> T3[2, :, :],
                "T3[:,3,2]" => () -> T3[:, 3, 2])
    r = f()
    tops[nm] = merge(enctop(immersion(r)), Dict("field" => encfield(r)))
end
sl["tops"] = tops
save("slices", Dict("meta" => meta, "cases" => sl))

# ---------- 7. simplex and face bundles ----------
V3 = Cartan.varmanifold(3)
pts = [Chain{V3}(1.0, x, y) for (x, y) in ((0.0, 0.0), (1.0, 0.0), (0.0, 1.0), (1.0, 1.0), (2.0, 0.5))]
tri = [Values(1, 2, 3), Values(2, 4, 3), Values(2, 5, 4)]
st = SimplexTopology(0, tri)
sb = PointCloud(pts)(st)
simp = Dict{String,Any}()
tf = TensorField(sb, [1.0, 2.0, 3.0, 4.0, 5.0])
simp["tf"] = encfield(tf)
simp["sin(tf)"] = encfield(sin(tf))
simp["tf*tf"] = encfield(tf * tf)
fb = Cartan.FaceBundle(sb)
simp["face_points"] = flatall(points(fb))
simp["face_field"] = encfield(TensorField(fb, [10.0, 20.0, 30.0]))
sub = sb(st[[2, 3]])
simp["sub_points"] = flatall(points(sub))
simp["sub_size"] = collect(size(sub))
simp["sub_field"] = encfield(TensorField(sub, [7.0, 8.0, 9.0, 10.0]))
simp["elem2"] = sprint(show, tf[2])
save("simplex", Dict("meta" => meta, "cases" => simp))

# ---------- 8. display ----------
disp = Dict{String,Any}()
sshow(x) = sprint(show, x); cshow(x) = sprint(show, x; context = :compact => true)
disp["LocalTensor(1.0,2.0)"] = sshow(LocalTensor(1.0, 2.0))
disp["LT(Coord(Chain),Chain)"] = sshow(LocalTensor(Coordinate(Chain(1.0, 2.0)), Chain(3.0, 4.0)))
disp["LT(Coord(Chain),Chain) compact"] = cshow(LocalTensor(Coordinate(Chain(1.0, 2.0)), Chain(3.0, 4.0)))
disp["Coordinate(Chain)"] = sshow(Coordinate(Chain(1.0, 2.0)))
disp["Coordinate(1.0,3.0)"] = sshow(Coordinate(1.0, 3.0))
disp["LT(Coordinate(1.0,3.0),1.0)"] = sshow(LocalTensor(Coordinate(1.0, 3.0), 1.0))
disp["ProductSpace 2D"] = sshow(ProductSpace(0:0.5:1, 0:1.0:2))
disp["ProductSpace 1D"] = sshow(ProductSpace(0:0.5:2))
disp["t[2]"] = sshow(TensorField(0:0.5:2)[2])
disp["tf 2D [2,3]"] = sshow(TensorField(ProductSpace(0:0.5:1, 0:1.0:2))[2, 3])
disp["tf 2D [2,3] compact"] = cshow(TensorField(ProductSpace(0:0.5:1, 0:1.0:2))[2, 3])
disp["v[2,3]"] = sshow(v[2, 3]); disp["v[2,3] compact"] = cshow(v[2, 3])
disp["q[2,3]"] = sshow(q[2, 3]); disp["(v∧w)[2,3]"] = sshow((v ∧ w)[2, 3])
disp["z[2]"] = sshow(z[2])
pa = Cartan.PointArray(0, 0:0.5:1, [2.0, 3.0, 4.0])
tfm = TensorField(pa, [1.0, 2.0, 3.0])
disp["pointwise metric base[2]"] = sshow(base(tfm)[2])
disp["pointwise metric tfm[2]"] = sshow(tfm[2])
disp["T[1]"] = sshow(TorusParameter(4, 5)[1]); disp["T[7]"] = sshow(TorusParameter(4, 5)[7])
disp["sb[2]"] = sshow(sb[2])
save("display", Dict("meta" => meta, "cases" => disp))
