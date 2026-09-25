# Oracle generator for Dendriform.jl 0.2.1 (port-notes/small-algebra.md §9.4).
#
#   julia --startup-file=no --project=<juliaenv2> oracle/dendriform/gen.jl
#
# Writes oracle/golden/dendriform/{totalgroves,tree_ops,poset,grove_ops,degenerate,display,
# float16,intervals,misc}.json and runs compositions.jl once per degree in a fresh process
# (Julia's composition cache depends on call order, port-notes §4.4.9).
# Trees are Loday names (Int arrays); groves are {d: degr, rows: [names...]}; BigInts are
# decimal strings.

using Dendriform, JSON3, Random
import Dendriform: TreeInteger, TreeRational, TreeBase, treeshift, grovedisplay,
    between_list, intervals, intcomp, intcompt, intervals_full, print_interval_bin,
    print_intcomp_bin, print_intcompt_bin, posetnext, posetprev

Random.seed!(0x5EED)
const OUT = joinpath(@__DIR__, "..", "golden", "dendriform")
mkpath(OUT)
redirect_stdout(devnull) do; Dendriform.Υ(8); Dendriform.ΥI(8); end
redirect_stderr(devnull)   # silence `@info` duplicate/non-interval logs

name(t::PBTree) = Int.(t.Y)
rows(g::Grove) = [Int.(g.Y[i, :]) for i in 1:g.size]
gj(g::Grove) = Dict("d" => Int(g.degr), "rows" => rows(g))
sh(x) = sprint(print, x)
function capture(f)
    tmp = tempname()
    r = open(tmp, "w") do io
        redirect_stdout(f, io)
    end
    s = read(tmp, String); rm(tmp)
    (r, s)
end
tryop(f) = try; gj(f()); catch e; Dict("err" => string(nameof(typeof(e)))); end
write_json(file, x) = open(io -> JSON3.write(io, x), joinpath(OUT, file), "w")
trees(d) = [PBTree(d, i) for i in 1:Int(Cn(d))]

# ------------------------------------------------------------------ total groves
tg = Any[]
for d in 0:8
    ts = trees(d)
    push!(tg, Dict("d" => d, "names" => name.(ts),
        "ti" => d == 0 ? [0] : Dendriform.ΥI(d),
        "rational_shift" => d in 1:5 ? string.(TreeRational(d)) : nothing))
end
treeshift(false)
for d in 1:5
    tg[d + 1]["rational_noshift"] = string.(TreeRational(d))
end
treeshift(true)
write_json("totalgroves.json", Dict("groves" => tg,
    "catalan" => [string(Cn(d)) for d in 0:20],
    "thetamax" => [Dendriform.ΘMax(UInt8(d)) for d in 1:12]))

# ------------------------------------------------------------------ tree operations
allt = vcat([trees(d) for d in 0:6]...)
ops = Any[]
for x in allt, y in allt
    dx, dy = Int(x.degr), Int(y.degr)
    dx + dy <= 6 || continue
    push!(ops, Dict("x" => name(x), "y" => name(y),
        "sum" => tryop(() -> x + y), "dashv" => tryop(() -> x ⊣ y),
        "vdash" => tryop(() -> x ⊢ y),
        "mul" => dx * dy <= 9 ? tryop(() -> x * Grove(y)) : nothing,
        "graft" => name(x ∨ y), "over" => name(over(x, y)), "under" => name(under(x, y))))
end
single = Any[]
for x in allt
    d = Int(x.degr)
    push!(single, Dict("x" => name(x), "sigma" => name(σ(x)), "left" => name(left(x)),
        "right" => name(right(x)), "index" => d == 0 ? 0 : treeindex(x),
        "ti" => d == 0 ? 0 : TreeInteger(x),
        "next" => name.(Dendriform.posetnext_list(x)), "prev" => name.(Dendriform.posetprev_list(x)),
        "print" => sh(x),
        "print_display" => (grovedisplay(true); s = sh(x); grovedisplay(false); s),
        "primitive" => Dendriform.PrimitiveTree(x),
        "rational" => d == 0 ? nothing : string(TreeRational(x))))
end
write_json("tree_ops.json", Dict("pairs" => ops, "single" => single))

# ------------------------------------------------------------------ Tamari poset
pos = Any[]
for d in 1:5, x in trees(d), y in trees(d)
    push!(pos, Dict("x" => name(x), "y" => name(y), "lt" => x < y, "le" => x ≤ y,
        "gt" => x > y, "ge" => x ≥ y, "covers" => x ⋖ y, "coveredby" => x ⋗ y,
        "between" => d <= 4 ? name.(between_list(x, y)) : nothing))
end
write_json("poset.json", Dict("pairs" => pos))

# ------------------------------------------------------------------ groves
function randgrove()
    d = rand(1:4)
    Grove(d, rand(1:(big(2)^Cn(d) - 1)))
end
gs = [randgrove() for _ in 1:150]
# multiset groves (repeated rows), which Julia's groveindex counts with multiplicity
for _ in 1:20
    g = randgrove()
    push!(gs, Grove(vcat(g.Y, g.Y[1:1, :])))
end
gsingle = Any[]
for g in gs
    push!(gsingle, Dict("g" => gj(g), "index" => string(groveindex(g)),
        "bits" => Int.(grovebit(g)), "treeindex" => treeindex(g),
        "bin" => sh(GroveBin(g)), "print" => sh(g),
        "print_display" => (grovedisplay(true); s = sh(g); grovedisplay(false); s),
        "sigma" => gj(σ(g)), "sorted" => rows(grovesort!(deepcopy(g)))))
end
gpairs = Any[]
for _ in 1:250
    g, h = rand(gs), rand(gs)
    e = Dict("x" => gj(g), "y" => gj(h),
        "sum" => tryop(() -> g + h), "dashv" => tryop(() -> g ⊣ h), "vdash" => tryop(() -> g ⊢ h),
        "mul" => Int(g.degr) * Int(h.degr) <= 8 ? tryop(() -> g * h) : nothing,
        "eq" => (deepcopy(g) == deepcopy(h)), "lt_index" => groveindex(g) < groveindex(h))
    if g.degr == h.degr
        u = g ∪ h
        e["union"] = gj(u)
        e["union_dups"] = g.size + h.size - u.size
    end
    push!(gpairs, e)
end
# Loday's identities Y_p + Y_q = Y_{p+q}, Y_p * Y_q = Y_{pq} (as GroveBins)
loday = Any[]
for p in 1:4, q in 1:4
    p + q <= 7 && push!(loday, Dict("p" => p, "q" => q, "op" => "sum", "bin" => sh(GroveBin(Grove(p) + Grove(q)))))
    p * q <= 8 && push!(loday, Dict("p" => p, "q" => q, "op" => "mul", "bin" => sh(GroveBin(Grove(p) * Grove(q)))))
end
write_json("grove_ops.json", Dict("groves" => gsingle, "pairs" => gpairs, "loday" => loday))

# ------------------------------------------------------------------ degenerate groves
deg = Dict("e3" => Grove(3, 0), "z" => Grove(0), "leafg" => Grove(PBTree(Int[])), "g2" => Grove(2),
           "g1" => Grove(1), "g3" => Grove(3, 5))
dg = Any[]
for (nm, f) in [("dashv", ⊣), ("vdash", ⊢), ("sum", +), ("mul", *)], a in keys(deg), b in keys(deg)
    push!(dg, Dict("op" => nm, "x" => a, "y" => b, "out" => tryop(() -> f(deg[a], deg[b]))))
end
write_json("degenerate.json", Dict("groves" => Dict(k => gj(v) for (k, v) in deg), "cases" => dg))

# ------------------------------------------------------------------ display / GroveBin
bins = Any[]
for d in 1:8
    c = Cn(d)
    idx = Set{BigInt}([1, 2, 3, big(2)^c - 1, big(2)^(c - 1)])
    for k in 0:min(c - 1, 60); push!(idx, big(2)^k); end
    for _ in 1:15; push!(idx, rand(1:(big(2)^c - 1))); end
    for i in idx
        push!(bins, Dict("d" => d, "gbin" => string(i), "size" => count_ones(i),
                         "str" => sh(GroveBin(d, count_ones(i), i))))
    end
end
write_json("display.json", Dict("bins" => bins,
    "empty_tree" => sh(PBTree(0, 1)),
    "empty_tree_display" => (grovedisplay(true); s = sh(PBTree(0, 1)); grovedisplay(false); s),
    "zero_grove" => sh(Grove(0)), "leaf_grove" => sh(Grove(PBTree(Int[]))),
    "readme" => (g = Grove(3, 7) ⊣ ([1, 2] ∪ [2, 1]); Dict("g" => gj(g), "print" => sh(g),
        "print_display" => (grovedisplay(true); s = sh(g); grovedisplay(false); s),
        "bin" => sh(GroveBin(g)))),
    "readme_mul" => sh(GroveBin(Grove(2, 3) * ([1, 2, 3] ∪ [3, 2, 1])))))

# ------------------------------------------------------------------ Float16
f16 = Any[]
for m in 1:64, _ in 1:30
    i = rand(1:(big(2)^m - 1))
    push!(f16, Dict("num" => string(100i), "den" => string(big(2)^m - 1),
                    "str" => string(Float16(100i // (big(2)^m - 1)))))
end
for _ in 1:300
    n, dd = rand(0:20000), rand(1:997)
    push!(f16, Dict("num" => string(n), "den" => string(dd), "str" => string(Float16(big(n) // dd))))
end
bitstr = [string(reinterpret(Float16, UInt16(b))) for b in 0:0x7bff]
write_json("float16.json", Dict("rationals" => f16, "bits" => bitstr))

# ------------------------------------------------------------------ intervals
iv = Any[]
for d in 2:4
    ins = intervals(d)
    push!(iv, Dict("d" => d, "intervals" => string.(ins), "intcomp" => intcomp(d),
        "intcompt" => intcompt(d), "full" => Bool.(intervals_full(d)),
        "print_interval_bin" => capture(() -> print_interval_bin(d))[2],
        "print_intcomp_bin" => capture(() -> print_intcomp_bin(d))[2],
        "print_intcompt_bin" => capture(() -> print_intcompt_bin(d))[2]))
end
write_json("intervals.json", Dict("cases" => iv))

# ------------------------------------------------------------------ misc
write_json("misc.json", Dict(
    "lt7" => PBTree([2, 1, 7, 4, 1, 3, 1]) < PBTree([2, 1, 7, 4, 3, 2, 1]),
    "treerational_131" => string(TreeRational([1, 3, 1])),
    "groveindex_union" => string(groveindex([1, 2, 3] ∪ [3, 2, 1])),
    "big_sum_eq" => Grove(8, groveindex(Grove(5, 1000) + Grove(3, 7))) == Grove(5, 1000) + Grove(3, 7),
    "big_sum" => gj(Grove(5, 1000) + Grove(3, 7)),
    "catalan_inv" => [Dendriform.CnInv(Int(Cn(d))) for d in 1:10]))

# ------------------------------------------------------------------ compositions
for d in 1:4
    run(`$(Base.julia_cmd()) --startup-file=no --project=$(Base.active_project()) $(joinpath(@__DIR__, "compositions.jl")) $d`)
end
println("dendriform goldens written to ", OUT)
