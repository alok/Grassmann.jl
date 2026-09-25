using Grassmann, DirectSum, Leibniz, LinearAlgebra, JSON
const Gm = Grassmann
fmtc(c) = c isa Number ? (isinteger(c) ? Int(c) : Float64(c)) : string(c)
function terms(x)
    x isa Zero && return Any[]
    x isa Submanifold && return Any[[Int(UInt(x)),1]]
    x isa Single && return Any[[Int(UInt(basis(x))),fmtc(value(x))]]
    x isa Number && return Any[[0,fmtc(x)]]
    V = Manifold(x); N = mdims(V)
    m = Multivector(x)
    ib = Leibniz.indexbasis(N)
    vals = value(m)
    Any[[Int(ib[i]),fmtc(vals[i])] for i in 1:length(vals) if !(vals[i] isa Number && iszero(vals[i]))]
end
function rec(f)
    try
        r = f()
        return Dict("s"=>string(r),"t"=>terms(r),"T"=>string(nameof(typeof(r))))
    catch e
        return Dict("err"=>sprint(showerror,e)[1:min(end,120)])
    end
end
E2 = Signature("++")
spaces = Any[
 ("E3",Signature("+++")),("M4",Signature("-+++")),("S4",Signature("+-+-")),("I4",4),
 ("C3",Signature("∞∅+")),("C5",Signature("∞∅+++")),("C4neg",Signature("∞∅+-")),
 ("P4inf",Signature("∞+++")),("P4orig",Signature("∅+++")),("P3infneg",Signature("∞-+")),
 ("D3",DiagonalForm((1,2,-3))),("D3deg",DiagonalForm((1,1,0))),("D4",DiagonalForm((2,-1,3,-4))),
 ("dual2",E2'),("dual3",Signature("+-+")'),("mixed2",E2⊕E2'),
 ("tan21",tangent(E2)),("tan22",tangent(E2,2,2)),("tanM",tangent(Signature("-+"),2,1)),
 ("MT3",Gm.MetricTensor([1 0.5 0; 0.5 1 0.5; 0 0.5 1])),
]
only = length(ARGS)>0 ? Set(ARGS) : nothing
open(get(ENV,"OUT","dump.jsonl"),"w") do io
for (nm,V0) in spaces
    (only !== nothing && !(nm in only)) && continue
    V = Submanifold(V0)
    b = Λ(V).b
    S0 = V0 isa Int ? Signature(V0) : V0
    info = Dict("space"=>nm,"show"=>string(V),"N"=>mdims(V),"opts"=>DirectSum.options(S0),
        "metricbits"=> (S0 isa Signature ? Int(DirectSum.metric(S0)) : -1),
        "diag"=> (S0 isa DiagonalForm ? collect(S0[:]) : nothing),
        "diffvars"=>diffvars(V),"diffmode"=>diffmode(V),"dyadmode"=>dyadmode(V),"grade"=>grade(V),
        "basis"=>[Int(UInt(x)) for x in b],"names"=>string.(b))
    println(io, JSON.json(Dict("info"=>info)))
    t0 = time()
    for x in b
        u = Dict("op"=>"unary","a"=>Int(UInt(x)))
        u["rev"] = rec(()->reverse(x)); u["inv"] = rec(()->involute(x)); u["cli"] = rec(()->clifford(x))
        u["arev"] = rec(()->antireverse(x)); u["conj"] = rec(()->conj(x))
        u["cr"] = rec(()->complementright(x)); u["cl"] = rec(()->complementleft(x))
        u["hr"] = rec(()->complementrighthodge(x)); u["hl"] = rec(()->complementlefthodge(x))
        u["hrc"] = rec(()->complementrighthodge(Chain(2.0x)))
        u["crc"] = rec(()->complementright(Chain(2.0x)))
        u["met"] = rec(()->metric(x)); u["ameta"] = rec(()->antimetric(x))
        u["sq"] = rec(()->x*x)
        println(io, JSON.json(Dict("space"=>nm,"u"=>u)))
        for y in b
            d = Dict("space"=>nm,"a"=>Int(UInt(x)),"b"=>Int(UInt(y)))
            d["mul"] = rec(()->x*y); d["wedge"] = rec(()->x∧y); d["vee"] = rec(()->x∨y)
            d["dot"] = rec(()->contraction(x,y)); d["cross"] = rec(()->cross(x,y))
            d["mulS"] = rec(()->(2.0x)*(3.0y))
            println(io, JSON.json(d))
        end
    end
    println(stderr, nm, " done in ", round(time()-t0,digits=1), "s")
end
end
