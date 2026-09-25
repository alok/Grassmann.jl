using Grassmann, DirectSum, Leibniz, LinearAlgebra, JSON
const Gm = Grassmann
fmtc(c) = (c isa Real && !(c isa Grassmann.TensorAlgebra)) ? (isinteger(c) ? Int(c) : Float64(c)) : string(c)
function terms(x)
    x isa Zero && return Any[]
    x isa Submanifold && return Any[Any[Int(UInt(x)),1]]
    x isa Single && return Any[Any[Int(UInt(basis(x))),fmtc(value(x))]]
    (x isa Number && !(x isa Grassmann.TensorAlgebra)) && return Any[Any[0,fmtc(x)]]
    V = Manifold(x); N = mdims(V)
    if x isa Chain
        ib = Leibniz.indexbasis(N,grade(x)); vals = value(x)
    else
        m = Multivector(x); ib = Leibniz.indexbasis(N); vals = value(m)
    end
    Any[Any[Int(ib[i]),fmtc(vals[i])] for i in 1:length(vals) if !((vals[i] isa Real && !(vals[i] isa Grassmann.TensorAlgebra)) && iszero(vals[i]))]
end
function mkchain(x)
    V = Manifold(x); N = mdims(V); G = grade(basis(x)); ib = Leibniz.indexbasis(N,G)
    Chain{V,G}(Values(Tuple(UInt(x)==ib[i] ? 2.0 : 0.0 for i in 1:length(ib))))
end
function rec(f)
    try
        r = f()
        return Dict("s"=>string(r),"t"=>terms(r),"T"=>string(nameof(typeof(r))))
    catch e
        return Dict("err"=>first(sprint(showerror,e),120))
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
        u["hrc"] = rec(()->complementrighthodge(mkchain(x)))
        u["crc"] = rec(()->complementright(mkchain(x)))
        u["clc"] = rec(()->complementleft(mkchain(x))); u["hlc"] = rec(()->complementlefthodge(mkchain(x)))
        u["revc"] = rec(()->reverse(mkchain(x))); u["arevc"] = rec(()->antireverse(mkchain(x)))
        u["met"] = rec(()->metric(x)); u["ameta"] = rec(()->antimetric(x))
        u["sq"] = rec(()->x*x)
        println(io, JSON.json(Dict("space"=>nm,"u"=>u)))
        for y in b
            d = Dict("space"=>nm,"a"=>Int(UInt(x)),"b"=>Int(UInt(y)))
            dm = diffvars(V)≠0 ? (dyadmode(V)<0 ? |(Leibniz.diffmask(V)...) : Leibniz.diffmask(V)) : UInt(0)
            if !iszero(UInt(x)&UInt(y)&dm)
                d["skipZ"] = true; println(io, JSON.json(d)); continue
            end
            d["mul"] = rec(()->x*y); d["wedge"] = rec(()->x∧y); d["vee"] = rec(()->x∨y)
            d["dot"] = rec(()->contraction(x,y)); d["cross"] = rec(()->cross(x,y))
            d["mulS"] = rec(()->(2.0x)*(3.0y))
            println(io, JSON.json(d))
        end
    end
    println(stderr, nm, " done in ", round(time()-t0,digits=1), "s")
end
end
