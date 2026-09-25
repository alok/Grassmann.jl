# Loaders for the MeshTopology.jl oracle (port-notes/meshtopology.md §9.1).
#
# `Upstream.MeshTopology` is the registered MeshTopology.jl 0.1.0 with a single import line
# added: upstream references `Grassmann.*`, `Leibniz.*`, `Submanifold` and `∂` without
# importing them (Q1), so every Lagrange constructor, `edges`/`adjacency` for N ≥ 3,
# `faces`/`facets`/`skeleton` and compact `resample` throw `UndefVarError`. Injecting the
# bindings at runtime does not work (generated functions run in their defining world age), so
# the package source is copied to a temporary directory, patched and `include`d.
#
# `Fixed.MeshTopology` additionally applies the textual fixes in `FIXES` below, one per
# documented defect (oracle/meshtopology/defects.toml). The Lean port implements exactly the
# `Fixed` semantics; goldens record the upstream value next to it wherever the two differ.

import Grassmann
import MeshTopology as _MTReg
const MT_SRC = dirname(pathof(_MTReg))

const IMPORT_FIX = ("MeshTopology.jl",
    "import AbstractTensors\n" => "import AbstractTensors\nimport Grassmann\nimport Grassmann: Leibniz, Submanifold, ∂\n", 1)

# (file, old => new, expected count); `old` may be a Regex.
const FIXES = [
    # Q2: iscompact(::CompactTopology) is a MethodError; intended O == 2N.
    ("quotient.jl", "iscompact(t::QuotientTopology) = false\niscompact(t::CompactTopology) = true" =>
        "iscompact(t::QuotientTopology{N,L,M,O}) where {N,L,M,O} = O==M", 1),
    # Q3: 1-D getlinear returns a Values, compared with an Int by elementfun.
    ("grid.jl", "getlinear(l,m::QuotientTopology{1},::Val,i::Int) = getindex(m,i)" =>
        "getlinear(l,m::QuotientTopology{1},::Val,i::Int) = getindex(l,getindex(m,i)...)", 1),
    # Q4: 1-D linearelements broadcasts over the values instead of the cells.
    ("grid.jl", "linearelements(l::AbstractVector) = linearelement.(l,length(l)-1)" =>
        "linearelements(l::AbstractVector) = [linearelement(l,i) for i ∈ OneTo(length(l)-1)]", 1),
    # Q5: 4-D linearelements uses s[3] for the w range.
    ("grid.jl", "k ∈ OneTo(s[3]-1), w ∈ OneTo(s[3]-1)]" => "k ∈ OneTo(s[3]-1), w ∈ OneTo(s[4]-1)]", 1),
    # Q8: BallTopology() and SphereTopology() build tubes.
    ("quotient.jl", "BallTopology() = TubeTopology(20,61)" => "BallTopology() = BallTopology(20,61)", 1),
    ("quotient.jl", "SphereTopology() = TubeTopology(31,61)" => "SphereTopology() = SphereTopology(31,61)", 1),
    # Q9: typo in BallTopology(Values{5}).
    ("quotient.jl", "PRoductTopology" => "ProductTopology", 1),
    # Q11: the upper face of axis 5 uses n4 as the source size.
    ("quotient.jl", "location(m.p,m.q,r,n4,s,o,i,j,k,l)" => "location(m.p,m.q,r,n5,s,o,i,j,k,l)", 1),
    # Q12: Int × Q does not shift the target faces by one axis.
    ("quotient.jl", "QuotientTopology(n.p,\n        Values((zeroprodtop(n.r[1],m)" =>
        "QuotientTopology(n.p.+2,\n        Values((zeroprodtop(n.r[1],m)", 1),
    ("quotient.jl", "QuotientTopology(n.p,m .× n.q," => "QuotientTopology(n.p.+2,m .× n.q,", 1),
    # Q14: general-O resample takes the transversal sizes of the wrong axis.
    ("quotient.jl", "i[perms[t[\$((j+1)÷2)]]]" => "i[perms[_to_axis(t[\$j])]]", 1),
    # Q31: resample and resize rebuild the topology without its collapse flags.
    ("quotient.jl", ":(m.r),Expr(:call,:Values,:i)))" => ":(m.r),Expr(:call,:Values,:i),:(m.c)))", 2),
    ("quotient.jl", "QuotientTopology(m.p,m.q,m.r,Values(i))" => "QuotientTopology(m.p,m.q,m.r,Values(i),m.c)", 1),
    ("quotient.jl", ": :i for j ∈ countvalues(1,N)]...))" => ": :i for j ∈ countvalues(1,N)]...),:(m.c))", 3),
    # Q15: resample(m, (i,)) of a 1-D ProductTopology or QuotientTopology is ambiguous with
    # resample(::AbstractVector, (i,)), which is meant for plain vectors.
    ("MeshTopology.jl", "resample(m::AbstractVector,i::NTuple{1,Int}) = resample(m,i...)" =>
        "resample(m::DenseVector,i::NTuple{1,Int}) = resample(m,i...)", 1),
    # Q16: resize compares slot numbers with the slots of the last-axis faces.
    ("quotient.jl", ":((@inbounds m.r[\$j])∉(@inbounds m.r[2N-1],@inbounds m.r[2N])" =>
        ":((@inbounds invert_q(\$(Val(O)),m.r)[\$j])∉(\$(2N-1),\$(2N))", 1),
    # Q17: DiscontinuousTopology of a non-full topology gets `i = nothing`.
    ("MeshTopology.jl", "            i[j:N:n] = cols[j]\n        end\n    end\n" =>
        "            i[j:N:n] = cols[j]\n        end\n        i\n    end\n", 1),
    # Q18a: typos in the Lagrange getelement chain.
    ("lagrange.jl", "_getelemeent" => "_getelement", 2),
    ("lagrange.jl", "getelment3" => "getelement3", 1),
    # Q18b: subimmersion(::Lagrange*) leaves M unbound; tetrahedra build triangles.
    ("lagrange.jl", r"function subimmersion\(m::(Lagrange\w+)\{M,N,<:(\w+)\} where \{M,N\}\)" =>
        s"function subimmersion(m::\1{M,N,<:\2}) where {M,N}", 6),
    ("lagrange.jl", "LagrangeTriangles{M}(0,subimmersion(cornertopology(m)),subimmersion(facets(m))" =>
        "LagrangeTetrahedra{M}(0,subimmersion(cornertopology(m)),subimmersion(facets(m))", 1),
    # Q18d: element center nodes use the subspace index instead of the full element index.
    ("lagrange.jl", "centerindex(i,np,ne,Val(M)))\nend\nfunction getlagrange4" =>
        "centerindex(ind,np,ne,Val(M)))\nend\nfunction getlagrange4", 1),
    ("lagrange.jl", "facetsindex(fi,np,ne,N),centerindex(i,np,ne,nf,N))\nend\nBase.getindex" =>
        "facetsindex(fi,np,ne,N),centerindex(ind,np,ne,nf,N))\nend\nBase.getindex", 1),
    # Q18e: tetrahedral vertex lists count triangle centers and call lagrangevertices4 wrongly.
    ("lagrange.jl", "function LagrangeTetrahedra{M}(id::Int,t::SimplexTopology{4},f,e,fi,ei) where M\n    np,ne,nc = totalnodes(t),totalnodes(ei),totalelements(t)*simplexnumber(2,M-2)\n    I = OneTo(np+(M-1)*ne+nc)\n    i = iscover(t) ? I : lagrangevertices4(t,ei,np,ne,Val(M))" =>
        "function LagrangeTetrahedra{M}(id::Int,t::SimplexTopology{4},f,e,fi,ei) where M\n    np,ne,nf = totalnodes(t),totalnodes(ei),totalnodes(fi)\n    I = OneTo(np+(M-1)*ne+facetsimplex(4,M)*nf+centersimplex(4,M)*totalelements(t))\n    i = iscover(t) ? I : lagrangevertices4(t,ei,fi,np,ne,nf,Val(M))", 1),
    # Q18f: LagrangeEdges keeps a Vector as its element→edge table.
    ("lagrange.jl", "edgesindices(m::LagrangeEdges) = Values.(subelements(edges(m))) # refine later" =>
        "edgesindices(m::LagrangeEdges) = (t=edges(m); ne=totalelements(t); et=SimplexTopology(0,Values.(OneTo(ne)),OneTo(ne),ne); isfull(t) ? et : et[subelements(t)])", 1),
    # Q19: interior(e) passes its arguments in the wrong order.
    ("element.jl", "interior(e) = interior(totalnodes(e),vertices(e))" => "interior(e) = interior(vertices(e),totalnodes(e))", 1),
    # Q20: degrees(t,B) multiplies by a vector of the wrong length; interp(t,B) is ambiguous.
    ("element.jl", "degrees(t::SimplexTopology,B::SparseMatrixCSC) = B*ones(Int,totalnodes(t))" =>
        "degrees(t::SimplexTopology,B::SparseMatrixCSC) = B*ones(Int,size(B,2))", 1),
    ("element.jl", "interp(t,B::SparseMatrixCSC=incidence(t)) = Diagonal(weights(t,B))*B\n" =>
        "interp(t,B::SparseMatrixCSC=incidence(t)) = Diagonal(weights(t,B))*B\ninterp(t::SimplexTopology,B::SparseMatrixCSC) = Diagonal(weights(t,B))*B\n", 1),
    # Q21: edgesindices sizes its lookup matrix by nodes instead of totalnodes.
    ("element.jl", "np,nt,ne = nodes(t),elements(t),totalelements(et)" => "np,nt,ne = totalnodes(t),elements(t),totalelements(et)", 1),
    # Q22: the fifth local facet of a 4-simplex has five vertices.
    ("element.jl", "Values(i[5],i[4],i[3],i[1]),Values(i[1],i[2],i[3],i[4],i[5]))" =>
        "Values(i[5],i[4],i[3],i[1]),Values(i[4],i[3],i[2],i[1]))", 1),
    # Q32: cross_sector(Q1, Q4) passes 8 of the 10 face slots (MethodError).
    ("quotient.jl", "n.r[6]+2),Values(M,N,R,P,Q)" =>
        "n.r[6]+2,iszero(n.r[7]) ? 0 : n.r[7]+2,iszero(n.r[8]) ? 0 : n.r[8]+2),Values(M,N,R,P,Q)", 1),
    # Q29: QuotientTopology(::ProductTopology) routes to Cartan's ProductSpace.
    ("quotient.jl", "QuotientTopology(n::ProductTopology) = OpenTopology(n.v)\nOpenTopology(n::ProductTopology) = OpenTopology(n.v)" =>
        "QuotientTopology(n::ProductTopology) = OpenTopology(Values(size(n)))\nOpenTopology(n::ProductTopology) = OpenTopology(Values(size(n)))", 1),
]

function patch(src::String, fix)
    (_, pr, cnt) = fix
    n = length(collect(eachmatch(pr.first isa Regex ? pr.first : Regex(escape_string_regex(pr.first)), src)))
    n == cnt || error("fix $(pr.first): expected $cnt matches, found $n")
    replace(src, pr)
end
escape_string_regex(s) = replace(s, r"([\\^$.|?*+()\[\]{}])" => s"\\\1")

function loadmt(wrapper::Symbol, fixes)
    dir = mktempdir()
    for f in readdir(MT_SRC)   # copy contents (package files are read-only)
        src = read(joinpath(MT_SRC, f), String)
        for fx in (IMPORT_FIX, fixes...)
            fx[1] == f && (src = patch(src, fx))
        end
        write(joinpath(dir, f), src)
    end
    Core.eval(Main, :(module $wrapper
        include($(joinpath(dir, "MeshTopology.jl")))
    end))
    Base.invokelatest(() -> getfield(getfield(Main, wrapper), :MeshTopology))
end

const U = loadmt(:Upstream, ())
const F = loadmt(:Fixed, FIXES)
