# Simplex meshes shared by gen_simplex.jl and gen_lagrange.jl (built once, seeded).

"Structured triangulation of an `nx × ny` node grid, two triangles per cell."
function gridtris(nx, ny)
    t = Values{3,Int}[]
    for j in 1:ny-1, i in 1:nx-1
        a = i + (j - 1) * nx
        b, c = a + 1, a + nx
        d = c + 1
        push!(t, Values(a, b, d), Values(a, d, c))
    end
    t
end

"Kuhn split of an `nx × ny × nz` cell block into 6 tetrahedra per cube."
function kuhntets(nx, ny, nz)
    id(i, j, k) = i + (j - 1) * (nx + 1) + (k - 1) * (nx + 1) * (ny + 1)
    t = Values{4,Int}[]
    for k in 1:nz, j in 1:ny, i in 1:nx
        for σ in ((1, 2, 3), (1, 3, 2), (2, 1, 3), (2, 3, 1), (3, 1, 2), (3, 2, 1))
            p = [i, j, k]
            vs = [id(p...)]
            for a in σ
                p[a] += 1
                push!(vs, id(p...))
            end
            push!(t, Values(vs...))
        end
    end
    t
end

"Random vertex relabelling, per-element rotation/reflection, and optional element dropping."
function relabel(t::Vector{Values{N,Int}}, drop = 0.0) where N
    n = maximum(maximum.(t))
    perm = randperm(n)
    out = Values{N,Int}[]
    for e in t
        rand() < drop && continue
        v = [perm[x] for x in e]
        v = circshift(v, rand(0:N-1))
        rand(Bool) && reverse!(v)
        push!(out, Values(v...))
    end
    out
end

meshes = [
    ("tri2", Values{3,Int}[Values(1, 2, 3), Values(2, 4, 3)]),
    ("tri8", gridtris(3, 3)),
    ("grid4x3", gridtris(4, 3)),
    ("noncontig", Values{3,Int}[Values(2, 5, 7), Values(5, 9, 7), Values(7, 9, 12)]),
    ("degenerate", Values{3,Int}[Values(3, 3, 1), Values(1, 2, 3)]),
    ("rand5x4", relabel(gridtris(5, 4))),
    ("rand6x5drop", relabel(gridtris(6, 5), 0.15)),
    ("rand4x4drop", relabel(gridtris(4, 4), 0.2)),
    ("tet2", Values{4,Int}[Values(1, 2, 3, 4), Values(2, 3, 4, 5)]),
    ("tet5cube", Values{4,Int}[Values(1, 2, 3, 5), Values(4, 2, 3, 8), Values(6, 2, 5, 8), Values(7, 3, 5, 8), Values(2, 3, 5, 8)]),
    ("kuhn2x1x1", kuhntets(2, 1, 1)),
    ("randkuhn2x2x1", relabel(kuhntets(2, 2, 1))),
    ("randkuhn2x2x2drop", relabel(kuhntets(2, 2, 2), 0.2)),
    ("edge3", Values{2,Int}[Values(1, 2), Values(2, 3), Values(3, 4)]),
    ("edgecycle", Values{2,Int}[Values(2, 1), Values(2, 3), Values(4, 3), Values(4, 1), Values(1, 3)]),
    ("pent4", Values{5,Int}[Values(1, 2, 3, 4, 5), Values(2, 3, 4, 5, 6), Values(6, 1, 3, 2, 7)]),
]

kind(v) = v isa Base.OneTo ? "OneTo" : "Vector"
"Everything a SimplexTopology stores, through its accessors."
function infoj(M, t)
    Dict("elements" => J(collect(t)), "vertices" => J(collect(M.vertices(t))), "vkind" => kind(M.vertices(t)),
         "fullvertices" => J(collect(M.fullvertices(t))), "verticesinv" => J(collect(M.verticesinv(t))),
         "subelements" => J(collect(M.subelements(t))), "fkind" => kind(M.subelements(t)),
         "totalnodes" => M.totalnodes(t), "totalelements" => M.totalelements(t), "nodes" => M.nodes(t),
         "elementcount" => M.elements(t), "istotal" => M.istotal(t), "isfull" => M.isfull(t),
         "iscover" => M.iscover(t), "summary" => summary(t))
end
"The same for a DiscontinuousTopology."
function dinfoj(M, d)
    Dict("elements" => J(collect(d)), "vertices" => J(collect(M.vertices(d))), "vkind" => kind(M.vertices(d)),
         "fullvertices" => J(collect(M.fullvertices(d))), "subelements" => J(collect(M.subelements(d))),
         "totalnodes" => M.totalnodes(d), "totalelements" => M.totalelements(d), "nodes" => M.nodes(d),
         "elementcount" => M.elements(d), "istotal" => M.istotal(d), "isfull" => M.isfull(d),
         "iscover" => M.iscover(d), "isdisconnected" => M.isdisconnected(d), "summary" => summary(d))
end
