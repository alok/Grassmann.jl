# Cartan's methods for simplex meshes (ext/MakieExt.jl:608-619, 799-874): a triangulated square
# (5×5 vertices, 32 triangles, MATLAB P/E/T format through `initmeshdata`), coloured by the
# nodal values of x² - y² (`mesh(t::ScalarMap)`), with `wireframe!` (the mesh edges),
# `scatter!` (the vertices) and `text!` (the vertex ids).
include("cartan_common.jl")
# MeshTopology 0.1.0's `edges` of a simplex bundle names `Grassmann` without importing it (an
# UndefVarError from `wireframe(::SimplexBundle)`); make the name visible there.
isdefined(MT, :Grassmann) || Core.eval(MT, :(const Grassmann = $Grassmann))
xs = range(-1, 1, length = 5)
P = reduce(hcat, [[x, y] for y in xs for x in xs])            # 2×25, column-major grid order
T = Int[]
for j in 0:3, i in 0:3
    a = 1 + i + 5j
    append!(T, [a, a + 1, a + 6]); append!(T, [a, a + 6, a + 5])
end
T = reshape(T, 3, :)
E = reshape(Int[1, 2], 2, 1)
pt, pe = Cartan.initmeshdata(P, E, T, Val(2))
f = TensorField(pt, [p[2]^2 - p[3]^2 for p in points(pt)])
fig, ax, pl = mesh(f)
wf = wireframe!(pt, color = :black)
sc = scatter!(pt, color = :white, strokecolor = :black, strokewidth = 1)
tx = text!(pt, fontsize = 10)
dumpdata("cartan-simplex-mesh", Dict("vertices" => pts_summary(Makie.GeometryBasics.coordinates(pl[1][])),
    "faces" => length(Makie.GeometryBasics.faces(pl[1][])), "color" => color_summary(pl.color[]),
    "wireframe" => pts_summary(wf[1][]), "scatter" => pts_summary(sc[1][]), "text" => tx.text[]))
savefig("cartan-simplex-mesh", fig)
