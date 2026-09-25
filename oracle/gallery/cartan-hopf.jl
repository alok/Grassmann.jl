# Cartan.jl docs/src/fiber.md:765-775 ("Hopf fibration", C16 of plot-inventory.md):
#   function stereohopf(theta,phi,psi)
#       a = cos(theta)*exp((im/2)*(psi-phi)); b = sin(theta)*exp((im/2)*(psi+phi))
#       Chain(imag(a),real(b),imag(b))/(1-real(a))
#   end
#   stereohopf(x) = stereohopf(x[1],x[2],x[3])
#   hs = stereohopf.(HopfParameter()); alteration!(hs,wireframe,wireframe!)
# `alteration!` draws the seven leaves `leaf(hs,i,1)` (60×61 tori) as wireframes on one axis,
# each in the next palette colour. HopfParameter needs the B1 shim of cartan_common.jl; an Axis3
# replaces the LScene so the Lean render is comparable.
include("cartan_common.jl")
function stereohopf(theta,phi,psi)
    a = cos(theta)*exp((im/2)*(psi-phi)); b = sin(theta)*exp((im/2)*(psi+phi))
    Chain(imag(a),real(b),imag(b))/(1-real(a))
end
stereohopf(x) = stereohopf(x[1],x[2],x[3])
hs = stereohopf.(HopfParameter())
# `wireframe` with an Axis3 and the figure size, so the first leaf opens the comparable axis
wf(x; kw...) = wireframe(x; axis = (type = Axis3,), figure = (size = (600, 500),), kw...)
fig, ax, _ = alteration!(hs,wf,wireframe!)
cs = coords(hs)
out = Dict{String,Any}("size" => collect(size(hs)), "nplots" => length(ax.scene.plots),
    "nseg" => [length(p.plots[1][1][]) for p in ax.scene.plots])
for i in 1:3
    out["x$i"] = summary_of([c[i] for c in cs], 97)
end
dumpdata("cartan-hopf", out)
savefig("cartan-hopf", fig)
