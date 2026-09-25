# Cartan.jl docs/src/plot.md:119-125 (Makie's contour3d example with explicit levels):
#   f = Figure(); Axis3(f[1, 1], aspect=(0.5,0.5,1), perspectiveness=0.75)
#   contour3d!(-xyz, levels=-(.025:0.05:.475), linewidth=2, color=:blue2)
#   contour3d!(+xyz, levels=  .025:0.05:.475,  linewidth=2, color=:red2)
include("cartan_common.jl")
xs = ys = LinRange(-0.5, 0.5, 100)
zs = [sqrt(x^2+y^2) for x in xs, y in ys]
xyz = TensorField(OpenParameter(xs,ys),zs)
f = Figure()
Axis3(f[1, 1], aspect=(0.5,0.5,1), perspectiveness=0.75)
p1 = contour3d!(-xyz, levels=-(.025:0.05:.475), linewidth=2, color=:blue2)
p2 = contour3d!(+xyz, levels=  .025:0.05:.475,  linewidth=2, color=:red2)
lines_of(p) = first(c for c in p.plots if c isa Lines)[1][]
dumpdata("cartan-plot-contour3d-levels", Dict("contours" => [lines_moments(lines_of(p)) for p in (p1, p2)]))
savefig("cartan-plot-contour3d-levels", f)
