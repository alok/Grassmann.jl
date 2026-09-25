# Gallery: the chakravala figures in Lean

Every figure of the Julia ecosystem that the Lean port can compute today, rendered with [LeanPlot](https://github.com/alok/LeanPlot) (left) next to the Julia/CairoMakie original (right, same data, same figure size). Regenerate with

```
cd gallery && lake exe gallery --docs            # Lean renders, data checks, this page
julia --startup-file=no --project=oracle oracle/gallery/run_all.jl   # Julia renders and data dumps
```

The data column compares the numbers behind each plot with the Julia dump (`oracle/gallery/data/<name>.json`): iteration counts of the fractals, curve samples, streamlines, graph edges and error curves. Images are compared by eye (DESIGN.md §0: plot data numerically, images visually).

## Fatou

| figure | Lean (LeanPlot) | Julia (CairoMakie) | data agreement |
|---|---|---|---|
| **fatou-orbit**<br>Cobweb orbit of x ↦ x² − 0.67<br><sub>`juliafill(:(z^2-0.67),∂=[-1.25,1.5],x0=1.25,orbit=17,depth=3,n=147) \|> orbit` (Fatou.jl `README.md:58-64`)</sub> | ![fatou-orbit (Lean)](lean/fatou-orbit.png) | ![fatou-orbit (Julia)](julia/fatou-orbit.png) | ✅ 8/8 checks<br>orbit x₀…x₁₇ (N2): max rel \|Δ\| = 0 over 18 values (tol 0)<br>cobweb x: max rel \|Δ\| = 0 over 51 values (tol 0)<br>cobweb y: max rel \|Δ\| = 0 over 51 values (tol 0)<br>ylim: max rel \|Δ\| = 0 over 2 values (tol 0)<br>ϕ^0(x) samples: max rel \|Δ\| = 0 over 147 values (tol 0)<br>ϕ^1(x) samples: max rel \|Δ\| = 0 over 147 values (tol 0)<br>ϕ^2(x) samples: max rel \|Δ\| = 0 over 147 values (tol 0)<br>ϕ^3(x) samples: max rel \|Δ\| = 0 over 147 values (tol 0) |
| **fatou-filled-julia**<br>Filled Julia set of z² − 0.06 + 0.67i (iteration counts, gnuplot)<br><sub>`plot(fatou(juliafill(:(z^2+$c),∂=[-1.5,1.5,-1,1],N=80,n=1501,cmap="gnuplot",iter=true)), bare=true)` (`README.md:66-74`)</sub> | ![fatou-filled-julia (Lean)](lean/fatou-filled-julia.png) | ![fatou-filled-julia (Julia)](julia/fatou-filled-julia.png) | ✅ 5/5 checks<br>raster size (rows × cols): equal (1001×1501)<br>iteration histogram: equal (81 bins, 1502501 pixels)<br>FNV-1a of the iteration counts: equal (0xd7605d2089529229)<br>mix NaN count: equal (0)<br>Σ mix: \|Δ\| / Σ\|mix\| = 1.49e-14 |
| **fatou-mandelbrot**<br>Mandelbrot set, limit colouring exp(−\|z₂₀\|) (gist_earth)<br><sub>`mandelbrot(:(z^2+c),n=800,N=20,∂=[-1.91,0.51,-1.21,1.21],cmap="gist_earth") \|> fatou \|> plot` (`README.md:76-82`)</sub> | ![fatou-mandelbrot (Lean)](lean/fatou-mandelbrot.png) | ![fatou-mandelbrot (Julia)](julia/fatou-mandelbrot.png) | ✅ 5/5 checks<br>raster size (rows × cols): equal (800×800)<br>iteration histogram: equal (21 bins, 640000 pixels)<br>FNV-1a of the iteration counts: equal (0x403251fa209bfc85)<br>mix NaN count: equal (0)<br>Σ mix: \|Δ\| / Σ\|mix\| = 8.29e-15 |
| **fatou-newton**<br>Newton fractal of z³ − 1 (iteration counts, jet)<br><sub>`newton(:(z^3-1),n=800,ϵ=0.1,N=25,iter=true,cmap="jet") \|> fatou \|> plot` (`README.md:96-104`)</sub> | ![fatou-newton (Lean)](lean/fatou-newton.png) | ![fatou-newton (Julia)](julia/fatou-newton.png) | ✅ 5/5 checks<br>raster size (rows × cols): equal (800×800)<br>iteration histogram: equal (26 bins, 640000 pixels)<br>FNV-1a of the iteration counts: equal (0x8610e251146353c5)<br>mix NaN count: equal (0)<br>Σ mix: \|Δ\| / Σ\|mix\| = 7.70e-16 |
| **fatou-generalized-newton**<br>Generalized Newton fractal of sin z − 1, m = 1 − i (cubehelix)<br><sub>`newton(:(sin(z)-1),m=1-1im,∂=[-2π/3,-π/3,-π/6,π/6],n=500,N=33,iter=true,ϵ=0.05,cmap="cubehelix") \|> fatou \|> plot` (`README.md:106-116`)</sub> | ![fatou-generalized-newton (Lean)](lean/fatou-generalized-newton.png) | ![fatou-generalized-newton (Julia)](julia/fatou-generalized-newton.png) | ✅ 4/4 checks<br>raster size (rows × cols): equal (500×500)<br>iteration histogram (libm tier): total variation 0 of 500000 (tol 0.1%)<br>mix NaN count: equal (6)<br>Σ mix: \|Δ\| / Σ\|mix\| = 2.23e-14 |

## Pending (need Cartan, Adapode or other unported packages)

From the ranked inventory in `docs/port-notes/plot-inventory.md` §6-§7.

| id | figure | waits for |
|---|---|---|
| C1 | plane curve with unit frames, arclength/speed/curvature (Cartan `fiber.md:442-451`) | Cartan (TensorField, frames, `scaledarrows`) |
| C2 | plane curves from curvature, `planecurve` (`fiber.md:452-457`) | Cartan (`planecurve`, cumulative integrals) |
| C3 | Lorenz vector-field 3D streamplot (`fiber.md:460-468`) | Cartan (TensorField over ProductSpace) |
| C4 / A1 | Lorenz, Rössler, dynamo attractors (`fiber.md:470-474`, Adapode `examples/chaos.jl`) | Adapode (`odesolve`, RK4/ABM4 on Chains) |
| C5 | Riemann-sphere curves as TensorFields (`fiber.md:477-493`) | Cartan (same curves as `grassmann-torus` etc. over `TensorField`) |
| C6 | bivector streamplots over 31×31 grid fields (`fiber.md:495-509`) | Cartan (grid interpolation of `tensorfield`) |
| C7 | conformal 3D streamplots over grids (`fiber.md:511-523`) | Cartan |
| C8 | Lie bracket streamplots on the torus (`fiber.md:552-563`) | Cartan (`gradient`, `Lie`) |
| C9 | circle and sphere wireframe (`fiber.md:602-613`) | Cartan (`SphereParameter`, `surfacearea`) |
| C10 | link curves and linkmap meshes (`fiber.md:649-656`) | Cartan (`linkmap`, `linknumber`) |
| C11 / C12 | torus and wiggle coloured by curvature (`fiber.md:669-695`) | Cartan (shape operator, `meancurvature`, `gaussintrinsic`) |
| C13 / C14 / C15 | torus, Klein-bottle and half-plane geodesics (`fiber.md:709-763`) | Cartan + Adapode (`geodesic`, `geosolve`) |
| C16 | Hopf fibration wireframes (`fiber.md:765-775`) | Cartan (`HopfParameter`, `alteration!`) |
| C17 | tangent-space streamplots on sphere and torus (`fiber.md:778-797`) | Cartan (streamplot transform hook over TensorFields) |
| C18 | da Rios vortex filament (`fiber.md:800-811`) | Adapode (`odesolve` on curve fields; upstream bug P9) |
| C19 | Bishop frame (`fiber.md:813-820`) | Cartan (`bishopunitframe`) |
| C20 / A11 | disk eigenmodes (`fiber.md:823-834`) | Adapode (FEM assembly, generalized eigensolver; MATLAB mesh upstream) |
| C21 / A12 | heat flow around a NACA airfoil (`fiber.md:874-895`) | Adapode + FlowGeometry + a 2D mesher |
| C22 / A13 | Poisson on a sphere-in-cube tetrahedral mesh (`fiber.md:898-910`) | Adapode + TetGen-like mesher |
| C23 | Stokes theorem on a paraboloid (`fiber.md:932-962`) | Cartan (`graph`, `unitnormal`, `curl`) |
| M-* | the 32 Makie-gallery ports of Cartan `docs/src/plot.md` | Cartan (TensorField plot recipes) |
| A2–A9 | leapfrog, wave, heat and rest-wave PDE surfaces and isosurfaces (Adapode `README.md:151-231`) | Adapode (spectral solvers, FFT) |
| A10 | L2 projector (Adapode `README.md:235-240`) | Adapode (1D FEM) |
| W1–W4 | NACA airfoils, double arc, wing surface, Rakich C-mesh (FlowGeometry) | FlowGeometry port |
| D1 | Tamari associahedron coloured by grove sums (Dendriform README) | external gist, not in the repositories |
| G10 | `vandermonde` terminal plot (`ext/UnicodePlotsExt.jl`) | UnicodePlots-style terminal backend (API only, no documented call) |

Videos (21 YouTube talks) and LaTeX formula images (Fatou basins, Dendriform) are out of scope (`plot-inventory.md` §1).
