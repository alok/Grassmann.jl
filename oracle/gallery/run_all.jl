# Run every gallery oracle script (or those named on the command line, by prefix):
#   julia --startup-file=no --project=oracle oracle/gallery/run_all.jl [prefix …]
# Each script runs in a fresh module, so their globals do not collide.
const HERE = @__DIR__
const SKIP = ("common.jl", "fatou_common.jl", "grassmann_common.jl", "run_all.jl", "colormaps.jl")
scripts = sort(filter(f -> endswith(f, ".jl") && !(f in SKIP), readdir(HERE)))
isempty(ARGS) || (scripts = filter(f -> any(p -> startswith(f, p), ARGS), scripts))
for f in scripts
    m = Module(Symbol(f))
    Core.eval(m, :(include(p) = Base.include($m, p)))
    t = @elapsed Base.include(m, joinpath(HERE, f))
    println(f, ": ", round(t, digits = 1), " s")
end
