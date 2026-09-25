# Shared helpers of the gallery oracle scripts (oracle/gallery/<name>.jl).
#
# Every script renders the Julia/CairoMakie original of one gallery figure to
# docs/gallery/julia/<name>.png (px_per_unit = 1, the figure size of the Lean render) and
# dumps the plotted data to oracle/gallery/data/<name>.json for `lake exe gallery` to compare.
# Run one with
#   julia --startup-file=no --project=oracle oracle/gallery/<name>.jl
# or all of them with oracle/gallery/run_all.jl.
using CairoMakie, JSON

const GALLERY_ROOT = normpath(joinpath(@__DIR__, "..", ".."))
const JULIA_PNG = joinpath(GALLERY_ROOT, "docs", "gallery", "julia")
const JULIA_DATA = joinpath(@__DIR__, "data")
mkpath(JULIA_PNG); mkpath(JULIA_DATA)

"Save `fig` as docs/gallery/julia/<name>.png at one pixel per unit (the Lean render's size)."
savefig(name, fig) = (save(joinpath(JULIA_PNG, name * ".png"), fig; px_per_unit = 1); println("wrote ", name, ".png"))

"JSON-safe float: non-finite values as Julia's spelling."
jf(x::Real) = isfinite(x) ? Float64(x) : string(Float64(x))
jf(v::AbstractArray) = map(jf, v)

"Write oracle/gallery/data/<name>.json."
dumpdata(name, d) = open(io -> JSON.print(io, d), joinpath(JULIA_DATA, name * ".json"), "w")

"FNV-1a (64-bit) over little-endian UInt16 values in row-major order, as `0x…`."
function fnv1a16(M::AbstractMatrix)
    h = 0xcbf29ce484222325
    for r in 1:size(M, 1), c in 1:size(M, 2)
        v = UInt16(M[r, c])
        h = (h ⊻ UInt64(v & 0xff)) * 0x100000001b3
        h = (h ⊻ UInt64(v >> 8)) * 0x100000001b3
    end
    "0x" * string(h, base = 16, pad = 16)
end

"Every `k`-th element (from the first)."
every(v, k) = v[1:k:end]
