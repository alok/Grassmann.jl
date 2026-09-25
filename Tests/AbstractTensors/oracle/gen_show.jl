# Oracle for the display of `Values` (Tests/AbstractTensors/ValuesShow.lean): `repr` (Julia's
# compact array form with the eltype prefix) and the `text/plain` display (header and aligned
# elements) of StaticVectors.Values (Julia's AbstractVector printing).
#
#   julia --startup-file=no --project=oracle Tests/AbstractTensors/oracle/gen_show.jl Tests/AbstractTensors/oracle/values_show.json
using StaticVectors, JSON

cases = Any[
    ("f64", Values(0.5, 1 / 3, 1.0e10, 1.0e-5, -0.0, 2.0)),
    ("f64special", Values(NaN, Inf, -Inf)),
    ("f64align", Values(-1.5, 2.25, 100.0)),
    ("f64two", Values(1.5, -2.0)),
    ("int", Values(1, 2, 3)),
    ("intneg", Values(-10, 2, 300)),
    ("f32", Values(1.5f0, 2.0f0, 0.1f0)),
    ("bool", Values(true, false)),
    ("rat", Values(1 // 2, -3 // 4)),
    ("cint", Values(1 + 2im, 3 + 0im)),
    ("cf64", Values(1.0 + 2.0im, -0.0 - 1.5im)),
    ("u8", Values(UInt8(3), UInt8(4))),
    ("nested", Values(Values(1, 2), Values(3, 4))),
    ("empty_int", Values{0,Int64}()),
    ("empty_f64", Values{0,Float64}()),
    ("single", Values(42.0)),
]
out = [Dict("name" => n, "repr" => repr(v), "plain" => sprint(show, MIME"text/plain"(), v)) for (n, v) in cases]
open(ARGS[1], "w") do io
    JSON.print(io, Dict("cases" => out))
end
println("wrote $(length(out)) cases")
