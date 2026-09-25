# Minimal dependency-free JSON writer shared by the units oracle generators.
# Floats are written with Julia `repr` when finite (round-trip exact) and as strings otherwise.
jesc(s::AbstractString) = replace(s, "\\" => "\\\\", "\"" => "\\\"", "\n" => "\\n", "\t" => "\\t", "\r" => "\\r")
function jw(io, x)
    if x === nothing
        print(io, "null")
    elseif x isa Bool
        print(io, x ? "true" : "false")
    elseif x isa Integer
        print(io, x)
    elseif x isa AbstractFloat
        isfinite(x) ? print(io, repr(Float64(x))) : print(io, "\"", string(x), "\"")
    elseif x isa AbstractString || x isa Symbol || x isa Char
        print(io, "\"", jesc(string(x)), "\"")
    elseif x isa AbstractDict
        print(io, "{")
        first = true
        for k in sort!(collect(keys(x)); by = string)
            first || print(io, ",")
            first = false
            print(io, "\"", jesc(string(k)), "\":")
            jw(io, x[k])
        end
        print(io, "}")
    elseif x isa Union{AbstractVector,Tuple}
        print(io, "[")
        for (i, v) in enumerate(x)
            i > 1 && print(io, ",")
            jw(io, v)
        end
        print(io, "]")
    else
        print(io, "\"", jesc(repr(x)), "\"")
    end
end
writejson(path, x) = (open(io -> (jw(io, x); println(io)), path, "w"); nothing)
