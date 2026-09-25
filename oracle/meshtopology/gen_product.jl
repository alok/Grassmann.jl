# product.json: ProductTopology (MT:113-208).

showj(x) = sprint(show, x)
function prodcase(name, f)
    d = Dict{String,Any}("name" => name)
    d["axes"] = both(M -> ptj(f(M)))
    d["size"] = both(M -> collect(size(f(M))))
    d["collect"] = both(M -> G(f(M)))
    d["linear"] = both(M -> (m = f(M); [m[k] for k in 1:length(m)]))
    d["summary"] = both(M -> summary(f(M)))
    d["show"] = both(M -> showj(f(M)))
    N = length(size(f(F)))
    if N ≥ 1
        d["resize"] = both(M -> ptj(M.resize(f(M), 7)))
        d["resample"] = both(M -> ptj(M.resample(f(M), Tuple(size(f(M)) .+ 2))))
        d["exclude1"] = [both(M -> ptj(M.exclude(f(M), Val(k)))) for k in 1:N]
    end
    if N ≥ 3
        d["exclude2"] = [Dict("ex" => [a, b], "out" => both(M -> ptj(M.exclude(f(M), Val(a), Val(b)))))
                         for a in 1:N for b in a+1:N]
    end
    if N ≥ 4
        d["exclude3"] = [Dict("ex" => [a, b, c], "out" => both(M -> ptj(M.exclude(f(M), Val(a), Val(b), Val(c)))))
                         for a in 1:N for b in a+1:N for c in b+1:N]
    end
    d["quotient"] = both(M -> qtj(M.QuotientTopology(f(M))))
    return d
end

products = Any[
    prodcase("PT(3,4)", M -> M.ProductTopology(3, 4)),
    prodcase("PT(5)", M -> M.ProductTopology(5)),
    prodcase("PT(1:3,2:5)", M -> M.ProductTopology(1:3, 2:5)),
    prodcase("PT(5:-1:1,CR(5))", M -> M.ProductTopology(5:-1:1, M.CrossRange(5))),
    prodcase("PT(1:1:4)", M -> M.ProductTopology(1:1:4)),
    prodcase("PT(CR(6))", M -> M.ProductTopology(M.CrossRange(6))),
    prodcase("PT([3,1,2],[5,4])", M -> M.ProductTopology([3, 1, 2], [5, 4])),
    prodcase("PT(2,3,4)", M -> M.ProductTopology(2, 3, 4)),
    prodcase("PT(2,3,2,3)", M -> M.ProductTopology(2, 3, 2, 3)),
    prodcase("PT(2,2,3,2,2)", M -> M.ProductTopology(2, 2, 3, 2, 2)),
    prodcase("[1,1]:[3,4]", M -> Values(1, 1):Values(3, 4)),
    prodcase("[1,1]:[1,2]:[3,6]", M -> Values(1, 1):Values(1, 2):Values(3, 6)),
    prodcase("[2,4,1]:[3,5,2]", M -> Values(2, 4, 1):Values(3, 5, 2)),
    prodcase("PT(3,4)×PT(5)", M -> M.cross(M.ProductTopology(3, 4), M.ProductTopology(5))),
    prodcase("PT(3,4)×[7,8]", M -> M.cross(M.ProductTopology(3, 4), [7, 8])),
    prodcase("[7,8]×PT(3)", M -> M.cross([7, 8], M.ProductTopology(3))),
    prodcase("PT(3)×4", M -> M.cross(M.ProductTopology(3), 4)),
    prodcase("4×PT(2,3)", M -> M.cross(4, M.ProductTopology(2, 3))),
]
prod0 = Dict("summary" => both(M -> summary(M.ProductTopology())), "size" => both(M -> collect(size(M.ProductTopology()))))

writejson("product.json", Dict("products" => products, "empty" => prod0))
