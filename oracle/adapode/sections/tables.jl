# tables.json: CB, CBA (stage rows, b, b - c), CAB, CAM, Gauss, the stage times sum(aₗ), TimeStep(h).
rowsx(t) = [hxs(collect(r)) for r in t]
cvec(t, nrows) = [hx(sum(t[k])) for k in 1:nrows]
function tablesout()
    Dict("meta" => meta,
        "CB" => [Dict("rows" => rowsx(t), "c" => cvec(t, length(t) - 1)) for t in Adapode.CB],
        "CBA" => [Dict("rows" => rowsx(t), "c" => cvec(t, length(t) - 2)) for t in Adapode.CBA],
        "CAB" => rowsx(Adapode.CAB), "CAM" => rowsx(Adapode.CAM),
        "Gauss" => [Dict("w" => hxs(collect(g[1])), "pts" => [hxs(collect(p)) for p in g[2]]) for g in Adapode.Gauss],
        "TimeStep" => [(ts = Adapode.TimeStep(h); Dict("h" => hx(h), "fields" => hxs([ts.h, ts.hmin, ts.hmax, ts.emin, ts.emax, ts.e])))
                       for h in (2.0^-7, 2.0^-11, 2.0^-15, 1e-5, 0.1, 3e-3)])
end
save("tables", tablesout())
