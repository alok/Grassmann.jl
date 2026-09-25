"""Compare Julia oracle dump (dump*.jsonl) against ref.py. Usage: python3 compare.py dump_all.jsonl"""
from __future__ import annotations
import json
import sys
from collections import Counter, defaultdict
import ref as R


def space_from(info: dict) -> R.Space | None:
    nm = info["space"]
    M = info["opts"] % 16
    inf = M in (1, 3, 5, 7, 9, 11)
    orig = M in (2, 3, 6, 7, 10, 11)
    dyad = -1 if M in range(8, 12) else (1 if M in (4, 5, 6, 7) else 0)
    if nm.startswith("MT"):
        return None
    if nm == "I4":
        kind = "int"
    elif info["diag"] is not None:
        kind = "diag"
    else:
        kind = "sig"
    return R.Space(N=info["N"], kind=kind, S=max(info["metricbits"], 0), diag=info["diag"],
                   inf=inf, orig=orig, dyad=dyad, D=info["diffvars"], mu=info["diffmode"])


def jterms(rec: dict):
    if "err" in rec:
        return "ERR"
    out = {}
    for k, c in rec["t"]:
        if isinstance(c, str):
            return "NESTED:" + rec["s"]
        if c != 0:
            out[int(k)] = out.get(int(k), 0) + c
    return out


def clean(d: dict, scale: float = 1.0):
    return {k: v * scale for k, v in d.items() if v != 0}


def eq(a, b) -> bool:
    if isinstance(a, str) or isinstance(b, str):
        return False
    if set(a) != set(b):
        return False
    return all(abs(a[k] - b[k]) < 1e-9 for k in a)


def main(path: str) -> None:
    spaces: dict[str, R.Space | None] = {}
    stats: Counter = Counter()
    fails = defaultdict(list)
    for line in open(path):
        rec = json.loads(line)
        if "info" in rec:
            spaces[rec["info"]["space"]] = space_from(rec["info"])
            continue
        nm = rec["space"]
        V = spaces[nm]
        if V is None:
            continue
        if "u" in rec:
            u = rec["u"]
            B = u["a"]
            checks = {
                "rev": R.reverse(V, B), "inv": R.involute(V, B), "cli": R.clifford(V, B),
                "arev": R.antireverse(V, B), "conj": R.reverse(V, B),
                "cr": R.complementright(V, B), "cl": R.complementleft(V, B),
                "sq": R.mul(V, B, B)[0] if R.mul(V, B, B)[1] == 0 else None,
            }
            if V.dyad >= 0:
                checks["hr"] = R.complementrighthodge(V, B)
                checks["hl"] = R.complementlefthodge(V, B)
                # Chain kernels: no null scaling; hodge uses P=0 complement for diag spaces
                nn = R.Space(**{**V.__dict__, "inf": V.inf and not V.conformal, "orig": V.orig and not V.conformal})
                checks["crc"] = {k: 2.0 * v for k, v in R.complementright(nn, B).items()} if not V.conformal else None
                checks["clc"] = {k: 2.0 * v for k, v in R.complementleft(nn, B).items()} if not V.conformal else None
                if V.conformal:
                    checks["crc"] = {k: 2.0 * v for k, v in R.complementright(R.Space(**{**V.__dict__, "inf": False, "orig": False}), B).items()}
                    checks["clc"] = {k: 2.0 * v for k, v in R.complementleft(R.Space(**{**V.__dict__, "inf": False, "orig": False}), B).items()}
                if V.isdiag:
                    checks["hrc"] = {k: 2.0 * v for k, v in R.complementrighthodge(V, B).items()}
                    checks["hlc"] = {k: 2.0 * v for k, v in R.complementlefthodge(V, B).items()}
            for op, want in checks.items():
                if want is None or op not in u:
                    continue
                got = jterms(u[op])
                ok = eq(got, clean(want))
                stats[(nm, op, ok)] += 1
                if not ok:
                    fails[(nm, op)].append((B, u[op].get("s", u[op].get("err")), want))
            continue
        if rec.get("skipZ"):
            continue
        a, b = rec["a"], rec["b"]
        for op, fn in (("mul", R.mul), ("wedge", R.wedge), ("vee", R.vee), ("dot", R.contraction), ("cross", R.cross)):
            if op == "cross" and V.dyad < 0:
                continue
            try:
                want, Z = fn(V, a, b)
            except Exception as e:  # noqa: BLE001
                want, Z = f"PYERR {e}", 0
            got = jterms(rec[op])
            if Z != 0:
                stats[(nm, op, "Znonzero")] += 1
                continue
            ok = (not isinstance(want, str)) and eq(got, clean(want))
            stats[(nm, op, ok)] += 1
            if not ok:
                fails[(nm, op)].append((a, b, rec[op].get("s", rec[op].get("err")), want))
    by = defaultdict(lambda: [0, 0])
    for (nm, op, ok), n in stats.items():
        if ok is True:
            by[(nm, op)][0] += n
        elif ok is False:
            by[(nm, op)][1] += n
    for (nm, op), (p, f) in sorted(by.items()):
        print(f"{nm:10s} {op:6s} pass={p:5d} fail={f:5d}")
    print("---- first failures ----")
    for k, v in sorted(fails.items()):
        print(k, len(v), v[:4])


if __name__ == "__main__":
    main(sys.argv[1])
