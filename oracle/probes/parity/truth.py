"""Independent ground-truth Clifford product for an arbitrary symmetric bilinear form
(Chevalley recursion, outer-product basis e_A = e_a1 ^ e_a2 ^ ... ^ e_ak with a1<a2<...).
Used to test mathematical correctness of Grassmann.jl paths (conformal, MetricTensor).
Usage: python3 truth.py dump_all.jsonl"""
from __future__ import annotations
import json
import sys
from collections import defaultdict

MV = dict  # bits -> coef


def bits(x: int) -> list[int]:
    return [k for k in range(x.bit_length()) if (x >> k) & 1]


def add(acc: MV, k: int, c: float) -> None:
    acc[k] = acc.get(k, 0.0) + c


def lcontr_vec(Bf, i: int, X: MV) -> MV:
    out: MV = {}
    for K, c in X.items():
        for j, kj in enumerate(bits(K)):
            if Bf[i][kj] != 0:
                add(out, K & ~(1 << kj), c * (-1) ** j * Bf[i][kj])
    return out


def wedge_vec(i: int, X: MV) -> MV:
    out: MV = {}
    for K, c in X.items():
        if (K >> i) & 1:
            continue
        s = bin(K & ((1 << i) - 1)).count("1")
        add(out, K | (1 << i), c * (-1) ** s)
    return out


def vec_mul(Bf, i: int, X: MV) -> MV:
    out = lcontr_vec(Bf, i, X)
    for k, c in wedge_vec(i, X).items():
        add(out, k, c)
    return out


def blade_mul(Bf, A: int, X: MV) -> MV:
    if A == 0:
        return dict(X)
    a1 = bits(A)[0]
    Ap = A & ~(1 << a1)
    out = vec_mul(Bf, a1, blade_mul(Bf, Ap, X))
    for K, c in lcontr_vec(Bf, a1, {Ap: 1.0}).items():
        for k, v in blade_mul(Bf, K, X).items():
            add(out, k, -c * v)
    return out


def geom(Bf, a: int, b: int) -> MV:
    return {k: v for k, v in blade_mul(Bf, a, {b: 1.0}).items() if abs(v) > 1e-12}


def form_for(info: dict, true_sig: bool):
    N = info["N"]
    M = info["opts"] % 16
    conf = M in (3, 7, 11)
    Bf = [[0.0] * N for _ in range(N)]
    if info["space"].startswith("MT"):
        Bf = [[1, .5, 0], [.5, 1, .5], [0, .5, 1]]
        return Bf
    if info["diag"] is not None:
        for i, x in enumerate(info["diag"]):
            Bf[i][i] = float(x)
        return Bf
    S = max(info["metricbits"], 0)
    for i in range(N):
        Bf[i][i] = -1.0 if (S >> i) & 1 else 1.0
    if conf:
        Bf[0][0] = Bf[1][1] = 0.0
        Bf[0][1] = Bf[1][0] = -1.0
        if not true_sig:
            for i in range(2, N):
                Bf[i][i] = 1.0
    return Bf


def main(path: str) -> None:
    infos = {}
    res = defaultdict(lambda: [0, 0, []])
    for line in open(path):
        r = json.loads(line)
        if "info" in r:
            infos[r["info"]["space"]] = r["info"]
            continue
        if "u" in r or r.get("skipZ"):
            continue
        info = infos[r["space"]]
        if info["diffvars"] or info["dyadmode"]:
            continue
        rec = r["mul"]
        if "err" in rec:
            continue
        got = {int(k): c for k, c in rec["t"] if not isinstance(c, str) and c != 0}
        for mode in (True, False):
            want = geom(form_for(info, mode), r["a"], r["b"])
            ok = set(got) == set(want) and all(abs(got[k] - want[k]) < 1e-9 for k in got)
            key = (r["space"], "truesig" if mode else "allplus")
            res[key][0 if ok else 1] += 1
            if not ok and len(res[key][2]) < 4:
                res[key][2].append((info["names"][info["basis"].index(r["a"])], info["names"][info["basis"].index(r["b"])], rec["s"], want))
    for k, (p, f, ex) in sorted(res.items()):
        print(k, "pass", p, "fail", f, ex[:3])


if __name__ == "__main__":
    main(sys.argv[1])
