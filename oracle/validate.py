# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Validate the element-oracle goldens against docs/port-notes/oracle-schema.md.

    uv run oracle/validate.py            # every suite
    uv run oracle/validate.py products   # some suites

This is an independent reader of the goldens, written from the schema document alone (it never
imports the Julia generator). It checks the file layout, the manifests and their totals, the
space descriptors (dense order), every element object (field presence per kind, coefficient
grammar per `T`, storage pattern of `dense`, `native` against `dense`), case references,
defect ids, and recomputes each shard's `stats`. The `floats` suite is checked for bit-exact
round trips of `show`. Exits 1 on the first file with errors (after reporting all of them).
"""

from __future__ import annotations

import json
import math
import re
import struct
import sys
from fractions import Fraction
from itertools import combinations
from pathlib import Path
from typing import Any

ORACLE = Path(__file__).resolve().parent
GOLDEN = ORACLE / "golden"
SUITES = ["construct", "arith", "products", "unary", "composite", "floats", "docs"]
MAX_BYTES = 4 * 1024 * 1024
SCHEMA = 1

ELEMENT_KINDS = {"Zero", "One", "Infinity", "Submanifold", "Single", "Chain", "Spinor", "CoSpinor",
                 "Multivector", "Couple", "PseudoCouple", "Phasor"}
SCALAR_KINDS = {"Number", "Bool"}
OTHER_KINDS = {"Space", "Other", "Error"}
GRADED = {"Zero", "One", "Infinity", "Submanifold", "Single", "Chain"}
WITH_BITS = {"One", "Submanifold", "Single", "Couple", "PseudoCouple"}

FLOAT_RE = re.compile(r"^-?(?:NaN|Inf|[0-9]+\.[0-9]+(?:e-?[0-9]+)?)$")
INT_RE = re.compile(r"^-?[0-9]+$")
RAT_RE = re.compile(r"^-?[0-9]+//[0-9]+$")
HEX_RE = re.compile(r"^[0-9a-f]{16}$")

Json = Any


class Errors:
    def __init__(self, where: str) -> None:
        self.where = where
        self.msgs: list[str] = []

    def add(self, msg: str) -> None:
        if len(self.msgs) < 50:
            self.msgs.append(msg)
        elif len(self.msgs) == 50:
            self.msgs.append("... (further errors suppressed)")

    def check(self, cond: bool, msg: str) -> bool:
        if not cond:
            self.add(msg)
        return cond


# ---------------------------------------------------------------------------------------------
# Scalars
# ---------------------------------------------------------------------------------------------

def parse_float(s: str) -> float:
    """Julia `repr(::Float64)` → float (Python's parser is correctly rounded)."""
    if not FLOAT_RE.match(s):
        raise ValueError(f"not a Julia Float64 literal: {s!r}")
    return float(s)


def parse_scalar(T: str, v: Json) -> Any:
    """Decode one coefficient per schema §Scalars. Raises on malformed input.

    Returns an exact value (int/Fraction/bool), a float, or a (re, im) tuple.
    """
    if T == "Int64":
        if not (isinstance(v, str) and INT_RE.match(v)):
            raise ValueError(f"bad Int64 {v!r}")
        x = int(v)
        if not -(2**63) <= x < 2**63:
            raise ValueError(f"Int64 out of range {v}")
        return x
    if T == "Bool":
        if v not in ("true", "false"):
            raise ValueError(f"bad Bool {v!r}")
        return v == "true"
    if T == "Rational{Int64}":
        if not (isinstance(v, str) and RAT_RE.match(v)):
            raise ValueError(f"bad Rational {v!r}")
        num, den = v.split("//")
        q = Fraction(int(num), int(den))
        if (q.numerator, q.denominator) != (int(num), int(den)):
            raise ValueError(f"Rational not reduced: {v}")
        return q
    if T == "Float64":
        if not isinstance(v, str):
            raise ValueError(f"bad Float64 {v!r}")
        return parse_float(v)
    if T.startswith("Complex{") and T.endswith("}"):
        inner = T[len("Complex{"):-1]
        if not (isinstance(v, list) and len(v) == 2):
            raise ValueError(f"bad {T} {v!r}")
        return (parse_scalar(inner, v[0]), parse_scalar(inner, v[1]))
    raise KeyError(T)


PARSEABLE = {"Int64", "Bool", "Rational{Int64}", "Float64"}


def parseable(T: str) -> bool:
    if T in PARSEABLE:
        return True
    return T.startswith("Complex{") and T[len("Complex{"):-1] in PARSEABLE


def is_zero(x: Any) -> bool:
    if isinstance(x, tuple):
        return all(is_zero(c) for c in x)
    if isinstance(x, float) and math.isnan(x):
        return False
    return x == 0


# ---------------------------------------------------------------------------------------------
# Dense order
# ---------------------------------------------------------------------------------------------

def dense_basis(n: int) -> list[int]:
    """Blade bitmasks in Multivector order: grade-major, lexicographic on sorted index tuples."""
    out = [0]
    for g in range(1, n + 1):
        for idx in combinations(range(n), g):
            out.append(sum(1 << i for i in idx))
    return out


_BASIS_CACHE: dict[int, tuple[list[int], dict[int, int]]] = {}


def basis_of(n: int) -> tuple[list[int], dict[int, int]]:
    if n not in _BASIS_CACHE:
        b = dense_basis(n)
        _BASIS_CACHE[n] = (b, {m: i for i, m in enumerate(b)})
    return _BASIS_CACHE[n]


def popcount(x: int) -> int:
    return bin(x).count("1")


# ---------------------------------------------------------------------------------------------
# Elements
# ---------------------------------------------------------------------------------------------

def check_element(e: Json, n: int | None, err: Errors, where: str, strict: bool = True) -> None:
    """Validate one element object ("E") of a space with `n` generators (None: unknown).

    With `strict = False` (outputs of defect-tagged cases, which may be Julia's malformed values)
    only the field grammar is checked, not the grade/bits/storage consistency.
    """
    if not err.check(isinstance(e, dict) and "kind" in e, f"{where}: not an element object"):
        return
    k = e["kind"]
    if k == "Error":
        err.check(isinstance(e.get("error"), str) and isinstance(e.get("msg"), str), f"{where}: Error without error/msg")
        return
    if k in SCALAR_KINDS:
        err.check("T" in e and "value" in e, f"{where}: {k} without T/value")
        if "T" in e and parseable(e["T"]):
            try:
                parse_scalar(e["T"], e["value"])
            except (ValueError, KeyError) as ex:
                err.add(f"{where}: {ex}")
        err.check("str" in e, f"{where}: {k} without str")
        return
    if k in ("Space", "Other"):
        err.check("str" in e and "type" in e, f"{where}: {k} without str/type")
        return
    if not err.check(k in ELEMENT_KINDS, f"{where}: unknown kind {k!r}"):
        return
    T = e.get("T")
    err.check(isinstance(T, str), f"{where}: element without T")
    err.check(("str" in e) != bool(e.get("str_error")), f"{where}: needs exactly one of str / str_error")
    if k in GRADED:
        err.check(isinstance(e.get("grade"), int), f"{where}: {k} without grade")
    if k in WITH_BITS:
        err.check(isinstance(e.get("bits"), int), f"{where}: {k} without bits")
        if strict and k in ("One", "Submanifold", "Single") and isinstance(e.get("bits"), int):
            err.check(popcount(e["bits"]) == e.get("grade"), f"{where}: grade != popcount(bits)")
    if k == "One":
        err.check(e.get("bits") == 0, f"{where}: One with bits != 0")
    if k == "Phasor":
        check_element(e.get("amp"), n, err, where + ".amp", strict)
        check_element(e.get("angle"), n, err, where + ".angle", strict)
        return
    if k == "Infinity":
        err.check("dense" not in e, f"{where}: Infinity with dense")
        return
    if "V" in e:
        # an element of another space (adjoint, docs): its n is not the shard's; take it from
        # the dense length, which must be a power of two
        d = e.get("dense")
        if isinstance(d, list):
            m = len(d).bit_length() - 1
            if not err.check(len(d) == 1 << m, f"{where}: dense length {len(d)} is not a power of 2"):
                return
            n = m
        else:
            n = None
    if n is None:
        return
    if "terms" in e:
        err.check(n > 10, f"{where}: terms for n = {n} <= 10")
        return
    if not err.check("dense" in e or n > 10, f"{where}: {k} without dense"):
        return
    d = e["dense"]
    if not err.check(isinstance(d, list) and len(d) == 1 << n, f"{where}: dense length != 2^{n}"):
        return
    if not (isinstance(T, str) and parseable(T)):
        return
    try:
        vals = [parse_scalar(T, c) for c in d]
    except (ValueError, KeyError) as ex:
        err.add(f"{where}: {ex}")
        return
    if not strict:
        return
    basis, index = basis_of(n)
    top = (1 << n) - 1
    allowed: set[int]
    if k == "Zero":
        allowed = set()
    elif k in ("One", "Submanifold"):
        allowed = {index[e["bits"]]}
        err.check(vals[index[e["bits"]]] in (1, True, (1, 0)), f"{where}: basis blade coefficient != 1")
    elif k == "Single":
        allowed = {index[e["bits"]]}
    elif k == "Chain":
        allowed = {i for i, m in enumerate(basis) if popcount(m) == e["grade"]}
    elif k == "Spinor":
        allowed = {i for i, m in enumerate(basis) if popcount(m) % 2 == 0}
    elif k == "CoSpinor":
        allowed = {i for i, m in enumerate(basis) if popcount(m) % 2 == 1}
    elif k == "Couple":
        allowed = {0, index[e["bits"]]}
    elif k == "PseudoCouple":
        allowed = {index[e["bits"]], index[top]}
    else:
        allowed = set(range(1 << n))
    for i, v in enumerate(vals):
        if i not in allowed and not is_zero(v):
            err.add(f"{where}: {k} has a nonzero coefficient on blade {basis[i]}")
            break
    if "native" in e:
        check_native(e, k, n, d, err, where)


def check_native(e: Json, k: str, n: int, d: list[Json], err: Errors, where: str) -> None:
    """`native` (the kind's storage order) must be a gather of `dense` (schema §Elements)."""
    basis, index = basis_of(n)
    nat = e["native"]
    top = (1 << n) - 1
    if k == "Single":
        idx = [index[e["bits"]]]
    elif k == "Chain":
        idx = [index[m] for m in basis if popcount(m) == e["grade"]]
    elif k == "Multivector":
        idx = list(range(1 << n))
    elif k == "Spinor":
        idx = [i for i, m in enumerate(basis) if popcount(m) % 2 == 0]
    elif k == "CoSpinor":
        idx = [i for i, m in enumerate(basis) if popcount(m) % 2 == 1]
    elif k == "Couple":
        idx = [0, index[e["bits"]]]
    elif k == "PseudoCouple":
        idx = [index[e["bits"]], index[top]]
    else:
        err.add(f"{where}: native on kind {k}")
        return
    if k in ("Couple", "PseudoCouple") and e["bits"] in (0, top):
        # degenerate B (B = 1 or B = I): both parts land on one blade, so dense holds their sum
        return
    err.check(nat == [d[i] for i in idx], f"{where}: native is not the storage gather of dense")


# ---------------------------------------------------------------------------------------------
# Shards
# ---------------------------------------------------------------------------------------------

SPACE_KEYS = ["name", "julia", "description", "show", "show_bundle", "n", "grade", "metric", "options",
              "hasinf", "hasorigin", "conformal", "isdiag", "dyadmode", "isdual", "diffvars", "diffmode",
              "Isq", "basis", "names"]

TOP_KEYS = {
    "construct": ["meta", "space", "cases", "stats"],
    "arith": ["meta", "space", "ops", "reference", "inputs", "cases", "stats"],
    "products": ["meta", "space", "ops", "reference", "inputs", "cases", "stats"],
    "unary": ["meta", "space", "ops", "reference", "inputs", "cases", "stats"],
    "composite": ["meta", "space", "ops", "tolerance", "inputs", "cases", "stats"],
    "floats": ["meta", "encoding", "fields", "cases", "stats"],
    "docs": ["meta", "sandbox", "cases", "stats"],
}


def check_space(sp: Json, err: Errors) -> int | None:
    if not err.check(list(sp.keys()) == SPACE_KEYS, f"space keys {list(sp.keys())}"):
        return None
    n = sp["n"]
    m = sp["metric"]
    err.check(m.get("kind") in ("signature", "diagonal", "euclidean"), f"metric kind {m.get('kind')}")
    if m["kind"] == "diagonal":
        err.check(len(m["diag"]) == n, "diagonal metric length != n")
    if m["kind"] == "signature":
        err.check(isinstance(m["neg"], int) and 0 <= m["neg"] < (1 << n), "signature neg out of range")
    err.check(sp["grade"] == n - sp["diffvars"], "grade != n - diffvars")
    if n <= 8:
        err.check(sp["basis"] == dense_basis(n), "basis is not the dense order")
        err.check(len(sp["names"]) == 1 << n, "names length != 2^n")
    else:
        err.check(sp["basis"] == [] and sp["names"] == [], "basis/names must be empty for n > 8")
    return n


def load_defects(err: Errors) -> dict[str, str]:
    p = GOLDEN / "defects.json"
    if not err.check(p.exists(), "golden/defects.json missing"):
        return {}
    d = json.loads(p.read_text())
    err.check(d["meta"]["schema"] == SCHEMA, "defects.json schema")
    pol: dict[str, str] = {}
    for e in d["defects"]:
        err.check(e["policy"] in ("ref", "skip", "replicate"), f"defect {e['id']}: policy {e['policy']}")
        err.check(e["id"] not in pol, f"duplicate defect id {e['id']}")
        pol[e["id"]] = e["policy"]
        for m in e["match"]:
            err.check(set(m) <= {"suite", "space", "op", "kinds", "when", "out", "msg", "block", "input", "file"},
                      f"defect {e['id']}: match keys {sorted(m)}")
    return pol


def check_shard(suite: str, shard: str, top: Json, defects: dict[str, str], err: Errors) -> dict[str, Any]:
    err.check(list(top.keys()) == TOP_KEYS[suite], f"top-level keys {list(top.keys())}")
    meta = top["meta"]
    err.check(meta["schema"] == SCHEMA and meta["suite"] == suite and meta["shard"] == shard, "meta mismatch")
    n: int | None = None
    if "space" in top:
        n = check_space(top["space"], err)
        err.check(top["space"]["name"] == shard, "space name != shard")
    inputs = top.get("inputs", [])
    for i, x in enumerate(inputs):
        err.check("label" in x and "src" in x, f"inputs[{i}] without label/src")
        check_element(x, n, err, f"inputs[{i}]")
    ops = top.get("ops", {})
    nerr = nmis = nunex = 0
    dcount: dict[str, int] = {}
    for ci, c in enumerate(top["cases"]):
        where = f"cases[{ci}]"
        if suite == "floats":
            check_float_case(c, err, where)
            continue
        if suite in ("arith", "products", "unary", "composite"):
            op = c.get("op")
            err.check(op in ops, f"{where}: op {op!r} not in ops")
            for key in ("a", "b"):
                if key in c:
                    err.check(isinstance(c[key], int) and 0 <= c[key] < len(inputs), f"{where}: bad input index {key}")
            if op == "pow":
                err.check(isinstance(c.get("k"), int), f"{where}: pow without k")
        elif suite == "construct":
            err.check(isinstance(c.get("label"), str) and isinstance(c.get("src"), str), f"{where}: label/src")
        elif suite == "docs":
            err.check(isinstance(c.get("block"), str) and isinstance(c.get("input"), str), f"{where}: block/input")
            out = c.get("out")
            if out is None or out.get("kind") != "Error":
                err.check("display" in c, f"{where}: successful statement without display")
        out = c.get("out")
        tags = c.get("defects", [])
        if out is not None:
            check_element(out, n, err, where + ".out", strict=not tags)
        flags = c.get("flags", [])
        err.check(set(flags) <= {"ref_mismatch"}, f"{where}: unknown flags {flags}")
        if "ref" in c:
            err.check("ref_mismatch" in flags, f"{where}: ref without the ref_mismatch flag")
            if n is not None:
                err.check(len(c["ref"]) == 1 << n, f"{where}: ref length")
        for t in tags:
            err.check(t in defects, f"{where}: unknown defect id {t}")
            dcount[t] = dcount.get(t, 0) + 1
        iserr = out is not None and out.get("kind") == "Error"
        ismis = "ref_mismatch" in flags
        nerr += iserr
        nmis += ismis
        nunex += (iserr or ismis) and not tags
    st = top["stats"]
    err.check(st["cases"] == len(top["cases"]), "stats.cases")
    err.check(st["errors"] == nerr and st["ref_mismatch"] == nmis and st["unexplained"] == nunex,
              f"stats {st} vs recount errors={nerr} ref_mismatch={nmis} unexplained={nunex}")
    err.check(st["defects"] == dcount, "stats.defects")
    return st


def f64(h: str) -> float:
    return struct.unpack(">d", bytes.fromhex(h))[0]


def check_float_case(c: Json, err: Errors, where: str) -> None:
    T = c["T"]
    v = c["value"]
    s = c["show"]
    cs = c["compact"]
    if T == "Float64":
        if not err.check(isinstance(v, str) and HEX_RE.match(v) is not None, f"{where}: value not 16 hex digits"):
            return
        x = f64(v)
        if not err.check(FLOAT_RE.match(s) is not None, f"{where}: show {s!r} not a Julia float literal"):
            return
        y = parse_float(s)
        if math.isnan(x):
            err.check(math.isnan(y), f"{where}: NaN shows as {s}")
        else:
            err.check(struct.pack(">d", y) == struct.pack(">d", x), f"{where}: show {s} does not round-trip {v}")
        if math.isfinite(x) and x != 0:
            try:
                z = float(cs)
                err.check(abs(z - x) <= 5e-6 * abs(x), f"{where}: compact {cs} too far from {s}")
            except ValueError:
                err.add(f"{where}: compact {cs!r} unparseable")
    elif T == "Int64":
        err.check(s == v and cs == v, f"{where}: Int64 show")
    elif T == "Rational{Int64}":
        err.check(s == f"{v[0]}//{v[1]}", f"{where}: Rational show")
    elif T == "Complex{Int64}":
        err.check(isinstance(v, list) and len(v) == 2 and all(INT_RE.match(p) for p in v), f"{where}: Complex{{Int64}} value")
    elif T == "Complex{Float64}":
        err.check(isinstance(v, list) and len(v) == 2 and all(HEX_RE.match(p) for p in v), f"{where}: Complex{{Float64}} value")
    elif T == "Bool":
        err.check(v in ("true", "false") and s == v, f"{where}: Bool")
    else:
        err.add(f"{where}: unknown T {T}")


def check_suite(suite: str, defects: dict[str, str]) -> list[Errors]:
    errs: list[Errors] = []
    mpath = GOLDEN / f"{suite}.json"
    merr = Errors(str(mpath.relative_to(ORACLE)))
    errs.append(merr)
    if not merr.check(mpath.exists(), "manifest missing"):
        return errs
    man = json.loads(mpath.read_text())
    merr.check(list(man.keys()) == ["meta", "totals", "shards"], "manifest keys")
    merr.check(man["meta"]["schema"] == SCHEMA and man["meta"]["suite"] == suite, "manifest meta")
    tot = {"cases": 0, "errors": 0, "ref_mismatch": 0, "unexplained": 0}
    dtot: dict[str, int] = {}
    listed = set()
    for sh in man["shards"]:
        p = GOLDEN / sh["file"]
        listed.add(p.name)
        e = Errors(str(p.relative_to(ORACLE)))
        errs.append(e)
        if not e.check(p.exists(), "listed in the manifest but missing"):
            continue
        size = p.stat().st_size
        e.check(size == sh["bytes"], f"bytes {sh['bytes']} != file size {size}")
        e.check(size <= MAX_BYTES, f"file is {size} bytes (> 4 MiB)")
        top = json.loads(p.read_text(encoding="utf-8"))
        st = check_shard(suite, sh["shard"], top, defects, e)
        for k in tot:
            tot[k] += st[k]
            e.check(sh[k] == st[k], f"manifest {k} {sh[k]} != shard {st[k]}")
        for k, v in st["defects"].items():
            dtot[k] = dtot.get(k, 0) + v
    stray = {p.name for p in (GOLDEN / suite).glob("*.json")} - listed
    merr.check(not stray, f"shard files not in the manifest: {sorted(stray)}")
    merr.check(man["totals"] == {**tot, "defects": dict(sorted(dtot.items()))}, "manifest totals != sum of shards")
    merr.check(tot["unexplained"] == 0, f"{tot['unexplained']} unexplained cases")
    return errs


def main(argv: list[str]) -> int:
    suites = argv or SUITES
    derr = Errors("golden/defects.json")
    defects = load_defects(derr)
    allerrs = [derr]
    for s in suites:
        allerrs += check_suite(s, defects)
    bad = [e for e in allerrs if e.msgs]
    for e in bad:
        print(f"{e.where}:")
        for m in e.msgs:
            print(f"  {m}")
    print(f"validated {len(suites)} suite(s), {len(allerrs) - 1} file(s): {'OK' if not bad else f'{len(bad)} with errors'}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
