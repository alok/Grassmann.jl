#!/usr/bin/env python3
"""ALOK-1007 Packed-Buffer Linearity Codegen Guard & Init-Only Runtime Audit.

Verifies two structural invariants on Lean 4.36 generated C (`+Mod:c`):
  1. Packed-buffer linearity on hot Float kernels (`Grassmann.Projective`,
     `Grassmann.Conformal`, `Grassmann.Types.Dims`, `Grassmann.Dynamic.Loops`):
     single `lean_mk_empty_float_array` allocation where expected, direct unboxed
     `lean_float_array_fget` / `fset` / `push`, tail-recursive `goto _start;` loops,
     and ZERO inner-loop `lean_box_float`, `lean_alloc_closure`, or runtime
     `l_Float_ofScientific` calls.
  2. Strict `Init`-only transitive `runtime_initialize_*` closure for all 11 core
     runtime targets (`Grassmann.{Projective,Conformal,GanjaCompat}` and
     `Grassmann.Kernel.Generated.{R2,R3,R4,STA,PGA2,PGA3,CGA2,CGA3}`).
"""

from __future__ import annotations

import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
IR_DIR = ROOT / ".lake" / "build" / "ir"

_c_cache: dict[str, str] = {}


def read_c(mod: str) -> str:
    if mod in _c_cache:
        return _c_cache[mod]
    rel = mod.replace(".", "/") + ".c"
    p = IR_DIR / rel
    if p.exists():
        txt = p.read_text()
    else:
        out = subprocess.check_output(
            ["lake", "query", f"{mod}:c"], cwd=ROOT, text=True
        ).strip()
        txt = pathlib.Path(out).read_text()
    _c_cache[mod] = txt
    return txt


def extract_fn(txt: str, pattern: str) -> tuple[str, str]:
    m = re.search(pattern, txt)
    if not m:
        raise AssertionError(f"Function pattern not found: {pattern}")
    start = m.start()
    brace = txt.find("{", m.start())
    depth = 0
    end = brace
    for k in range(brace, len(txt)):
        ch = txt[k]
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                end = k + 1
                break
    sig = txt[start:brace].strip()
    return sig, txt[start:end]


def check_packed_linearity() -> list[str]:
    failures: list[str] = []

    specs = [
        # (module, regex, expectations)
        (
            "Grassmann.Projective",
            r"LEAN_EXPORT lean_object\* lp_Grassmann_Grassmann_Projective_transformXYZBatch\([^\n]*\{",
            dict(
                max_box_float=0,
                max_closures=0,
                max_of_scientific=0,
                exact_mk_empty=1,
            ),
        ),
        (
            "Grassmann.Projective",
            r"LEAN_EXPORT lean_object\* lp_Grassmann___private_Grassmann_Projective_0__Grassmann_Projective_transformXYZLoop___redArg\([^\n]*\{",
            dict(
                max_box_float=0,
                max_closures=0,
                max_of_scientific=0,
                min_fget=3,
                min_push=3,
                min_tail_loop=1,
            ),
        ),
        (
            "Grassmann.Projective",
            r"LEAN_EXPORT lean_object\* lp_Grassmann_Grassmann_Projective_motorExp\([^\n]*\{",
            dict(
                max_box_float=0,
                max_closures=0,
                max_of_scientific=0,
                min_fget=6,
                min_fset=8,
            ),
        ),
        (
            "Grassmann.Projective",
            r"LEAN_EXPORT lean_object\* lp_Grassmann_Grassmann_Projective_motorLog\([^\n]*\{",
            dict(
                max_box_float=0,
                max_closures=0,
                max_of_scientific=0,
                min_fget=8,
                min_fset=6,
            ),
        ),
        (
            "Grassmann.Projective",
            r"LEAN_EXPORT lean_object\* lp_Grassmann_Grassmann_Projective_motorSlerp\([^\n]*\{",
            dict(
                max_box_float=0,
                max_closures=0,
                max_of_scientific=0,
                min_fget=16,
                min_fset=8,
            ),
        ),
        (
            "Grassmann.Projective",
            r"LEAN_EXPORT lean_object\* lp_Grassmann___private_Grassmann_Projective_0__Grassmann_Projective_sliceLoop___redArg\([^\n]*\{",
            dict(
                max_box_float=0,
                max_closures=0,
                max_of_scientific=0,
                min_fget=9,
                min_tail_loop=1,
            ),
        ),
        (
            "Grassmann.Projective",
            r"LEAN_EXPORT lean_object\* lp_Grassmann___private_Grassmann_Projective_0__Grassmann_Projective_stitchPass___redArg\([^\n]*\{",
            dict(
                max_box_float=0,
                max_closures=0,
                max_of_scientific=0,
                min_fget=4,
                min_push=4,
                min_tail_loop=1,
            ),
        ),
        (
            "Grassmann.Projective",
            r"LEAN_EXPORT lean_object\* lp_Grassmann___private_Grassmann_Projective_0__Grassmann_Projective_projectSegs2DLoop___redArg\([^\n]*\{",
            dict(
                max_box_float=0,
                max_closures=0,
                max_of_scientific=0,
                min_fget=6,
                min_push=4,
                min_tail_loop=1,
            ),
        ),
        (
            "Grassmann.Conformal",
            r"LEAN_EXPORT lean_object\* lp_Grassmann_Grassmann_Conformal_point3\([^\n]*\{",
            dict(
                max_box_float=0,
                max_closures=0,
                max_of_scientific=0,
                min_fset=5,
            ),
        ),
        (
            "Grassmann.Conformal",
            r"LEAN_EXPORT lean_object\* lp_Grassmann_Grassmann_Conformal_dualSphere3\([^\n]*\{",
            dict(
                max_box_float=0,
                max_closures=0,
                max_of_scientific=0,
                min_fset=5,
            ),
        ),
        (
            "Grassmann.Types.Dims",
            r"LEAN_EXPORT lean_object\* lp_Grassmann_Grassmann_applyPermLoop___redArg\([^\n]*\{",
            dict(
                max_box_float=0,
                max_closures=0,
                max_of_scientific=0,
                min_tail_loop=1,
            ),
        ),
        (
            "Grassmann.Dynamic.Loops",
            r"LEAN_EXPORT lean_object\* lp_Grassmann_Grassmann_Loops_fill___redArg\([^\n]*\{",
            dict(
                max_box_float=0,
                max_closures=0,
                max_of_scientific=0,
                min_tail_loop=1,
            ),
        ),
        (
            "Grassmann.Dynamic.Loops",
            r"LEAN_EXPORT lean_object\* lp_Grassmann_Grassmann_Loops_rows___redArg\([^\n]*\{",
            dict(
                max_box_float=0,
                max_closures=0,
                max_of_scientific=0,
                min_tail_loop=1,
            ),
        ),
    ]

    print("=== ALOK-1007 Packed-Buffer Linearity Codegen Guard ===")
    for mod, pat, exp in specs:
        txt = read_c(mod)
        try:
            sig, body = extract_fn(txt, pat)
        except AssertionError as e:
            failures.append(f"{mod}: {e}")
            continue
        metrics = {
            "box_float": len(re.findall(r"\blean_box_float\b", body)),
            "closures": len(re.findall(r"\blean_alloc_closure\b", body)),
            "of_scientific": len(re.findall(r"\bl_Float_ofScientific\b", body)),
            "mk_empty": len(re.findall(r"\blean_mk_empty_float_array\b", body)),
            "fget": len(re.findall(r"\blean_float_array_(fget|uget)\b", body)),
            "fset": len(re.findall(r"\blean_float_array_(fset|uset)\b", body)),
            "push": len(re.findall(r"\blean_float_array_push\b", body)),
            "tail_loop": len(re.findall(r"\bgoto _start;", body)),
        }
        errs = []
        if "max_box_float" in exp and metrics["box_float"] > exp["max_box_float"]:
            errs.append(f"box_float={metrics['box_float']} > {exp['max_box_float']}")
        if "max_closures" in exp and metrics["closures"] > exp["max_closures"]:
            errs.append(f"closures={metrics['closures']} > {exp['max_closures']}")
        if "max_of_scientific" in exp and metrics["of_scientific"] > exp["max_of_scientific"]:
            errs.append(f"of_scientific={metrics['of_scientific']} > {exp['max_of_scientific']}")
        if "exact_mk_empty" in exp and metrics["mk_empty"] != exp["exact_mk_empty"]:
            errs.append(f"mk_empty={metrics['mk_empty']} != {exp['exact_mk_empty']}")
        if "min_fget" in exp and metrics["fget"] < exp["min_fget"]:
            errs.append(f"fget={metrics['fget']} < {exp['min_fget']}")
        if "min_fset" in exp and metrics["fset"] < exp["min_fset"]:
            errs.append(f"fset={metrics['fset']} < {exp['min_fset']}")
        if "min_push" in exp and metrics["push"] < exp["min_push"]:
            errs.append(f"push={metrics['push']} < {exp['min_push']}")
        if "min_tail_loop" in exp and metrics["tail_loop"] < exp["min_tail_loop"]:
            errs.append(f"tail_loop={metrics['tail_loop']} < {exp['min_tail_loop']}")

        short_name = sig.split("(")[0].split()[-1]
        status = "PASS" if not errs else "FAIL"
        print(
            f"  [{status}] {mod} :: {short_name}\n"
            f"         box={metrics['box_float']} closures={metrics['closures']} "
            f"ofSci={metrics['of_scientific']} mkEmpty={metrics['mk_empty']} "
            f"fget={metrics['fget']} fset={metrics['fset']} push={metrics['push']} "
            f"tail={metrics['tail_loop']}"
        )
        if errs:
            failures.append(f"{mod}::{short_name}: {', '.join(errs)}")
    return failures


def c_sym_to_mod(sym: str) -> str | None:
    if not sym.startswith("Grassmann_"):
        return None
    parts = sym[len("Grassmann_") :].split("_")
    cur = ROOT
    res: list[str] = []
    i = 0
    while i < len(parts):
        found = False
        for j in range(len(parts), i, -1):
            cand = "_".join(parts[i:j])
            if j == len(parts) and (cur / (cand + ".lean")).exists():
                res.append(cand)
                return ".".join(res)
            if (cur / cand).is_dir():
                cur = cur / cand
                res.append(cand)
                i = j
                found = True
                break
        if not found:
            return None
    return None


def check_init_only() -> list[str]:
    targets = [
        "Grassmann.Projective",
        "Grassmann.Conformal",
        "Grassmann.GanjaCompat",
        "Grassmann.Kernel.Generated.R2",
        "Grassmann.Kernel.Generated.R3",
        "Grassmann.Kernel.Generated.R4",
        "Grassmann.Kernel.Generated.STA",
        "Grassmann.Kernel.Generated.PGA2",
        "Grassmann.Kernel.Generated.PGA3",
        "Grassmann.Kernel.Generated.CGA2",
        "Grassmann.Kernel.Generated.CGA3",
    ]
    forbidden_substrings = ("FloatLit", "Alias", "DirectSum.Basis", "Kernel.Codegen")
    visited: set[str] = set()
    external: set[str] = set()
    forbidden: list[tuple[str, str]] = []
    queue = list(targets)

    while queue:
        m = queue.pop(0)
        if m in visited:
            continue
        visited.add(m)
        txt = read_c(m)
        pat = re.search(
            r"LEAN_EXPORT lean_object\* runtime_initialize_[A-Za-z0-9_]+\(uint8_t builtin\)\s*\{(.*?)\n\}",
            txt,
            re.S,
        )
        if not pat:
            return [f"{m}: missing runtime_initialize_* (not a Lean module file?)"]
        body = pat.group(1)
        for dep in re.findall(r"\bruntime_initialize_([A-Za-z0-9_]+)\(", body):
            if dep == "Init" or dep.startswith("Init_"):
                external.add(dep)
            else:
                local = c_sym_to_mod(dep)
                if local:
                    if any(bad in local for bad in forbidden_substrings):
                        forbidden.append((m, local))
                    queue.append(local)
                else:
                    external.add(dep)

    print("\n=== Strict Init-Only Runtime C Closure Audit ===")
    print(f"  Targets: {len(targets)} -> {len(visited)} transitive local runtime modules")
    print(f"  External runtime_initialize_* deps: {sorted(external)}")
    print(f"  Forbidden meta/elab deps: {forbidden}")
    failures: list[str] = []
    non_init = [e for e in sorted(external) if not (e == "Init" or e.startswith("Init_"))]
    if non_init:
        failures.append(f"Non-Init external runtime_initialize deps: {non_init}")
    if forbidden:
        failures.append(f"Forbidden meta/elab runtime deps: {forbidden}")
    if not failures:
        print("  [PASS] All 11 targets are 100% strictly Init-only at runtime!")
    return failures


def main() -> int:
    failures = check_packed_linearity()
    failures.extend(check_init_only())
    if failures:
        print("\nFAILURES:")
        for f in failures:
            print(f"  - {f}")
        return 1
    print("\nALL CODEGEN LINEARITY & INIT-ONLY CHECKS PASSED!")
    return 0


if __name__ == "__main__":
    sys.exit(main())
