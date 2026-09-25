#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Run the Lean and Julia benchmark suites and compare them.

    uv run scripts/bench/run.py [--smoke] [--filter substr]... [--suite name]...
        [--julia-env DIR] [--julia-env2 DIR] [--chakravala DIR] [--out DIR]
        [--no-build] [--no-lean] [--no-julia] [--guard] [--no-record] [--no-latest]

Steps: ``lake build bench``; ``lake exe bench --json OUT/lean.json``; one Julia process per
environment group (``oracle/bench/run.jl --include ...``, see ``JULIA_SUITES``); then
``scripts/bench/compare.py`` on all result files (writes docs/perf/latest.md and appends to
docs/perf/history.jsonl unless ``--no-record``). Julia environments default to
``$GRASSMANN_JULIA_ENV`` (else ``oracle/``) and ``$GRASSMANN_JULIA_ENV2`` (else
``oracle/bench/env2``, the Dendriform/DeMorgan environment: Dendriform conflicts with
AbstractAnalysis in the main one).
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]

# suite -> (environment group, Julia threads). Fatou's parallel cases compare Lean tasks with
# Julia threads, so its process gets every core; all other suites are single-threaded. Adapode
# loads Adapode.jl master with patches to Cartan methods, so it runs in a process of its own.
JULIA_SUITES: dict[str, tuple[str, str]] = {
    "math": ("main", "1"),
    "juliabase": ("main", "1"),
    "staticvectors": ("main", "1"),
    "directsum": ("main", "1"),
    "unitsystems": ("main", "1"),
    "geophysics": ("main", "1"),
    "wilkinson": ("main", "1"),
    "meshtopology": ("main", "1"),
    "grassmann": ("main", "1"),
    "dynamic": ("main", "1"),
    "composite": ("main", "1"),
    "forms": ("main", "1"),
    "cartan": ("main", "1"),
    "adapode": ("adapode", "1"),
    "fatou": ("threads", "auto"),
    "dendriform": ("env2", "1"),
    "demorgan": ("env2", "1"),
}


def run(cmd: list[str], env: dict[str, str] | None = None) -> int:
    """Echo and run a command in the repository root."""
    print("$ " + " ".join(cmd), flush=True)
    return subprocess.run(cmd, cwd=ROOT, env=env).returncode


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--smoke", action="store_true")
    ap.add_argument("--filter", action="append", default=[])
    ap.add_argument("--suite", action="append", default=[], help="suite name (repeatable; default all)")
    ap.add_argument("--julia", default=os.environ.get("JULIA", "julia"))
    ap.add_argument("--julia-env", default=os.environ.get("GRASSMANN_JULIA_ENV", str(ROOT / "oracle")))
    ap.add_argument("--julia-env2", default=os.environ.get("GRASSMANN_JULIA_ENV2", str(ROOT / "oracle/bench/env2")))
    ap.add_argument("--chakravala", default=os.environ.get("CHAKRAVALA", str(Path.home() / "chakravala")),
                    help="checkout of the chakravala Julia sources (Geophysics.jl is included from it)")
    ap.add_argument("--out", type=Path, default=ROOT / ".lake/bench")
    ap.add_argument("--no-build", action="store_true")
    ap.add_argument("--no-lean", action="store_true")
    ap.add_argument("--no-julia", action="store_true")
    ap.add_argument("--guard", action="store_true")
    ap.add_argument("--no-record", action="store_true")
    ap.add_argument("--no-latest", action="store_true")
    ap.add_argument("--note", default="", help="note recorded with the run (compare.py --note)")
    a = ap.parse_args()

    a.out.mkdir(parents=True, exist_ok=True)
    common: list[str] = (["--smoke"] if a.smoke else []) + [x for f in a.filter for x in ("--filter", f)]
    suites = [s.lower() for s in a.suite]
    lean_json = a.out / "lean.json"
    julia_jsons: list[Path] = []

    if not a.no_lean:
        if not a.no_build and run(["lake", "build", "bench"]) != 0:
            return 1
        if run([str(ROOT / ".lake/build/bin/bench"), "--json", str(lean_json), *common, *suites]) != 0:
            return 1

    if not a.no_julia:
        env = dict(os.environ, CHAKRAVALA=a.chakravala)
        groups: dict[tuple[str, str], list[str]] = {}
        for s, (grp, thr) in JULIA_SUITES.items():
            if not suites or s in suites:
                groups.setdefault((grp, thr), []).append(s)
        for (grp, thr), ss in groups.items():
            proj = a.julia_env2 if grp == "env2" else a.julia_env
            out = a.out / f"julia-{grp}.json"
            cmd = [a.julia, "--startup-file=no", f"--project={proj}", f"--threads={thr}",
                   str(ROOT / "oracle/bench/run.jl"), "--include", ",".join(ss), "--json", str(out), *common]
            if run(cmd, env) != 0:
                print(f"warning: Julia group {grp} failed", file=sys.stderr)
                continue
            julia_jsons.append(out)

    if not lean_json.exists():
        print("no Lean results; nothing to compare", file=sys.stderr)
        return 1
    cmp = ["uv", "run", str(ROOT / "scripts/bench/compare.py"), "--lean", str(lean_json)]
    for j in julia_jsons:
        cmp += ["--julia", str(j)]
    cmp += (["--guard"] if a.guard else []) + (["--no-record"] if a.no_record else []) + \
        (["--no-latest"] if a.no_latest else []) + (["--note", a.note] if a.note else [])
    return run(cmp)


if __name__ == "__main__":
    sys.exit(main())
