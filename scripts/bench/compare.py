#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Join Lean and Julia benchmark results into the Lean-vs-Julia dashboard.

    uv run scripts/bench/compare.py --lean lean.json --julia julia.json [--julia more.json ...]
        [--budgets docs/perf/budgets.toml] [--history docs/perf/history.jsonl]
        [--latest docs/perf/latest.md] [--no-record] [--guard] [--threshold 0.2]
        [--machine NAME] [--commit SHA]

Inputs are the files written by `lake exe bench --json` and `oracle/bench/*.jl --json`
(schema: docs/perf/README.md). The script

* prints and writes (``--latest``) a markdown report: per case Lean and Julia ns/op (min and
  median), the Lean/Julia ratio of the minima, the budget and a status;
* appends a timestamped record (commit, machine, date, every case) to ``--history`` unless
  ``--no-record`` or the run is a smoke run;
* with ``--guard``, exits 1 when a case exceeds its budget ratio (or absolute ``max_ns``) or its
  Lean minimum regressed by more than ``--threshold`` against the previous history record of
  the same machine.
"""

from __future__ import annotations

import argparse
import datetime as dt
import fnmatch
import json
import math
import os
import platform
import subprocess
import sys
import tomllib
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[2]


@dataclass(frozen=True)
class Case:
    """One measured case of one language."""

    key: str
    suite: str
    case: str
    param: str
    min_ns: float
    median_ns: float
    check: float | None


@dataclass
class Run:
    """All results of one language (possibly merged from several files)."""

    lang: str
    smoke: bool = False
    meta: dict[str, Any] = field(default_factory=dict)
    cases: dict[str, Case] = field(default_factory=dict)


@dataclass(frozen=True)
class Budget:
    """A budget rule: the first rule whose pattern matches a key applies."""

    pattern: str
    ratio: float | None
    max_ns: float | None
    note: str


@dataclass(frozen=True)
class Row:
    """One line of the report."""

    key: str
    suite: str
    case: str
    param: str
    lean: Case | None
    julia: Case | None
    ratio: float | None
    budget: Budget
    status: str
    check: str


def load_run(paths: list[Path], lang: str) -> Run:
    """Load and merge result files; later files override earlier keys."""
    run = Run(lang=lang)
    for p in paths:
        doc = json.loads(p.read_text())
        run.smoke = run.smoke or bool(doc.get("smoke", False))
        for k, v in doc.items():
            if k != "results":
                run.meta.setdefault(k, v)
        for r in doc.get("results", []):
            chk = r.get("check")
            run.cases[r["key"]] = Case(
                key=r["key"],
                suite=r["suite"],
                case=r["case"],
                param=r.get("param", ""),
                min_ns=float(r["min_ns"]),
                median_ns=float(r["median_ns"]),
                check=None if chk is None else float(chk),
            )
    return run


def load_budgets(path: Path) -> tuple[float, list[Budget]]:
    """Read ``default`` and the ordered ``[[budget]]`` rules."""
    if not path.exists():
        return 2.0, []
    doc = tomllib.loads(path.read_text())
    rules = [
        Budget(
            pattern=b["pattern"],
            ratio=float(b["ratio"]) if "ratio" in b else None,
            max_ns=float(b["max_ns"]) if "max_ns" in b else None,
            note=str(b.get("note", "")),
        )
        for b in doc.get("budget", [])
    ]
    return float(doc.get("default", 2.0)), rules


def budget_for(key: str, default: float, rules: list[Budget]) -> Budget:
    """First matching rule, else the default ratio."""
    for b in rules:
        if fnmatch.fnmatchcase(key, b.pattern):
            return b
    return Budget(pattern="*", ratio=default, max_ns=None, note="")


def check_status(a: float | None, b: float | None) -> str:
    """``=`` when both checks agree (rtol 1e-9), ``≠`` when they differ, ``·`` when absent."""
    if a is None or b is None or not (math.isfinite(a) and math.isfinite(b)):
        return "·"
    if a == b:
        return "="
    return "=" if abs(a - b) <= 1e-9 * max(abs(a), abs(b)) else "≠"


def build_rows(lean: Run, julia: Run, default: float, rules: list[Budget]) -> list[Row]:
    """Join both runs by key (Lean order first, then Julia-only keys)."""
    keys = list(lean.cases) + [k for k in julia.cases if k not in lean.cases]
    rows: list[Row] = []
    for k in keys:
        lc, jc = lean.cases.get(k), julia.cases.get(k)
        ref = lc or jc
        assert ref is not None
        b = budget_for(k, default, rules)
        ratio = lc.min_ns / jc.min_ns if lc and jc and jc.min_ns > 0 else None
        if lc is None:
            status = "julia-only"
        elif b.max_ns is not None and lc.min_ns > b.max_ns:
            status = "OVER"
        elif ratio is None:
            status = "lean-only"
        elif b.ratio is not None and ratio > b.ratio:
            status = "OVER"
        else:
            status = "ok"
        rows.append(
            Row(
                key=k,
                suite=ref.suite,
                case=ref.case,
                param=ref.param,
                lean=lc,
                julia=jc,
                ratio=ratio,
                budget=b,
                status=status,
                check=check_status(lc.check if lc else None, jc.check if jc else None),
            )
        )
    return rows


def fmt_ns(ns: float | None) -> str:
    """Compact ns/µs/ms/s."""
    if ns is None or not math.isfinite(ns):
        return "—"
    if ns < 1e3:
        return f"{ns:.3g} ns"
    if ns < 1e6:
        return f"{ns / 1e3:.3g} µs"
    if ns < 1e9:
        return f"{ns / 1e6:.3g} ms"
    return f"{ns / 1e9:.3g} s"


def fmt_ratio(r: float | None) -> str:
    """Ratio with two significant digits (``×``)."""
    if r is None:
        return "—"
    return f"{r:.2g}×" if r < 10 else f"{r:.0f}×"


def geomean(xs: list[float]) -> float | None:
    """Geometric mean of positive numbers."""
    xs = [x for x in xs if x > 0 and math.isfinite(x)]
    return math.exp(sum(math.log(x) for x in xs) / len(xs)) if xs else None


def git(*args: str) -> str:
    """Run git in the repository root; empty string on failure."""
    try:
        return subprocess.run(
            ["git", *args], cwd=ROOT, capture_output=True, text=True, check=True
        ).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return ""


def machine_id() -> str:
    """CPU, core count and OS (no hostname)."""
    cpu = platform.processor() or platform.machine()
    if sys.platform == "darwin":
        try:
            cpu = subprocess.run(
                ["sysctl", "-n", "machdep.cpu.brand_string"], capture_output=True, text=True, check=True
            ).stdout.strip()
        except (OSError, subprocess.CalledProcessError):
            pass
    return f"{cpu}, {os.cpu_count()} cores, {platform.system()} {platform.release()}"


def render(rows: list[Row], lean: Run, julia: Run, meta: dict[str, str]) -> str:
    """The markdown report."""
    out: list[str] = []
    out.append("# Lean vs Julia: latest benchmark run\n")
    out.append(
        f"Generated by `scripts/bench/compare.py` on {meta['date']} · commit `{meta['commit']}`"
        f"{' (dirty)' if meta['dirty'] == 'true' else ''} · {meta['machine']} (load average "
        f"{meta['load']}) · {meta['lean']} · Julia "
        f"{julia.meta.get('julia', '?')}. Times are ns per operation; the ratio is Lean min / Julia min "
        f"(< 1: Lean faster). Budgets: `docs/perf/budgets.toml`. Check: `=` both sides computed the same "
        f"checksum, `≠` they differ, `·` not comparable.\n"
    )
    if lean.smoke or julia.smoke:
        out.append("> **Smoke run**: tiny sizes and one sample; the numbers are not meaningful.\n")
    if meta.get("note"):
        out.append(f"> {meta['note']}\n")
    both = [r for r in rows if r.ratio is not None]
    over = [r for r in rows if r.status == "OVER"]
    out.append(
        f"{len(rows)} cases, {len(both)} with both languages; geometric-mean ratio "
        f"{fmt_ratio(geomean([r.ratio for r in both if r.ratio]))}; "
        f"{sum(1 for r in both if r.ratio and r.ratio <= 1)} where Lean is at least as fast; "
        f"{len(over)} over budget.\n"
    )
    # per-suite summary
    out.append("## Summary by suite\n")
    out.append("| suite | cases (both) | geomean Lean/Julia | best | worst | over budget |")
    out.append("|---|---|---|---|---|---|")
    suites: dict[str, list[Row]] = {}
    for r in rows:
        suites.setdefault(r.suite, []).append(r)
    for s, rs in suites.items():
        rb = [r for r in rs if r.ratio is not None]
        best = min(rb, key=lambda r: r.ratio or 0.0) if rb else None
        worst = max(rb, key=lambda r: r.ratio or 0.0) if rb else None
        out.append(
            f"| {s} | {len(rs)} ({len(rb)}) | {fmt_ratio(geomean([r.ratio for r in rb if r.ratio]))} | "
            f"{f'{best.case} {fmt_ratio(best.ratio)}' if best else '—'} | "
            f"{f'{worst.case} {fmt_ratio(worst.ratio)}' if worst else '—'} | "
            f"{sum(1 for r in rs if r.status == 'OVER')} |"
        )
    out.append("")
    slow = sorted([r for r in both if r.ratio and r.ratio > 2], key=lambda r: -(r.ratio or 0))
    if slow:
        out.append("## Cases more than 2× slower than Julia\n")
        out.append("| case | Lean | Julia | ratio | note |")
        out.append("|---|---|---|---|---|")
        for r in slow:
            assert r.lean and r.julia
            out.append(
                f"| `{r.key}` | {fmt_ns(r.lean.min_ns)} | {fmt_ns(r.julia.min_ns)} | "
                f"{fmt_ratio(r.ratio)} | {r.budget.note} |"
            )
        out.append("")
    for s, rs in suites.items():
        out.append(f"## {s}\n")
        out.append("| case | size | Lean min | Lean median | Julia min | Julia median | Lean/Julia | budget | status | check |")
        out.append("|---|---|---|---|---|---|---|---|---|---|")
        for r in rs:
            bud = (
                f"≤ {r.budget.ratio:g}×" if r.budget.ratio is not None else ""
            ) + (f" ≤ {fmt_ns(r.budget.max_ns)}" if r.budget.max_ns is not None else "")
            out.append(
                f"| {r.case} | {r.param} | {fmt_ns(r.lean.min_ns if r.lean else None)} | "
                f"{fmt_ns(r.lean.median_ns if r.lean else None)} | {fmt_ns(r.julia.min_ns if r.julia else None)} | "
                f"{fmt_ns(r.julia.median_ns if r.julia else None)} | {fmt_ratio(r.ratio)} | {bud.strip() or '—'} | "
                f"{r.status} | {r.check} |"
            )
        out.append("")
    return "\n".join(out)


def history_record(rows: list[Row], meta: dict[str, str], julia: Run) -> dict[str, Any]:
    """One JSON line of docs/perf/history.jsonl."""
    cases: dict[str, dict[str, float]] = {}
    for r in rows:
        d: dict[str, float] = {}
        if r.lean:
            d["lean_min"] = r.lean.min_ns
            d["lean_median"] = r.lean.median_ns
        if r.julia:
            d["julia_min"] = r.julia.min_ns
            d["julia_median"] = r.julia.median_ns
        cases[r.key] = d
    return {
        "date": meta["date"],
        "commit": meta["commit"],
        "dirty": meta["dirty"] == "true",
        "machine": meta["machine"],
        "lean": meta.get("lean", ""),
        "julia": julia.meta.get("julia", ""),
        "load": meta.get("load", ""),
        "note": meta.get("note", ""),
        "cases": cases,
    }


def previous_record(history: Path, machine: str) -> dict[str, Any] | None:
    """The last history record of this machine."""
    if not history.exists():
        return None
    prev = None
    for line in history.read_text().splitlines():
        line = line.strip()
        if not line:
            continue
        rec = json.loads(line)
        if rec.get("machine") == machine:
            prev = rec
    return prev


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--lean", type=Path, action="append", default=[], help="Lean result JSON (repeatable)")
    ap.add_argument("--julia", type=Path, action="append", default=[], help="Julia result JSON (repeatable)")
    ap.add_argument("--budgets", type=Path, default=ROOT / "docs/perf/budgets.toml")
    ap.add_argument("--history", type=Path, default=ROOT / "docs/perf/history.jsonl")
    ap.add_argument("--latest", type=Path, default=ROOT / "docs/perf/latest.md")
    ap.add_argument("--no-record", action="store_true", help="do not append to the history")
    ap.add_argument("--no-latest", action="store_true", help="do not write the markdown report")
    ap.add_argument("--guard", action="store_true", help="exit 1 on budget violations or regressions")
    ap.add_argument("--threshold", type=float, default=0.20, help="regression threshold (fraction)")
    ap.add_argument("--machine", default=None, help="machine id (default: CPU, cores, OS)")
    ap.add_argument("--commit", default=None, help="commit id (default: git HEAD)")
    ap.add_argument("--quiet", action="store_true", help="do not print the report")
    ap.add_argument("--note", default="", help="free-form note for the report and the history")
    a = ap.parse_args()

    lean = load_run(a.lean, "lean")
    julia = load_run(a.julia, "julia")
    default, rules = load_budgets(a.budgets)
    rows = build_rows(lean, julia, default, rules)
    machine = a.machine or machine_id()
    meta = {
        "date": dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "commit": a.commit or git("rev-parse", "--short=12", "HEAD") or "unknown",
        "dirty": "true" if git("status", "--porcelain", "--untracked-files=no") else "false",
        "machine": machine,
        "lean": (ROOT / "lean-toolchain").read_text().strip() if (ROOT / "lean-toolchain").exists() else "",
        "load": f"{os.getloadavg()[0]:.0f}",
        "note": a.note,
    }
    report = render(rows, lean, julia, meta)
    if not a.quiet:
        print(report)
    if not a.no_latest:
        a.latest.parent.mkdir(parents=True, exist_ok=True)
        a.latest.write_text(report + "\n")

    failures: list[str] = []
    for r in rows:
        if r.status == "OVER":
            failures.append(f"{r.key}: over budget ({fmt_ratio(r.ratio)} vs {r.budget.ratio}×"
                            f"{'' if r.budget.max_ns is None else f', max {fmt_ns(r.budget.max_ns)}'})")
    smoke = lean.smoke or julia.smoke
    prev = None if smoke else previous_record(a.history, machine)
    if prev is not None:
        for r in rows:
            old = prev["cases"].get(r.key, {}).get("lean_min")
            if r.lean and old and r.lean.min_ns > old * (1 + a.threshold):
                failures.append(
                    f"{r.key}: Lean regressed {fmt_ns(old)} → {fmt_ns(r.lean.min_ns)} "
                    f"(+{100 * (r.lean.min_ns / old - 1):.0f}% vs {prev['commit']})"
                )
    if not a.no_record and not smoke and rows:
        a.history.parent.mkdir(parents=True, exist_ok=True)
        with a.history.open("a") as f:
            f.write(json.dumps(history_record(rows, meta, julia), separators=(",", ":")) + "\n")
    if failures:
        print(f"\n{len(failures)} guard failure(s):", file=sys.stderr)
        for m in failures:
            print(f"  {m}", file=sys.stderr)
    return 1 if (a.guard and failures) else 0


if __name__ == "__main__":
    sys.exit(main())
