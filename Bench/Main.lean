import Bench

/-!
# `lake exe bench`

```
lake exe bench [--smoke] [--json out.json] [--filter substr]… [--samples n] [--sample-ms n]
               [--quiet] [--list] [suite …]
```

* positional arguments pick suites by name (case-insensitive); none means all;
* `--filter s` keeps cases whose key `suite/case` contains `s` (repeatable);
* `--json path` writes the results (schema in `docs/perf/README.md`), consumed by
  `scripts/bench/compare.py` together with the Julia twin `oracle/bench/run.jl`;
* `--smoke` shrinks sizes and takes one short sample per case (CI).
-/

open Bench

/-- Every suite `lake exe bench` knows, in run order. `Bench.Grassmann.run` joins automatically
once its module is imported into `Bench.lean` (`optional_suite%`). -/
def suites : List Suite :=
  [ Bench.Math.suite, Bench.MeshTopology.suite, Bench.Fatou.suite ] ++
  (optional_suite% "Grassmann" Bench.Grassmann.run).toList

/-- Usage text. -/
def usage : String :=
  "usage: lake exe bench [--smoke] [--json out.json] [--filter substr]... [--samples n]\n" ++
  "                      [--sample-ms n] [--quiet] [--list] [suite ...]\n" ++
  "suites: " ++ ", ".intercalate (suites.map (·.name))

/-- Parsed command line. -/
structure Cli where
  /-- Harness options. -/
  cfg : Config := {}
  /-- `--json` target. -/
  json : Option System.FilePath := none
  /-- Suite names. -/
  names : List String := []
  /-- `--list`. -/
  list : Bool := false
  /-- `--help`. -/
  help : Bool := false

/-- Parse arguments. -/
def parse : List String → Cli → Except String Cli
  | [], c => .ok c
  | "--smoke" :: r, c => parse r { c with cfg.smoke := true, cfg.sampleNs := 1000000 }
  | "--quiet" :: r, c => parse r { c with cfg.quiet := true }
  | "--list" :: r, c => parse r { c with list := true }
  | "--help" :: r, c | "-h" :: r, c => parse r { c with help := true }
  | "--json" :: p :: r, c => parse r { c with json := some p }
  | "--filter" :: f :: r, c => parse r { c with cfg.filters := c.cfg.filters.push f }
  | "--samples" :: n :: r, c => match n.toNat? with
    | some k => parse r { c with cfg.samples := max k 1 }
    | none => .error s!"--samples expects a number, got {n}"
  | "--sample-ms" :: n :: r, c => match n.toNat? with
    | some k => parse r { c with cfg.sampleNs := max k 1 * 1000000 }
    | none => .error s!"--sample-ms expects a number, got {n}"
  | a :: r, c =>
    if a.startsWith "-" then .error s!"unknown option {a}" else parse r { c with names := c.names ++ [a] }

/-- Benchmark driver. -/
def main (args : List String) : IO UInt32 := do
  match parse args {} with
  | .error e => IO.eprintln e; IO.eprintln usage; return 2
  | .ok c =>
    if c.help then IO.println usage; return 0
    let low (s : String) := s.toLower
    let chosen := if c.names.isEmpty then suites
      else suites.filter fun s => c.names.any (low · == low s.name)
    if chosen.isEmpty then IO.eprintln s!"no suite matches {c.names}"; IO.eprintln usage; return 2
    if c.list then
      for s in chosen do IO.println s.name
      return 0
    let rs ← runSuites c.cfg chosen
    if let some p := c.json then
      IO.FS.writeFile p (toJson c.cfg rs)
      IO.println s!"wrote {rs.size} results to {p}"
    return 0
