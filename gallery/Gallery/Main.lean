import Gallery

/-!
# `lake exe gallery`

```
lake exe gallery [--only NAME,PREFIX,…] [--docs] [--no-svg] [--root DIR]
```

Renders every gallery figure to `out/<name>.png` and `out/<name>.svg` (relative to the
working directory, `gallery/` under `lake exe`), compares its data with the Julia dump
`<root>/oracle/gallery/data/<name>.json` when there is one, and prints the checks.
`--docs` also copies the PNGs to `<root>/docs/gallery/lean/` and regenerates
`<root>/docs/gallery/index.md`. `<root>` defaults to `..` (the repository root). The exit
code is 1 when a data check fails.
-/

open Gallery

/-- Command-line options. -/
structure Opts where
  only : List String := []
  docs : Bool := false
  svg : Bool := true
  root : System.FilePath := ".."

/-- Parse the arguments. -/
def parseArgs : List String → Opts → Opts
  | "--only" :: v :: rest, o => parseArgs rest { o with only := v.splitOn "," }
  | "--docs" :: rest, o => parseArgs rest { o with docs := true }
  | "--no-svg" :: rest, o => parseArgs rest { o with svg := false }
  | "--root" :: v :: rest, o => parseArgs rest { o with root := v }
  | _ :: rest, o => parseArgs rest o
  | [], o => o

/-- Whether an entry is selected by `--only` (exact names or prefixes). -/
def selected (o : Opts) (e : Entry) : Bool :=
  o.only.isEmpty || o.only.any fun p => e.name == p || e.name.startsWith p

/-- Render, compare and (with `--docs`) publish every selected figure. -/
def main (args : List String) : IO UInt32 := do
  let o := parseArgs args {}
  IO.FS.createDirAll "out"
  let mut results : Array (Entry × Array Check × String) := #[]
  let mut failed := 0
  for e in Gallery.registry do
    if !selected o e then continue
    let dataPath := o.root / "oracle" / "gallery" / "data" / s!"{e.name}.json"
    let j? ← if ← dataPath.pathExists then
        match Lean.Json.parse (← IO.FS.readFile dataPath) with
        | .ok j => pure (some j)
        | .error err => IO.eprintln s!"{e.name}: bad JSON {dataPath}: {err}"; pure none
      else pure none
    let t0 ← IO.monoMsNow
    let out ← e.build j?
    let t1 ← IO.monoMsNow
    let png : System.FilePath := "out" / s!"{e.name}.png"
    out.fig.save png
    if o.svg then out.fig.save ("out" / s!"{e.name}.svg")
    let t2 ← IO.monoMsNow
    IO.println s!"{e.name}: data {t1 - t0} ms, render {t2 - t1} ms{if j?.isNone then " (no Julia dump)" else ""}"
    for c in out.checks do
      IO.println s!"  [{if c.ok then "ok" else "FAIL"}] {c.label}: {c.detail}"
      if !c.ok then failed := failed + 1
    let juliaPng := o.root / "docs" / "gallery" / "julia" / s!"{e.name}.png"
    let img ← if ← juliaPng.pathExists then
        match Gallery.ImageDiff.comparePNG (← IO.FS.readBinFile png) (← IO.FS.readBinFile juliaPng) with
        | .ok st => pure st.summary
        | .error err => pure s!"not compared ({err})"
      else pure "no Julia render"
    IO.println s!"  image: {img}"
    if o.docs then
      let dst := o.root / "docs" / "gallery" / "lean" / s!"{e.name}.png"
      IO.FS.createDirAll (o.root / "docs" / "gallery" / "lean")
      IO.FS.writeBinFile dst (← IO.FS.readBinFile png)
    results := results.push (e, out.checks, img)
  if o.docs && o.only.isEmpty then
    let md ← Gallery.Index.render o.root results
    IO.FS.writeFile (o.root / "docs" / "gallery" / "index.md") md
    IO.println "wrote docs/gallery/index.md"
  IO.println s!"{results.size} figures, {failed} failed checks"
  return if failed == 0 then 0 else 1
