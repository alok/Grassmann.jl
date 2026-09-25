import Tests.JuliaBase.Util

/-!
Julia float printing against the oracle: `show`, compact `show` (and `print` for `Float32`)
must agree byte for byte.

The committed golden (`Tests/JuliaBase/float_show.json`, ~2k cases) runs in CI. The same
checker also runs over the TSV fuzz files produced by `Tests/JuliaBase/gen_golden.jl`
(`bits⇥show⇥compact[⇥print]` per line); `Tests.JuliaBase.FloatShow.fuzz` is the entry point
used for the 10⁵-case oracle fuzz.
-/

open JuliaBase

namespace Tests.JuliaBase.FloatShow

/-- Check one Float64 case. -/
def checkF64 (t : Tally) (hex want wantCompact : String) : Tally :=
  match floatOfHex hex with
  | none => t.check false fun _ => s!"bad hex {hex}"
  | some x =>
    let s := F64.showString x
    let c := F64.showCompact x
    let t := t.check (s == want) fun _ => s!"show 0x{hex}: got {s}, want {want}"
    t.check (c == wantCompact) fun _ => s!"compact 0x{hex}: got {c}, want {wantCompact}"

/-- Check one Float32 case. -/
def checkF32 (t : Tally) (hex want wantCompact wantPrint : String) : Tally :=
  match float32OfHex hex with
  | none => t.check false fun _ => s!"bad hex {hex}"
  | some x =>
    let s := F32.showString x
    let c := F32.showCompact x
    let p := F32.printString x
    let t := t.check (s == want) fun _ => s!"show32 0x{hex}: got {s}, want {want}"
    let t := t.check (c == wantCompact) fun _ => s!"compact32 0x{hex}: got {c}, want {wantCompact}"
    t.check (p == wantPrint) fun _ => s!"print32 0x{hex}: got {p}, want {wantPrint}"

/-- Run a TSV fuzz file (`f32 = true` for the four-column Float32 format). -/
def runTsv (path : System.FilePath) (f32 : Bool) : IO Tally := do
  let txt ← IO.FS.readFile path
  let mut t : Tally := {}
  for line in txt.splitOn "\n" do
    if line.isEmpty then continue
    match line.splitOn "\t", f32 with
    | [h, s, c], false => t := checkF64 t h s c
    | [h, s, c, p], true => t := checkF32 t h s c p
    | _, _ => t := t.check false fun _ => s!"malformed line: {line}"
  return t

/-- Oracle fuzz entry point: `fuzz f64.tsv f32.tsv`. -/
def fuzz (f64 f32 : System.FilePath) : IO (Nat × Nat) := do
  let a ← runTsv f64 false
  let b ← runTsv f32 true
  (a.merge b).report "float-show fuzz"

/-- The committed golden `float_show.json`. -/
def golden : IO (Nat × Nat) := do
  let j ← loadGolden "float_show.json"
  let mut t : Tally := {}
  for row in jArr j "f64" do
    match jRow row with
    | [h, s, c] => t := checkF64 t h s c
    | r => t := t.check false fun _ => s!"malformed row {r}"
  for row in jArr j "f32" do
    match jRow row with
    | [h, s, c, p] => t := checkF32 t h s c p
    | r => t := t.check false fun _ => s!"malformed row {r}"
  t.report "float-show golden"

/-! Compile-time checks: the oracle table of port-notes/grassmann-types.md §5.5. -/

#guard F64.showString (1/3) == "0.3333333333333333"
#guard F64.showCompact (1/3) == "0.333333"
#guard F64.showString 1e-4 == "0.0001"
#guard F64.showString 1e-5 == "1.0e-5"
#guard F64.showString 999999.0 == "999999.0"
#guard F64.showString 1e6 == "1.0e6"
#guard F64.showCompact 1234567.0 == "1.23457e6"
#guard F64.showString 123456.789 == "123456.789"
#guard F64.showCompact 123456.789 == "1.23457e5"
#guard F64.showString (0.1 + 0.2) == "0.30000000000000004"
#guard F64.showCompact (0.1 + 0.2) == "0.3"
#guard F64.showString F64.floatmax == "1.7976931348623157e308"
#guard F64.showCompact F64.floatmax == "1.79769e308"
#guard F64.showString (Float.ofBits 1) == "5.0e-324"
#guard F64.showString (-0.0) == "-0.0"
#guard F64.showString (-F64.inf) == "-Inf"
#guard F64.showString F64.nan == "NaN"
#guard F32.showString 1.5 == "1.5f0"
#guard F32.showString 1e-5 == "1.0f-5"
#guard F32.printString 1e-5 == "1.0e-5"
#guard F32.showCompact (1/3) == "0.333333"

end Tests.JuliaBase.FloatShow
