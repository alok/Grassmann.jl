import FlowGeometry
import Tests.Cartan.Common

/-!
# Shared helpers for the FlowGeometry golden tests

Goldens live in `oracle/golden/flowgeometry/*.json` (written by `oracle/flowgeometry/gen.jl`).
Floats are IEEE bit patterns `"0x…"`, complex vectors and homogeneous points are flattened, and a
Julia exception is `{"E": "<Type>: …"}`. Every float must match **bit for bit**. A Julia
`DomainError` (`log`/`sqrt` of a negative number) must be `NaN` in Lean; any other Julia error
marks a Julia defect that the port fixes or replaces by its intent (`oracle/flowgeometry/defects.toml`)
and is counted as skipped.
-/

open Lean Tests.Small Tests.CartanTests JuliaBase

namespace Tests.FlowGeometryTests

/-- Load a FlowGeometry golden file. -/
def load (name : String) : IO Json := readJson s!"oracle/golden/flowgeometry/{name}.json"

/-- A golden entry recording a Julia error other than `DomainError` (a Julia defect the port fixes
or replaces by its intent) is not compared; the `*_patched` goldens check the intent. -/
def skip : TestM Unit := pure ()

/-- The error message of a golden Julia exception, if it is one. -/
def errMsg? (j : Json) : Option String :=
  match j.getObjVal? "E" with
  | .ok (.str s) => some s
  | _ => none

/-- `true` for a golden `DomainError` (Lean must give `NaN`). -/
def isDomain (s : String) : Bool := s.startsWith "DomainError"

/-- Compare one float with a golden entry: bits, or `NaN` for a Julia `DomainError`; other
Julia errors are skipped. -/
def checkF (label : String) (got : Float) (want : Json) : TestM Unit := do
  match errMsg? want with
  | some m =>
    if isDomain m then check label got.isNaN fun _ => s!"Julia DomainError, got {fmt got}"
    else skip
  | none =>
    let w ← gFloat want
    check label (near exact got w) fun _ => s!"got {fmt got}, expected {fmt w}"

/-- Compare a float array with a golden array whose elements may be Julia errors (one check per
element). -/
def checkFs (label : String) (got : FloatArray) (want : Json) : TestM Unit := do
  match errMsg? want with
  | some m =>
    if isDomain m then check label (got.toList.any (·.isNaN)) fun _ => "Julia DomainError, no NaN"
    else skip
  | none =>
    let ws ← jArr want
    if ws.size != got.size then
      check label false fun _ => s!"length {got.size}, expected {ws.size}"
      return
    for i in [0:ws.size] do
      let w := ws[i]!
      let g := got[i]!
      match errMsg? w with
      | some m =>
        if isDomain m then check s!"{label}[{i}]" g.isNaN fun _ => s!"Julia DomainError, got {fmt g}"
        else skip
      | none =>
        let wf ← gFloat w
        check s!"{label}[{i}]" (near exact g wf) fun _ => s!"got {fmt g}, expected {fmt wf}"

/-- Compare integer lists (1-based Julia ids). -/
def checkNats (label : String) (got : Array (Array Nat)) (want : Json) : TestM Unit := do
  match errMsg? want with
  | some _ => skip
  | none =>
    let ws ← (← jArr want).mapM jNats
    check label (got == ws) fun _ => s!"got {got.toList.take 6}…, expected {ws.toList.take 6}…"

/-- Compare a string (skipping a Julia error). -/
def checkS (label : String) (got : String) (want : Json) : TestM Unit := do
  match errMsg? want with
  | some _ => skip
  | none =>
    let w ← jStr want
    check label (got == w) fun _ => s!"\n    got      {got}\n    expected {w}"

/-- Flatten homogeneous points. -/
def flatPoints {V : DirectSum.TensorBundle} (ps : Array (Grassmann.Chain V 1 Float)) : FloatArray :=
  ps.foldl (fun acc c => c.v.toArray.foldl FloatArray.push acc) .empty

end Tests.FlowGeometryTests
