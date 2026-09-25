import Tests.JuliaBase.Util

/-!
Julia ranges against the oracle (`Tests/JuliaBase/range.json`): every element of
`range(a, b, length=n)`, `LinRange(a, b, n)`, `range(ia, ib, length=n)` for integers,
`a:st:b`, `range(a; step, length)`, and the scalar/broadcast range arithmetic
(`x * r`, `x .* r`, `r ./ x`, `r .+ x`, `r / x`), compared bit for bit.
-/

open JuliaBase

namespace Tests.JuliaBase.Range

/-- Compare a computed range with the oracle's comma-separated hex elements. -/
def checkElems (t : Tally) (what : String) (got : FloatArray) (want : String) : Tally :=
  let ws := if want.isEmpty then [] else want.splitOn ","
  let wf := ws.map floatOfHex
  if got.size != ws.length then
    t.check false fun _ => s!"{what}: length {got.size}, want {ws.length}"
  else
    let bad := (List.range got.size).find? fun i =>
      match wf[i]! with
      | some w => !sameFloat got[i]! w
      | none => true
    match bad with
    | none => t.check true fun _ => ""
    | some i => t.check false fun _ =>
      s!"{what}: element {i + 1} got {F64.showString got[i]!}, want {(wf[i]!).map F64.showString}"

/-- Compare a computed `Float32` range with the oracle's hex elements. -/
def checkElems32 (t : Tally) (what : String) (got : Array Float32) (want : String) : Tally :=
  let ws := if want.isEmpty then [] else want.splitOn ","
  let wf := ws.map float32OfHex
  if got.size != ws.length then
    t.check false fun _ => s!"{what}: length {got.size}, want {ws.length}"
  else
    let bad := (List.range got.size).find? fun i =>
      match wf[i]! with
      | some w => !((got[i]!.isNaN && w.isNaN) || got[i]!.toBits == w.toBits)
      | none => true
    match bad with
    | none => t.check true fun _ => ""
    | some i => t.check false fun _ =>
      s!"{what}: element {i + 1} got {F32.showString got[i]!}, want {(wf[i]!).map F32.showString}"

/-- Check one range row. -/
def checkRow (t : Tally) (row : List String) : Tally :=
  let f (h : String) : Float := (floatOfHex h).getD 0
  let f32 (h : String) : Float32 := (float32OfHex h).getD 0
  let n (s : String) : Nat := s.toNat!
  match row with
  | ["range32", a, b, len, e] =>
    checkElems32 t s!"range({f32 a}, {f32 b}, {len}) :: Float32"
      (range32 (f32 a) (f32 b) (n len)).toArray e
  | ["linrange32", a, b, len, e] =>
    checkElems32 t s!"LinRange({f32 a}, {f32 b}, {len}) :: Float32"
      ((Array.range (n len)).map fun (i : Nat) => linRange32Get (f32 a) (f32 b) (n len) ((i : Int) + 1)) e
  | ["range", a, b, len, e] => checkElems t s!"range({f a}, {f b}, {len})" (JuliaBase.range (f a) (f b) (n len)).toFloatArray e
  | ["linrange", a, b, len, e] => checkElems t s!"LinRange({f a}, {f b}, {len})" (LinRange.mk' (f a) (f b) (n len)).toFloatArray e
  | ["rangeint", a, b, len, e] => checkElems t s!"range({a}, {b}, {len})" (rangeInt a.toInt! b.toInt! (n len)).toFloatArray e
  | ["colon", a, st, b, e] => checkElems t s!"{f a}:{f st}:{f b}" (colon (f a) (f st) (f b)).toFloatArray e
  | ["rangestep", a, st, len, e] => checkElems t s!"range({f a}; step={f st}, length={len})" (rangeStep (f a) (f st) (n len)).toFloatArray e
  | [op, a, b, len, x, e] =>
    let r := JuliaBase.range (f a) (f b) (n len)
    let r' : Option StepRangeLen :=
      match op with
      | "mul" => some (r.mulFloat (f x))
      | "bmul" => some (StepRangeLen.bcastMul (f x) r)
      | "bdiv" => some (r.bcastDiv (f x))
      | "badd" => some (r.bcastAdd (f x))
      | "div" => some (r.divFloat (f x))
      | _ => none
    match r' with
    | some r' => checkElems t s!"{op} {f x} range({f a}, {f b}, {len})" r'.toFloatArray e
    | none => t.check false fun _ => s!"unknown range op {op}"
  | r => t.check false fun _ => s!"malformed range row {r.take 4}"

/-- The committed golden `range.json`. -/
def golden : IO (Nat × Nat) := do
  let j ← loadGolden "range.json"
  let mut t : Tally := {}
  for row in jArr j "cases" do t := checkRow t (jRow row)
  t.report "range golden"

/-- The TSV fuzz file `PREFIX_range.tsv`. -/
def fuzz (path : System.FilePath) : IO (Nat × Nat) := do
  let mut t : Tally := {}
  for row in ← readTsv path do t := checkRow t row
  t.report "range fuzz"

/-! Compile-time checks. -/

-- `range(0.1, 1.1, length=11)` hits the rational path: every element is the nearest double,
-- while `LinRange` computes `(1-t)*a + t*b` directly (oracle: `0.3` vs `0.30000000000000004`)
#guard (JuliaBase.range 0.1 1.1 11).get 3 == 0.3
#guard (LinRange.mk' 0.1 1.1 11).get 3 == 0.30000000000000004
#guard (JuliaBase.range 0.1 1.1 11).get 6 == 0.6 && (LinRange.mk' 0.1 1.1 11).get 6 == 0.6000000000000001
#guard (colon 0 0.1 1).len == 11 && (colon 0 0.1 1).last == 1.0
#guard rat 0.1 == (1, 10) && rat (-0.5) == (1, -2)

end Tests.JuliaBase.Range
