import Adapode
import Tests.AbstractLattices.Harness

/-!
# Shared helpers for the Adapode golden tests

Goldens live in `oracle/golden/adapode/*.json` (written by `oracle/adapode/gen.jl`). Floats are IEEE
bit patterns `"0x…"`; states are flattened point by point. Long trajectories are summarized by
`digest`, word-wise FNV-1a over the bit patterns of all times and then all state coefficients
(`gen.jl` computes the same), so a match means every float of the trajectory is bit-identical.
-/

open Lean Tests.Small JuliaBase

namespace Tests.AdapodeTests

/-- Load an Adapode golden file. -/
def load (name : String) : IO Json := readJson s!"oracle/golden/adapode/{name}.json"

/-- Parse `"0x…"` hex bits. -/
def hexBits (s : String) : UInt64 :=
  (s.drop 2).foldl (fun acc c =>
    let d : UInt64 :=
      if '0' ≤ c ∧ c ≤ '9' then (c.toNat - '0'.toNat).toUInt64
      else if 'a' ≤ c ∧ c ≤ 'f' then (c.toNat - 'a'.toNat + 10).toUInt64
      else if 'A' ≤ c ∧ c ≤ 'F' then (c.toNat - 'A'.toNat + 10).toUInt64 else 0
    acc * 16 + d) 0

/-- A golden float. -/
def gFloat (j : Json) : TestM Float := do return Float.ofBits (hexBits (← jStr j))

/-- A golden float array. -/
def gFloats (j : Json) : TestM FloatArray := do
  let a ← jArr j
  a.foldlM (fun acc x => do return acc.push (← gFloat x)) (FloatArray.emptyWithCapacity a.size)

/-- A float array field of a golden object. -/
def gFloatsAt (j : Json) (k : String) : TestM FloatArray := do gFloats (← jField j k)

/-- A float field of a golden object. -/
def gFloatAt (j : Json) (k : String) : TestM Float := do gFloat (← jField j k)

/-- Julia's digits of a float, for messages. -/
def fmt (x : Float) : String := F64.showString x

/-- Word-wise FNV-1a of the bit patterns of `xs` then `ys` (the `digest` of `gen.jl`). -/
def digest (xs ys : FloatArray) : String :=
  let step (h : UInt64) (x : Float) : UInt64 := (h ^^^ x.toBits) * 0x100000001b3
  let h := ys.foldl step (xs.foldl step 0xcbf29ce484222325)
  let s := String.ofList (Nat.toDigits 16 h.toNat)
  "0x" ++ String.ofList (List.replicate (16 - s.length) '0') ++ s

/-- The float array of a range of indices of `a`. -/
def sub (a : FloatArray) (lo n : Nat) : FloatArray := Adapode.slice a lo n

/-- `a[i]` for every `i ≡ 0 (mod every)`, `k` floats at a time (Julia `X[1:every:end]` of
`k`-vectors). -/
def every (a : FloatArray) (k every : Nat) : FloatArray := Id.run do
  let n := a.size / k
  let mut out := FloatArray.emptyWithCapacity (n / every * k + k)
  let mut i := 0
  while i < n do
    for j in [0:k] do out := out.push (a.get! (i * k + j))
    i := i + every
  return out

/-- Bitwise equality of two floats (NaNs equal, `-0.0 ≠ 0.0`). -/
def same (x y : Float) : Bool := F64.isequal x y

/-- Compare two float arrays bit for bit. -/
def checkBits (label : String) (got want : FloatArray) : TestM Unit := do
  if got.size != want.size then
    check label false fun _ => s!"length {got.size}, expected {want.size}"
    return
  let bad := (List.range got.size).find? fun i => !same (got.get! i) (want.get! i)
  match bad with
  | none => check label true
  | some i => check label false fun _ =>
      s!"[{i}] got {fmt (got.get! i)}, expected {fmt (want.get! i)} ({F64.ulpDist (got.get! i) (want.get! i)} ulps)"

/-- Compare two float arrays within a relative tolerance (`|a - b| ≤ rtol·max(|a|,|b|) + atol`). -/
def checkClose (label : String) (got want : FloatArray) (rtol : Float) (atol : Float := 0) :
    TestM Unit := do
  if got.size != want.size then
    check label false fun _ => s!"length {got.size}, expected {want.size}"
    return
  let bad := (List.range got.size).find? fun i =>
    let a := got.get! i
    let b := want.get! i
    !((a - b).abs ≤ rtol * (if a.abs > b.abs then a.abs else b.abs) + atol)
  match bad with
  | none => check label true
  | some i => check label false fun _ =>
      s!"[{i}] got {fmt (got.get! i)}, expected {fmt (want.get! i)} (rtol {rtol})"

/-- Compare a float with a golden float bit for bit. -/
def checkFloat (label : String) (got : Float) (want : Json) : TestM Unit := do
  let w ← gFloat want
  check label (same got w) fun _ => s!"got {fmt got}, expected {fmt w}"

end Tests.AdapodeTests
