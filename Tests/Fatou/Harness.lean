import Fatou
import Lean.Data.Json

/-!
Test harness for the Fatou suites: a pass/fail tally, JSON field access, hexadecimal float
bits, ulp distances, FNV-1a hashes, and readers for the raw little-endian raster dumps of
`oracle/fatou/gen.jl` (`oracle/golden/fatou/`).
-/

namespace Tests.Fatou

open _root_.Fatou

/-- Running tally of a suite. -/
structure Tally where
  /-- passing checks -/
  passed : Nat := 0
  /-- failing checks -/
  failed : Nat := 0

/-- Test monad: a tally threaded through `IO`. -/
abbrev TestM := StateT Tally IO

/-- Failures beyond this many are counted but not printed. -/
def maxPrinted : Nat := 30

/-- Record one check; `detail` is only forced on failure. -/
def check (label : String) (ok : Bool) (detail : Unit → String := fun _ => "") : TestM Unit := do
  if ok then modify fun t => { t with passed := t.passed + 1 }
  else
    let t ← get
    if t.failed < maxPrinted then IO.eprintln s!"  FAIL {label}: {detail ()}"
    set { t with failed := t.failed + 1 }

/-- Equality check printing both sides on failure. -/
def checkEq {α : Type} [BEq α] [ToString α] (label : String) (got expected : α) : TestM Unit :=
  check label (got == expected) fun _ => s!"got {got}, expected {expected}"

/-- Informational line (not a check). -/
def note (msg : String) : TestM Unit := IO.println s!"  {msg}"

/-- Golden directory, relative to the repository root where `lake test` runs. -/
def goldenDir : System.FilePath := "oracle" / "golden" / "fatou"

/-- Load a golden JSON file. -/
def readJson (name : String) : IO Lean.Json := do
  let path := goldenDir / name
  match Lean.Json.parse (← IO.FS.readFile path) with
  | .ok j => return j
  | .error e => throw <| IO.userError s!"{path}: {e}"

/-- Field access (throws with the field name). -/
def field (j : Lean.Json) (k : String) : IO Lean.Json :=
  match j.getObjVal? k with
  | .ok v => return v
  | .error _ => throw <| IO.userError s!"missing field {k}"

/-- Array value. -/
def arr (j : Lean.Json) : IO (Array Lean.Json) :=
  match j.getArr? with
  | .ok v => return v
  | .error e => throw <| IO.userError e

/-- String value. -/
def str (j : Lean.Json) : IO String :=
  match j.getStr? with
  | .ok v => return v
  | .error e => throw <| IO.userError e

/-- Natural-number value. -/
def nat (j : Lean.Json) : IO Nat :=
  match j.getNat? with
  | .ok v => return v
  | .error e => throw <| IO.userError e

/-- Bool value. -/
def bool (j : Lean.Json) : IO Bool :=
  match j.getBool? with
  | .ok v => return v
  | .error e => throw <| IO.userError e

/-- `j[k]` as a string / natural / bool / array. -/
def gStr (j : Lean.Json) (k : String) : IO String := do str (← field j k)
/-- natural field -/
def gNat (j : Lean.Json) (k : String) : IO Nat := do nat (← field j k)
/-- bool field -/
def gBool (j : Lean.Json) (k : String) : IO Bool := do bool (← field j k)
/-- array field -/
def gArr (j : Lean.Json) (k : String) : IO (Array Lean.Json) := do arr (← field j k)

/-- Parse hexadecimal digits. -/
def parseHex (s : String) : Option Nat :=
  s.foldl (fun acc c => acc.bind fun n =>
    if '0' ≤ c && c ≤ '9' then some (16 * n + (c.toNat - '0'.toNat))
    else if 'a' ≤ c && c ≤ 'f' then some (16 * n + (c.toNat - 'a'.toNat + 10))
    else if 'A' ≤ c && c ≤ 'F' then some (16 * n + (c.toNat - 'A'.toNat + 10))
    else none) (some 0)

/-- A float from its hexadecimal bit pattern. -/
def hexF (j : Lean.Json) : IO Float := do
  let s ← str j
  match parseHex s with
  | some n => return Float.ofBits n.toUInt64
  | none => throw <| IO.userError s!"bad hex {s}"

/-- A complex number from `[re, im]` hex bit patterns. -/
def hexC (j : Lean.Json) : IO C64 := do
  let a ← arr j
  return ⟨← hexF a[0]!, ← hexF a[1]!⟩

/-- Float field / complex field / float-array field. -/
def gF (j : Lean.Json) (k : String) : IO Float := do hexF (← field j k)
/-- complex field -/
def gC (j : Lean.Json) (k : String) : IO C64 := do hexC (← field j k)
/-- float-array field -/
def gFs (j : Lean.Json) (k : String) : IO (Array Float) := do (← gArr j k).mapM hexF

/-- Bitwise float equality with every NaN equal. -/
def sameF (x y : Float) : Bool := (x.isNaN && y.isNaN) || x.toBits == y.toBits

/-- Bitwise complex equality with NaN parts equal. -/
def sameC (z w : C64) : Bool := sameF z.re w.re && sameF z.im w.im

/-- Distance in units in the last place (`0` for bit-equal or both NaN, huge across signs). -/
def ulps (x y : Float) : Nat :=
  if sameF x y || x == y then 0
  else if x.isNaN || y.isNaN then 1000000000000
  else
    let key (v : Float) : Int :=
      let b := v.toBits.toNat
      if b ≥ 2 ^ 63 then -((b - 2 ^ 63 : Nat) : Int) else (b : Int)
    (key x - key y).natAbs

/-- `x ≈ y` within `n` ulps, or within `atol` absolutely. -/
def closeF (x y : Float) (n : Nat := 4) (atol : Float := 0) : Bool :=
  ulps x y ≤ n || (x - y).abs ≤ atol

/-- Complex version of `closeF`, part by part. -/
def closeC (z w : C64) (n : Nat := 4) (atol : Float := 0) : Bool :=
  closeF z.re w.re n atol && closeF z.im w.im n atol

/-- Julia `string(x, base = 16, pad = 16)` of a float's bits. -/
def hexOf (x : Float) : String :=
  let ds := Nat.toDigits 16 x.toBits.toNat
  String.ofList (List.replicate (16 - ds.length) '0' ++ ds)

/-- FNV-1a 64 of a byte array, as 16 hex digits. -/
def fnv1a (b : ByteArray) : String :=
  let h := b.foldl (fun (h : UInt64) (x : UInt8) => (h ^^^ x.toUInt64) * 0x100000001b3) 0xcbf29ce484222325
  let ds := Nat.toDigits 16 h.toNat
  String.ofList (List.replicate (16 - ds.length) '0' ++ ds)

/-- Little-endian bytes of a float array (the layout of the `.f64` dumps). -/
def floatBytes (a : FloatArray) : ByteArray :=
  a.foldl (init := ByteArray.emptyWithCapacity (8 * a.size)) fun acc x =>
    let u := x.toBits
    (List.range 8).foldl (fun acc k => acc.push (u >>> (8 * k).toUInt64).toUInt8) acc

/-- Read a raw little-endian `Float64` dump. -/
def readF64 (name : String) : IO FloatArray := do
  let b ← IO.FS.readBinFile (goldenDir / name)
  let n := b.size / 8
  return floatArrayOfFn n fun i =>
    Float.ofBits ((List.range 8).foldl (fun (u : UInt64) k =>
      u ||| (b[8 * i + k]!.toUInt64 <<< (8 * k).toUInt64)) 0)

/-- Read a raw little-endian `UInt16` dump (kept as bytes, the layout of `FilledSet.iter`). -/
def readU16 (name : String) : IO ByteArray := IO.FS.readBinFile (goldenDir / name)

end Tests.Fatou
