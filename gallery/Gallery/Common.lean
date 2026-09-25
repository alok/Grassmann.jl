import LeanPlot
import Lean.Data.Json

/-!
# Gallery plumbing

* `Entry`: one gallery figure: a name (the file stem under `gallery/out/`,
  `docs/gallery/{lean,julia}/` and `oracle/gallery/`), its Julia source, and a builder that
  returns the LeanPlot `Figure` plus the numeric checks of its data against the Julia dump
  (`oracle/gallery/data/<name>.json`, written by `oracle/gallery/<name>.jl`).
* `Check`: one comparison (a label, pass/fail, and a human-readable detail such as
  `max |Δ| = 3.1e-16 over 7854 samples`).
* JSON accessors for the dumps (floats as JSON numbers, `"NaN"`/`"Inf"` strings allowed).
* Small numeric helpers (FNV-1a over little-endian `UInt16` counts, max relative deviation).
-/

namespace Gallery

open Lean

/-- One numeric comparison of Lean's plot data against Julia's. -/
structure Check where
  /-- what is compared -/
  label : String
  /-- within tolerance -/
  ok : Bool
  /-- the measured agreement, e.g. `max |Δ| = 2.2e-16 (1964 samples)` -/
  detail : String
  deriving Inhabited

/-- The result of building one gallery figure. -/
structure Outcome where
  /-- the LeanPlot figure -/
  fig : LeanPlot.Figure
  /-- comparisons with the Julia data dump -/
  checks : Array Check := #[]
  deriving Inhabited

/-- A gallery figure. -/
structure Entry where
  /-- file stem (`gallery/out/<name>.png`) -/
  name : String
  /-- one-line caption -/
  title : String
  /-- the Julia call it reproduces, with its source citation -/
  source : String
  /-- package group for the index (`Fatou`, `Grassmann`, `Wilkinson`) -/
  group : String
  /-- the upstream image (README/paper PNG) this figure reproduces, if any -/
  upstream : String := ""
  /-- build the figure; the argument is the parsed Julia dump if present -/
  build : Option Json → IO Outcome

/-! ## JSON accessors -/

/-- Field `k` of an object (`null` if absent). -/
def jget (j : Json) (k : String) : Json := (j.getObjVal? k).toOption.getD .null

/-- A JSON number or one of Julia's non-finite spellings as a float. -/
def jfloat (j : Json) : Float :=
  match j with
  | .num n => n.toFloat
  | .str "NaN" => 0.0 / 0.0
  | .str "Inf" => 1.0 / 0.0
  | .str "-Inf" => -1.0 / 0.0
  | _ => 0.0 / 0.0

/-- A JSON natural number (0 if not one). -/
def jnat (j : Json) : Nat := (j.getNat?).toOption.getD 0

/-- A JSON array (empty if not one). -/
def jarr (j : Json) : Array Json := (j.getArr?).toOption.getD #[]

/-- A JSON array of floats. -/
def jfloats (j : Json) : FloatArray := (jarr j).foldl (fun acc x => acc.push (jfloat x)) .empty

/-- A JSON array of naturals. -/
def jnats (j : Json) : Array Nat := (jarr j).map jnat

/-- A JSON string (empty if not one). -/
def jstr (j : Json) : String := (j.getStr?).toOption.getD ""

/-! ## Numeric helpers -/

/-- Scientific notation with 2 significant digits after the point (`3.1e-16`). -/
def sci (x : Float) : String :=
  if x == 0 then "0" else if x.isNaN then "NaN" else if x.isInf then "Inf" else
  let e := (Float.log10 x.abs).floor
  let m := x / Float.pow 10 e
  let (m, e) := if m.abs ≥ 9.995 then (m / 10, e + 1) else (m, e)
  let mi := (m * 100).round / 100
  let ms := toString mi
  -- `toString` of a float prints 6 decimals; trim to 3 significant digits
  let ms := match ms.splitOn "." with
    | [a, b] => a ++ "." ++ (b.take 2)
    | _ => ms
  s!"{ms}e{(if e < 0 then "-" else "")}{(e.abs.toUInt64.toNat)}"

/-- Largest `|a[i] - b[i]|` over the common prefix, NaN-aware (both NaN counts as equal, one NaN
as infinite). -/
def maxAbsDiff (a b : FloatArray) : Float :=
  let n := min a.size b.size
  go 0 n 0
where
  /-- the scan -/
  go (i n : Nat) (m : Float) : Float :=
    if i < n then
      let x := a[i]!
      let y := b[i]!
      let d := if x.isNaN && y.isNaN then 0 else if x.isNaN || y.isNaN then 1.0 / 0.0 else (x - y).abs
      go (i + 1) n (if d > m then d else m)
    else m
  termination_by n - i

/-- Largest `|a[i] - b[i]| / max(1, |b[i]|)` over the common prefix (a relative deviation
that degrades to absolute near zero). -/
def maxRelDiff (a b : FloatArray) : Float :=
  let n := min a.size b.size
  go 0 n 0
where
  /-- the scan -/
  go (i n : Nat) (m : Float) : Float :=
    if i < n then
      let x := a[i]!
      let y := b[i]!
      let s := if y.abs > 1 then y.abs else 1
      let d := if x.isNaN && y.isNaN then 0 else if x.isNaN || y.isNaN then 1.0 / 0.0 else (x - y).abs / s
      go (i + 1) n (if d > m then d else m)
    else m
  termination_by n - i

/-- A deviation check: `max rel |Δ| ≤ tol` over equally long arrays. -/
def closeCheck (label : String) (lean julia : FloatArray) (tol : Float) : Check :=
  let d := maxRelDiff lean julia
  let sizeOk := lean.size == julia.size
  { label, ok := sizeOk && d ≤ tol
    detail := if sizeOk then s!"max rel |Δ| = {sci d} over {julia.size} values (tol {sci tol})"
              else s!"sizes differ: Lean {lean.size}, Julia {julia.size}" }

/-- An exact equality check. -/
def eqCheck {α : Type} [BEq α] [ToString α] (label : String) (lean julia : α) : Check :=
  { label, ok := lean == julia, detail := if lean == julia then s!"equal ({julia})" else s!"Lean {lean} ≠ Julia {julia}" }

/-- Every `k`-th entry (from 0). -/
def every (a : FloatArray) (k : Nat) : FloatArray :=
  go 0 (FloatArray.emptyWithCapacity (a.size / k + 1))
where
  /-- the stride loop -/
  go (i : Nat) (acc : FloatArray) : FloatArray :=
    if h : i < a.size then go (i + max k 1) (acc.push a[i]) else acc
  termination_by a.size - i
  decreasing_by have := Nat.le_max_right k 1; omega

/-- Sum, NaN-skipping. -/
def sumFinite (a : FloatArray) : Float := a.foldl (fun s x => if x.isNaN then s else s + x) 0

/-- FNV-1a (64-bit) of little-endian `UInt16` values, Julia's `fnv` of the gallery dumps. -/
def fnv1aU16 (vals : Nat → Nat) (n : Nat) : UInt64 :=
  go 0 0xcbf29ce484222325
where
  /-- one value = two bytes -/
  go (i : Nat) (h : UInt64) : UInt64 :=
    if i < n then
      let v := vals i
      let h := (h ^^^ (v % 256).toUInt64) * 0x100000001b3
      let h := (h ^^^ ((v / 256) % 256).toUInt64) * 0x100000001b3
      go (i + 1) h
    else h
  termination_by n - i

/-- `0x…` spelling of a hash, 16 hex digits. -/
def hex16 (h : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 h.toNat)
  "0x" ++ "".pushn '0' (16 - s.length) ++ s

end Gallery
