import Similitude
import Tests.FieldAlgebra.Harness

/-!
# Shared decoders for the Similitude golden tests

Goldens are written by `oracle/similitude/gen.jl`: exponent vectors are
space-separated strings of integers, `p/q` rationals or `0x…` float bits; Julia
numbers are `["I", "3"]`, `["R", "1/3"]` or `["F", "0x…"]`; floats are bit
patterns.
-/

namespace Tests.SimilitudeTests

open Lean Tests.Units FieldConstants FieldAlgebra UnitSystems Similitude

/-- Parse `"3"`, `"-1/2"` (exact) or `"0x…"` (float) exponent tokens. -/
def expoTok (s : String) : Expo :=
  if s.startsWith "0x" then .float (Float.ofBits (hexU64 s))
  else match s.splitOn "/" with
    | [a, b] => .rat (Rat.divInt (a.toInt?.getD 0) (b.toInt?.getD 1))
    | _ => .int (s.toInt?.getD 0)

/-- Parse a space-separated exponent vector of length `n`. -/
def expsOfStr (n : Nat) (s : String) : Exps n :=
  let es := ((s.splitOn " ").filter (· ≠ "")).toArray.map expoTok
  if es.any (fun e => match e with | .float _ => true | _ => false) then
    .float (FVec.ofFn fun i => (es[i.1]?.getD (.int 0)).toFloat)
  else
    .exact (Vector.ofFn fun i => match es[i.1]?.getD (.int 0) with
      | .int k => (k : Rat) | .rat q => q | .float _ => 0)

/-- Rational exponents of a space-separated exact vector. -/
def ratsOfStr (s : String) : List Rat :=
  ((s.splitOn " ").filter (· ≠ "")).map fun t => match expoTok t with
    | .int k => (k : Rat) | .rat q => q | .float x => (x.toInt64.toInt : Rat)

/-- Decode a Julia number `["I", …]`, `["R", "p/q"]`, `["F", "0x…"]`. -/
def scalarOf (j : Json) : Scalar :=
  match str (idx j 0) with
  | "I" => .ofInt ((str (idx j 1)).toInt?.getD 0)
  | "R" => match (str (idx j 1)).splitOn "/" with
    | [a, b] => .rat (Rat.divInt (a.toInt?.getD 0) (b.toInt?.getD 1))
    | _ => .ofInt 0
  | _ => .ofFloat (hexFloat (idx j 1))

/-- Decode a coefficient. -/
def coefOf (j : Json) : Coef :=
  match scalarOf j with
  | .num (.int n) => .int n.toInt
  | .num (.float x) => .float x
  | .rat q => .rat q
  | .grp _ => .int 1

/-- Decode a constants group `[exps, coef]`. -/
def constsOf (j : Json) : Consts := Group.mk' (expsOfStr 44 (str (idx j 0))) (coefOf (idx j 1))

/-- A golden float given as `"0x…"` bits, or `none` for `"ERROR"`. -/
def goldFloat? (j : Json) : Option Float :=
  let s := str j
  if s.startsWith "0x" then some (Float.ofBits (hexU64 s)) else none

/-- Julia system names as the goldens spell them (`IAU☉` is `Sys.IAU`). -/
def sysOf! (s : String) : Sys := (Sys.ofName? s).getD .Metric

end Tests.SimilitudeTests
