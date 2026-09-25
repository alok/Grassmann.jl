import UnitSystems
import Tests.FieldAlgebra.Harness

/-!
# Shared helpers for the UnitSystems golden tests

Golden numbers are encoded as `["I", "3"]` (Julia `Int64`), `["F", "0x…"]`
(`Float64` bits) or `["E", message]` (Julia threw). A Lean `Num` matches when the
kind agrees and the value is bit-identical (`exact`), or within the relative
tolerance `1e-12` (`close`).
-/

namespace Tests.UnitSystemsTests

open Lean Tests.Units FieldConstants UnitSystems

/-- Decoded golden number. -/
inductive GNum where
  | int (n : Int)
  | float (x : Float)
  | err (msg : String)

/-- Decode `["I", …]`, `["F", …]`, `["E", …]`. -/
def gnum (j : Json) : GNum :=
  match str (idx j 0) with
  | "I" => .int ((str (idx j 1)).toInt?.getD 0)
  | "F" => .float (hexFloat (idx j 1))
  | _ => .err (str (idx j 1))

/-- Printable form of a golden number. -/
def GNum.show : GNum → String
  | .int n => s!"{n}"
  | .float x => Julia.showFloat x
  | .err m => s!"ERROR({m})"

/-- Relative tolerance for float goldens. -/
def rtol : Float := 1e-12

/-- Kind-and-bits agreement. -/
def exactMatch (x : Num) : GNum → Bool
  | .int n => match x.v with | .int m => m.toInt == n | _ => false
  | .float f => match x.v with | .float y => sameBits y f | _ => false
  | .err _ => false

/-- Kind agreement and relative closeness. -/
def closeMatch (x : Num) : GNum → Bool
  | .int n => match x.v with | .int m => m.toInt == n | .float y => y == Float.ofInt n
  | .float f => Julia.closeRel x.toFloat f rtol
  | .err _ => false

/-- Record a numeric comparison in two suites: `s` (tolerance) and `e` (bit-exact). -/
def checkNum (s e : Suite) (x : Num) (g : GNum) (what : Unit → String) : Suite × Suite :=
  match g with
  | .err _ => (s, e)
  | _ =>
    let s := s.check (closeMatch x g) fun _ => s!"{what ()}: got {x} ({x.v.kind}), want {g.show}"
    let e := e.check (exactMatch x g) fun _ => s!"{what ()}: got {x} ({x.v.kind}), want {g.show}"
    (s, e)

/-- Julia `Systems` names → `Sys`. -/
def sysOf! (s : String) : Sys := (Sys.ofName? s).getD .Metric

end Tests.UnitSystemsTests
