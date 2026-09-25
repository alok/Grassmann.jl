import Tests.JuliaBase.Util

/-!
Julia `show`/`print` of non-float scalars against the oracle (`Tests/JuliaBase/show.json`):
`Int`, `Bool`, `Rational`, `Complex{Int,Float64,Float32,Rational}`, `Complex{Bool}`,
unsigned integers and `Float32`, each in plain and `:compact => true` contexts. The oracle
file is keyed by an id; `values` rebuilds the same values in Lean.

Also checks the Leibniz `showvalue` coefficient rules (port-notes/leibniz.md §5.5 table) and
Grassmann `showterm` signs (port-notes/grassmann-types.md §5.2).
-/

open JuliaBase JuliaShow

namespace Tests.JuliaBase.Show

/-- `(show, compact show, print, compact print)` of a value. -/
def four {α : Type} [JuliaShow α] (x : α) : String × String × String × String :=
  (showString x, showCompact x, printString x, printCompact x)

/-- The oracle's values by id (see `SHOW_VALUES` in `gen_golden.jl`). -/
def values : List (String × (String × String × String × String)) := [
  ("int_0", four (0 : Int)), ("int_1", four (1 : Int)), ("int_m3", four (-3 : Int)),
  ("int_max", four (9223372036854775807 : Int)), ("int_min", four (-9223372036854775808 : Int)),
  ("bool_t", four true), ("bool_f", four false),
  ("rat_1_3", four ((1 : Rat) / 3)), ("rat_m1_3", four ((-1 : Rat) / 3)),
  ("rat_0", four (0 : Rat)), ("rat_2", four (2 : Rat)),
  ("ci_1_2", four (Complex.mk (1 : Int) 2)), ("ci_1_m2", four (Complex.mk (1 : Int) (-2))),
  ("ci_0_0", four (Complex.mk (0 : Int) 0)), ("ci_m1_m2", four (Complex.mk (-1 : Int) (-2))),
  ("cf_1_2", four (Complex.mk (1.0 : Float) 2.0)), ("cf_15_m25", four (Complex.mk (1.5 : Float) (-2.5))),
  ("cf_1_m0", four (Complex.mk (1.0 : Float) (-0.0))), ("cf_m0_0", four (Complex.mk (-0.0 : Float) 0.0)),
  ("cf_1_nan", four (Complex.mk (1.0 : Float) F64.nan)),
  ("cf_1_minf", four (Complex.mk (1.0 : Float) (-F64.inf))),
  ("cf_inf_inf", four (Complex.mk F64.inf F64.inf)),
  ("cf_third", four (Complex.mk ((1 : Float) / 3) ((2 : Float) / 3))),
  ("cf32_15_2", four (Complex.mk (1.5 : Float32) 2)),
  ("cr_half_third", four (Complex.mk ((1 : Rat) / 2) ((1 : Rat) / 3))),
  ("u8_3", four (3 : UInt8)), ("u16_3", four (3 : UInt16)), ("u32_3", four (3 : UInt32)),
  ("u64_42", four (42 : UInt64)),
  ("cb_im", four (Complex.mk false true)), ("cb_tt", four (Complex.mk true true)),
  ("f32_15", four (1.5 : Float32)), ("f32_nan", four (Float32.ofBits 0x7FC00000)),
  ("f32_minf", four (Float32.ofBits 0xFF800000))]

/-- The committed golden `show.json`. -/
def golden : IO (Nat × Nat) := do
  let j ← loadGolden "show.json"
  let mut t : Tally := {}
  for row in jArr j "cases" do
    let get (k : String) := jStr (row.getObjValD k)
    let id := get "id"
    match values.lookup id with
    | none => t := t.check false fun _ => s!"no Lean value for {id}"
    | some (s, c, p, pc) =>
      t := t.check (s == get "show") fun _ => s!"{id} show: got {s}, want {get "show"}"
      t := t.check (c == get "compact") fun _ => s!"{id} compact: got {c}, want {get "compact"}"
      t := t.check (p == get "print") fun _ => s!"{id} print: got {p}, want {get "print"}"
      t := t.check (pc == get "pcompact") fun _ => s!"{id} print compact: got {pc}, want {get "pcompact"}"
  t.report "show golden"

/-! Leibniz `showvalue` (without the blade label; port-notes/leibniz.md §5.5 goldens). -/

#guard showValue false (1 : Int) == "1"
#guard showValue false (-2 : Int) == "-2"
#guard showValue false (2.5 : Float) == "2.5"
#guard showValue false (-0.0 : Float) == "-0.0"
#guard showValue false F64.inf == "Inf*"
#guard showValue false F64.nan == "NaN*"
#guard showValue false true == "true*"
#guard showValue false false == "false*"
#guard showValue false ((1 : Rat) / 2) == "(1//2)"
#guard showValue false (Complex.mk (1 : Int) 2) == "(1 + 2im)"
#guard showValue false (Complex.mk (1.0 : Float) 0.0) == "(1.0 + 0.0im)"
#guard showValue false (1.5 : Float32) == "1.5f0"
#guard showValue false (3 : UInt8) == "0x03"

/-! Grassmann `showterm` (port-notes/grassmann-types.md §5.2, §5.4): the separator follows the
caller's compact flag, the value the `compactio` stream. -/

#guard showTerm false true (-0.0 : Float) == " - 0.0"
#guard showTerm false true ((-1 : Rat) / 2) == " - (1//2)"
#guard showTerm false true (Complex.mk (-1 : Int) (-2)) == " + (-1-2im)"
#guard showTerm false true (2 / 3 : Float) == " + 0.666667"
#guard showTerm false false (2 / 3 : Float) == " + 0.6666666666666666"
#guard showTerm true true (-3 : Int) == "-3"

end Tests.JuliaBase.Show
