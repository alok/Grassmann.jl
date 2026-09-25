import Tests.Adapode.Common

/-!
# `constants.jl` tables and the `TimeStep` controller against Julia (`tables.json`)

Every entry of `CB`, `CBA` (stage rows, advancing weights, error weights `b - c`), `CAB`, `CAM` and
`Gauss`, the stage times `sum(aₗ)`, and the fields of `TimeStep(h)`, bit for bit.
-/

open Lean Tests.Small JuliaBase Adapode

namespace Tests.AdapodeTests.Tables

/-- The rows of a `Float` tableau as Julia lists them: the stage rows, `b`, and (adaptive) `db`. -/
def rowsOf (T : Tableau) : FloatArray :=
  let b := T.b.toList
  let db := T.db.toList
  ⟨(T.a.toList ++ b ++ db).toArray⟩

/-- A row of a Julia table: an array of floats, or a bare float (Julia's `Values(Values(1))` is
`Values(1)`, so `CBA[1]`'s one-entry stage row is the number itself). -/
def gRow (j : Json) : TestM FloatArray :=
  match j with
  | .str _ => do return FloatArray.empty.push (← gFloat j)
  | _ => gFloats j

/-- Compare a tableau with Julia's `rows` (flattened) and stage times `c`. -/
def checkTableau (label : String) (T : Tableau) (g : Json) : TestM Unit := do
  let rows ← (← gArr g "rows").mapM gRow
  let flat := rows.foldl (fun acc r => r.foldl (·.push ·) acc) FloatArray.empty
  -- Julia's CB[1] has an empty first row; `rowsOf` has none
  checkBits s!"{label} rows" (rowsOf T) flat
  -- `c[0] = 0` is not a row sum, except for Euler, whose only row is Julia's empty `Values{0}()`
  checkBits s!"{label} c" (if T.s == 1 then T.c else sub T.c 1 (T.c.size - 1)) (← gFloatsAt g "c")

/-- Run the table checks. -/
def run : TestM Unit := do
  let j ← load "tables"
  let cb ← gArr j "CB"
  for o in [1, 2, 3, 4] do checkTableau s!"CB[{o}]" (CB o) cb[o - 1]!
  let cba ← gArr j "CBA"
  for o in [1, 2, 3, 4, 5] do checkTableau s!"CBA[{o}]" (CBA o) cba[o - 1]!
  let cab ← gArr j "CAB"
  let cam ← gArr j "CAM"
  for k in [1, 2, 3, 4, 5] do
    checkBits s!"CAB[{k}]" (CAB k) (← gFloats cab[k - 1]!)
    checkBits s!"CAM[{k}]" (CAM k) (← gFloats cam[k - 1]!)
  let gauss ← gArr j "Gauss"
  for n in [1, 2, 3, 4] do
    let g := gauss[n - 1]!
    let R := Gauss n
    checkBits s!"Gauss[{n}] w" R.w (← gFloatsAt g "w")
    -- Julia's `Gauss[1][2]` is the point itself: `Values(Values(1,1)/3)` copies its argument
    let raw ← gArr g "pts"
    let pts ← if n == 1 then pure #[← gFloats (Json.arr raw)] else raw.mapM gFloats
    checkBits s!"Gauss[{n}] r" R.r ⟨pts.map (·.get! 0)⟩
    checkBits s!"Gauss[{n}] s" R.s ⟨pts.map (·.get! 1)⟩
  for c in ← gArr j "TimeStep" do
    let h ← gFloatAt c "h"
    let t := TimeStep.new h
    checkBits s!"TimeStep({fmt h})" ⟨#[t.h, t.hmin, t.hmax, t.emin, t.emax, t.e]⟩ (← gFloatsAt c "fields")
  -- the corrected pairs differ from Julia's exactly where the typos are
  check "Fehlberg fixed a63" ((CBA.fixed 3).a.get! 12 == -(CBA 3).a.get! 12)
  check "Cash-Karp fixed a41" ((CBA.fixed 4).a.get! 3 == 0.3 && (CBA 4).a.get! 3 == 0.075)

end Tests.AdapodeTests.Tables
