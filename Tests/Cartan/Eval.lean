import Tests.Cartan.Common

/-!
# Evaluating grid fields (`oracle/golden/cartan/eval.json`)

Julia `t(x)` (multilinear interpolation, `grid.jl:98-456`) on polynomial fibers (bit-exact):
1-D open, torus, mirror and clamped intervals (repositioning through glued ends), a 2-D open grid
(zero outside, `NaN` in), a 2-D torus, a `Chain`-valued field, a 3-D grid and `resample`.
-/

open Lean Tests.Small Cartan JuliaBase Grassmann

namespace Tests.CartanTests.Eval

/-- Julia `poly(x) = x*x/7 - x/3`. -/
def poly (x : Float) : Float := x * x / 7 - x / 3

/-- A golden coordinate tuple (or a single coordinate). -/
def coordsOf (x : Json) : TestM (Array Float) :=
  match x with
  | .arr a => a.mapM gFloat
  | _ => do
    let v ← gFloat x
    pure #[v]

/-- A golden fiber value (flat), or a single float. -/
def valueOf (v : Json) : TestM FloatArray :=
  match v with
  | .arr _ => gFloats v
  | _ => do
    let y ← gFloat v
    pure (FloatArray.empty.push y)

/-- Check `f` at the golden coordinates. -/
def checkAt {N : Nat} (label : String) (j : Json) (f : Vector Float N → FloatArray) : TestM Unit := do
  let xs ← jArr (← jField j "x")
  let vs ← jArr (← jField j "v")
  check s!"{label} count" (xs.size == vs.size)
  for (x, v, i) in (xs.toList.zip vs.toList).zipIdx.map (fun ((x, v), i) => (x, v, i)) do
    let coords ← coordsOf x
    if h : coords.size = N then
      let want ← valueOf v
      checkFloats s!"{label}[{i}]" (f (Vector.ofFn fun a => coords[a.1]'(h ▸ a.2))) want
    else check s!"{label}[{i}] arity" false

/-- Run the evaluation checks. -/
def run : TestM Unit := do
  let c ← jField (← load "eval") "cases"
  let p1 := TensorField.ofAxisFn (Axis.colon 0 0.5 3) poly
  checkAt "eval open1" (← jField c "open1") fun x => flatOf [p1.eval x]
  let tor := Parameter.torus1 9
  let fT := (TensorField.ofArray? tor.base (tor.fiberArray.map poly)).get!
  checkAt "eval torus1" (← jField c "torus1") fun x => flatOf [fT.eval x]
  let mir := Parameter.mirror1 9
  let fM := (TensorField.ofArray? mir.base (mir.fiberArray.map poly)).get!
  checkAt "eval mirror1" (← jField c "mirror1") fun x => flatOf [fM.eval x]
  let cla := Parameter.clamped1 9
  let fC := (TensorField.ofArray? cla.base (cla.fiberArray.map poly)).get!
  checkAt "eval clamped1" (← jField c "clamped1") fun x => flatOf [fC.eval x]
  let g3 : GridBundle 2 (AffinePoint 2) := .ofSpace (.ofAxes #v[Axis.colon 0 0.5 1, Axis.colon 0 0.5 1])
  let gx := TensorField.tabulate2 g3 fun x y => x + 10 * y
  checkAt "eval open2" (← jField c "open2") fun x => flatOf [gx.eval x]
  let T2 := Parameter.torus #v[7, 9]
  let fT2 := T2.map fun p => poly (p.get! 0) + 2 * poly (p.get! 1)
  checkAt "eval torus2" (← jField c "torus2") fun x => flatOf [fT2.eval x]
  let vx : TensorField g3 (Chain ℝ3 1 Float) := TensorField.tabulate2 g3 fun x y =>
    Chain.ofFn fun i => #[x, y * x, 1 + y][i.1]!
  checkAt "eval chain2" (← jField c "chain2") fun x => flatOf [vx.eval x]
  let g33 : GridBundle 3 (AffinePoint 3) :=
    .ofSpace (.ofAxes #v[Axis.colon 0 1 2, Axis.colon 0 1 3, Axis.colon 0 1 1])
  let f3 := TensorField.tabulate3 g33 fun x y z => poly x + 10 * y + 100 * poly z
  checkAt "eval open3" (← jField c "open3") fun x => flatOf [f3.eval x]
  checkField "eval resample" (out (gx.resample #v[5, 4])) (← jField c "resample") (checkRange := false)

end Tests.CartanTests.Eval
