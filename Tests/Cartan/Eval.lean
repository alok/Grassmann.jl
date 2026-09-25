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
  -- the axis-by-axis resampling has the bits of the point-by-point one
  let bits {M F : Type} [FrameBundle M] [FlatFiber F] {m : M} (t : TensorField m F) : List UInt64 :=
    t.data.toList.map Float.toBits
  let sameResample {N : Nat} {P F : Type} [FlatFiber F] [LinearFiber F] {b : GridBundle N P}
      (label : String) (t : TensorField b F) (n : Vector Nat N) : TestM Unit := do
    let brk := TensorField.resampleBrackets b n
    check s!"{label} inside" (brk.toArray.all (·.all (· != 0)))
    checkEq s!"{label} = pointwise" (bits (t.resample n)) (bits (t.resamplePointwise n brk))
  let g2 : GridBundle 2 (AffinePoint 2) := .ofSpace (.ofAxes #v[Axis.range 0 1 37, Axis.range (-1) 2 23])
  let s2 := TensorField.tabulate2 g2 fun x y => Float.sin (3 * x) * Float.exp y + poly (x * y)
  sameResample "resample scalar 37×23 → 50×17" s2 #v[50, 17]
  sameResample "resample scalar 37×23 → 7×61" s2 #v[7, 61]
  let v2 : TensorField g2 (Chain ℝ3 1 Float) := TensorField.tabulate2 g2 fun x y =>
    Chain.ofFn fun i => #[Float.cos (x + y), y * x, poly y][i.1]!
  sameResample "resample chain 37×23 → 29×41" v2 #v[29, 41]
  let g3' : GridBundle 3 (AffinePoint 3) :=
    .ofSpace (.ofAxes #v[Axis.range 0 2 9, Axis.linRange 0 3 7, Axis.range 0 1 5])
  let s3 := TensorField.tabulate3 g3' fun x y z => poly x + Float.sin (10 * y) + 100 * poly z
  sameResample "resample 3-D 9×7×5 → 13×4×8" s3 #v[13, 4, 8]
  let s1 := TensorField.ofAxisFn (Axis.colon 0 0.1 3) fun x => Float.exp (-x) * poly x
  sameResample "resample 1-D 31 → 100" s1 #v[100]
  -- `eval1`/`eval2` inside the grid have the bits of `eval`; outside they defer to it
  let pts : List Float := [-0.5, 0, 1e-3, 0.37, 0.5, 0.999, 1, 1.4, 2.9, 3, 3.2, (0 : Float) / 0]
  let pairs : List (Float × Float) := pts.flatMap fun x => pts.map fun y => (x, y)
  let bitsOf {F : Type} [FlatFiber F] (x : F) : List UInt64 :=
    (FlatFiber.push FloatArray.empty x).toList.map Float.toBits
  checkEq "eval1 = eval" (pts.map fun x => (s1.eval1 x).toBits) (pts.map fun x => (s1.eval #v[x]).toBits)
  checkEq "eval2 = eval (scalar)" (pairs.map fun (x, y) => (s2.eval2 x y).toBits)
    (pairs.map fun (x, y) => (s2.eval #v[x, y]).toBits)
  checkEq "eval2 = eval (chain)" (pairs.map fun (x, y) => bitsOf (v2.eval2 x y))
    (pairs.map fun (x, y) => bitsOf (v2.eval #v[x, y]))
  checkEq "eval2 = eval (torus)" (pairs.map fun (x, y) => (fT2.eval2 (4 * x) (2 * y)).toBits)
    (pairs.map fun (x, y) => (fT2.eval #v[4 * x, 2 * y]).toBits)
  -- the guessed search counts as the bisection on ascending ranges, at and between the points
  for a in [Axis.range 0 1 1000, Axis.colon (-3) 0.1 7, Axis.linRange (-1) 2 37, Axis.range 5 6 2] do
    let c := a.toFloatArray
    let n := c.size
    let ts := (List.range (4 * n + 8)).map fun k =>
      let q := (Float.ofNat k - 4) / 4
      c.get! 0 + (c.get! (n - 1) - c.get! 0) * q / Float.ofNat (n - 1)
    let ts := ts ++ c.toList ++ [(0 : Float) / 0, 1e300, -1e300]
    check s!"countBelowAsc = countBelow on {a}" (ts.all fun t =>
      Interp.countBelowAsc c t == Interp.countBelow c t 0 n)

end Tests.CartanTests.Eval
