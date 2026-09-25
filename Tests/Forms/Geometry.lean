import Tests.Forms.Common

/-!
# Simplices, element operators, metrics, Cayley tables, rank-one forms and evaluation

* `simplex.json`: homogeneous simplices (2-D to 4-D): `affineframe`, `mean`,
  `barycenter`, `centroid`, `det`, the Cramer inverse, the barycentric `gradient`,
  `cofactor`, point-in-simplex `∈` and Cramer `\` on probes, display. Bit for bit, the
  display strings included except for the labels of Julia's subspace `↓V` (the port
  numbers the generators of the restricted space from 1: compared after relabelling).
* `spaces.json`: `metrictensor`, its second compound, `antimetrictensor`,
  `metricextensor` (`ℝⁿ`, `⟨+++⟩`, `⟨-++⟩`, `⟨2,3,5⟩`, conformal, origin-only,
  spacetime); the sandwich operators `operator(t, G)` of random chains of every grade and
  of a spinor; `alltex`, and the Cayley tables' display.
* `dyadic.json`: projectors, dyadics and their products, contractions, materialisations,
  traces and display (`rtol = 1e-12`: the normalisation `v/|v|`).
* `eval.json`: `t(y₁, …, y_k)`, `t(y)`, `M(y…)` and `vecdot`, exact.
-/

namespace Tests.FormsTests.GeometrySuite

open Lean Tests.Units Grassmann DirectSum StaticVectors Tests.FormsTests

/-- Replace Julia's subspace labels `v₂, v₃, …` (generators 2…n of `↓V`) by `v₁, v₂, …`
inside the parentheses (the inner elements); the outer labels are the domain's. -/
def relabel (s : String) : String :=
  let subs := #['₁', '₂', '₃', '₄', '₅', '₆', '₇', '₈', '₉']
  let (out, _) := s.toList.foldl (fun (acc : List Char × Nat) c =>
    let (out, depth) := acc
    let depth' := if c == '(' then depth + 1 else if c == ')' then depth - 1 else depth
    let c' := if depth > 0 then
        match subs.findIdx? (· == c) with
        | some i => if i ≥ 1 then subs[i - 1]! else c
        | none => c
      else c
    (c' :: out, depth')) ([], 0)
  String.ofList out.reverse

/-- One simplex case. -/
def simplexCase (t : Tally) (c : Json) (k : Nat) : Tally := Id.run do
  let pts := floatRows (fld c "pts")
  let n := pts.length
  let d := (pts.headD []).length
  let V := En n
  let W := En d
  let T : Simplex V W Float :=
    (TensorOperator.ofColumnList? (pts.map fun p => chainOf W 1 p)).getD TensorOperator.zero
  let w := fun (s : String) => fun (_ : Unit) => s!"simplex case {k} ({n} points in {d}) {s}"
  let mut t := t
  t := t.mat .bits (opRows T.affineframe) (fld c "affineframe") (w "affineframe")
  t := t.nums .bits (vals T.mean.v) (fld c "mean") (w "mean")
  t := t.nums .bits (vals T.barycenter.v) (fld c "barycenter") (w "barycenter")
  t := t.nums .bits (vals T.centroid.v) (fld c "centroid") (w "centroid")
  t := t.num .bits (.flt T.det) (fld c "det") (w "det")
  t := t.mat .bits (opRows T.inv) (fld c "inv") (w "inv")
  t := t.mat .bits (opRows T.gradient) (fld c "gradient") (w "gradient")
  t := t.mat .bits (opRows T.cofactor) (fld c "cofactor") (w "cofactor")
  let probes := floatRows (fld c "probes")
  let ins := arr (fld c "in")
  let sols := arr (fld c "solve")
  for (p, i) in probes.zipIdx do
    let v : Chain W 1 Float := chainOf W 1 p
    t := t.num .bits (.int (if T.contains v then 1 else 0)) (ins[i]!) (w s!"probe {i} ∈")
    t := t.nums .bits (vals (T.solve v).v) (sols[i]!) (w s!"probe {i} \\")
  t := t.str T.inv.showJulia (fld c "showInv") (w "show(inv)")
  match fld c "showGradient" with
  | .str g => t := t.ok (T.gradient.showJulia == relabel g) (w s!"show(gradient):\n got  {T.gradient.showJulia}\n want {relabel g}")
  | _ => t := t.skip
  return t

/-- One space case. -/
def spaceCase (t : Tally) (c : Json) (k : Nat) : Tally := Id.run do
  let V := spaceOf (fld c "space")
  let n := V.n
  let w := fun (s : String) => fun (_ : Unit) => s!"space case {k} {V} {s}"
  let mut t := t
  let g : Endomorphism V (.chain 1) Rat := metrictensor V
  t := t.mat .bits (opRows g) (fld c "metric") (w "metrictensor")
  if n ≥ 2 then t := t.mat .bits (opRows (g.compound 2)) (fld c "metric2") (w "metrictensor(V,2)")
  t := t.mat .bits (opRows (antimetrictensor (α := Rat) V)) (fld c "antimetric") (w "antimetrictensor")
  t := t.mat .bits (opRows (metricextensor (α := Rat) V).toOperator) (fld c "metricext") (w "metricextensor")
  if V.metric matches .diagonal _ then t := t.skip
  else t := t.str (metrictensor (α := Int) V).displayBody (fld c "displayMetric") (w "display(metrictensor)")
  for e in (arr (fld c "operators")).toList do
    let ops := arr (fld e "op")
    match (fld e "grade").getNat? with
    | .ok gr =>
      let tc : Chain V gr Int := chainOf V gr (ints (fld e "c"))
      for G in [1:n + 1] do
        t := t.mat .bits (opRows (operator tc G)) (ops[G - 1]!) (w s!"operator(grade {gr}, {G})")
    | .error _ =>
      let sp : Spinor V Int := (Half.ofList? (ints (fld e "spinor"))).getD Half.zero
      for G in [1:n + 1] do
        t := t.mat .bits (opRows (operator sp G)) (ops[G - 1]!) (w s!"operator(spinor, {G})")
  match fld c "alltex" with
  | .arr tex =>
    let mine := alltex V
    for (s, i) in mine.zipIdx do
      t := t.str s (tex[i]!) (w s!"alltex[{i}]")
  | _ => pure ()
  match fld c "cayleyFull" with
  | .str _ => t := t.str (cayley V .mul).displayBody (fld c "cayleyFull") (w "display(cayley)")
  | _ => pure ()
  match fld c "cayley1" with
  | .str _ => t := t.str (cayley V .mul (.chain 1)).displayBody (fld c "cayley1") (w "display(cayley(V,1))")
  | _ => t := t.skip  -- Julia's `cayley(V, 1)` of a `Signature` throws a `MethodError`
  return t

/-- One rank-one case. -/
def dyadicCase (t : Tally) (c : Json) (k : Nat) : Tally := Id.run do
  let x0 := flts (fld c "x")
  let n := x0.length
  let V := En n
  let x : Chain V 1 Float := chainOf V 1 x0
  let y : Chain V 1 Float := chainOf V 1 (flts (fld c "y"))
  let z : Chain V 1 Float := chainOf V 1 (flts (fld c "z"))
  let lam := match jnum (fld c "lam") with | some (.flt f) => f | _ => 0
  let P := Projector.ofVector x lam
  let P1 := Projector.ofVector x
  let D : Dyadic V 1 V 1 Float := ⟨x, y⟩
  let w := fun (s : String) => fun (_ : Unit) => s!"dyadic case {k} {s}"
  let m : Mode := .approx 1e-12
  let mut t := t
  t := t.nums m (vals P.v.v) (fld c "Pv") (w "P.v")
  t := t.nums m (vals (P * z).v) (fld c "Pz") (w "P(z)")
  t := t.nums m (vals (z ⋅ P : Chain V 1 Float).v) (fld c "zP") (w "z⋅P")
  t := t.num m (.flt (Forms.vdot (P * z).v z.v)) (fld c "Pzz") (w "P(z,z)")
  t := t.mat m (opRows P.toOperator) (fld c "PChain") (w "Chain(P)")
  t := t.num m (.flt P.tr) (fld c "Ptr") (w "tr(P)")
  t := t.nums .bits (vals (D * z).v) (fld c "Dz") (w "D(z)")
  t := t.nums .bits (vals (z ⋅ D : Chain V 1 Float).v) (fld c "zD") (w "z⋅D")
  t := t.num .bits (.flt (Forms.vdot (D * z).v z.v)) (fld c "Dzz") (w "D(z,z)")
  t := t.num .bits (.flt D.tr) (fld c "Dtr") (w "tr(D)")
  t := t.mat .bits (opRows D.toOperator) (fld c "DChain") (w "Chain(D)")
  let DD : Dyadic V 1 V 1 Float := D ⋅ D
  t := t.nums .bits (vals DD.x.v) (fld (fld c "DD") "x") (w "(D⋅D).x")
  t := t.nums .bits (vals DD.y.v) (fld (fld c "DD") "y") (w "(D⋅D).y")
  let PD : Dyadic V 1 V 1 Float := P ⋅ D
  t := t.nums m (vals PD.x.v) (fld (fld c "PD") "x") (w "(P⋅D).x")
  t := t.nums m (vals PD.y.v) (fld (fld c "PD") "y") (w "(P⋅D).y")
  let DP : Dyadic V 1 V 1 Float := D ⋅ P
  t := t.nums m (vals DP.x.v) (fld (fld c "DP") "x") (w "(D⋅P).x")
  t := t.nums m (vals DP.y.v) (fld (fld c "DP") "y") (w "(D⋅P).y")
  let PP : Dyadic V 1 V 1 Float := P1 ⋅ P1
  t := t.nums m (vals PP.x.v) (fld (fld c "PP") "x") (w "(P⋅P).x")
  t := t.nums m (vals PP.y.v) (fld (fld c "PP") "y") (w "(P⋅P).y")
  t := t.str (toString P) (fld c "showP") (w "show(P)")
  t := t.str (toString P1) (fld c "showP1") (w "show(Proj(x))")
  t := t.str (toString D) (fld c "showD") (w "show(D)")
  return t

/-- One evaluation case. -/
def evalCase (t : Tally) (c : Json) (k : Nat) : Tally := Id.run do
  let V := spaceOf (fld c "space")
  let g := (fld c "g").getNat?.toOption.getD 1
  let tc : Chain V g Int := chainOf V g (ints (fld c "t"))
  let ys : List (Chain V 1 Int) := (arr (fld c "ys")).toList.map fun y => chainOf V 1 (ints y)
  let M : Multivector V Int := mvOf V (ints (fld c "m"))
  let w := fun (s : String) => fun (_ : Unit) => s!"eval case {k} {V} g={g} {s}"
  let mut t := t
  t := t.nums .bits (vals (tc.eval ys).v) (fld c "eval") (w "t(y…)")
  t := t.nums .bits (vals (tc.eval (ys.take 1)).v) (fld c "eval1") (w "t(y₁)")
  -- Julia returns a scalar-kind result when only the scalar part survives
  let mv := M.eval ys
  if (arr (fld c "evalM")).size == 1 then
    t := t.ok (mv.v.toList.drop 1 |>.all (· == 0)) (w "M(y…) is a scalar")
    t := t.nums .bits [.int mv.scalarValue] (fld c "evalM") (w "M(y…)")
  else
    t := t.nums .bits (vals mv.v) (fld c "evalM") (w "M(y…)")
  t := t.num .bits (.int (vecdot tc tc)) (fld c "vecdot") (w "vecdot(t,t)")
  t := t.num .bits (.int (vecdot M tc)) (fld c "vecdotM") (w "vecdot(M,t)")
  t := t.num .bits (.int (vecdot M M)) (fld c "vecdotMM") (w "vecdot(M,M)")
  return t

/-- Run the suite. -/
def suite : IO Tally := do
  let js ← load "simplex"
  let t := (cases js).toList.zipIdx.foldl (fun t (c, k) => simplexCase t c k) (Tally.new "forms/geometry")
  let jp ← load "spaces"
  let t := (cases jp).toList.zipIdx.foldl (fun t (c, k) => spaceCase t c k) t
  let jd ← load "dyadic"
  let t := (cases jd).toList.zipIdx.foldl (fun t (c, k) => dyadicCase t c k) t
  let je ← load "eval"
  return (cases je).toList.zipIdx.foldl (fun t (c, k) => evalCase t c k) t

end Tests.FormsTests.GeometrySuite
