import Wilkinson.Range
import Wilkinson.SyntaxTree

/-!
# Wilkinson: polynomial round-off analysis

Port of Wilkinson.jl 0.1.1 (`src/Wilkinson.jl`, `src/polynomial.jl`). For a
polynomial `f` written in some form (expanded, Horner, factored, …), Reed's
method samples a logarithmic grid `sc` of `3000` points spanning
`[log eps, log floatmax]` and computes the **Stieltjes bound**

`stj(x) = log|abs(f)|_T(x) - log x + log(callcount(f) · eps)`

where `abs(f)` is `f` with every sign made positive and every literal made
non-negative (`SyntaxTree.abs`), evaluated in the float type `T`. This is the
classical Wilkinson bound `|fl(f)(x) - f(x)| ≤ γ · |f|(|x|)` on a log scale,
relative to `x`. A Simpson-type average of `stj` up to the first overflow
(`Ω`) scores the form; `exacterr` measures the *actual* error against a
256-bit `BigFloat` evaluation of the optimal form.

The REDUCE computer-algebra calls (`expand`, `horner`, `factor`) are
abstracted as a `CAS` record so the numerics can be driven either by REDUCE's
actual output (the oracle tests) or by the built-in `ℚ[x]` forms
(`Wilkinson.Poly`). Plotting (PyPlot in Julia) becomes plain series data.
Allocation counts, nondeterministic in Julia, are reported as `0`.
-/

namespace Wilkinson

open AbstractAnalysis JuliaBase SyntaxTree

/-- Element `i` of a grid as a Julia number of the grid's element type. -/
def FloatSet.num (s : FloatSet) (i : Nat) : JNum :=
  match s with
  | .f64 r => .f64 (r.get i)
  | .f32 r => .f32 (r.get i)

/-- Julia `exp` in the element type. -/
def JNum.exp : JNum → JNum
  | .f32 v => .f32 (JuliaMath.exp32 v)
  | .big v => .f64 (JuliaMath.exp v.toFloat)
  | x => .f64 (JuliaMath.exp x.toF64)

/-- Julia `floatset(Float64, N; scale) = scale(eps):(scale(floatmax) - scale(eps))/(N-1):scale(floatmax)`
(src/Wilkinson.jl:17-21). -/
def floatset (N : Nat) (scale : Float → Float := id) : FloatSet :=
  let l := scale F64.eps
  let u := scale (F64.prevfloat F64.inf)
  .f64 (colon l ((u - l) / Float.ofNat (N - 1)) u)

/-- `floatset(Float32, N; scale)`. -/
def floatset32 (N : Nat) (scale : Float32 → Float32 := id) : FloatSet :=
  let l := scale (IEEEFloat.eps Float32)
  let u := scale (IEEEFloat.prevFloat (IEEEFloat.inf Float32))
  .f32 (colon32 l ((u - l) / Float32.ofNat (N - 1)) u)

/-- The standard grid: `floatset(T, 3000; scale = log)`. -/
def logset (T : NumType) (N : Nat := 3000) : FloatSet :=
  match T with
  | .f32 => floatset32 N JuliaMath.log32
  | _ => floatset N JuliaMath.log

/-- Julia `geonorm(x) = 1/(1-x)`. -/
def geonorm (x : Float) : Float := 1 / (1 - x)

/-- Julia `Ω(p)`: the index before the first `Inf`, else `length(p) - 1` (quirk
#28: the last point is always dropped). -/
def Ω (p : FloatArray) : Nat :=
  go 0 p.size
where
  /-- First `+Inf`. -/
  go (k : Nat) : Nat → Nat
    | 0 => p.size - 1
    | fuel + 1 => if k < p.size && p[k]!.isInf && p[k]! > 0 then k else go (k + 1) fuel

/-- Julia `stieltjes(set, expr, T, T2 = T)` (src/Wilkinson.jl:60-67): the
log-scale Wilkinson bound at every grid point, as `Float64`. -/
def stieltjes (set : FloatSet) (e : JExpr) (T : NumType) (T2 : NumType := T)
    (logi : JNum → JNum := JNum.log) (expi : JNum → JNum := JNum.exp) : FloatArray :=
  let t := SyntaxTree.abs (sub T e)
  let c := logi (JNum.int (Int64.ofNat (callcount e)) * T2.eps)
  go t c 1 (FloatArray.emptyWithCapacity set.len) set.len
where
  /-- One grid point at a time. -/
  go (t : JExpr) (c : JNum) (i : Nat) (acc : FloatArray) : Nat → FloatArray
    | 0 => acc
    | k + 1 =>
      let sc := set.num i
      let p := SyntaxTree.eval (expi sc) t
      go t c (i + 1) (acc.push ((logi p.abs - sc + c).toF64)) k

/-- Julia `sum(v[a:s:b])`: materialise the strided slice (1-based indices), then
Julia's vectorised `sum`. -/
def stridedSum (p : FloatArray) (a s b : Nat) : Float :=
  juliaSum (go a (FloatArray.emptyWithCapacity (b / s + 1)) (b + 1))
where
  /-- Tail-recursive gather. -/
  go (i : Nat) (acc : FloatArray) : Nat → FloatArray
    | 0 => acc
    | fuel + 1 => if i ≤ b && i ≥ 1 then go (i + s) (acc.push p[i - 1]!) fuel else acc

/-- Julia `simpson(set, p, n = Ω(p))` (src/Wilkinson.jl:69-74), literally:
`(4Σp[1:2:n-1] + 2Σp[2:2:n-1] + p[1] + p[n]) / (3n·(set[n] - set[1]))`.
Quirk #27: `p[1]` carries weight 5 and the normalisation is `3n·range`. -/
def simpson (set : FloatSet) (p : FloatArray) (n : Nat := Ω p) : Float :=
  let s : Float := (4 : Float) * stridedSum p 1 2 (n - 1) + (2 : Float) * stridedSum p 2 2 (n - 1) +
    (p[0]! + p[n - 1]!)
  -- `r = set[n] - set[1]` and `3n*r` are computed in the grid's element type
  let d : Float := match set with
    | .f64 g => Float.ofNat (3 * n) * (g.get n - g.get 1)
    | .f32 g => (Float32.ofNat (3 * n) * (g.get n - g.get 1)).toFloat
  s / d

/-- Julia `exacterr(set, exprs, T, …)` (src/Wilkinson.jl:76-88): for each form
after the first, `log|f_big(x) - f_T(x)| - log x`, where `f_big` is the first
(optimal) form evaluated in 256-bit `BigFloat`. -/
def exacterr (set : FloatSet) (exprs : List JExpr) (T : NumType)
    (logi : JNum → JNum := JNum.log) (expi : JNum → JNum := JNum.exp) : Array FloatArray :=
  match exprs with
  | [] => #[]
  | e0 :: rest =>
    let fb := sub .big e0
    let xs := (List.range set.len).toArray.map fun i => (set.num (i + 1), expi (set.num (i + 1)))
    let bs := xs.map fun (_, x) => SyntaxTree.eval x fb
    rest.toArray.map fun e =>
      let fe := sub T e
      (xs.zip bs).foldl (fun acc ((esc, x), b) =>
        acc.push ((logi (b - SyntaxTree.eval x fe).abs - esc).toF64)) (FloatArray.emptyWithCapacity set.len)

/-- Julia `renormalize!(p)` (src/Wilkinson.jl:90-96): zero the `Inf`s from the end
and return the index before the first one. -/
def renormalize (p : FloatArray) : FloatArray × Nat :=
  go p (p.size - 1) p.size
where
  /-- Backwards scan. -/
  go (p : FloatArray) (n : Nat) : Nat → FloatArray × Nat
    | 0 => (p, n)
    | k + 1 => if p[k]!.isInf && p[k]! > 0 then go (p.set! k 0) k k else go p n k

/-- Julia `errval(expr, T, N = 3000) = geonorm(simpson(set, stieltjes(...)))`. -/
def errval (e : JExpr) (T : NumType) (N : Nat := 3000) : Float :=
  let set := logset T N
  geonorm (simpson set (stieltjes set e T))

/-- The computer-algebra operations Wilkinson takes from REDUCE. -/
structure CAS where
  /-- REDUCE `expand`. -/
  expand : JExpr → JExpr
  /-- REDUCE `horner`. -/
  horner : JExpr → JExpr
  /-- REDUCE `factor`. -/
  factor : JExpr → JExpr
  /-- REDUCE `factor` with `on rounded`. -/
  factorRounded : JExpr → JExpr

/-- Julia `optimal(expr)` (src/Wilkinson.jl:32-43): the lowest `exprval` among
`horner(expr)`, `factor(horner(expr))` and `expr`, ties favouring Horner. -/
def optimal (cas : CAS) (e : JExpr) : JExpr :=
  let h := cas.horner e
  let f := cas.factor h
  let eh := (exprval h).1
  let ef := (exprval f).1
  let eo := (exprval e).1
  if eh ≤ ef then (if eh ≤ eo then h else e) else (if ef ≤ eo then f else e)

/-- Julia `PolynomialAnalysis` (src/polynomial.jl:4-17). -/
structure PolynomialAnalysis where
  /-- The analysed form. -/
  expr : JExpr
  /-- Sample grid. -/
  set : FloatSet
  /-- `exprval(expr)`. -/
  val : Float × Nat × Float × Float × Float
  /-- Stieltjes bound on the grid. -/
  stj : FloatArray
  /-- Simpson score up to `ω`. -/
  smp : Float
  deriving Inhabited

/-- Julia's constructor: `PolynomialAnalysis(expr, T = (Float64,), set, ω, stj)`,
with `T = (T,)` or `(T, T2)` passed as `T`/`T2`. -/
def PolynomialAnalysis.make (e : JExpr) (T : NumType := .f64) (T2 : NumType := T)
    (set : Option FloatSet := none) (ω : Option Nat := none) (stj : Option FloatArray := none) :
    PolynomialAnalysis :=
  let set := set.getD (logset T2)
  let stj := stj.getD (stieltjes set e T T2)
  { expr := e, set, val := exprval e, stj, smp := simpson set stj (ω.getD (Ω stj)) }

/-- Julia `PolynomialComparison` (src/polynomial.jl:30-69). -/
structure PolynomialComparison where
  /-- The input polynomial. -/
  expr : JExpr
  /-- Sample grid. -/
  set : FloatSet
  /-- `[optimal (BigFloat), expand, horner, factor, (rounded), (original)]`. -/
  results : Array PolynomialAnalysis
  /-- The original differs from all three CAS forms and is analysed too. -/
  extra : Bool
  /-- The rounded factorisation differs from the exact one. -/
  rxtra : Bool
  /-- Common cut-off `min Ω` over expand/horner/factor. -/
  ω : Nat
  /-- Actual errors (`exacterr`). -/
  exact : Array FloatArray
  /-- Simpson scores of the actual errors. -/
  integral : FloatArray
  /-- Evaluation type. -/
  typ : NumType

/-- The five forms `[optimal, expand, horner, factor, factor rounded]` REDUCE
returns for a polynomial (with Julia's `Reduce.Rational(false)`). -/
structure Forms where
  /-- `optimal(j)`. -/
  optimal : JExpr
  /-- `rcall(j, :expand)`. -/
  expand : JExpr
  /-- `rcall(j, :horner)`. -/
  horner : JExpr
  /-- `rcall(j, :factor)`. -/
  factor : JExpr
  /-- `rcall(j, :factor, :rounded)`. -/
  factorRounded : JExpr

/-- Compute the five forms with a CAS. -/
def Forms.ofCAS (cas : CAS) (j : JExpr) : Forms :=
  ⟨Wilkinson.optimal cas j, cas.expand j, cas.horner j, cas.factor j, cas.factorRounded j⟩

/-- Julia `PolynomialComparison(j, T, N)` given the CAS forms of `j`. -/
def PolynomialComparison.ofForms (j : JExpr) (F : Forms) (T : NumType := .f64) (N : Nat := 3000) :
    PolynomialComparison :=
  let set := logset T N
  let extra := !(j == F.expand) && !(j == F.horner) && !(j == F.factor)
  let rxtra := !(F.factor == F.factorRounded)
  let forms := [F.expand, F.horner, F.factor] ++ (if rxtra then [F.factorRounded] else []) ++
    (if extra then [j] else [])
  let stjs := forms.map fun e => stieltjes set e T
  let ω := min (Ω stjs[0]!) (min (Ω stjs[1]!) (Ω stjs[2]!))
  let res := (forms.zip stjs).map fun (e, s) => PolynomialAnalysis.make e T T (some set) (some ω) (some s)
  let best := PolynomialAnalysis.make F.optimal .big T (some set) (some ω)
  let EE := exacterr set (F.optimal :: forms) T
  { expr := j, set, results := (best :: res).toArray, extra, rxtra, ω, exact := EE,
    integral := EE.foldl (fun acc r => acc.push (simpson set r ω)) {}, typ := T }

/-- Julia `PolynomialComparison(j, T, N)` with a CAS. -/
def PolynomialComparison.make (cas : CAS) (j : JExpr) (T : NumType := .f64) (N : Nat := 3000) :
    PolynomialComparison :=
  ofForms j (Forms.ofCAS cas j) T N

/-- Julia tuple display `(a, b, c, d)` of `val[2:5]`. -/
def valTuple (v : Float × Nat × Float × Float × Float) : String :=
  s!"({v.2.1}, {F64.showString v.2.2.1}, {F64.showString v.2.2.2.1}, {F64.showString v.2.2.2.2})"

/-- Julia `print(::PolynomialAnalysis)` (src/polynomial.jl:19-26). REDUCE's 2-D
display of the expression is replaced by its Julia infix form; allocation is
reported as `0.0`. -/
def PolynomialAnalysis.toJulia (a : PolynomialAnalysis) : String :=
  s!"{a.expr.toJulia}\n" ++
  s!"characteristic values (c,σ,s,p): {valTuple a.val}\n" ++
  s!"expression value ν: {F64.showString a.val.1}\n" ++
  s!"predicted error bound ϕ: {F64.showString a.smp}\n" ++
  "bytes allocated: 0.0\n"

/-- Labels of the compared forms (Julia `n = ["e","h","f", "r"?, "o"?]`). -/
def PolynomialComparison.labels (c : PolynomialComparison) : List String :=
  ["e", "h", "f"] ++ (if c.rxtra then ["r"] else []) ++ (if c.extra then ["o"] else [])

/-- Julia `print(::PolynomialComparison)` (src/polynomial.jl:71-92), same
substitutions as `PolynomialAnalysis.toJulia`. -/
def PolynomialComparison.toJulia (c : PolynomialComparison) : String :=
  let ls := c.labels.zipIdx
  let r (k : Nat) := c.results[k + 1]!
  s!"{c.expr.toJulia}\n" ++
  "characteristic values (c,σ,s,p):\n" ++ String.join (ls.map fun (l, k) => s!"{l} = {valTuple (r k).val}\n") ++
  "expression value ν:\n" ++ String.join (ls.map fun (l, k) => s!"{l} = {F64.showString (r k).val.1}\n") ++
  "predicted error bound Φ:\n" ++
    String.join (ls.map fun (l, k) => s!"{l} = {F64.showString ((r k).smp / c.results[0]!.smp)}\n") ++
  "bytes allocated:\n" ++ String.join (ls.map fun (l, _) => s!"{l} = 0.0\n")

/-- One plotted curve of Julia `plot(::PolynomialComparison)`. -/
structure Series where
  /-- Legend entry. -/
  label : String
  /-- PyPlot colour letter. -/
  color : String
  /-- Dashed with circle markers (the "actual" curves). -/
  actual : Bool
  /-- `y` values over `collect(set)`. -/
  ys : FloatArray

/-- The data of Julia `plot(::PolynomialComparison)` (src/polynomial.jl:96-133):
bound and actual curves relative to the optimal form's `BigFloat` bound, in
Julia's drawing order, plus the axis label. -/
def PolynomialComparison.plotData (c : PolynomialComparison) : Array Series × String :=
  let base := c.results[0]!.stj
  let rel (v : FloatArray) : FloatArray :=
    (List.range (min v.size base.size)).foldl (fun acc i => acc.push (v[i]! - base[i]!)) {}
  let bound (k : Nat) (label color : String) : Series := ⟨label, color, false, rel c.results[k]!.stj⟩
  let actual (k : Nat) (label color : String) : Series := ⟨label, color, true, rel c.exact[k]!⟩
  let s := (if c.rxtra then #[bound 4 "approx (bound)" "y"] else #[]) ++
    #[bound 1 "expand (bound)" "r", bound 2 "horner (bound)" "b", bound 3 "factor (bound)" "g"] ++
    (if c.rxtra then #[actual 3 "approx (actual)" "y"] else #[]) ++
    (if c.extra then #[bound (c.results.size - 1) "original (bound)" "k",
                       actual (c.exact.size - 1) "original (actual)" "k"] else #[]) ++
    #[actual 0 "expand (actual)" "r", actual 1 "horner (actual)" "b", actual 2 "factor (actual)" "g"]
  (s, s!"$\\log|x|,\\,\\Delta={F64.showString c.set.stepValue}$")

/-- Julia's `isless` on floats (`NaN` sorts last, `-0.0 < 0.0`). -/
def islessF (a b : Float) : Bool := JuliaBase.F64.isless a b

/-- Julia `≤` on `exprval` tuples: lexicographic, component by component. -/
def valLE (a b : Float × Nat × Float × Float × Float) : Bool :=
  let (a1, a2, a3, a4, a5) := a
  let (b1, b2, b3, b4, b5) := b
  let fs : List (Float × Float) := [(a1, b1), (Float.ofNat a2, Float.ofNat b2), (a3, b3), (a4, b4), (a5, b5)]
  go fs
where
  /-- First differing component decides; all equal means `≤`. -/
  go : List (Float × Float) → Bool
    | [] => true
    | (x, y) :: rest => if islessF x y then true else if islessF y x then false else go rest

/-- Julia `testpoly(expr, T)` (src/polynomial.jl:135-161): does the `exprval`
ordering of the Horner and factored forms agree with the ordering of their
Stieltjes error values (`agree`), is the polynomial factorizable (`fact`), and
does the lower `exprval` form also have the lower error value than the expanded
form (`conj`)? Julia also accepts a form whose evaluation *allocated* fewer bytes
(`ehb[1] < eeb[1] || ehb[2] ≤ eeb[2]`), which makes the result depend on the
allocator; the port compares the error values alone. -/
def testpoly (cas : CAS) (e : JExpr) (T : NumType) : Bool × Bool × Bool :=
  let ee := cas.expand e
  let eh := cas.horner e
  let ef := cas.factor eh
  let ehv := exprval eh
  let eev := exprval ee
  let better (a b : Float) : Bool := a < b
  if eh == ef then
    (true, false, valLE ehv eev && better (errval eh T) (errval ee T))
  else
    let efv := exprval ef
    (valLE ehv efv == better (errval eh T) (errval ef T), true,
      (valLE ehv eev && better (errval eh T) (errval ee T)) || (valLE efv eev && better (errval ef T) (errval ee T)))

end Wilkinson
