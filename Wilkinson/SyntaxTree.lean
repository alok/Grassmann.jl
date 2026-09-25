import Wilkinson.Num

/-!
# SyntaxTree.jl (the parts Wilkinson uses)

Ported from SyntaxTree.jl 1.0.1 (`src/SyntaxTree.jl`, `src/exprval.jl`):
`callcount`, `sub`, `abs`, `alg` and the characteristic "expression value"
`exprval` of Reed's *Optimal polynomial characteristic methods* (2018), plus
an interpreter standing in for `genfun`/`genlatest`.

`exprval` is reproduced with its quirks, since Wilkinson's optimal-form choice
depends on them:
* a sub-expression whose log-sum is `0` reports an average of `1.0` (the
  `0 ∈ [s, cs]` test), and that `1.0` then enters its parent's weighted sum;
* the exponent of `x^k` is *not* a scalar for the average but *is* one for the
  deviation `exprdev`, which also divides by `callcount - 1` (quirk #30).
-/

namespace Wilkinson

open AbstractAnalysis

namespace NumType

/-- Julia `eps(T)` as a number of that type. -/
def eps : NumType → JNum
  | .f64 => .f64 JuliaBase.F64.eps
  | .f32 => .f32 (IEEEFloat.eps Float32)
  | .big => .big (BigFloat.round 256 false 1 (-255))

/-- Julia `convert(T, x)` for a literal. -/
def convert (T : NumType) (l : Lit) : Lit :=
  let x := JNum.ofLit l
  match T with
  | .f64 => .f64 x.toF64
  | .f32 => .f32 x.toF32
  | .big => .big x.toBig

/-- Julia `T(x)` for a number. -/
def cast (T : NumType) (x : JNum) : JNum :=
  match T with
  | .f64 => .f64 x.toF64
  | .f32 => .f32 x.toF32
  | .big => .big x.toBig

end NumType

namespace SyntaxTree

/-- Julia `callcount(expr)`: the number of `:call` nodes. -/
def callcount : JExpr → Nat
  | .call _ args => 1 + go args
  | _ => 0
where
  /-- Over the arguments. -/
  go : List JExpr → Nat
    | [] => 0
    | a :: as => callcount a + go as

/-- Julia `SyntaxTree.sub(T, expr)`: convert every numeric literal to `T`,
except a literal exponent of `^` (src/SyntaxTree.jl:50-71). -/
def sub (T : NumType) : JExpr → JExpr
  | .lit l => .lit (T.convert l)
  | .sym s => .sym s
  | .call "^" [b, .lit k] => .call "^" [sub T b, .lit k]
  | .call "^" [b, .sym s] => .call "^" [sub T b, .sym s]
  | .call op args => .call op (go args)
where
  /-- Over the arguments. -/
  go : List JExpr → List JExpr
    | [] => []
    | a :: as => sub T a :: go as

/-- Absolute value of a literal. -/
def Lit.abs : Lit → Lit
  | .int v => .int v.natAbs
  | .f64 v => .f64 v.abs
  | .f32 v => .f32 v.abs
  | .big v => .big v.abs

/-- Julia `SyntaxTree.abs(expr)`: every `-` becomes `+` (unary ones too) and
every literal its absolute value; a literal exponent is kept
(src/SyntaxTree.jl:78-102). The result bounds `|expr|` termwise. -/
def abs : JExpr → JExpr
  | .lit l => .lit (Lit.abs l)
  | .sym s => .sym s
  | .call "^" [b, .lit k] => .call "^" [abs b, .lit k]
  | .call "^" [b, .sym s] => .call "^" [abs b, .sym s]
  | .call op args => .call (if op == "-" then "+" else op) (go args)
where
  /-- Over the arguments. -/
  go : List JExpr → List JExpr
    | [] => []
    | a :: as => abs a :: go as

/-- Julia `alg(expr, f = :(1 + ϵ))`: wrap every call as `f * call(...)`,
recursively (src/SyntaxTree.jl:109-120). -/
def alg (f : JExpr := .call "+" [.int 1, .sym "ϵ"]) : JExpr → JExpr
  | .call op args => .call "*" [f, .call op (go args)]
  | e => e
where
  /-- Over the arguments. -/
  go : List JExpr → List JExpr
    | [] => []
    | a :: as => alg f a :: go as

/-- Julia `log(abs(literal))` as `Float64`, with Julia's own `log` kernels
(`log(::Int)` works in `Float64`, `log(::Float32)` in `Float32`). -/
def logAbs : Lit → Float
  | .int v => JuliaMath.log (Float.ofInt v.natAbs)
  | .f64 v => JuliaMath.log v.abs
  | .f32 v => (JuliaMath.log32 v.abs).toFloat
  | .big v => (BigFloat.log v.abs).toFloat

/-- Julia `expravg(expr) = (cs, avg, cp, pavg)` (src/exprval.jl:9-38): the number
of scalars, the average of their logarithms, the number of literal exponents and
their average. -/
def expravg : JExpr → Nat × Float × Nat × Float
  | .lit l => finish 1 (logAbs l) 0 0
  | .sym _ => finish 0 0 0 0
  | .call "^" [b, .lit k] =>
    let (cst, st, cpt, pt) := expravg b
    let kabs : Float := match k with
      | .int v => Float.ofNat v.natAbs
      | .f64 v => v.abs
      | .f32 v => v.abs.toFloat
      | .big v => v.abs.toFloat
    finish cst (0 + Float.ofNat cst * st) (1 + cpt) (0 + kabs + Float.ofNat cpt * pt)
  | .call _ args => combine (go args)
where
  /-- Over the arguments. -/
  go : List JExpr → List (Nat × Float × Nat × Float)
    | [] => []
    | a :: as => expravg a :: go as
  /-- Accumulate child statistics in Julia's order. -/
  combine (kids : List (Nat × Float × Nat × Float)) : Nat × Float × Nat × Float :=
    let (cs, s, cp, p) := kids.foldl (fun (cs, s, cp, p) (cst, st, cpt, pt) =>
      (cs + cst, s + Float.ofNat cst * st, cp + cpt, p + Float.ofNat cpt * pt)) (0, 0.0, 0, 0.0)
    finish cs s cp p
  /-- `(cs, 0 ∈ [s, cs] ? 1.0 : s/cs, cp, cp == 0 ? 1.0 : p/cp)`. -/
  finish (cs : Nat) (s : Float) (cp : Nat) (p : Float) : Nat × Float × Nat × Float :=
    (cs, (if s == 0 || cs == 0 then 1.0 else s / Float.ofNat cs), cp, (if cp == 0 then 1.0 else p / Float.ofNat cp))

/-- Julia `exprdev(expr, val, cal)`: `Σ (log|v| - val)² / (cal - 1)` over *all*
literals, exponents included (src/exprval.jl:46-56). -/
def exprdev (val : Float) (cal : Nat) : JExpr → Float
  | .lit l => let d := logAbs l - val; (d * d) / (Float.ofNat cal - 1)
  | .sym _ => 0
  | .call _ args => go 0.0 args
where
  /-- Left fold over the arguments (Julia's `s += …` order). -/
  go (s : Float) : List JExpr → Float
    | [] => s
    | a :: as => go (s + exprdev val cal a) as

/-- Julia `exprval(expr) = (ν, c, σ, s, p)` (src/exprval.jl:66-71): the
expression value `ν = c·√(|s|·σ)·p` with `c` the call count, `σ` the deviation,
`s` the mean log-scalar and `p` the mean exponent. Lower is better. -/
def exprval (e : JExpr) : Float × Nat × Float × Float × Float :=
  let (_, avg, _, pavg) := expravg e
  let cal := callcount e
  let mal := Float.sqrt (exprdev avg cal e)
  (Float.ofNat cal * Float.sqrt (avg.abs * mal) * pavg, cal, mal, avg, pavg)

/-- Evaluate an expression at `x` (the interpreter replacing `genfun`): Julia's
promotion rules for mixed types, `literal_pow` for literal exponents, n-ary
`+`/`*` folded left. Unbound symbols evaluate to `NaN`. -/
def eval (x : JNum) : JExpr → JNum
  | .lit l => JNum.ofLit l
  | .sym s => if s == "x" then x else .f64 (0 / 0)
  | .call "^" [b, .lit (.int k)] => (eval x b).powLit k
  | .call "^" [b, e] => (eval x b).pow (eval x e)
  | .call "-" [a] => -(eval x a)
  | .call "+" [a] => eval x a
  | .call op (a :: rest) => go (binop op) (eval x a) rest
  | .call _ [] => .f64 (0 / 0)
where
  /-- The binary operation of an operator symbol. -/
  binop (op : String) : JNum → JNum → JNum :=
    match op with
    | "+" => (· + ·) | "-" => (· - ·) | "*" => (· * ·) | "/" => (· / ·)
    | "//" => JNum.rdiv | "^" => JNum.pow | _ => fun _ _ => .f64 (0 / 0)
  /-- Left fold (Julia's `afoldl` for n-ary `+`/`*`). -/
  go (f : JNum → JNum → JNum) (acc : JNum) : List JExpr → JNum
    | [] => acc
    | b :: bs => go f (f acc (eval x b)) bs

end SyntaxTree

end Wilkinson
