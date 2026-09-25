import Wilkinson.Parse
import Wilkinson.Poly

/-!
# A small computer-algebra system for Fatou's symbolic front-end

Fatou.jl hands its expressions to the REDUCE CAS (through Reduce.jl) for three things
(`src/internals.jl:9-19`, `ext/PyPlotExt.jl:31`):

* the Newton map `newton_raphson(E, m) = factor(z - m*(E/df(E, z)))`, which is compiled and
  iterated;
* `recomp(E, x, j)`, the `j`-fold composition with `c := 0`, for `basin`;
* `latex(E)` (package `rlfi`), the LaTeX of titles and basins.

This module replaces REDUCE by an exact computer algebra over the Gaussian rationals `ℚ(i)`:

* `QI`: Gaussian rationals; floats are rationalized from their shortest decimal form, as REDUCE
  reads the decimal Reduce.jl prints (`1.5 ↦ 3/2`, `1 - 0.4im ↦ 1 - 2i/5`);
* `Kern`: REDUCE's *kernels*, the indeterminates: the variables `z`, `c`, `e`, `pi` and function
  applications `sin(u)`, `cos(u)`, `log(u)`, `sqrt(u)`, `e^u`, `z^a` (non-integer `a`) with a
  canonical argument;
* `Poly`: sparse polynomials over `ℚ(i)` in kernels, terms in REDUCE's order (a function kernel
  before a variable, variables alphabetically, higher powers first);
* `RF`: rational functions in lowest terms (common monomial factors and, for polynomials in `z`
  alone, the polynomial gcd are cancelled), with Gaussian-integer coefficients whose content is
  divided out (`i` counts as a kernel, as in REDUCE), and a positive leading denominator
  coefficient;
* `simp` (Julia `Expr` → `RF`), `deriv` (`d/dz`, chain rule for every kernel), `subst`;
* `newtonRaphson`, `recomp`;
* `Out`: REDUCE's printed prefix form, with `on factor` (content, factors over `ℤ` in REDUCE's
  order through `Wilkinson.factorZ`, the power of `z` last) or without (a negative leading
  coefficient is pulled out as `-(…)`), printed as REDUCE's linear output re-parsed by Julia
  (`toJExpr`, with Reduce.jl's `treecombine!` rewrites) and as `rlfi` LaTeX (`toLatex`).

**Scope.** Reduce.jl runs REDUCE with `off exp`, so products of sums built in a pipeline can
stay unexpanded (`((4i - 1)(i - z²) + 4z²)/(4z)`). This CAS always expands (REDUCE's `on exp`
normal form): it reproduces REDUCE's output exactly when that output is the expanded normal
form, which holds for the README Newton map `(2z³ + 1)/(3z²)` and most polynomial maps
(`Tests/Fatou/Symbolic.lean` lists which golden forms agree); otherwise the map is the same
rational function written differently, which can round differently in the last bits.
-/

namespace Fatou

namespace CAS

open Wilkinson

/-! ## Gaussian rationals -/

/-- A Gaussian rational `re + im·i`. -/
structure QI where
  /-- real part -/
  re : Rat
  /-- imaginary part -/
  im : Rat
  deriving BEq, Inhabited, Repr

namespace QI

/-- `0`. -/
def zero : QI := ⟨0, 0⟩
/-- `1`. -/
def one : QI := ⟨1, 0⟩
/-- `i`. -/
def I : QI := ⟨0, 1⟩
/-- A rational. -/
def ofRat (r : Rat) : QI := ⟨r, 0⟩
/-- An integer. -/
def ofInt (n : Int) : QI := ⟨n, 0⟩
/-- Is it zero? -/
def isZero (a : QI) : Bool := a.re == 0 && a.im == 0
/-- Is it a real integer? -/
def isInt (a : QI) : Bool := a.im == 0 && a.re.den == 1

instance : Add QI := ⟨fun a b => ⟨a.re + b.re, a.im + b.im⟩⟩
instance : Sub QI := ⟨fun a b => ⟨a.re - b.re, a.im - b.im⟩⟩
instance : Neg QI := ⟨fun a => ⟨-a.re, -a.im⟩⟩
instance : Mul QI := ⟨fun a b => ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩⟩
/-- `1/a` (for `a ≠ 0`). -/
def inv (a : QI) : QI := let n := a.re * a.re + a.im * a.im; ⟨a.re / n, -a.im / n⟩
instance : Div QI := ⟨fun a b => a * b.inv⟩
instance {n : Nat} : OfNat QI n := ⟨ofInt n⟩

end QI

/-- The rational REDUCE reads from Julia's printed decimal of `x` (`0.06 ↦ 3/50`). -/
def ratOfFloat (x : Float) : Rat := Poly.decimalRat x

/-! ## Kernels -/

/-- A REDUCE kernel. Function arguments are canonical expressions, stored as the Julia `Expr`
of their normal form (`RF.toJExpr`), which identifies them. -/
inductive Kern where
  /-- an identifier: `z`, `c`, `e`, `pi`, `i` (the last only when printing) -/
  | var (name : String)
  /-- `f(u)` for `f ∈ {sin, cos, tan, sinh, cosh, log, sqrt}` -/
  | app (f : String) (arg : JExpr)
  /-- `e^u` (REDUCE's `e**u`) with `u` not an integer or half-integer constant -/
  | exp (arg : JExpr)
  /-- `b^a` with a constant, non-integer exponent `a` (REDUCE splits `z^(4+3i)` into
  `z^4 · z^(3i)`); the base is canonical -/
  | pow (base : JExpr) (ex : JExpr)
  deriving BEq, Inhabited

namespace Kern

/-- The sort key: function kernels (REDUCE's non-atomic kernels) before identifiers,
then by name alphabetically (an earlier name is a *higher* kernel), then by argument. -/
def key : Kern → Nat × String × String
  | var n => (1, n, "")
  | app f a => (0, f, toString a)
  | exp a => (0, "expt", "e^" ++ toString a)
  | pow b a => (0, "expt", toString b ++ "^" ++ toString a)

/-- `a` is a higher kernel than `b` (REDUCE's `ordop`). -/
def higher (a b : Kern) : Bool :=
  let (x₁, y₁, z₁) := a.key
  let (x₂, y₂, z₂) := b.key
  x₁ < x₂ || (x₁ == x₂ && (y₁ < y₂ || (y₁ == y₂ && z₁ < z₂)))

/-- Is it the variable `z`? -/
def isZ : Kern → Bool
  | var "z" => true
  | _ => false

end Kern

/-! ## Polynomials -/

/-- A monomial: kernels with positive exponents, highest kernel first. -/
abbrev Mono := List (Kern × Nat)

/-- Multiply two monomials. -/
def Mono.mul : Mono → Mono → Mono
  | [], b => b
  | a, [] => a
  | (k, e) :: as, (l, f) :: bs =>
    if k == l then (k, e + f) :: Mono.mul as bs
    else if k.higher l then (k, e) :: Mono.mul as ((l, f) :: bs)
    else (l, f) :: Mono.mul ((k, e) :: as) bs
termination_by a b => a.length + b.length

/-- REDUCE's term order: compare the exponent of the highest kernel first. -/
def Mono.cmp : Mono → Mono → Ordering
  | [], [] => .eq
  | [], _ => .lt
  | _, [] => .gt
  | (k, e) :: as, (l, f) :: bs =>
    if k == l then (if e == f then Mono.cmp as bs else compare e f)
    else if k.higher l then .gt else .lt

/-- The exponent of a kernel in a monomial. -/
def Mono.expOf (m : Mono) (k : Kern) : Nat := (m.find? (·.1 == k)).map (·.2) |>.getD 0

/-- Total degree in `z`. -/
def Mono.zdeg (m : Mono) : Nat := m.expOf (.var "z")

/-- A polynomial: terms with nonzero coefficients, in decreasing term order. -/
abbrev Poly := List (Mono × QI)

namespace Poly

/-- Add a term, keeping the order. -/
def insert (t : Mono × QI) : Poly → Poly
  | [] => if t.2.isZero then [] else [t]
  | s :: ss =>
    match Mono.cmp t.1 s.1 with
    | .gt => if t.2.isZero then s :: ss else t :: s :: ss
    | .eq => let c := t.2 + s.2; if c.isZero then ss else (s.1, c) :: ss
    | .lt => s :: insert t ss

/-- Sum. -/
def add (p q : Poly) : Poly := q.foldl (fun acc t => insert t acc) p

/-- Scalar multiple. -/
def smul (c : QI) (p : Poly) : Poly := if c.isZero then [] else p.map fun (m, a) => (m, c * a)

/-- Negation. -/
def neg (p : Poly) : Poly := p.map fun (m, a) => (m, -a)

/-- Difference. -/
def sub (p q : Poly) : Poly := add p (neg q)

/-- Product. -/
def mul (p q : Poly) : Poly :=
  p.foldl (fun acc (m, a) => q.foldl (fun acc (n, b) => insert (Mono.mul m n, a * b) acc) acc) []

/-- The constant polynomial. -/
def const (c : QI) : Poly := if c.isZero then [] else [([], c)]

/-- A kernel. -/
def kern (k : Kern) : Poly := [([(k, 1)], QI.one)]

/-- Natural power. -/
def pow (p : Poly) : Nat → Poly
  | 0 => const QI.one
  | n + 1 => mul (pow p n) p

/-- Is it a constant (possibly zero)? -/
def isConst (p : Poly) : Bool := p.all (·.1.isEmpty)

/-- The constant value of a constant polynomial. -/
def constVal (p : Poly) : QI := match p with
  | [] => QI.zero
  | (_, c) :: _ => c

/-- The kernels occurring in `p`. -/
def kernels (p : Poly) : List Kern :=
  p.foldl (fun acc (m, _) => m.foldl (fun acc (k, _) => if acc.contains k then acc else acc ++ [k]) acc) []

/-- Is `p` a polynomial in `z` alone? -/
def isUnivariate (p : Poly) : Bool := p.kernels.all Kern.isZ

/-- The monomial dividing every term (common powers of kernels). -/
def monoGcd (p : Poly) : Mono :=
  match p with
  | [] => []
  | (m, _) :: rest =>
    rest.foldl (fun g (n, _) => g.filterMap fun (k, e) =>
      let f := n.expOf k; if f == 0 then none else some (k, min e f)) m

/-- Divide every term by a monomial that divides it. -/
def divMono (p : Poly) (g : Mono) : Poly :=
  p.map fun (m, a) => (m.filterMap fun (k, e) => let f := e - g.expOf k; if f == 0 then none else some (k, f), a)

/-- Dense coefficients `[c₀, c₁, …]` of a polynomial in `z` alone. -/
def toDense (p : Poly) : Array QI :=
  let d := p.foldl (fun acc (m, _) => max acc m.zdeg) 0
  p.foldl (fun (acc : Array QI) (m, a) => acc.modify m.zdeg (· + a)) (Array.replicate (d + 1) QI.zero)

/-- The polynomial in `z` with dense coefficients `[c₀, c₁, …]`. -/
def ofDense (a : Array QI) : Poly :=
  (List.range a.size).foldl (fun acc k =>
    insert ((if k == 0 then [] else [(.var "z", k)]), a[k]!) acc) []

end Poly

/-! ### Dense polynomials over `ℚ(i)` (for the gcd of polynomials in `z`) -/

namespace Dense

/-- Drop high zero coefficients. -/
def trim (a : Array QI) : Array QI :=
  let n := (List.range a.size).foldl (fun acc k => if a[k]!.isZero then acc else k + 1) 0
  a.extract 0 n

/-- Remainder of `a` by `b ≠ 0`. -/
def rem (a b : Array QI) : Array QI := Id.run do
  let b := trim b
  let mut r := trim a
  if b.isEmpty then return r
  let lb := b.back!
  for _ in [0:a.size + 1] do
    if r.size < b.size then break
    let q := r.back! / lb
    let sh := r.size - b.size
    for k in [0:b.size] do
      r := r.modify (sh + k) (· - q * b[k]!)
    r := trim r
  return r

/-- Quotient of `a` by `b ≠ 0` (exact division assumed). -/
def quot (a b : Array QI) : Array QI := Id.run do
  let b := trim b
  let mut r := trim a
  if b.isEmpty || r.size < b.size then return #[]
  let lb := b.back!
  let mut q : Array QI := Array.replicate (r.size - b.size + 1) QI.zero
  for _ in [0:a.size + 1] do
    if r.size < b.size then break
    let c := r.back! / lb
    let sh := r.size - b.size
    q := q.set! sh c
    for k in [0:b.size] do
      r := r.modify (sh + k) (· - c * b[k]!)
    r := trim r
  return q

/-- Monic gcd. -/
def gcd (a b : Array QI) : Array QI := Id.run do
  let mut x := trim a
  let mut y := trim b
  for _ in [0:a.size + b.size + 2] do
    if y.isEmpty then break
    let r := rem x y
    x := y
    y := r
  if x.isEmpty then return x
  let l := x.back!
  return x.map (· / l)

end Dense

/-! ## Rational functions -/

/-- A rational function `num/den` in lowest terms (see the module doc). -/
structure RF where
  /-- numerator -/
  num : Poly
  /-- denominator (never zero) -/
  den : Poly
  deriving Inhabited

namespace RF

/-- Integer components of the coefficients (`i` counting as a kernel). -/
def intParts (p : Poly) : List Rat := p.flatMap fun (_, a) => [a.re, a.im]

/-- The leading coefficient of `p` in REDUCE's order with `i` a kernel: the `i`-part if the
leading term has one and `i` ranks above every other kernel of the term, else the real part. -/
def leadSign (p : Poly) : Int :=
  match p with
  | [] => 0
  | (m, a) :: _ =>
    let iFirst := a.im != 0 && (m.all fun (k, _) => (Kern.var "i").higher k)
    let c := if iFirst then a.im else if a.re != 0 then a.re else a.im
    if c < 0 then -1 else 1

/-- REDUCE's rule `sqrt(u)^2 = u` for a kernel `u` (`sqrt(e)^2 = e`, `sqrt(z)^3 = z·sqrt(z)`). -/
def sqrtSquares (p : Poly) : Poly :=
  p.foldl (fun acc (m, a) =>
    let m' := m.foldl (fun (mm : Mono) (k, e) =>
      match k with
      | .app "sqrt" (.sym s) =>
        let u : Kern := match s with
          | "ℯ" => .var "e" | "π" => .var "pi" | v => .var v
        let mm := if e ≥ 2 then Mono.mul mm [(u, e / 2)] else mm
        if e % 2 == 1 then Mono.mul mm [(k, 1)] else mm
      | _ => Mono.mul mm [(k, e)]) []
    Poly.insert (m', a) acc) []

/-- Normalize: cancel common monomials, the gcd of polynomials in `z`, clear denominators,
divide out the integer content, make the denominator's leading coefficient positive. -/
def normalize (n d : Poly) : RF := Id.run do
  let n := sqrtSquares n
  let d := sqrtSquares d
  if n.isEmpty then return ⟨[], Poly.const QI.one⟩
  -- common monomial factor
  let g := Mono.mul [] ((Poly.monoGcd n).filterMap fun (k, e) =>
    let f := (Poly.monoGcd d).expOf k; if f == 0 then none else some (k, min e f))
  let mut n := Poly.divMono n g
  let mut d := Poly.divMono d g
  -- polynomial gcd for polynomials in `z` alone
  if n.isUnivariate && d.isUnivariate && !d.isConst && !n.isConst then
    let gz := Dense.gcd n.toDense d.toDense
    if gz.size > 1 then
      n := Poly.ofDense (Dense.quot n.toDense gz)
      d := Poly.ofDense (Dense.quot d.toDense gz)
  -- clear rational denominators
  let dens := (intParts n ++ intParts d).map (·.den)
  let l : Nat := dens.foldl Nat.lcm 1
  n := Poly.smul (QI.ofInt l) n
  d := Poly.smul (QI.ofInt l) d
  -- integer content
  let c : Nat := (intParts n ++ intParts d).foldl (fun g r => Nat.gcd g r.num.natAbs) 0
  if c > 1 then
    n := Poly.smul (QI.ofRat (1 / (c : Rat))) n
    d := Poly.smul (QI.ofRat (1 / (c : Rat))) d
  if leadSign d < 0 then
    n := Poly.neg n
    d := Poly.neg d
  return ⟨n, d⟩

/-- A polynomial as a rational function. -/
def ofPoly (p : Poly) : RF := normalize p (Poly.const QI.one)
/-- A constant. -/
def const (c : QI) : RF := ofPoly (Poly.const c)
/-- A kernel. -/
def kern (k : Kern) : RF := ⟨Poly.kern k, Poly.const QI.one⟩
/-- Zero. -/
def zero : RF := const QI.zero
/-- One. -/
def one : RF := const QI.one

/-- Is it zero? -/
def isZero (r : RF) : Bool := r.num.isEmpty
/-- Is it a constant? -/
def isConst (r : RF) : Bool := r.num.isConst && r.den.isConst
/-- The value of a constant. -/
def constVal (r : RF) : QI := r.num.constVal / r.den.constVal

/-- Sum. -/
def add (a b : RF) : RF := normalize (Poly.add (Poly.mul a.num b.den) (Poly.mul b.num a.den)) (Poly.mul a.den b.den)
/-- Negation. -/
def neg (a : RF) : RF := ⟨Poly.neg a.num, a.den⟩
/-- Difference. -/
def sub (a b : RF) : RF := add a (neg b)
/-- Product. -/
def mul (a b : RF) : RF := normalize (Poly.mul a.num b.num) (Poly.mul a.den b.den)
/-- Quotient (`b ≠ 0`). -/
def div (a b : RF) : RF := normalize (Poly.mul a.num b.den) (Poly.mul a.den b.num)
/-- Integer power. -/
def pow (a : RF) (n : Int) : RF :=
  match n with
  | .ofNat k => normalize (Poly.pow a.num k) (Poly.pow a.den k)
  | .negSucc k => normalize (Poly.pow a.den (k + 1)) (Poly.pow a.num (k + 1))

instance : Add RF := ⟨add⟩
instance : Sub RF := ⟨sub⟩
instance : Mul RF := ⟨mul⟩
instance : Div RF := ⟨div⟩
instance : Neg RF := ⟨neg⟩

end RF

/-! ## From and to Julia expressions -/

/-- A rational as a Julia literal expression (`3`, `3 / 2`). -/
def ratJ (r : Rat) : JExpr :=
  let n := JExpr.int r.num.natAbs
  let v := if r.den == 1 then n else .call "/" [n, JExpr.int r.den]
  if r < 0 then .call "-" [v] else v

/-- A Gaussian rational as a Julia expression. -/
def qiJ (a : QI) : JExpr :=
  if a.im == 0 then ratJ a.re
  else
    let imPart := if a.im == 1 then JExpr.sym "im" else .call "*" [ratJ a.im, .sym "im"]
    if a.re == 0 then imPart else .call "+" [ratJ a.re, imPart]

/-- The kernel as a Julia expression (its identity, and the input of `simp` when re-read). -/
def Kern.toJExpr : Kern → JExpr
  | .var "e" => .sym "ℯ"
  | .var "pi" => .sym "π"
  | .var "i" => .sym "im"
  | .var n => .sym n
  | .app f a => .call f [a]
  | .exp a => .call "^" [.sym "ℯ", a]
  | .pow b a => .call "^" [b, a]

/-- A polynomial as a plain Julia expression (a sum of products). -/
def Poly.toJExpr (p : Poly) : JExpr :=
  let term (m : Mono) (a : QI) : JExpr :=
    let ks := m.map fun (k, e) => if e == 1 then k.toJExpr else .call "^" [k.toJExpr, JExpr.int e]
    match ks with
    | [] => qiJ a
    | _ => if a == QI.one then (match ks with | [k] => k | _ => .call "*" ks) else .call "*" (qiJ a :: ks)
  match p with
  | [] => JExpr.int 0
  | [(m, a)] => term m a
  | ts => .call "+" (ts.map fun (m, a) => term m a)

/-- A rational function as a plain Julia expression. -/
def RF.toJExpr (r : RF) : JExpr :=
  if r.den.isConst && r.den.constVal == QI.one then r.num.toJExpr
  else .call "/" [r.num.toJExpr, r.den.toJExpr]

/-- The functions `simp` knows as kernels. -/
def kernelFns : List String := ["sin", "cos", "tan", "sinh", "cosh", "log", "sqrt"]

/-- Split a constant exponent into its integer part and the rest (`4 + 3i ↦ (4, 3i)`,
`5/2 ↦ (2, 1/2)`, `-1/2 ↦ (-1, 1/2)`). -/
def splitExponent (a : QI) : Int × QI :=
  let n : Int := a.re.floor
  (n, a - QI.ofInt n)

mutual

/-- REDUCE's simplification of a Julia expression to a rational function: the symbols `z`,
`c`, `im`, `ℯ`, `π`; integer and float literals (rationalized); `+ - * / // ^ %`; and
`sin cos tan sinh cosh exp log sqrt`. -/
partial def simp : JExpr → Except String RF
  | .sym "z" => return RF.kern (.var "z")
  | .sym "c" => return RF.kern (.var "c")
  | .sym "im" => return RF.const QI.I
  | .sym "ℯ" | .sym "e" => return RF.kern (.var "e")
  | .sym "π" | .sym "pi" => return RF.kern (.var "pi")
  | .sym s => throw s!"unknown symbol {s}"
  | .lit (.int n) => return RF.const (QI.ofInt n)
  | .lit (.f64 x) => return RF.const (QI.ofRat (ratOfFloat x))
  | .lit _ => throw "unsupported literal"
  | .call "+" args => do args.foldlM (fun acc a => return acc + (← simp a)) RF.zero
  | .call "-" [a] => return - (← simp a)
  | .call "-" [a, b] => return (← simp a) - (← simp b)
  | .call "*" args => do args.foldlM (fun acc a => return acc * (← simp a)) RF.one
  | .call "/" [a, b] | .call "//" [a, b] => do
    let d ← simp b
    if d.isZero then throw "division by zero"
    return (← simp a) / d
  | .call "^" [a, b] => do
    let e ← simp b
    if e.isConst && e.constVal.isInt then
      let n := e.constVal.re.num
      let base ← simp a
      if base.isZero && n < 0 then throw "division by zero"
      return base.pow n
    else if a == .sym "ℯ" then mkExp e
    else mkPow (← simp a) e
  | .call "exp" [a] => do mkExp (← simp a)
  | .call f [a] =>
    if kernelFns.contains f then do mkApp f (← simp a) else throw s!"unsupported function {f}"
  | .call "%" _ => throw "`%` is not supported (REDUCE hangs on it too)"
  | .call f _ => throw s!"unsupported call {f}"

/-- `f(u)` with REDUCE's evaluations at 0 and its parity rules (`sin(-u) = -sin(u)`,
`cos(-u) = cos(u)`). -/
partial def mkApp (f : String) (u : RF) : Except String RF := do
  if u.isZero then
    match f with
    | "sin" | "tan" | "sinh" | "sqrt" => return RF.zero
    | "cos" | "cosh" => return RF.one
    | "log" => throw "log(0)"
    | _ => pure ()
  if f == "log" && u.isConst && u.constVal == QI.one then return RF.zero
  let neg := RF.leadSign u.num < 0
  if neg && (f == "sin" || f == "tan" || f == "sinh") then return - (RF.kern (.app f (-u).toJExpr))
  if neg && (f == "cos" || f == "cosh") then return RF.kern (.app f (-u).toJExpr)
  return RF.kern (.app f u.toJExpr)

/-- `e^u`: REDUCE's `e**u`, with the integer and half-integer part of a constant term split
off (`e^(3/2) = e·√e`) and a negative exponent written as a quotient. -/
partial def mkExp (u : RF) : Except String RF := do
  -- the constant term of a polynomial exponent
  let (k, rest) : QI × RF :=
    if u.den.isConst then
      let c := (u.num.find? (·.1.isEmpty)).map (·.2) |>.getD QI.zero
      (c / u.den.constVal, u - RF.const (c / u.den.constVal))
    else (QI.zero, u)
  let (n, frac) := splitExponent k
  let eInt : RF := (RF.kern (.var "e")).pow n
  let eFrac ← if frac.isZero then pure RF.one
    else if frac == QI.ofRat (1 / 2) then mkApp "sqrt" (RF.kern (.var "e"))
    else pure (RF.kern (.exp (RF.const frac).toJExpr))
  let eRest : RF :=
    if rest.isZero then RF.one
    else if RF.leadSign rest.num < 0 then RF.one / RF.kern (.exp (-rest).toJExpr)
    else RF.kern (.exp rest.toJExpr)
  return eInt * eFrac * eRest

/-- `base^a` for a non-integer exponent: `z^(n + r) = z^n · z^r` for a constant `a`, `sqrt` for
`r = 1/2`, a kernel otherwise. -/
partial def mkPow (base : RF) (a : RF) : Except String RF := do
  if a.isConst then
    let (n, r) := splitExponent a.constVal
    let rPart ← if r.isZero then pure RF.one
      else if r == QI.ofRat (1 / 2) then mkApp "sqrt" base
      else pure (RF.kern (.pow base.toJExpr (RF.const r).toJExpr))
    return base.pow n * rPart
  else throw "symbolic exponent"

end

/-- REDUCE's `i` does not occur in `RF`s built by `simp`: it lives in the coefficients. -/
def reread (e : JExpr) : RF := (simp e).toOption.getD RF.zero

/-! ## Derivative and substitution -/

mutual

/-- `d/dz` of a kernel. -/
partial def Kern.deriv : Kern → RF
  | .var "z" => RF.one
  | .var _ => RF.zero
  | .app f a =>
    let u := reread a
    let du := RF.deriv u
    match f with
    | "sin" => (reread (.call "cos" [a])) * du
    | "cos" => - ((reread (.call "sin" [a])) * du)
    | "tan" => (RF.kern (.app "tan" a) * RF.kern (.app "tan" a) + RF.one) * du
    | "sinh" => (reread (.call "cosh" [a])) * du
    | "cosh" => (reread (.call "sinh" [a])) * du
    | "log" => du / u
    | "sqrt" => du / (RF.const (QI.ofInt 2) * RF.kern (.app "sqrt" a))
    | _ => RF.zero
  | .exp a => RF.kern (.exp a) * RF.deriv (reread a)
  | .pow b a =>
    let u := reread b
    (reread a) * RF.kern (.pow b a) * RF.deriv u / u

/-- `d/dz` of a polynomial. -/
partial def Poly.deriv (p : Poly) : RF :=
  p.foldl (fun acc (m, a) =>
    (List.range m.length).foldl (fun acc j =>
      let (k, e) := m[j]!
      let rest : Mono := m.set j (k, e - 1) |>.filter (·.2 > 0)
      acc + RF.const (a * QI.ofInt e) * RF.ofPoly [(rest, QI.one)] * k.deriv) acc) RF.zero

/-- `d/dz` of a rational function (quotient rule). -/
partial def RF.deriv (r : RF) : RF :=
  let dn := Poly.deriv r.num
  if r.den.isConst then dn / RF.ofPoly r.den
  else
    let dd := Poly.deriv r.den
    let n := RF.ofPoly r.num
    let d := RF.ofPoly r.den
    (dn * d - n * dd) / (d * d)

end

mutual

/-- Substitute `z := x` and `c := 0` in a kernel. -/
partial def Kern.subst (x : RF) : Kern → RF
  | .var "z" => x
  | .var "c" => RF.zero
  | .var v => RF.kern (.var v)
  | .app f a => (mkApp f (RF.subst (reread a) x)).toOption.getD RF.zero
  | .exp a => (mkExp (RF.subst (reread a) x)).toOption.getD RF.zero
  | .pow b a => (mkPow (RF.subst (reread b) x) (reread a)).toOption.getD RF.zero

/-- Substitute `z := x`, `c := 0` in a polynomial. -/
partial def Poly.subst (x : RF) (p : Poly) : RF :=
  p.foldl (fun acc (m, a) =>
    acc + m.foldl (fun t (k, e) => t * (k.subst x).pow e) (RF.const a)) RF.zero

/-- Substitute `z := x`, `c := 0` (REDUCE `sub((z = x, c = 0), E)`). -/
partial def RF.subst (r : RF) (x : RF) : RF := Poly.subst x r.num / Poly.subst x r.den

end

/-- Julia `newton_raphson(E, m)` (`src/internals.jl:9-12`): `z - m*(E/df(E, z))`. -/
def newtonRaphson (E : JExpr) (m : QI) : Except String RF := do
  let f ← simp E
  let df := RF.deriv f
  if df.isZero then throw "the derivative vanishes"
  return RF.kern (.var "z") - RF.const m * (f / df)

/-- Julia `recomp(E, x, j)` (`src/internals.jl:15`): the `j`-fold composition of `E` at `x`,
with `c := 0`. -/
def recomp (E : RF) (x : RF) : Nat → RF
  | 0 | 1 => E.subst x
  | j + 1 => E.subst (recomp E x j)

/-! ## REDUCE's printed forms -/

/-- REDUCE's prefix forms as its printer sees them. -/
inductive Out where
  /-- a nonnegative integer -/
  | num (n : Nat)
  /-- a kernel -/
  | kern (k : Kern)
  /-- `b^e`, `e ≥ 2` -/
  | pow (b : Out) (e : Nat)
  /-- a product -/
  | times (fs : List Out)
  /-- a sum -/
  | plus (ts : List Out)
  /-- a negation -/
  | minus (a : Out)
  /-- a quotient -/
  | quot (n d : Out)
  deriving Inhabited

namespace Out

/-- A term `c · k₁^e₁ ⋯` with `c > 0`. -/
def term (c : Nat) (m : Mono) : Out :=
  let ks := m.map fun (k, e) => if e == 1 then kern k else pow (kern k) e
  match c, ks with
  | c, [] => num c
  | 1, [k] => k
  | 1, ks => times ks
  | c, ks => times (num c :: ks)

/-- A signed term. -/
def sterm (c : Int) (m : Mono) : Out := if c < 0 then minus (term c.natAbs m) else term c.natAbs m

/-- The terms of a Gaussian-integer polynomial with `i` as a kernel, in REDUCE's order. -/
def terms (p : Poly) : List (Int × Mono) :=
  let iK := Kern.var "i"
  let ts : List (Int × Mono) := p.flatMap fun (m, a) =>
    (if a.re != 0 then [(a.re.num, m)] else []) ++
    (if a.im != 0 then [(a.im.num, Mono.mul [(iK, 1)] m)] else [])
  (ts.toArray.qsort fun a b => Mono.cmp a.2 b.2 == .gt).toList

/-- A polynomial as a sum (a single term stays a term). -/
def ofPoly (p : Poly) : Out :=
  match terms p with
  | [] => num 0
  | [(c, m)] => sterm c m
  | ts => plus (ts.map fun (c, m) => sterm c m)

/-- A polynomial with a negative leading coefficient printed as `-(…)` (REDUCE's printer). -/
def ofPolySigned (p : Poly) : Out :=
  match terms p with
  | (c, _) :: _ :: _ => if c < 0 then minus (ofPoly (Poly.neg p)) else ofPoly p
  | _ => ofPoly p

/-- REDUCE's default printing with `allfac`: a sum's common integer factor and common powers of
kernels are written outside it (`(z^{2}-2) z^{2}`), a negative leading coefficient as `-(…)`. -/
def ofPolyAllfac (p : Poly) : Out :=
  let ts := terms p
  if ts.length < 2 then ofPoly p else
  let content : Nat := ts.foldl (fun g (c, _) => Nat.gcd g c.natAbs) 0
  let g := Poly.monoGcd p
  if content ≤ 1 && g.isEmpty then ofPolySigned p else
  let prim := Poly.divMono (Poly.smul (QI.ofRat (1 / (content : Rat))) p) g
  let sgn := match terms prim with
    | (c, _) :: _ => decide (c < 0)
    | [] => false
  let body := ofPoly (if sgn then Poly.neg prim else prim)
  let monos : List Out := g.map fun (k, e) => if e == 1 then kern k else pow (kern k) e
  let fs := (if content ≤ 1 then [] else [num content]) ++ [body] ++ monos
  let prod := match fs with | [f] => f | fs => times fs
  if sgn then minus prod else prod

/-- An integer polynomial in `z` (coefficients `[c₀, c₁, …]`) as a sum. -/
def ofZ (a : Array Int) : Out :=
  ofPoly (Poly.ofDense (a.map fun c => QI.ofInt c))

/-- A factor raised to a power. -/
def powOf (b : Out) (e : Nat) : Out := if e == 1 then b else pow b e

/-- REDUCE's `on factor` form of a polynomial: content, the irreducible factors over `ℤ` of a
polynomial in `z` (REDUCE's order, `Wilkinson.factorZ`), the other kernels' common powers and
the power of `z` last; a content of `-1` negates the product. Polynomials with other kernels or
`i` keep their primitive part as one factor. -/
def factored (p : Poly) : Out := Id.run do
  let ts := terms p
  if ts.isEmpty then return num 0
  let content : Nat := ts.foldl (fun g (c, _) => Nat.gcd g c.natAbs) 0
  let lead : Int := (ts.head?.map (·.1)).getD 1
  let sgn : Int := if lead < 0 then -1 else 1
  let prim := Poly.smul (QI.ofRat (sgn / (content : Rat))) p
  let g := Poly.monoGcd prim
  let prim := Poly.divMono prim g
  let (zpow, gOther) := (g.expOf (.var "z"), g.filter fun (k, _) => !k.isZ)
  let facs : List Out :=
    if prim.isUnivariate && prim.all (fun (_, a) => a.im == 0 && a.re.den == 1) && !prim.isConst then
      let fz := factorZ (prim.toDense.map fun a => a.re.num)
      fz.factors.map fun (f, e) => powOf (ofZ f) e
    else if prim.isConst then
      (if prim.constVal == QI.one then [] else [ofPoly prim])
    else [ofPoly prim]
  let monos : List Out := (gOther.map fun (k, e) => powOf (kern k) e) ++
    (if zpow > 0 then [powOf (kern (.var "z")) zpow] else [])
  let fs := (if content == 1 then [] else [num content]) ++ facs ++ monos
  let body := match fs with
    | [] => num 1
    | [f] => f
    | fs => times fs
  return if sgn < 0 then minus body else body

/-- REDUCE's output of a rational function: `num/den`, each `factored` (with `on factor`)
or as sums with the sign pulled out (default printing; `allfac` factors out common monomials
and integers when `allfac` is set). -/
def ofRF (r : RF) (factor : Bool) (allfac : Bool := false) : Out :=
  let pr (p : Poly) : Out :=
    if factor then factored p else if allfac then ofPolyAllfac p else ofPolySigned p
  if r.den.isConst && r.den.constVal == QI.one then pr r.num
  else quot (pr r.num) (pr r.den)

/-! ### Julia expression (REDUCE's linear output, parsed by Julia, `treecombine!`) -/

mutual

/-- Julia-syntax text of REDUCE's linear output (`**` already `^`, `i` already `im`). -/
partial def str : Out → String
  | num n => toString n
  | kern k => kernStr k
  | pow b e => atomStr b ++ "^" ++ toString e
  | times fs => "*".intercalate (fs.map atomStr)
  | plus ts => sumStr ts
  | minus a => "-(" ++ str a ++ ")"
  | quot n d => atomStr n ++ "/" ++ atomStr d

/-- An operand: sums, products, quotients and negations in parentheses. -/
partial def atomStr : Out → String
  | num n => toString n
  | kern k => kernStr k
  | pow b e => atomStr b ++ "^" ++ toString e
  | a => "(" ++ str a ++ ")"

/-- A sum, ` + `/` - ` joined. -/
partial def sumStr : List Out → String
  | [] => "0"
  | t :: ts =>
    ts.foldl (fun acc u => match u with
      | minus a => acc ++ " - " ++ str a
      | a => acc ++ " + " ++ str a) (str t)

/-- A kernel. -/
partial def kernStr : Kern → String
  | .var "e" => "ℯ"
  | .var "pi" => "π"
  | .var "i" => "im"
  | .var v => v
  | .app f a => f ++ "(" ++ str (ofRF (reread a) false) ++ ")"
  | .exp a => "ℯ^" ++ expArg (reread a)
  | .pow b a => powBase (reread b) ++ "^" ++ expArg (reread a)

/-- A power base: parenthesised unless it is a variable. -/
partial def powBase (u : RF) : String :=
  match ofRF u false with
  | kern (.var v) => kernStr (.var v)
  | o => "(" ++ str o ++ ")"

/-- An exponent: parenthesised unless it is a variable. -/
partial def expArg (u : RF) : String :=
  match ofRF u false with
  | kern (.var v) => kernStr (.var v)
  | o => "(" ++ str o ++ ")"

end

/-- Reduce.jl's `treecombine!` rewrites (`src/parser.jl`): a unary minus of a binary minus
becomes the swapped difference (`-(a - b) = b - a`); products and quotients of quotients are
flattened into one quotient. -/
partial def treecombine : JExpr → JExpr
  | .call "-" [a] =>
    match treecombine a with
    | .call "-" [x, y] => .call "-" [y, x]
    | a' => .call "-" [a']
  | .call "*" args =>
    let args := args.map treecombine
    match args.findIdx? (fun a => match a with | .call "/" [_, _] => true | _ => false) with
    | some i =>
      match args[i]! with
      | .call "/" [n, d] => treecombine (.call "/" [.call "*" (args.set i n), d])
      | _ => .call "*" args
    | none => .call "*" args
  | .call "/" [a, b] =>
    match treecombine a, treecombine b with
    | .call "/" [n, d], b' => treecombine (.call "/" [n, .call "*" [d, b']])
    | a', .call "/" [n, d] => treecombine (.call "/" [.call "*" [a', d], n])
    | a', b' => .call "/" [a', b']
  | .call f args => .call f (args.map treecombine)
  | e => e

/-- The Julia `Expr` Fatou.jl gets for a REDUCE result: the linear output parsed by Julia's
parser (`JExpr.parse`) and rewritten by `treecombine`. -/
def toJExpr (o : Out) : Except String JExpr := do
  return treecombine (← JExpr.parse (str o))

/-! ### LaTeX (REDUCE's `rlfi` package) -/

/-- Is it an atomic LaTeX operand (no parentheses needed as an argument)? -/
def isAtomic : Out → Bool
  | num _ => true
  | kern (.var _) => true
  | _ => false

mutual

/-- The `rlfi` LaTeX of a form. -/
partial def latex : Out → String
  | num n => toString n
  | kern k => latexKern k
  | pow b e => latexBase b ++ "^{" ++ toString e ++ "}"
  | times fs => latexTimes fs
  | plus ts => latexSum ts
  | minus a => "-" ++ latexParen a
  | quot n d => latexOperand n ++ "/" ++ latexOperand d

/-- A power base: sums, products, negations and function kernels parenthesised. -/
partial def latexBase : Out → String
  | num n => toString n
  | kern (.var v) => latexKern (.var v)
  | kern (.pow b a) => "\\left(" ++ latexKern (.pow b a) ++ "\\right)"
  | a => "\\left(" ++ latex a ++ "\\right)"

/-- A quotient operand: anything but an atom or a single kernel (power) in `\left(…\right)`. -/
partial def latexOperand : Out → String
  | num n => toString n
  | kern k => latexKern k
  | pow b e => latex (pow b e)
  | a => "\\left(" ++ latex a ++ "\\right)"

/-- A negated operand: sums and quotients parenthesised. -/
partial def latexParen : Out → String
  | plus ts => "\\left(" ++ latexSum ts ++ "\\right)"
  | quot n d => "\\left(" ++ latex (quot n d) ++ "\\right)"
  | a => latex a

/-- A product: factors separated by spaces; a function kernel with an atomic argument is
followed by `\:` (rlfi's spacing after `\sin \,z`). -/
partial def latexTimes (fs : List Out) : String :=
  let parts := fs.map fun f => match f with
    | plus ts => "\\left(" ++ latexSum ts ++ "\\right)"
    | minus a => "\\left(-" ++ latexParen a ++ "\\right)"
    | a => latex a
  let spaced := (List.range parts.length).map fun j =>
    let p := parts[j]!
    let atomicFn := match fs[j]! with
      | kern (.app f a) => f != "sqrt" && isAtomicArg a
      | _ => false
    if atomicFn && j + 1 < parts.length then p ++ "\\:" else p
  " ".intercalate spaced

/-- A sum: terms joined by `+`/`-` without spaces. -/
partial def latexSum : List Out → String
  | [] => "0"
  | t :: ts => ts.foldl (fun acc u => match u with
      | minus a => acc ++ "-" ++ latexTerm a
      | a => acc ++ "+" ++ latexTerm a) (latexTerm t)

/-- A term of a sum. -/
partial def latexTerm : Out → String
  | minus a => "-" ++ latexTerm a
  | plus ts => "\\left(" ++ latexSum ts ++ "\\right)"
  | a => latex a

/-- Is a kernel argument atomic (a variable)? -/
partial def isAtomicArg (a : JExpr) : Bool := isAtomic (ofRF (reread a) false)

/-- A kernel in LaTeX. -/
partial def latexKern : Kern → String
  | .var "pi" => "\\pi "
  | .var v => v
  | .app "sqrt" a => "\\sqrt {" ++ latex (ofRF (reread a) false) ++ "}"
  | .app f a =>
    let o := ofRF (reread a) false
    let name := "\\" ++ f ++ " "
    if isAtomic o then name ++ "\\," ++ latex o else name ++ "\\left(" ++ latex o ++ "\\right)"
  | .exp a => "e^{" ++ latex (ofRF (reread a) false) ++ "}"
  | .pow b a => latexBase (ofRF (reread b) false) ++ "^{" ++ latex (ofRF (reread a) false) ++ "}"

end

end Out

/-- REDUCE's `latex(E)` of a rational function (default printing; line breaks omitted). -/
def latexOf (r : RF) : String := Out.latex (Out.ofRF r false)

/-- The Julia `Expr` of `factor(r)` as Fatou.jl gets it from Reduce.jl. -/
def factorJExpr (r : RF) : Except String JExpr := Out.toJExpr (Out.ofRF r true)

/-- The LaTeX of `factor(r)`. -/
def latexFactor (r : RF) : String := Out.latex (Out.ofRF r true)

/-- REDUCE's `latex(r)` with `allfac` grouping of common factors (the basin bodies `jL`). -/
def latexAllfac (r : RF) : String := Out.latex (Out.ofRF r false (allfac := true))

end CAS

end Fatou
