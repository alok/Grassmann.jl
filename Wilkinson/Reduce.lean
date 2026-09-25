import Wilkinson.Poly
import Wilkinson.Parse
import Wilkinson.Analysis

/-!
# REDUCE's expanded, Horner and factored forms

Wilkinson.jl asks the REDUCE CAS (through Reduce.jl, with `Reduce.Rational(false)`)
for `expand`, `horner` and `factor` of a polynomial and gets back a Julia `Expr`:
REDUCE's linear output re-parsed by Julia's parser. The *shape* of that tree is
what the analysis measures (`exprval` counts calls and literals; the Stieltjes
bound depends on the evaluation order), so this module reproduces the shapes
from the polynomial alone, following REDUCE's own algorithms:

* **expand**: the polynomial over its least common denominator `N/D`, printed
  with `allfac` (on by default): `ckrn1`/`gck2` (packages/alg/extout.red) pull a
  common numeric factor and power of `x` out of `N` (`2 * x * (3 * x ^ 2 + 2)`).
  `gck2` keeps a *negative* common factor only when two coefficients are equal
  (`-2 * (x ^ 2 + 1)` but `3 * (-(x ^ 2) - 2)`);
* **horner**: `hornerf1` (packages/poly/horner.red) folds `x^n a + x^m b + c` into
  `x^m (x^(n-m) a + b) + c`; every folded sum becomes a product kernel through
  `mkprod`/`mksp!*` (packages/poly/polrep.red), which divides out its content and
  makes it positive (`-3 * (x ^ 2 - 2) * x`, `-((x + 5)) * x - 6`);
* **factor**: content, factors over `ℤ` in REDUCE's order (degree, then
  coefficients, descending), the power of `x` last; a content of `-1` negates the
  first factor;
* the printer writes `-(p - c)` for a negated sum ending in a negative constant
  as `c - p` (`4 - x`, `(1 - (x + 2) * x) * x`).

The result is printed as a Julia-syntax string and parsed by `JExpr.parse`, so
the parser's flattening rules (`(x ^ 3 + 5 * x ^ 2 + 3x) - 9`) apply exactly as
in Julia. `factor` with `rounded` (numeric roots) is not reproduced; the
`CAS` built here returns the exact factorization for it.
-/

namespace Wilkinson

namespace Reduce

/-- REDUCE prefix forms, as its printer sees them. -/
inductive RF where
  /-- An integer. -/
  | num (n : Int)
  /-- `x^k`, `k ≥ 1`. -/
  | xpow (k : Nat)
  /-- `c*x^k`, `c ≥ 2`, `k ≥ 1`. -/
  | term (c : Nat) (k : Nat)
  /-- A sum; negative terms are `minus`. -/
  | plus (ts : List RF)
  /-- Negation. -/
  | minus (a : RF)
  /-- A product. -/
  | times (fs : List RF)
  /-- A power of a sum. -/
  | expt (b : RF) (e : Nat)
  /-- A quotient by a positive integer. -/
  | quot (a : RF) (d : Nat)
  deriving Inhabited, BEq

namespace RF

/-- `c·x^k` for `c > 0`. -/
def mono (c : Nat) (k : Nat) : RF :=
  if k = 0 then num c else if c = 1 then xpow k else term c k

/-- `c·x^k` with a sign. -/
def signed (c : Int) (k : Nat) : RF :=
  if c < 0 then minus (mono c.natAbs k) else mono c.natAbs k

/-- A sum of signed monomials (descending powers). -/
def ofTerms (ts : List (Int × Nat)) : RF :=
  match ts with
  | [(c, k)] => signed c k
  | _ => plus (ts.map fun (c, k) => signed c k)

/-- Is this a sum whose last term is negative (printed `c - p` when negated)? -/
def endsNegative : RF → Bool
  | plus ts => match ts.getLast? with
    | some (minus _) => ts.length ≥ 2
    | _ => false
  | _ => false

mutual

/-- Julia-syntax text of a form at top level. -/
partial def str : RF → String
  | num n => toString n
  | xpow k => if k = 1 then "x" else s!"x^{k}"
  | term c k => if k = 1 then s!"{c}*x" else s!"{c}*x^{k}"
  | plus ts => sumStr ts
  | minus a => negStr a
  | times fs => "*".intercalate (fs.map factorStr)
  | expt b e => factorStr b ++ s!"^{e}"
  | quot a d => quotOperand a ++ s!"/{d}"

/-- Terms joined by ` + `/` - `. -/
partial def sumStr : List RF → String
  | [] => "0"
  | t :: ts =>
    ts.foldl (fun acc u => match u with
      | minus a => acc ++ " - " ++ termStr a
      | a => acc ++ " + " ++ termStr a) (match t with | minus a => negStr a | a => termStr a)

/-- A term of a sum (a nested sum is parenthesised). -/
partial def termStr : RF → String
  | plus ts => "(" ++ sumStr ts ++ ")"
  | a => str a

/-- REDUCE's printing of `(minus a)`: `-(p) - …` is written `c - p` when `a` is a
sum ending in a negative constant (`4 - x`, `1 - (x ^ 2 - x)`). -/
partial def negStr : RF → String
  | num n => toString (-n)
  | plus ts =>
    match ts.getLast?, ts.dropLast with
    | some (minus c), [r] => termStr c ++ " - " ++ termStr r
    | some (minus c), rs@(_ :: _ :: _) => termStr c ++ " - (" ++ sumStr rs ++ ")"
    | _, _ => "-(" ++ sumStr ts ++ ")"
  | a => "-" ++ factorStr a

/-- A factor of a product (sums parenthesised). -/
partial def factorStr : RF → String
  | plus ts => "(" ++ sumStr ts ++ ")"
  | minus a => if endsNegative a then "(" ++ negStr a ++ ")" else negStr a
  | quot a d => "(" ++ str (quot a d) ++ ")"
  | a => str a

/-- The numerator of a quotient. -/
partial def quotOperand : RF → String
  | plus ts => "(" ++ sumStr ts ++ ")"
  | minus a => if endsNegative a then "(" ++ negStr a ++ ")" else negStr a
  | a => str a

end

end RF

open RF

/-- Descending nonzero terms `(c, k)` of an integer polynomial. -/
def termsDesc (a : Array Int) : List (Int × Nat) :=
  ((List.range a.size).reverse.filterMap fun k => let c := a[k]!; if c == 0 then none else some (c, k))

/-- REDUCE `gck2` on integers: equal arguments give themselves (even when
negative); otherwise the positive gcd, `1` if either is `1`. -/
def gck2 (u v : Int) : Int :=
  if u == v then u else if u == 1 || v == 1 then 1 else Nat.gcd u.natAbs v.natAbs

/-- REDUCE `ckrn1` of a univariate integer polynomial (terms descending): the
common numeric factor and power of `x` that `allfac` prints outside. -/
def ckrn (ts : List (Int × Nat)) : Int × Nat :=
  match ts with
  | [] => (1, 0)
  | (c, k) :: rest => go c k rest
where
  /-- Fold `gck2` down the terms. -/
  go (g : Int) (k : Nat) : List (Int × Nat) → Int × Nat
    | [] => (g, k)
    | (c, j) :: rest => if j = 0 then (gck2 c g, 0) else go (gck2 c g) j rest

/-- The `allfac` product `g · x^m · inner` (`-1` becomes a negation). -/
def withContent (g : Int) (m : Nat) (inner : RF) : RF :=
  let fs := (if g.natAbs != 1 then [num g] else []) ++ (if m > 0 then [xpow m] else []) ++ [inner]
  let t := match fs with | [f] => f | fs => times fs
  if g == -1 then minus t else t

/-- Divide by the denominator when it is not `1`. -/
def over (body : RF) (D : Nat) : RF := if D == 1 then body else quot body D

/-- REDUCE's `expand` output (`on exp`, `on allfac`, `off rational`). -/
def expandRF (p : Poly) : RF :=
  let (N, D) := p.toZ
  match termsDesc N with
  | [] => num 0
  | [(c, k)] => over (signed c k) D
  | ts =>
    let (g, m) := ckrn ts
    if g == 1 && m == 0 then over (ofTerms ts) D
    else over (withContent g m (ofTerms (ts.map fun (c, k) => (c / g, k - m)))) D

/-- A folded Horner kernel `lead · x^d + b` (`b ≠ 0`, `lead` positive). -/
inductive HK where
  /-- `a · x^d + b` with a numeric `a > 0`. -/
  | base (a : Int) (d : Nat) (b : Int)
  /-- `h · K · x^d + b` with `h > 0` and an inner kernel `K`. -/
  | nest (h : Int) (k : HK) (d : Nat) (b : Int)
  deriving Inhabited

/-- The coefficient in front of the current Horner state: a number, or `g · K`. -/
inductive HLead where
  /-- A plain coefficient. -/
  | num (a : Int)
  /-- A normalised kernel with its multiplier. -/
  | ker (g : Int) (k : HK)
  deriving Inhabited

/-- A kernel as a sum. -/
def hkRF : HK → RF
  | .base a d b => plus [mono a.natAbs d, signed b 0]
  | .nest h k d b =>
    plus [times ((if h != 1 then [num h] else []) ++ [hkRF k, xpow d]), signed b 0]

/-- `g · K · x^p` as a product (`g = -1` negates the kernel). -/
def kerProduct (g : Int) (k : HK) (p : Nat) : RF :=
  let kf := if g == -1 then minus (hkRF k) else hkRF k
  times ((if g.natAbs != 1 then [num g] else []) ++ [kf] ++ (if p > 0 then [xpow p] else []))

/-- One `hornerf1` fold: `F · x^(p - e) + a` as a normalised kernel (`mkprod`:
content out, leading coefficient positive). -/
def fold (F : HLead) (p : Nat) (a : Int) (e : Nat) : HLead :=
  let leadVal : Int := match F with | .num c => c | .ker g _ => g
  let g' : Int := (if leadVal < 0 then -1 else 1) * Nat.gcd leadVal.natAbs a.natAbs
  let d := p - e
  match F with
  | .num c => .ker g' (.base (c / g') d (a / g'))
  | .ker g k => .ker g' (.nest (g / g') k d (a / g'))

/-- REDUCE's `horner` output. -/
def hornerRF (p : Poly) : RF :=
  let (N, D) := p.toZ
  let ts := termsDesc N
  let xts := ts.filter (·.2 > 0)
  let c0 := N[0]?.getD 0
  match xts with
  | (a1, e1) :: rest@(_ :: _) =>
    let (F, pw) := rest.foldl (fun (F, pw) (a, e) => (fold F pw a e, e)) (HLead.num a1, e1)
    match F with
    | .num _ => expandRF p
    | .ker g k =>
      if c0 == 0 then over (kerProduct g k pw) D
      else
        let ct := gck2 c0 g
        if ct == 1 then over (plus [kerProduct g k pw, signed c0 0]) D
        else over (withContent ct 0 (plus [kerProduct (g / ct) k pw, signed (c0 / ct) 0])) D
  | _ => expandRF p

/-- REDUCE's `factor` output (exact factorization over `ℤ`). -/
def factorRF (p : Poly) : RF :=
  let (N, D) := p.toZ
  if N.all (· == 0) then num 0 else
  let fz := factorZ N
  let elems := fz.factors.map (fun (f, e) =>
      let s := ofTerms (termsDesc f)
      if e == 1 then s else expt s e) ++ (if fz.xpow > 0 then [xpow fz.xpow] else [])
  let c := fz.content
  let body := match elems with
    | [] => num c
    | [e] => if c == 1 then e else if c == -1 then minus e else times [num c, e]
    | e :: es => if c == 1 then times (e :: es) else if c == -1 then times (minus e :: es)
                 else times (num c :: e :: es)
  over body D

/-- Render a form as the Julia `Expr` Reduce.jl returns. -/
def toJExpr (f : RF) : JExpr :=
  match JExpr.parse f.str with
  | .ok e => e
  | .error _ => .sym f.str

/-- `rcall(e, :expand)`; `e` itself if it is not a polynomial in `x`. -/
def expand (e : JExpr) : JExpr := ((Poly.ofJExpr e).map (toJExpr ∘ expandRF)).getD e
/-- `rcall(e, :horner)`. -/
def horner (e : JExpr) : JExpr := ((Poly.ofJExpr e).map (toJExpr ∘ hornerRF)).getD e
/-- `rcall(e, :factor)`. -/
def factor (e : JExpr) : JExpr := ((Poly.ofJExpr e).map (toJExpr ∘ factorRF)).getD e

/-- A Julia number as REDUCE reads it (`Float64` literals by their decimal text). -/
def litRat : Lit → Rat
  | .int n => n
  | .f64 v => Poly.decimalRat v
  | .f32 v => Poly.decimalRat v.toFloat
  | .big v => Poly.decimalRat v.toFloat

/-- Wilkinson's `polyfactors(x, a) = (x - a₁)(x - a₂)⋯(x - aₙ)`, REDUCE-simplified
(src/Wilkinson.jl:26-27). -/
def polyfactors (a : List Lit) : JExpr :=
  toJExpr (factorRF (a.foldl (fun acc r => acc * (Poly.X - Poly.const (litRat r))) 1))

/-- `a₁ + a₂ x + ⋯ + aₙ x^(n-1)`. -/
def ofCoeffs (a : List Lit) : Poly :=
  a.zipIdx.foldl (fun acc (c, i) => acc + Poly.const (litRat c) * Poly.pow Poly.X i) Poly.zero

/-- Wilkinson's `polyhorner(x, a) = a₁ + x(a₂ + x(⋯ aₙ))` (src/Wilkinson.jl:23-24).
Julia builds it with `Reduce.Algebra` operations, whose printed shapes come from
REDUCE's `off exp` simplifier; the port returns the same polynomial in REDUCE's
`horner` shape (and, as in Julia, a one-element list as its literal). -/
def polyhorner (a : List Lit) : JExpr :=
  match a with
  | [c] => .lit c
  | _ => toJExpr (hornerRF (ofCoeffs a))

/-- Wilkinson's `polyexpand(x, a) = aₙ x^(n-1) + ⋯ + a₁` (src/Wilkinson.jl:29-30),
in REDUCE's `expand` shape (see `polyhorner`). -/
def polyexpand (a : List Lit) : JExpr :=
  match a with
  | [c] => .lit c
  | _ => toJExpr (expandRF (ofCoeffs a))

/-- The REDUCE emulation as Wilkinson's computer-algebra backend (`factor` stands in
for `factor` with `on rounded`, so `rxtra` is always false). -/
def cas : CAS := ⟨expand, horner, factor, factor⟩

end Reduce

/-- Julia `PolynomialComparison(j, T, N)` with the REDUCE emulation. -/
def PolynomialComparison.ofReduce (j : JExpr) (T : NumType := .f64) (N : Nat := 3000) : PolynomialComparison :=
  PolynomialComparison.make Reduce.cas j T N

end Wilkinson
