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
`CAS` built here returns the exact factorization for it. REDUCE's rounded factorizer splits
into linear factors over `ℂ` with 12-digit roots, keeps roots it finds by trial (`±1`, …) as
integers, and orders the factors by its internal bigfloat representation (probed: neither by
value nor by exact factor), so its output cannot be derived from the polynomial alone; the
comparison goldens carry REDUCE's rounded forms, and `PolynomialComparison.ofForms` analyses
them.
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
  | .bigint n => n

/-- Wilkinson's `polyfactors(x, a) = (x - a₁)(x - a₂)⋯(x - aₙ)`, REDUCE-simplified
(src/Wilkinson.jl:26-27). -/
def polyfactors (a : List Lit) : JExpr :=
  toJExpr (factorRF (a.foldl (fun acc r => acc * (Poly.X - Poly.const (litRat r))) 1))

/-- `a₁ + a₂ x + ⋯ + aₙ x^(n-1)`. -/
def ofCoeffs (a : List Lit) : Poly :=
  a.zipIdx.foldl (fun acc (c, i) => acc + Poly.const (litRat c) * Poly.pow Poly.X i) Poly.zero

/-! ### `Reduce.Algebra`: one REDUCE call per operation, `off exp`

Wilkinson's `polyhorner` and `polyexpand` build their polynomial with `Reduce.Algebra`
operations. Each operation on symbolic operands is one REDUCE evaluation, with `exp` off, of
the text of its operands (the previous results as REDUCE printed them); operations on two
Julia numbers are Julia arithmetic. With `exp` off REDUCE does not multiply sums out:

* a number times a sum is distributed (`multd`), but a sum times a power of `x` (or times
  another such product) goes through `mkprod` in `multf` and becomes a product whose sum is a
  *kernel*; the kernel's own text is simplified the same way when it is read;
* `mkprod` (packages/poly/polrep.red) takes out the common numeric factor and power of `x`,
  then keeps the remaining sum `u` unexpanded only if REDUCE's term count `tmsf u` does not
  exceed that of its expansion made primitive (`Alg.tmsf`), makes the leading term (kernel
  terms first, then descending powers) positive, and is applied to each result as well;
* the printer writes a negative content `-1` as `-(p)`, or `c - p` when `p` ends in a negative
  constant, and a kernel with coefficient `1` and no power of `x` inline inside a sum.

This reproduces all of REDUCE's shapes for the ~600 golden coefficient lists
(`reduce.json`, `algebra.json`); the sign and kernel structure is what `exprval` and the
Stieltjes bound see. -/

namespace Alg

/-- A kernel: a primitive sum of terms `(c, kernel?, power of x)` with a positive first term. -/
inductive Ker where
  | mk (ts : List (Int × Option Ker × Nat))
  deriving Inhabited

/-- A working term: rational coefficient, optional kernel, power of `x`. -/
abbrev Term := Rat × Option Ker × Nat

/-- A REDUCE result as printed by `mkprod`: `g · x^m · P / D` with `P` primitive, its first
term positive. -/
structure NF where
  /-- Signed numeric content. -/
  g : Int
  /-- Power of `x` taken out. -/
  m : Nat
  /-- The primitive sum (or a single term with coefficient `1`). -/
  P : List (Int × Option Ker × Nat)
  /-- Denominator. -/
  D : Nat
  deriving Inhabited

mutual

/-- A kernel as a sum. -/
partial def kerRF : Ker → RF
  | .mk ts => plus (ts.flatMap fun (c, k, e) => termRF c k e true)

/-- A term's forms: `c · K · x^e` (negated when `c < 0`); inside a sum, a kernel with
coefficient `1` and no power of `x` is spliced in as its terms. -/
partial def termRF (c : Int) (k : Option Ker) (e : Nat) (inSum : Bool) : List RF :=
  match k with
  | none => [signed c e]
  | some K =>
    if inSum && c == 1 && e == 0 then
      match K with | .mk ts => ts.flatMap fun (c', k', e') => termRF c' k' e' true
    else if inSum || c > 0 then
      let fs := (if c.natAbs != 1 then [num c.natAbs] else []) ++ [kerRF K] ++
        (if e > 0 then [xpow e] else [])
      let t := match fs with | [f] => f | fs => times fs
      [if c < 0 then minus t else t]
    else
      -- a negative product at top level: the sign goes on the kernel factor (`-(p) * x`,
      -- printed `(c - q) * x` when `p = q - c`) or on the number (`-2 * (p) * x`)
      let fs := (if c == -1 then [minus (kerRF K)] else [num c, kerRF K]) ++
        (if e > 0 then [xpow e] else [])
      [match fs with | [f] => f | fs => times fs]

end

/-- Printing key of a kernel (for combining like terms). -/
def kerKey : Option Ker → String
  | none => ""
  | some K => (kerRF K).str

/-- Combine like terms and drop zeros. -/
def combine (ts : List Term) : List Term :=
  let out := ts.foldl (fun (acc : List Term) (c, k, e) =>
    match acc.findIdx? (fun (_, k', e') => e' == e && kerKey k' == kerKey k) with
    | some i => acc.modify i fun (c', k', e') => (c' + c, k', e')
    | none => acc ++ [(c, k, e)]) []
  out.filter (·.1 != 0)

/-- REDUCE's order of the terms of a sum: kernel terms first, then descending powers. -/
def order (ts : List Term) : List Term :=
  let ks := ts.filter (·.2.1.isSome)
  let ns := ts.filter (·.2.1.isNone)
  ks.mergeSort (fun a b => a.2.2 ≥ b.2.2) ++ ns.mergeSort (fun a b => a.2.2 ≥ b.2.2)

/-- `mkprod` on a numerator: content, power of `x` and sign out. -/
def normalize0 (ts : List Term) : NF :=
  match order (combine ts) with
  | [] => ⟨0, 0, [], 1⟩
  | ts@(first :: _) =>
    let D := ts.foldl (fun acc (c, _, _) => Nat.lcm acc c.den) 1
    let N := ts.map fun (c, k, e) => ((c * (D : Rat)).num, k, e)
    let G : Nat := N.foldl (fun (acc : Nat) (c, _, _) => Nat.gcd acc c.natAbs) 0
    let s : Int := if first.1 < 0 then -1 else 1
    let m := N.foldl (fun acc (_, _, e) => min acc e) (first.2.2)
    ⟨s * G, m, N.map fun (c, k, e) => (c / (s * G), k, e - m), D⟩

/-- Every kernel multiplied out (REDUCE `expnd`). -/
partial def expandAll (ts : List (Int × Option Ker × Nat)) : List Term :=
  combine (ts.flatMap fun (c, k, e) =>
    match k with
    | none => [((c : Rat), none, e)]
    | some (.mk inner) => (expandAll inner).map fun (c', _, e') => ((c : Rat) * c', none, e + e'))

/-- `expandAll` on working terms. -/
def expandTerms (ts : List Term) : List Term :=
  combine (ts.flatMap fun (c, k, e) =>
    match k with
    | none => [(c, none, e)]
    | some (.mk inner) => (expandAll inner).map fun (c', _, e') => (c * c', none, e + e'))

/-- REDUCE `tmsf!*` of a numeric coefficient: `0` for `±1`, else `1`. -/
@[inline] def tmsCoeff (c : Int) : Nat := if c.natAbs == 1 then 0 else 1

/-- REDUCE's degree surcharge in `tmsf`: `+1` for a square, `+2` for a higher power. -/
@[inline] def tmsDeg (e : Nat) : Nat := if e ≤ 1 then 0 else if e == 2 then 1 else 2

/-- REDUCE `tmsf` of a polynomial in `x` alone: per term `1 + tmsf*(c) + degree surcharge`,
and `1` for a constant term. -/
def tmsX (ts : List (Int × Nat)) : Nat :=
  ts.foldl (fun acc (c, e) => acc + (if e == 0 then 1 else 1 + tmsCoeff c + tmsDeg e)) 0

/-- REDUCE `tmsf u` (packages/poly/polrep.red), the size `mkprod` compares, on the recursive
form in which a sum kernel `K` ranks above `x`: `K · lc + red` costs `tmsf K + tmsf*(lc)`
(`tmsf*` is `0` for `±1`), each `c·x^e` of the reductum `1 + tmsf*(c)` plus `1` for `e = 2` and
`2` for `e > 2`, and the constant term `1`. -/
partial def tmsf (ts : List (Int × Option Ker × Nat)) : Nat :=
  let ks := ts.filterMap fun (c, k, e) => k.map fun K => (K, c, e)
  let keys := (ks.map fun (K, _, _) => kerKey (some K)).eraseDups
  let kcost := keys.foldl (fun acc key =>
    let grp := ks.filter fun (K, _, _) => kerKey (some K) == key
    match grp with
    | [] => acc
    | (Ker.mk inner, _, _) :: _ =>
      let lc := grp.map fun (_, c, e) => (c, e)
      let star := match lc with
        | [(c, 0)] => tmsCoeff c
        | _ => tmsX lc
      acc + tmsf inner + star) 0
  kcost + tmsX (ts.filterMap fun (c, k, e) => if k.isNone then some (c, e) else none)

/-- REDUCE `mkprod` (packages/poly/polrep.red) on a numerator: the common factor `w` (numeric
content and power of `x`) comes out; a sum `u` with a kernel is kept only if `tmsf u` does not
exceed `tmsf` of its expansion made primitive, otherwise the expansion replaces it
(`2*(x - 3) + x^2` stays, `3*(2x + 1) - 2x^3` becomes `3 + 6x - 2x^3`); the leading term
(kernel terms first, then descending powers) is made positive. REDUCE applies it to every
sum it makes a kernel of and to each result. -/
partial def normalize (ts : List Term) : NF :=
  let nf := normalize0 ts
  if nf.P.length ≥ 2 && nf.P.any (·.2.1.isSome) then
    let ex := normalize0 (expandAll nf.P)
    if ex.P.length ≤ 1 || tmsf nf.P > tmsf ex.P then normalize0 (expandTerms ts) else nf
  else nf

mutual

/-- REDUCE reading a printed sum back: a kernel with no power of `x` is distributed, one
times a power of `x` stays a (re-read, re-normalized) kernel. -/
partial def reread (ts : List (Int × Option Ker × Nat)) : List Term :=
  combine (ts.flatMap fun (c, k, e) =>
    match k with
    | none => [((c : Rat), none, e)]
    | some (.mk inner) =>
      if e == 0 then (reread inner).map fun (c', k', e') => ((c : Rat) * c', k', e')
      else kerTerm (c : Rat) (reread inner) e)

/-- `coef · (sum) · x^e` with `e ≥ 1`: the sum becomes a kernel through `mkprod`. -/
partial def kerTerm (coef : Rat) (ts : List Term) (e : Nat) : List Term :=
  let nf := normalize ts
  match nf.P with
  | [] => []
  | [(c, k, e')] => [(coef * (nf.g : Rat) * (c : Rat) / (nf.D : Rat), k, e + nf.m + e')]
  | P => [(coef * (nf.g : Rat) / (nf.D : Rat), some (.mk P), e + nf.m)]

end

/-- A printed result read back as terms. -/
def read (nf : NF) : List Term :=
  let scale : Rat := (nf.g : Rat) / (nf.D : Rat)
  match nf.P with
  | [] => []
  | [(c, k, e)] =>
    match k with
    | some (.mk inner) =>
      if e + nf.m == 0 then (reread inner).map fun (c', k', e') => (scale * (c : Rat) * c', k', e')
      else kerTerm (scale * (c : Rat)) (reread inner) (e + nf.m)
    | none => [(scale * (c : Rat), none, e + nf.m)]
  | P => if nf.m ≥ 1 then kerTerm scale (reread P) nf.m else (reread P).map fun (c, k, e) => (scale * c, k, e)

/-- `x · H` for a printed `H`: a sum times `x` is a kernel. -/
def mulX (nf : NF) : List Term :=
  match nf.P with
  | [] => []
  | [_] => (read nf).map fun (c, k, e) => (c, k, e + 1)
  | P => kerTerm ((nf.g : Rat) / (nf.D : Rat)) (reread P) (nf.m + 1)

/-- The printed form of a result. -/
def nfRF (nf : NF) : RF :=
  let body : RF := match nf.P with
    | [] => num 0
    | [(c, k, e)] =>
      (termRF (nf.g * c) k (e + nf.m) false).headD (num 0)
    | P =>
      let sum := plus (P.flatMap fun (c, k, e) => termRF c k e true)
      let core := if nf.g == 1 then [sum] else if nf.g == -1 then [minus sum] else [num nf.g, sum]
      let fs := core ++ (if nf.m > 0 then [xpow nf.m] else [])
      match fs with | [f] => f | fs => times fs
  over body nf.D

/-- A `Reduce.Algebra` value: a Julia number or a REDUCE result. -/
inductive AV where
  /-- A Julia number (`Int64` or `Float64`). -/
  | lit (l : Lit)
  /-- A REDUCE result (Julia `Expr`). -/
  | red (nf : NF)
  deriving Inhabited

/-- Terms of a value. -/
def terms : AV → List Term
  | .lit l => let r := litRat l; if r == 0 then [] else [(r, none, 0)]
  | .red nf => read nf

/-- A REDUCE evaluation: an integer result comes back as a Julia `Int`. -/
def ofTerms (ts : List Term) : AV :=
  let nf := normalize ts
  match nf.P with
  | [] => .lit (.int 0)
  | [(_, none, 0)] => if nf.m == 0 && nf.D == 1 then .lit (.int nf.g) else .red nf
  | _ => .red nf

/-- Julia `+` on two numbers. -/
def litAdd : Lit → Lit → Lit
  | .int a, .int b => .int (a + b)
  | .int a, .f64 b => .f64 (Float.ofInt a + b)
  | .f64 a, .int b => .f64 (a + Float.ofInt b)
  | .f64 a, .f64 b => .f64 (a + b)
  | a, _ => a

/-- `Algebra.:+(a, b)`. -/
def add : AV → AV → AV
  | .lit a, .lit b => .lit (litAdd a b)
  | a, b => ofTerms (terms a ++ terms b)

/-- `Algebra.:*(x, h)`. -/
def mulX' : AV → AV
  | .lit l => ofTerms ((terms (.lit l)).map fun (c, k, e) => (c, k, e + 1))
  | .red nf => ofTerms (mulX nf)

/-- `Algebra.:*(a, Algebra.:^(x, j))` for `j ≥ 1`. -/
def monomial (a : Lit) (j : Nat) : AV :=
  ofTerms ((terms (.lit a)).map fun (c, k, _) => (c, k, j))

/-- The Julia expression of a value. -/
def toJ : AV → JExpr
  | .lit l => .lit l
  | .red nf => toJExpr (nfRF nf)

end Alg

/-- Wilkinson's `polyhorner(x, a) = a₁ + x(a₂ + x(⋯ aₙ))` (src/Wilkinson.jl:23-24), step by step
through `Reduce.Algebra` (`polyhorner(x,a,k) = k == length(a) ? a[k] : a[k] + x*polyhorner(x,a,k+1)`;
see `Alg`). -/
def polyhorner (a : List Lit) : JExpr :=
  match a.reverse with
  | [] => .lit (.int 0)
  | last :: rest => Alg.toJ (rest.foldl (fun h ak => Alg.add (.lit ak) (Alg.mulX' h)) (.lit last))

/-- Wilkinson's `polyexpand(x, a) = aₙ x^(n-1) + ⋯ + a₁` (src/Wilkinson.jl:29-30), step by step
through `Reduce.Algebra` (`polyexpand(x,a,k) = k == 1 ? a[1] : a[k]*x^(k-1) + polyexpand(x,a,k-1)`). -/
def polyexpand (a : List Lit) : JExpr :=
  match a with
  | [] => .lit (.int 0)
  | a1 :: rest =>
    Alg.toJ ((rest.zipIdx.foldl (fun (s : Alg.AV) (ak, i) => Alg.add (Alg.monomial ak (i + 1)) s)) (.lit a1))

/-- The REDUCE emulation as Wilkinson's computer-algebra backend (`factor` stands in
for `factor` with `on rounded`, so `rxtra` is always false). -/
def cas : CAS := ⟨expand, horner, factor, factor⟩

end Reduce

/-- Julia `tests(d, n, T; apply = polyfactors)` (src/polynomial.jl:163-179): run
`testpoly` on `apply(x, roots)` for each root list (Julia draws `rand(d)` roots;
the caller supplies them) and return the fractions `(agree, factorizable, conj)`. -/
def tests (rootSets : List (List Float)) (T : NumType := .f64)
    (apply : List Lit → JExpr := Reduce.polyfactors) : Rat × Rat × Rat :=
  let n : Rat := rootSets.length
  let (a, f, c) := rootSets.foldl (fun (a, f, c) rs =>
    let (x, y, z) := testpoly Reduce.cas (apply (rs.map Lit.f64)) T
    (a + (if x then 1 else 0), f + (if y then 1 else 0), c + (if z then 1 else 0))) ((0 : Nat), (0 : Nat), (0 : Nat))
  if rootSets.isEmpty then (0, 0, 0) else ((a : Rat) / n, (f : Rat) / n, (c : Rat) / n)

/-- Julia `PolynomialComparison(j, T, N)` with the REDUCE emulation. -/
def PolynomialComparison.ofReduce (j : JExpr) (T : NumType := .f64) (N : Nat := 3000) : PolynomialComparison :=
  PolynomialComparison.make Reduce.cas j T N

end Wilkinson
