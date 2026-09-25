import JuliaBase.Ryu
import Wilkinson.Expr
import Wilkinson.Zassenhaus

/-!
# `ℚ[x]` and factorization over `ℤ`

Wilkinson hands every polynomial to the REDUCE computer-algebra system for its
expanded, Horner and factored forms. The port replaces REDUCE with exact
univariate arithmetic: `Poly` is `ℚ[x]` (dense, ascending coefficients), read
from Julia expressions the way REDUCE reads them (a float literal is its printed
decimal, `0.1 = 1/10`, since Julia sends REDUCE the text `0.1`), and `factorZ`
factors a primitive integer polynomial into irreducibles over `ℤ`:

1. content and the power of `x` are split off;
2. Yun's square-free decomposition (over `ℚ`, made primitive);
3. linear factors from rational roots, found `p`-adically (roots mod a small
   prime, Newton lifting, rational reconstruction), for coefficients of any size;
4. the Berlekamp–Zassenhaus algorithm for what remains (`Wilkinson.Zassenhaus`: modular
   factorization, Hensel lifting, recombination), which is complete: every square-free
   primitive polynomial is split into its irreducible factors, as REDUCE's `factor` does.

The printed shapes REDUCE gives these objects are in `Wilkinson.Reduce`.
-/

namespace Wilkinson

/-- A polynomial in `x` over `ℚ`: coefficients in ascending order, no trailing zeros. -/
structure Poly where
  /-- `coeffs[i]` is the coefficient of `x^i`. -/
  coeffs : Array Rat
  deriving BEq, Inhabited

namespace Poly

/-- Drop trailing zero coefficients. -/
def trim (a : Array Rat) : Array Rat :=
  go a a.size
where
  /-- Pop zeros from the end. -/
  go (a : Array Rat) : Nat → Array Rat
    | 0 => a
    | k + 1 => if a.back? == some 0 then go a.pop k else a

/-- Normalising constructor. -/
def mk' (a : Array Rat) : Poly := ⟨trim a⟩

/-- The zero polynomial. -/
def zero : Poly := ⟨#[]⟩
/-- A constant. -/
def const (c : Rat) : Poly := mk' #[c]
/-- The variable `x`. -/
def X : Poly := ⟨#[0, 1]⟩

instance {n : Nat} : OfNat Poly n := ⟨const n⟩

/-- Coefficient of `x^i`. -/
@[inline] def coeff (p : Poly) (i : Nat) : Rat := p.coeffs[i]?.getD 0
/-- Is it the zero polynomial? -/
@[inline] def isZero (p : Poly) : Bool := p.coeffs.isEmpty
/-- Degree (`0` for constants and for zero). -/
@[inline] def degree (p : Poly) : Nat := p.coeffs.size - 1
/-- Leading coefficient (`0` for zero). -/
@[inline] def lc (p : Poly) : Rat := p.coeffs.back?.getD 0

/-- Sum. -/
def add (p q : Poly) : Poly :=
  mk' ((Array.range (max p.coeffs.size q.coeffs.size)).map fun i => p.coeff i + q.coeff i)

/-- Scalar multiple. -/
def smul (c : Rat) (p : Poly) : Poly := mk' (p.coeffs.map (c * ·))

/-- Negation. -/
def neg (p : Poly) : Poly := ⟨p.coeffs.map (- ·)⟩

/-- Product (schoolbook). -/
def mul (p q : Poly) : Poly :=
  if p.isZero || q.isZero then zero else
  mk' <| (Array.range (p.coeffs.size + q.coeffs.size - 1)).map fun k =>
    (List.range (k + 1)).foldl (fun acc i => acc + p.coeff i * q.coeff (k - i)) 0

instance : Add Poly := ⟨add⟩
instance : Neg Poly := ⟨neg⟩
instance : Sub Poly := ⟨fun p q => add p (neg q)⟩
instance : Mul Poly := ⟨mul⟩

/-- `p^n` by repeated squaring. -/
def pow (p : Poly) (n : Nat) : Poly :=
  go p 1 n (n + 1)
where
  /-- Square and multiply, fuelled. -/
  go (b acc : Poly) (e : Nat) : Nat → Poly
    | 0 => acc
    | fuel + 1 => if e = 0 then acc else go (b * b) (if e % 2 == 1 then acc * b else acc) (e / 2) fuel

/-- Evaluation (Horner). -/
def eval (p : Poly) (x : Rat) : Rat := p.coeffs.foldr (fun c acc => acc * x + c) 0

/-- Formal derivative. -/
def deriv (p : Poly) : Poly :=
  mk' ((Array.range (p.coeffs.size - 1)).map fun i => ((i + 1 : Nat) : Rat) * p.coeff (i + 1))

/-- Division with remainder over `ℚ` (`q = 0`, `r = p` when `d = 0`). -/
def divMod (p d : Poly) : Poly × Poly :=
  if d.isZero then (zero, p) else
  go zero p (p.coeffs.size + 1)
where
  /-- Long division, one leading term per step. -/
  go (q r : Poly) : Nat → Poly × Poly
    | 0 => (q, r)
    | fuel + 1 =>
      if r.isZero || r.degree < d.degree then (q, r) else
      let c := r.lc / d.lc
      let k := r.degree - d.degree
      let t := mk' ((Array.replicate k (0 : Rat)).push c)
      go (q + t) (r - t * d) fuel

/-- Monic greatest common divisor. -/
def gcd (p q : Poly) : Poly :=
  let g := go p q (p.coeffs.size + q.coeffs.size + 1)
  if g.isZero then g else smul (1 / g.lc) g
where
  /-- Euclid, fuelled by the degrees. -/
  go (a b : Poly) : Nat → Poly
    | 0 => a
    | fuel + 1 => if b.isZero then a else go b (divMod a b).2 fuel

/-- Julia `print(x::Float64)` read back as an exact decimal: what REDUCE sees
when Julia sends it a float literal (`0.1 ↦ 1/10`, `2.25 ↦ 9/4`). -/
def decimalRat (x : Float) : Rat :=
  if x == 0 || !x.isFinite then 0 else
  let d := JuliaBase.Ryu.reduceShortest64 x
  let m : Rat := (d.digits.toNat : Rat)
  let v := if d.exp10 ≥ 0 then m * ((10 ^ d.exp10.toNat : Nat) : Rat) else m / ((10 ^ (-d.exp10).toNat : Nat) : Rat)
  if x < 0 then -v else v

/-- Read a polynomial in `x` from a Julia expression: `+ - * /` (by constants),
`//`, `^` with a non-negative integer literal exponent, integer and float
literals. `none` for anything else. -/
def ofJExpr : JExpr → Option Poly
  | .sym "x" => some X
  | .sym _ => none
  | .lit (.int n) | .lit (.bigint n) => some (const n)
  | .lit (.f64 v) => some (const (decimalRat v))
  | .lit _ => none
  | .call "+" args => (ofList args).map fun ps => ps.foldl (· + ·) zero
  | .call "*" args => (ofList args).map fun ps => ps.foldl (· * ·) 1
  | .call "-" [a] => (ofJExpr a).map (- ·)
  | .call "-" [a, b] => do return (← ofJExpr a) - (← ofJExpr b)
  | .call "/" [a, b] | .call "//" [a, b] => do
    let q ← ofJExpr b
    if q.degree = 0 && !q.isZero then return smul (1 / q.coeff 0) (← ofJExpr a) else none
  | .call "^" [b, .lit (.int k)] => do
    if k < 0 then none else return pow (← ofJExpr b) k.toNat
  | _ => none
where
  /-- Over the arguments. -/
  ofList : List JExpr → Option (List Poly)
    | [] => some []
    | a :: as => do return (← ofJExpr a) :: (← ofList as)

/-- Common denominator: `p = N / D` with `N ∈ ℤ[x]`, `D > 0` the least common
multiple of the coefficient denominators (so `gcd(content N, D) = 1`). -/
def toZ (p : Poly) : Array Int × Nat :=
  let D := p.coeffs.foldl (fun acc c => Nat.lcm acc c.den) 1
  (p.coeffs.map fun c => (c * (D : Rat)).num, D)

/-- The rational polynomial of integer coefficients. -/
def ofZ (a : Array Int) : Poly := mk' (a.map fun (n : Int) => (n : Rat))

end Poly

/-! ## Integer polynomials -/

namespace ZPoly

/-- Degree of a nonempty coefficient array. -/
@[inline] def degree (a : Array Int) : Nat := a.size - 1

/-- Content: gcd of the coefficients (non-negative). -/
def content (a : Array Int) : Nat := a.foldl (fun g c => Nat.gcd g c.natAbs) 0

/-- Primitive part with positive leading coefficient. -/
def primitive (a : Array Int) : Array Int :=
  let g := content a
  let s : Int := if (a.back?.getD 0) < 0 then -1 else 1
  if g = 0 then a else a.map fun c => c / (s * g)

/-- A rational polynomial made integral, primitive, with positive leading coefficient. -/
def ofPoly (p : Poly) : Array Int := primitive (Poly.toZ p).1

/-- Evaluate at an integer. -/
def eval (a : Array Int) (t : Int) : Int := a.foldr (fun c acc => acc * t + c) 0

/-- Exact quotient `a / b` when `b ∣ a` in `ℤ[x]`. -/
def divExact? (a b : Array Int) : Option (Array Int) :=
  let (q, r) := Poly.divMod (Poly.ofZ a) (Poly.ofZ b)
  if r.isZero && q.coeffs.all (·.den == 1) then some (q.coeffs.map (·.num)) else none

/-! ### Rational roots, `p`-adically

A rational root `r/s` of a square-free `f` (`s ∣ lc f`, `r ∣ f(0)`) reduces to a
simple root of `f mod p` for any prime `p ∤ lc f` at which `f` stays
square-free. Such roots are found by trying all residues, lifted by Newton's
iteration to `p^k > 2·|f(0)|·|lc f|`, and read back by rational reconstruction;
each candidate is then checked exactly. Unlike divisor enumeration this works for
coefficients of any size (a product of linear factors with 16-digit decimal
roots, as Wilkinson's random experiments build, has 150-digit coefficients). -/

/-- `x mod m` in `[0, m)`. -/
@[inline] def emod (x : Int) (m : Nat) : Nat := (x % (m : Int)).toNat

/-- Extended Euclid: `(g, u)` with `u·a ≡ g (mod m)`. -/
def xgcd (a m : Int) : Int × Int :=
  go a m 1 0 (m.natAbs + a.natAbs + 2)
where
  /-- Remainders `r₀, r₁` with Bezout coefficients of `a`. -/
  go (r0 r1 s0 s1 : Int) : Nat → Int × Int
    | 0 => (r0, s0)
    | fuel + 1 => if r1 == 0 then (r0, s0) else
      let q := r0 / r1
      go r1 (r0 - q * r1) s1 (s0 - q * s1) fuel

/-- Inverse of `a` modulo `m` (when `gcd(a, m) = 1`). -/
def invMod (a : Int) (m : Nat) : Option Nat :=
  let (g, u) := xgcd (emod a m) m
  if g == 1 then some (emod u m) else none

/-- Evaluate an integer polynomial at `t` modulo `m`. -/
def evalMod (a : Array Int) (t : Nat) (m : Nat) : Nat :=
  a.foldr (fun c acc => (acc * t + emod c m) % m) 0

/-- Coefficients of the derivative. -/
def derivZ (a : Array Int) : Array Int := (Array.range (a.size - 1)).map fun i => ((i + 1 : Nat) : Int) * a[i + 1]!

/-- `gcd(f mod p, g mod p)` has positive degree (polynomial Euclid over `𝔽_p`). -/
def sharesFactorMod (f g : Array Int) (p : Nat) : Bool :=
  let red (a : Array Int) : Array Nat := trimN (a.map (emod · p))
  let r := go (red f) (red g) (f.size + g.size + 2)
  r.size > 1
where
  /-- Drop trailing zeros. -/
  trimN (a : Array Nat) : Array Nat := (a.toList.reverse.dropWhile (· == 0)).reverse.toArray
  /-- `a mod b` over `𝔽_p`. -/
  modP (a b : Array Nat) : Array Nat :=
    let inv := (invMod (b.back?.getD 1) p).getD 1
    let rec loop (a : Array Nat) : Nat → Array Nat
      | 0 => a
      | fuel + 1 =>
        if a.size < b.size || b.size == 0 then a else
        let c := a.back?.getD 0 * inv % p
        let k := a.size - b.size
        let a := (Array.range a.size).map fun i =>
          if i ≥ k && i - k < b.size then (a[i]! + p * p - c * b[i - k]! % p) % p else a[i]!
        loop (trimN a) fuel
    loop a (a.size + 1)
  /-- Euclid. -/
  go (a b : Array Nat) : Nat → Array Nat
    | 0 => a
    | fuel + 1 => if b.isEmpty then a else go b (modP a b) fuel

/-- Rational reconstruction: `n/d ≡ r (mod m)` with `|n| ≤ N`, `0 < d ≤ D`. -/
def ratRecon (r : Nat) (m : Nat) (N D : Nat) : Option (Int × Nat) :=
  go (m : Int) (r : Int) 0 1 (m + 2)
where
  /-- Half-extended Euclid, stopped at the first remainder `≤ N`. -/
  go (r0 r1 t0 t1 : Int) : Nat → Option (Int × Nat)
    | 0 => none
    | fuel + 1 =>
      if r1.natAbs ≤ N then
        if t1 == 0 || t1.natAbs > D then none
        else some (if t1 < 0 then (-r1, t1.natAbs) else (r1, t1.natAbs))
      else
        let q := r0 / r1
        go r1 (r0 - q * r1) t1 (t0 - q * t1) fuel

/-- The primes used for the modular search. -/
def smallPrimes : List Nat :=
  (List.range 2000).filter fun n => n ≥ 101 && (List.range n).all fun d => d < 2 || d * d > n || n % d != 0

/-- Newton lifting of a simple root `t mod m` of `a` (squaring the modulus each
step) until the modulus exceeds `bound`: `(root, modulus)`. -/
def liftRoot (a : Array Int) (t m bound : Nat) : Nat × Nat :=
  go t m (Nat.log2 bound + 2)
where
  /-- Double the precision each step. -/
  go (t m : Nat) : Nat → Nat × Nat
    | 0 => (t, m)
    | fuel + 1 =>
      if m > bound then (t, m) else
      let m2 := m * m
      match invMod (evalMod (derivZ a) t m2) m2 with
      | some inv => go ((t + m2 - evalMod a t m2 * inv % m2) % m2) m2 fuel
      | none => (t, m)

/-- Rational roots `r/s` of a square-free primitive `a` with `a(0) ≠ 0`, as the
primitive linear factors `s x - r` (`s > 0`). -/
def linearFactors (a : Array Int) : List (Array Int) :=
  let lc := a.back?.getD 0
  let a0 := a[0]?.getD 0
  let da := derivZ a
  match smallPrimes.find? (fun (p : Nat) => lc % (p : Int) != 0 && !sharesFactorMod a da p) with
  | none => []
  | some p =>
    let bound := 2 * a0.natAbs * lc.natAbs + 1
    let roots := (List.range p).filter fun t => evalMod a t p == 0
    roots.filterMap fun t =>
      let (r, m) := liftRoot a t p bound
      match ratRecon r m a0.natAbs lc.natAbs with
      | some (n, d) =>
        if (Poly.ofZ a).eval ((n : Rat) / (d : Rat)) == 0 then some #[-n, (d : Int)] else none
      | none => none

/-- Split a square-free primitive factor into irreducibles: the rational roots `p`-adically,
then Berlekamp–Zassenhaus for the rest (a remainder of degree `≤ 3` without rational roots is
already irreducible). -/
def splitSquareFree (a : Array Int) : List (Array Int) :=
  let lin := linearFactors a
  let rest := lin.foldl (fun r l => (divExact? r l).getD r) a
  let restFactors :=
    if degree rest ≤ 0 then []
    else if degree rest ≤ 3 then [rest]
    else Zassenhaus.factorSquareFree rest
  lin ++ restFactors

/-- Yun's square-free decomposition of a primitive polynomial: `[(sᵢ, i)]` with
`a = ∏ sᵢ^i`, each `sᵢ` primitive with positive leading coefficient. -/
def squareFree (a : Array Int) : List (Array Int × Nat) :=
  let f := Poly.ofZ a
  let f' := f.deriv
  let b := Poly.gcd f f'
  let c := (Poly.divMod f b).1
  let d := (Poly.divMod f' b).1 - c.deriv
  go c d 1 [] (a.size + 1)
where
  /-- Yun's loop. -/
  go (c d : Poly) (i : Nat) (acc : List (Array Int × Nat)) : Nat → List (Array Int × Nat)
    | 0 => acc.reverse
    | fuel + 1 =>
      if c.degree == 0 then acc.reverse else
      let g := Poly.gcd c d
      let c' := (Poly.divMod c g).1
      let d' := (Poly.divMod d g).1 - c'.deriv
      let acc := if g.degree ≥ 1 then (ZPoly.ofPoly g, i) :: acc else acc
      go c' d' (i + 1) acc fuel

/-- REDUCE's `ordp` on two univariate standard forms: does `a` print before `b`? A standard form
is its list of nonzero terms `((x . k) . c)` of degree `≥ 1`, highest first, ending in the
constant term (a number) or `nil` when that is zero. `ordp` walks both lists: at the first
differing term the higher power, then the larger coefficient, comes first; a remaining term
list comes before a number, and anything before `nil`; two constants compare as numbers
(larger first). So the zero coefficients do not count: `x⁴ - x³ + 2` precedes `x⁴ + x + 1`
(its next term is `x³`), and `x² + x + 1`, `x² - x + 1`, `x² + 1` are in that order. -/
def reduceBefore (a b : Array Int) : Bool :=
  go (terms a) (terms b)
where
  /-- Nonzero terms of degree `≥ 1`, highest first, and the constant term. -/
  terms (a : Array Int) : List (Nat × Int) × Int :=
    (((List.range a.size).reverse.filter fun k => k ≥ 1 && a[k]! != 0).map fun k => (k, a[k]!),
     a[0]?.getD 0)
  /-- `ordp` on the term lists. -/
  go : List (Nat × Int) × Int → List (Nat × Int) × Int → Bool
    | ((k, c) :: ts, c0), ((k', c') :: ts', c0') =>
      if k == k' && c == c' then go (ts, c0) (ts', c0')
      else if k != k' then k > k' else c > c'
    | (_ :: _, _), ([], _) => true
    | ([], _), (_ :: _, _) => false
    | ([], c0), ([], c0') =>
      if c0 == 0 then c0' == 0      -- `nil` before `nil` only
      else if c0' == 0 then true
      else c0 ≥ c0'

end ZPoly

/-- A factorization `N = content · ∏ fᵢ^eᵢ · x^xpow` over `ℤ` (each `fᵢ` primitive,
positive leading coefficient, degree ≥ 1, not `x`), factors in REDUCE's output
order (`ZPoly.reduceBefore`: higher degree first, then the next nonzero terms). -/
structure Factored where
  /-- Signed integer content. -/
  content : Int
  /-- Irreducible factors with multiplicities. -/
  factors : List (Array Int × Nat)
  /-- Power of `x`. -/
  xpow : Nat
  deriving Inhabited

/-- Factor a nonzero integer polynomial over `ℤ`. -/
def factorZ (a : Array Int) : Factored :=
  let m := (a.findIdx? (· != 0)).getD 0
  let a := a.extract m a.size
  let g : Int := ZPoly.content a
  let s : Int := if (a.back?.getD 0) < 0 then -1 else 1
  let prim := a.map fun c => c / (s * g)
  let parts := if prim.size ≤ 1 then [] else ZPoly.squareFree prim
  let fs := parts.flatMap fun (sq, e) => (ZPoly.splitSquareFree sq).map fun f => (f, e)
  let sorted := fs.toArray.qsort (fun x y => ZPoly.reduceBefore x.1 y.1 && x.1 != y.1) |>.toList
  { content := s * g, factors := sorted, xpow := m }

end Wilkinson
