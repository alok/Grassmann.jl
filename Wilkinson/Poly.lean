import JuliaBase.Ryu
import Wilkinson.Expr

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
3. linear factors from the rational-root test (`p ∣ a₀`, `q ∣ aₙ`);
4. Kronecker's method for factors of degree `2 … ⌊n/2⌋` (interpolation through
   divisors of the values at small integers).

Steps 3 and 4 enumerate divisors, so they are bounded (coefficients up to about
`10¹⁰`, at most `2·10⁶` Kronecker candidates); past the bounds the remaining
factor is reported unsplit. The printed shapes REDUCE gives these objects are in
`Wilkinson.Reduce`.
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
  | .lit (.int n) => some (const n)
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

/-- Trial-division factorization of `n > 0` into prime powers, `none` when a
cofactor above `bound²` remains unfactored. -/
def primeFactors (n : Nat) (bound : Nat := 100000) : Option (List (Nat × Nat)) :=
  go n 2 [] (bound + 1)
where
  /-- Divide out primes up to `bound`. -/
  go (n p : Nat) (acc : List (Nat × Nat)) : Nat → Option (List (Nat × Nat))
    | 0 => if n = 1 then some acc else if n < bound * bound then some ((n, 1) :: acc) else none
    | fuel + 1 =>
      if n = 1 then some acc
      else if p * p > n then some ((n, 1) :: acc)
      else if n % p == 0 then
        let (k, m) := strip n p 0 64
        go m (p + 1) ((p, k) :: acc) fuel
      else go n (p + 1) acc fuel
  /-- Multiplicity of `p` in `n`. -/
  strip (n p k : Nat) : Nat → Nat × Nat
    | 0 => (k, n)
    | fuel + 1 => if n % p == 0 && n > 0 then strip (n / p) p (k + 1) fuel else (k, n)

/-- Positive divisors of `n > 0` (`none` when `n` cannot be factored within the bound). -/
def divisors (n : Nat) : Option (List Nat) := do
  let fs ← primeFactors n
  return fs.foldl (fun ds (p, k) => ds.flatMap fun d => (List.range (k + 1)).map fun i => d * p ^ i) [1]

/-- Rational roots `p/q` of a square-free primitive `a` with `a(0) ≠ 0`, as the
primitive linear factors `q x - p` (`q > 0`). -/
def linearFactors (a : Array Int) : Option (List (Array Int)) := do
  let a0 := (a[0]?.getD 0).natAbs
  let an := (a.back?.getD 0).natAbs
  let ps ← divisors a0
  let qs ← divisors an
  let cands := qs.flatMap fun q => ps.flatMap fun p =>
    if Nat.gcd p q == 1 then [((p : Int), q), (-(p : Int), q)] else []
  return cands.filterMap fun (p, q) =>
    if (Poly.ofZ a).eval ((p : Rat) / (q : Rat)) == 0 then some #[-p, (q : Int)] else none

/-- Lagrange interpolation through `(tᵢ, vᵢ)` over `ℚ`. -/
def interpolate (pts : List (Int × Int)) : Poly :=
  pts.foldl (fun acc (ti, vi) =>
    let basis := pts.foldl (fun b (tj, _) =>
      if tj == ti then b else b * Poly.smul (1 / ((ti - tj : Int) : Rat)) (Poly.X - Poly.const tj)) (1 : Poly)
    acc + Poly.smul (vi : Rat) basis) Poly.zero

/-- Kronecker's method: an integer factor of `a` of degree exactly `d`, if one
exists within the search budget. -/
def kroneckerFactor (a : Array Int) (d : Nat) (budget : Nat := 2000000) : Option (Array Int) := do
  -- evaluation points with nonzero values, fewest divisors first
  let cands := (List.range (4 * d + 8)).map fun i : Nat => if i % 2 == 0 then (i / 2 : Int) else -((i + 1) / 2 : Int)
  let scored := cands.filterMap fun t =>
    let v := eval a t
    if v == 0 then none else (divisors v.natAbs).map fun ds => (t, v, ds)
  let pts := (scored.toArray.qsort (fun x y => x.2.2.length < y.2.2.length)).toList.take (d + 1)
  guard (pts.length == d + 1)
  let size := pts.foldl (fun acc (_, _, ds) => acc * (2 * ds.length)) 1
  guard (size ≤ budget)
  -- first value positive (fixes the sign of the factor), the others ±
  let choices : List (List Int) := pts.zipIdx.map fun ((_, _, ds), i) =>
    if i == 0 then ds.map (Int.ofNat ·) else ds.flatMap fun (x : Nat) => [(x : Int), -(x : Int)]
  let ts := pts.map (·.1)
  search ts choices []
where
  /-- Depth-first over value choices. -/
  search (ts : List Int) : List (List Int) → List Int → Option (Array Int)
    | [], vs =>
      let g := interpolate (ts.zip vs.reverse)
      if g.degree == d && g.coeffs.all (·.den == 1) then
        let gi := g.coeffs.map (·.num)
        let gi := if (gi.back?.getD 0) < 0 then gi.map (- ·) else gi
        (divExact? a gi).map fun _ => gi
      else none
    | c :: cs, vs => c.firstM (fun v => search ts cs (v :: vs))

/-- Split a square-free primitive factor into irreducibles (rational roots, then
Kronecker for degrees `2 … ⌊n/2⌋`). -/
def splitSquareFree (a : Array Int) : List (Array Int) :=
  let lin := (linearFactors a).getD []
  let rest := lin.foldl (fun r l => (divExact? r l).getD r) a
  lin ++ kron rest 2 (rest.size + 1)
where
  /-- Kronecker search, smallest degree first. -/
  kron (r : Array Int) (d : Nat) : Nat → List (Array Int)
    | 0 => [r]
    | fuel + 1 =>
      if degree r ≤ 1 then (if degree r == 1 then [r] else [])
      else if 2 * d > degree r then [r]
      else match kroneckerFactor r d with
        | some g => g :: kron ((divExact? r g).getD r) d fuel
        | none => kron r (d + 1) fuel

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

/-- Lexicographic comparison of coefficient arrays from the leading coefficient down. -/
def cmpDesc (a b : Array Int) : Ordering :=
  if a.size != b.size then compare a.size b.size
  else go (a.size) (a.size + 1)
where
  /-- Compare from the top index. -/
  go (i : Nat) : Nat → Ordering
    | 0 => .eq
    | fuel + 1 =>
      if i = 0 then .eq else
      match compare (a[i - 1]?.getD 0) (b[i - 1]?.getD 0) with
      | .eq => go (i - 1) fuel
      | o => o

end ZPoly

/-- A factorization `N = content · ∏ fᵢ^eᵢ · x^xpow` over `ℤ` (each `fᵢ` primitive,
positive leading coefficient, degree ≥ 1, not `x`), factors in REDUCE's output
order: higher degree first, then larger coefficients from the leading one down. -/
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
  let sorted := fs.toArray.qsort (fun x y => ZPoly.cmpDesc x.1 y.1 == .gt) |>.toList
  { content := s * g, factors := sorted, xpow := m }

end Wilkinson
