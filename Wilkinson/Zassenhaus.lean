/-!
# Zassenhaus factorization over `ℤ`

REDUCE's `factor` splits a square-free primitive polynomial into its irreducible factors over
`ℤ` with the Berlekamp–Zassenhaus algorithm (packages/factor: `factorf` → modular factoring,
Hensel lifting, recombination). `Wilkinson.ZPoly.splitSquareFree` runs the same algorithm
after taking out the rational roots:

1. a prime `p ∤ lc f` with `f mod p` square-free, the one with the fewest modular factors among
   the first few candidates (this bounds the recombination);
2. **Berlekamp**: the fixed space of the Frobenius `v ↦ v^p` on `𝔽_p[x]/(f)` has dimension
   `r`, the number of irreducible factors mod `p`; `f = ∏ₛ gcd(f, v - s)` splits `f` for every
   non-constant fixed `v`;
3. **Hensel lifting** (linear, one power of `p` per step) of `f ≡ lc · u₁ ⋯ u_r (mod p)` to
   `p^k > 2·B`, where `B = 2ⁿ (n+1) ‖f‖_∞ |lc f|` bounds the coefficients of `lc f` times any
   factor (Mignotte);
4. **recombination**: subsets of the lifted factors, smallest first; `pp(lc · ∏ uᵢ mod p^k)`
   (symmetric residues) is a true factor exactly when it divides `f` over `ℤ`.

The result does not depend on the prime or the subset order: the irreducible factorization over
`ℤ` is unique up to signs, and `factorZ` normalizes signs and sorts the factors in REDUCE's
order. Coefficient arrays are ascending (`a[i]` is the coefficient of `x^i`); polynomials over
`𝔽_p` are `Array Nat` with entries in `[0, p)` and no trailing zeros.
-/

namespace Wilkinson

namespace Fp

/-- Drop trailing zeros. -/
def trim (a : Array Nat) : Array Nat := go a (a.size + 1)
where
  /-- Pop zeros from the end. -/
  go (a : Array Nat) : Nat → Array Nat
    | 0 => a
    | k + 1 => if a.back? == some 0 then go a.pop k else a

/-- Degree (`0` for constants and zero). -/
@[inline] def deg (a : Array Nat) : Nat := a.size - 1

/-- Coefficient `i` (zero past the end). -/
@[inline] def co (a : Array Nat) (i : Nat) : Nat := a[i]?.getD 0

/-- `x mod m` in `[0, m)` for an integer. -/
@[inline] def emod (x : Int) (m : Nat) : Nat := (x % (m : Int)).toNat

/-- Reduction of an integer polynomial mod `p`. -/
def ofZ (p : Nat) (a : Array Int) : Array Nat := trim (a.map (emod · p))

/-- `b^e mod m`. -/
def powMod (b e m : Nat) : Nat := go (b % m) e 1 (e.log2 + 2)
where
  /-- Square and multiply. -/
  go (b e acc : Nat) : Nat → Nat
    | 0 => acc
    | fuel + 1 => if e = 0 then acc else go (b * b % m) (e / 2) (if e % 2 = 1 then acc * b % m else acc) fuel

/-- Inverse mod a prime `p` (Fermat). -/
@[inline] def inv (p a : Nat) : Nat := powMod a (p - 2) p

/-- Sum. -/
def add (p : Nat) (a b : Array Nat) : Array Nat :=
  trim ((Array.range (max a.size b.size)).map fun i => (co a i + co b i) % p)

/-- Difference. -/
def sub (p : Nat) (a b : Array Nat) : Array Nat :=
  trim ((Array.range (max a.size b.size)).map fun i => (co a i + p - co b i) % p)

/-- Scalar multiple. -/
def smul (p c : Nat) (a : Array Nat) : Array Nat := trim (a.map (c * · % p))

/-- Product (schoolbook). -/
def mul (p : Nat) (a b : Array Nat) : Array Nat := Id.run do
  if a.isEmpty || b.isEmpty then return #[]
  let mut out := Array.replicate (a.size + b.size - 1) 0
  for i in [0:a.size] do
    let ai := a[i]!
    if ai != 0 then
      for j in [0:b.size] do
        out := out.set! (i + j) ((out[i + j]! + ai * b[j]!) % p)
  return trim out

/-- Division with remainder by a nonzero `b`. -/
def divMod (p : Nat) (a b : Array Nat) : Array Nat × Array Nat := Id.run do
  if b.isEmpty then return (#[], a)
  let il := inv p b.back!
  let db := b.size - 1
  let mut r := a
  let mut q := Array.replicate (a.size - db) 0
  for _ in [0:a.size] do
    if r.size < b.size then break
    let k := r.size - b.size
    let c := r.back! * il % p
    q := q.set! k c
    let mut r' := r
    for j in [0:b.size] do
      r' := r'.set! (k + j) ((r'[k + j]! + p * p - c * b[j]! % p) % p)
    r := trim r'
  return (trim q, r)

/-- Remainder. -/
@[inline] def mod (p : Nat) (a b : Array Nat) : Array Nat := (divMod p a b).2

/-- Monic multiple (zero stays zero). -/
def monic (p : Nat) (a : Array Nat) : Array Nat := if a.isEmpty then a else smul p (inv p a.back!) a

/-- Monic greatest common divisor. -/
def gcd (p : Nat) (a b : Array Nat) : Array Nat := monic p (go a b (a.size + b.size + 2))
where
  /-- Euclid. -/
  go (a b : Array Nat) : Nat → Array Nat
    | 0 => a
    | fuel + 1 => if b.isEmpty then a else go b (mod p a b) fuel

/-- Extended Euclid for coprime `a`, `b`: `(s, t)` with `s·a + t·b = 1`. -/
def xgcd (p : Nat) (a b : Array Nat) : Array Nat × Array Nat :=
  go a b #[1] #[] #[] #[1] (a.size + b.size + 2)
where
  /-- Remainder sequence with both Bezout coefficients. -/
  go (r0 r1 s0 s1 t0 t1 : Array Nat) : Nat → Array Nat × Array Nat
    | 0 => (s0, t0)
    | fuel + 1 =>
      if r1.isEmpty then
        -- `r0` is a nonzero constant: normalize to 1
        let c := inv p (co r0 0)
        (smul p c s0, smul p c t0)
      else
        let (q, r) := divMod p r0 r1
        go r1 r s1 (sub p s0 (mul p q s1)) t1 (sub p t0 (mul p q t1)) fuel

/-- `a·b mod f`. -/
@[inline] def mulMod (p : Nat) (a b f : Array Nat) : Array Nat := mod p (mul p a b) f

/-- `a^e mod f`. -/
def powModPoly (p : Nat) (a : Array Nat) (e : Nat) (f : Array Nat) : Array Nat :=
  go (mod p a f) e #[1] (e.log2 + 2)
where
  /-- Square and multiply. -/
  go (b : Array Nat) (e : Nat) (acc : Array Nat) : Nat → Array Nat
    | 0 => acc
    | fuel + 1 =>
      if e = 0 then acc
      else go (mulMod p b b f) (e / 2) (if e % 2 = 1 then mulMod p acc b f else acc) fuel

/-- Formal derivative. -/
def deriv (p : Nat) (a : Array Nat) : Array Nat :=
  trim ((Array.range (a.size - 1)).map fun i => (i + 1) * a[i + 1]! % p)

/-- Is `f` square-free mod `p` (`gcd(f, f') = 1`)? -/
def squareFree (p : Nat) (f : Array Nat) : Bool := (gcd p f (deriv p f)).size == 1

/-- Kernel basis of an `m × n` matrix over `𝔽_p` (row-major), by reduction to row echelon
form. -/
def nullspace (p : Nat) (M : Array (Array Nat)) (n : Nat) : Array (Array Nat) := Id.run do
  let mut A := M
  let mut pivots : Array (Nat × Nat) := #[]   -- (row, column)
  let mut row := 0
  for col in [0:n] do
    if row < A.size then
      match (List.range (A.size - row)).find? (fun i => A[row + i]![col]! != 0) with
      | none => pure ()
      | some i =>
        let pr := row + i
        let tmp := A[pr]!
        A := (A.set! pr A[row]!).set! row tmp
        let c := inv p A[row]![col]!
        A := A.set! row (A[row]!.map (c * · % p))
        for r in [0:A.size] do
          if r != row then
            let f := A[r]![col]!
            if f != 0 then
              let pivotRow := A[row]!
              A := A.set! r ((Array.range n).map fun j => (A[r]![j]! + p * p - f * pivotRow[j]! % p) % p)
        pivots := pivots.push (row, col)
        row := row + 1
  let pivotCols := pivots.map (·.2)
  let mut basis : Array (Array Nat) := #[]
  for free in [0:n] do
    if !pivotCols.contains free then
      let mut v := Array.replicate n 0
      v := v.set! free 1
      for (r, c) in pivots do
        v := v.set! c ((p - A[r]![free]! % p) % p)
      basis := basis.push v
  return basis

/-- Berlekamp's algorithm: the monic irreducible factors of a monic square-free `f` mod `p`. -/
def berlekamp (p : Nat) (f : Array Nat) : List (Array Nat) := Id.run do
  let n := deg f
  if n ≤ 1 then return [f]
  -- rows `x^(i p) mod f`
  let xp := powModPoly p #[0, 1] p f
  let mut rows : Array (Array Nat) := #[]
  let mut cur : Array Nat := #[1]
  for _ in [0:n] do
    rows := rows.push ((Array.range n).map (co cur ·))
    cur := mulMod p cur xp f
  -- the fixed vectors `v Q = v`: the kernel of `(Q - I)ᵀ`
  let M := (Array.range n).map fun k => (Array.range n).map fun j =>
    (rows[j]![k]! + p - (if j == k then 1 else 0)) % p
  let basis := nullspace p M n
  let r := basis.size
  let mut factors : List (Array Nat) := [f]
  for v in basis do
    if factors.length < r then
      let vp := trim v
      if vp.size > 1 then
        factors := factors.flatMap fun g =>
          if deg g ≤ 1 then [g]
          else
            let parts := (List.range p).filterMap fun s =>
              let h := gcd p g (sub p vp #[s])
              if h.size > 1 then some h else none
            if parts.isEmpty then [g] else parts
  return factors

end Fp

namespace Zassenhaus

/-- Symmetric residue of `c` mod `m`: in `(-m/2, m/2]`. -/
@[inline] def symm (c : Int) (m : Nat) : Int :=
  let r := c % (m : Int)
  if 2 * r > (m : Int) then r - m else r

/-- Integer polynomial product. -/
def mulZ (a b : Array Int) : Array Int := Id.run do
  if a.isEmpty || b.isEmpty then return #[]
  let mut out : Array Int := Array.replicate (a.size + b.size - 1) 0
  for i in [0:a.size] do
    for j in [0:b.size] do
      out := out.set! (i + j) (out[i + j]! + a[i]! * b[j]!)
  return out

/-- Coefficientwise `a + c·b`. -/
def addScaled (a : Array Int) (c : Int) (b : Array Nat) : Array Int :=
  (Array.range (max a.size b.size)).map fun i => a[i]?.getD 0 + c * ((b[i]?.getD 0 : Nat) : Int)

/-- Drop trailing zeros. -/
def trimZ (a : Array Int) : Array Int := (a.toList.reverse.dropWhile (· == 0)).reverse.toArray

/-- Exact quotient over `ℤ` when `b ∣ a` (`b` nonzero). -/
def divExact? (a b : Array Int) : Option (Array Int) := Id.run do
  let b := trimZ b
  let a := trimZ a
  if b.isEmpty then return none
  if a.isEmpty then return some #[]
  if a.size < b.size then return none
  let lb := b.back!
  let mut r := a
  let mut q : Array Int := Array.replicate (a.size - b.size + 1) 0
  for i in [0:a.size - b.size + 1] do
    let k := a.size - b.size - i
    let top := r[k + b.size - 1]!
    if top % lb != 0 then return none
    let c := top / lb
    q := q.set! k c
    for j in [0:b.size] do
      r := r.set! (k + j) (r[k + j]! - c * b[j]!)
  if r.all (· == 0) then return some q else return none

/-- Content of an integer polynomial. -/
def content (a : Array Int) : Nat := a.foldl (fun g c => Nat.gcd g c.natAbs) 0

/-- Primitive part with positive leading coefficient. -/
def primitive (a : Array Int) : Array Int :=
  let a := trimZ a
  let g := content a
  let s : Int := if (a.back?.getD 0) < 0 then -1 else 1
  if g = 0 then a else a.map fun c => c / (s * g)

/-- One Hensel step from `p^j` to `p^(j+1)`: `f ≡ G·H (mod p^j)`, `G` monic, `s·g + t·h ≡ 1
(mod p)` for the reductions `g`, `h`. -/
def henselStep (p : Nat) (f G H : Array Int) (g h s t : Array Nat) (pj : Nat) : Array Int × Array Int :=
  let e := (Array.range (max f.size (G.size + H.size))).map fun i =>
    (f[i]?.getD 0 - (mulZ G H)[i]?.getD 0) / (pj : Int)
  let c := Fp.ofZ p e
  let (q, r) := Fp.divMod p (Fp.mul p c t) g
  let dh := Fp.add p (Fp.mul p c s) (Fp.mul p q h)
  (addScaled G pj r, addScaled H pj dh)

/-- Lift `f ≡ g·h (mod p)` (`g` monic, `h` with the leading coefficient of `f`) to `mod p^k`:
`(G, H)` with `G` monic and `f ≡ G·H (mod p^k)`, coefficients in `[0, p^k)`. -/
def liftPair (p k : Nat) (f : Array Int) (g h : Array Nat) : Array Int × Array Int := Id.run do
  let (s, t) := Fp.xgcd p g h
  let mut G : Array Int := g.map (Int.ofNat ·)
  let mut H : Array Int := h.map (Int.ofNat ·)
  let mut pj := p
  for _ in [1:k] do
    let (G', H') := henselStep p f G H g h s t pj
    pj := pj * p
    G := G'.map fun c => c % (pj : Int)
    H := H'.map fun c => c % (pj : Int)
  return (trimZ G, trimZ H)

/-- Multifactor lifting of `f ≡ lc · u₁ ⋯ u_r (mod p)` to monic `Uᵢ` with
`f ≡ lc · U₁ ⋯ U_r (mod p^k)`. -/
def liftAll (p k : Nat) (f : Array Int) : List (Array Nat) → List (Array Int)
  | [] => []
  | [_] =>
    let m := p ^ k
    let lc := f.back?.getD 1
    -- `lc⁻¹ mod p^k` (`lc` is a unit mod `p`)
    let il := invModPk lc m
    [trimZ (f.map fun c => (c * il) % (m : Int))]
  | u :: us =>
    let lc := Fp.emod (f.back?.getD 1) p
    let h := us.foldl (fun acc v => Fp.mul p acc v) #[lc]
    let (G, H) := liftPair p k f u h
    G :: liftAll p k H us
where
  /-- Inverse of a unit modulo `m` by extended Euclid. -/
  invModPk (a : Int) (m : Nat) : Int :=
    let rec go (r0 r1 s0 s1 : Int) : Nat → Int
      | 0 => s0
      | fuel + 1 => if r1 == 0 then s0 else go r1 (r0 - (r0 / r1) * r1) s1 (s0 - (r0 / r1) * s1) fuel
    (go (a % (m : Int)) m 1 0 (2 * Nat.log2 m + 8)) % (m : Int)

/-- All `s`-element sublists of `l`, in lexicographic order of positions. -/
def choose {α : Type} : List α → Nat → List (List α)
  | _, 0 => [[]]
  | [], _ + 1 => []
  | x :: xs, s + 1 => (choose xs s).map (x :: ·) ++ choose xs (s + 1)

/-- Recombination: the irreducible factors of `f` over `ℤ` from its monic lifted factors
`us` modulo `m = p^k > 2B`. -/
def recombine (f : Array Int) (us : List (Array Int)) (m : Nat) : List (Array Int) :=
  go f (us.zipIdx.map fun (u, i) => (i, u)) 1 [] (us.length * us.length + us.length + 4)
where
  /-- `lc · ∏ S mod m`, symmetric. -/
  candidate (lc : Int) (S : List (Nat × Array Int)) : Array Int :=
    let prod := S.foldl (fun acc (_, u) => (mulZ acc u).map fun c => c % (m : Int)) #[lc % (m : Int)]
    prod.map (symm · m)
  /-- Subsets of size `s`, then larger ones. -/
  go (f : Array Int) (rest : List (Nat × Array Int)) (s : Nat) (acc : List (Array Int)) :
      Nat → List (Array Int)
    | 0 => (primitive f) :: acc
    | fuel + 1 =>
      if 2 * s > rest.length then
        if (trimZ f).size > 1 then primitive f :: acc else acc
      else
        let lc := f.back?.getD 1
        let found := (choose rest s).find? fun S =>
          let g := primitive (candidate lc S)
          -- constant-term test before the division
          (g[0]?.getD 0 == 0 || (f[0]?.getD 0) % (g[0]?.getD 1) == 0) && (divExact? f g).isSome
        match found with
        | some S =>
          let g := primitive (candidate lc S)
          let f' := ((divExact? f g).getD f)
          let idx := S.map (·.1)
          go f' (rest.filter fun (i, _) => !idx.contains i) s (g :: acc) fuel
        | none => go f rest (s + 1) acc fuel

/-- Odd primes up to 1000. -/
def primes : List Nat :=
  (List.range 1000).filter fun n => n ≥ 3 && (List.range n).all fun d => d < 2 || d * d > n || n % d != 0

/-- The irreducible factors over `ℤ` of a square-free primitive `f` of degree `≥ 2` with
positive leading coefficient (each primitive, positive leading coefficient; any order). -/
def factorSquareFree (f : Array Int) : List (Array Int) :=
  let f := trimZ f
  let n := f.size - 1
  if n ≤ 1 then [f] else
  let lc := f.back!
  -- candidate primes: `p ∤ lc`, `f mod p` square-free; keep the one with fewest factors
  let good := (primes.filter fun (p : Nat) => lc % (p : Int) != 0 && Fp.squareFree p (Fp.ofZ p f)).take 5
  match good with
  | [] => [f]
  | _ =>
    let tries := good.map fun p => (p, Fp.berlekamp p (Fp.monic p (Fp.ofZ p f)))
    let (p, us) := tries.foldl (fun best t => if t.2.length < best.2.length then t else best) tries.head!
    if us.length ≤ 1 then [f] else
    -- Mignotte-style bound on `lc ·` (any factor)
    let maxc := f.foldl (fun acc c => max acc c.natAbs) 0
    let B := 2 ^ n * (n + 1) * maxc * lc.natAbs
    let k := kFor p (2 * B + 1) 1 p (B.log2 + 4)
    let m := p ^ k
    recombine f (liftAll p k f us) m
where
  /-- Least `k` with `p^k > bound`. -/
  kFor (p bound k pk : Nat) : Nat → Nat
    | 0 => k
    | fuel + 1 => if pk > bound then k else kFor p bound (k + 1) (pk * p) fuel

end Zassenhaus

end Wilkinson
