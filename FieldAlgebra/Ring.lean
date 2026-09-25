import FieldAlgebra.Group

/-!
# `Ring`: sums of monomials over a named basis (`FieldAlgebra.Ring`)

Julia's `Ring{G,T,S,N,M}` (`FieldAlgebra.jl/src/ring.jl`) is a formal sum of `M`
monomials `cᵢ · ∏ bⱼ^{vᵢⱼ}` over the basis `G`: a sparse Laurent polynomial whose
terms are kept **in insertion order**, not sorted. The order is observable (it
is the printed order, and `==` compares term by term), so the port reproduces
Julia's merge rules operation by operation:

* `Ring{1} ± Ring{1}`: two terms, or one term whose coefficient may be zero
  (`x - x` prints `x/Inf`, `ring.jl:108-121`);
* `Ring{M} ± monomial` (`add`, `ring.jl:125-146`): combine in place (dropping a
  term that cancels) or append;
* `monomial ± Ring{M}` (`add2`, `ring.jl:153-174`): combine in place or prepend;
* `Ring{M} ± Ring{L}` (`ring.jl:181-220`): combine the terms of the right operand
  that already occur on the left, keep the left's nonzero terms in order, then
  append the right's new terms;
* `Ring * monomial` multiplies every term (no merging), `Ring{1} * Ring{1}` is one
  term, and `Ring{M} * Ring{L}` accumulates `a * bᵢ` over the right's terms into
  `𝟎` with `+` (`ring.jl:222-247`); integer powers use Julia's
  `power_by_squaring`, negative literal powers `inv(x)^n`.

Terms are `Group B` values (a coefficient normalised like Julia's `promoteint`);
this is display-equivalent to Julia's per-ring coefficient vector, which prints
each term through the same `Group` constructor.

Fixed Julia defects (`oracle/defects.toml`):
* `Group - Group` with equal monomials builds a malformed `Ring` (a `MethodError`,
  `ring.jl:100`); here it is the one-term difference, like `Ring{1} - Ring{1}`;
* evaluation `f(x…)` drops the coefficients (`ring.jl:75`: `sum(prod(v.^f.v[i]))`);
  here it is `∑ cᵢ ∏ xⱼ^{vᵢⱼ}`;
* `Ring ± Ring` with different coefficient types (`x + 0.5y`, `x + 2.5`) is an
  ambiguity error in Julia; here coefficients promote as numbers do.
-/

namespace FieldAlgebra

/-- A formal sum of monomials over the basis `B` (Julia `Ring{G,T,S,N,M}`), terms
in Julia's order. -/
structure Ring (B : Basis) where
  /-- the terms (`M = terms.size`) -/
  terms : Array (Group B)
  deriving Inhabited

namespace Ring

variable {B : Basis}

/-- The zero ring `𝟎` (`Ring{G,T,S,N,0}`, `zero(r)`). -/
def zero : Ring B := ⟨#[]⟩

/-- The unit `𝟙` (`one(r)`: one term with zero exponents and coefficient `1`). -/
def one : Ring B := ⟨#[Group.one]⟩

/-- A monomial as a one-term ring (Julia `Ring(g::Group)`, `ring.jl:40`). -/
def ofGroup (g : Group B) : Ring B := ⟨#[g]⟩

/-- A number as a ring: `c·𝟙` (Julia `c*one(r)`). -/
def const (c : Coef) : Ring B := ⟨#[Group.mk' .zero c]⟩

instance (n : Nat) : OfNat (Ring B) n := ⟨const (.int n)⟩
instance : OfScientific (Ring B) := ⟨fun m s e => const (.float (OfScientific.ofScientific m s e))⟩

/-- Number of terms (Julia `length(r) = M`). -/
def size (a : Ring B) : Nat := a.terms.size

/-- Julia `==` (`ring.jl:62`): the same terms in the same order (exponents and
coefficients compared as numbers). -/
def beq (a b : Ring B) : Bool :=
  a.size == b.size && (a.terms.zip b.terms).all fun (x, y) => x.v.beq y.v && x.c == y.c

instance : BEq (Ring B) := ⟨beq⟩


/-- The coefficient operation of `±`: `op(c)`. -/
@[inline] private def sgn (plus : Bool) (c : Coef) : Coef := if plus then c else c.neg

/-- `op(a, b)` on coefficients. -/
@[inline] private def comb (plus : Bool) (a b : Coef) : Coef := if plus then a.add b else a.sub b

/-- The first term of `a` with exponents `v` (Julia `findfirst(z -> z == v, a.v)`). -/
def findTerm (a : Ring B) (v : Exps B.n) : Option Nat := a.terms.findIdx? (·.v.beq v)

/-- Julia `add(a, bv, bc, op)` (`ring.jl:125-141`): combine the monomial `bc·bv`
into `a` (in place, dropping a cancelled term) or append it. -/
def addTerm (a : Ring B) (bv : Exps B.n) (bc : Coef) (plus : Bool) : Ring B :=
  match a.findTerm bv with
  | none => ⟨a.terms.push (Group.mk' bv (sgn plus bc))⟩
  | some j =>
    let t := a.terms[j]!
    let c := comb plus t.c bc
    if c.isZero then (if a.size == 1 then zero else ⟨a.terms.eraseIdx! j⟩)
    else ⟨a.terms.set! j (Group.mk' t.v c)⟩

/-- Julia `add2(av, ac, b, op)` (`ring.jl:153-169`): combine the monomial `ac·av`
into `op(b)` (in place, dropping a cancelled term) or prepend it. -/
def addTerm2 (av : Exps B.n) (ac : Coef) (b : Ring B) (plus : Bool) : Ring B :=
  let bs := b.terms.map fun g => Group.mk' g.v (sgn plus g.c)
  match b.findTerm av with
  | none => ⟨#[Group.mk' av ac] ++ bs⟩
  | some j =>
    let c := comb plus ac (b.terms[j]!).c
    if c.isZero then (if b.size == 1 then zero else ⟨bs.eraseIdx! j⟩)
    else ⟨bs.set! j (Group.mk' (b.terms[j]!).v c)⟩

/-- Julia `Ring{M} ± Ring{L}` in general (`ring.jl:181-220`). -/
def addGen (a b : Ring B) (plus : Bool) : Ring B := Id.run do
  let hits := (List.range b.size).filter fun i => (a.findTerm (b.terms[i]!).v).isSome
  if hits.isEmpty then return ⟨a.terms ++ b.terms.map fun g => Group.mk' g.v (sgn plus g.c)⟩
  let mut c := a.terms.map (·.c)
  for i in hits do
    if let some k := a.findTerm (b.terms[i]!).v then
      c := c.set! k (comb plus c[k]! (b.terms[i]!).c)
  let fresh := (List.range b.size).filter fun i => !hits.contains i
  let keep := (List.range a.size).filter fun k => !(c[k]!).isZero
  if keep.length + fresh.length == 0 then return zero
  return ⟨(keep.map fun k => Group.mk' (a.terms[k]!).v c[k]!).toArray ++
    (fresh.map fun i => let g := b.terms[i]!; Group.mk' g.v (sgn plus g.c)).toArray⟩

/-- Julia `a ± b` on rings, dispatching on the term counts exactly as Julia's
methods do (`ring.jl:108-220`). -/
def addRing (a b : Ring B) (plus : Bool) : Ring B :=
  match a.size, b.size with
  | 1, 1 =>
    let x := a.terms[0]!
    let y := b.terms[0]!
    if x.v.beq y.v then ⟨#[Group.mk' x.v (comb plus x.c y.c)]⟩
    else ⟨#[x, Group.mk' y.v (sgn plus y.c)]⟩
  | 0, 0 => a
  | _, 1 => let y := b.terms[0]!; a.addTerm y.v y.c plus
  | 1, _ => let x := a.terms[0]!; addTerm2 x.v x.c b plus
  | _, _ => addGen a b plus

/-- Julia unary `-` (`ring.jl:92`). -/
def neg (a : Ring B) : Ring B := ⟨a.terms.map (·.neg)⟩

/-- Julia `times(k, r)` / `r * k` for a number `k` (`ring.jl:83-90`): scale every
coefficient. -/
def scale (k : Coef) (a : Ring B) : Ring B := ⟨a.terms.map fun g => Group.mk' g.v (k.mul g.c)⟩

/-- Julia `r * g` for a monomial `g` (`ring.jl:228-230`): every term times `g`. -/
def mulGroup (a : Ring B) (g : Group B) : Ring B :=
  ⟨a.terms.map fun t => Group.mk' (t.v.add g.v) (t.c.mul g.c)⟩

/-- Julia `g * r` (`ring.jl:231-233`). -/
def groupMul (g : Group B) (a : Ring B) : Ring B :=
  ⟨a.terms.map fun t => Group.mk' (g.v.add t.v) (g.c.mul t.c)⟩

/-- Julia `r / g` (`ring.jl:234-236`): exponents subtract, coefficients divide
(`a.c ./ b.c`, one rounding). -/
def divGroup (a : Ring B) (g : Group B) : Ring B :=
  ⟨a.terms.map fun t => Group.mk' (t.v.sub g.v) (t.c.div g.c)⟩

/-- Julia `a * b` on rings (`ring.jl:222-247`): one term for two monomials,
otherwise `∑ᵢ a * bᵢ` accumulated from `𝟎` with `+`. -/
def mul (a b : Ring B) : Ring B :=
  match a.size, b.size with
  | 1, 1 =>
    let x := a.terms[0]!
    let y := b.terms[0]!
    ⟨#[Group.mk' (x.v.add y.v) (x.c.mul y.c)]⟩
  | _, _ => b.terms.foldl (fun s t => s.addRing (a.mulGroup (Group.mk' t.v t.c)) true) zero

/-- Is this a pure number `c·𝟙` (one term, zero exponents)? Dividing by one is
Julia's `r / c` for a number `c`. -/
def scalar? (a : Ring B) : Option Coef :=
  if a.size == 1 && (a.terms[0]!).v.allZero then some (a.terms[0]!).c else none

/-- Julia `inv(r)` (`ring.jl:78-79`): a monomial inverts; `inv` of `𝟎` is `Inf`
and of a sum a `MethodError` in Julia, `none` here. -/
def inv? (a : Ring B) : Option (Ring B) :=
  if a.size == 1 then let x := a.terms[0]!; some ⟨#[Group.mk' x.v.neg x.c.inv]⟩ else none

/-- Julia `a / b` (`ring.jl:81, 225-236`): by a number `c` (a ring `c·𝟙`) it is
`times(a, inv(c))`; by a monomial every term is divided (`Ring{1}/Ring{1}` and
`Ring/Group`; a `Group` divisor coerces to a one-term ring). A quotient by a sum
is Julia's experimental `Field` (not ported): `none`. -/
def div? (a b : Ring B) : Option (Ring B) :=
  match b.scalar? with
  | some c => some (a.scale c.inv)
  | none => if b.size == 1 then some (a.divGroup (b.terms[0]!)) else none

/-- Julia `x^p` for `p ≥ 0` (`power_by_squaring`: `x^0 = one(x)`, `x^1 = copy(x)`). -/
def npow (a : Ring B) (p : Nat) : Ring B := JuliaBase.powBySquaring mul one a p

/-- Julia's literal power `x^n`: `inv(x)^(-n)` for negative `n`, which exists for
monomials only. -/
def zpow? (a : Ring B) (n : Int) : Option (Ring B) :=
  if n ≥ 0 then some (a.npow n.toNat) else (a.inv?).map (·.npow (-n).toNat)

instance : Add (Ring B) := ⟨fun a b => a.addRing b true⟩
instance : Sub (Ring B) := ⟨fun a b => a.addRing b false⟩
instance : Neg (Ring B) := ⟨neg⟩
instance : Mul (Ring B) := ⟨mul⟩
instance : HPow (Ring B) Nat (Ring B) := ⟨npow⟩
instance : One (Ring B) := ⟨one⟩
instance : HMul (Ring B) (Group B) (Ring B) := ⟨mulGroup⟩
instance : HMul (Group B) (Ring B) (Ring B) := ⟨groupMul⟩
instance : HDiv (Ring B) (Group B) (Ring B) := ⟨divGroup⟩
instance : HAdd (Ring B) (Group B) (Ring B) := ⟨fun a g => a.addTerm g.v g.c true⟩
instance : HSub (Ring B) (Group B) (Ring B) := ⟨fun a g => a.addTerm g.v g.c false⟩
instance : HAdd (Group B) (Ring B) (Ring B) := ⟨fun g a => addTerm2 g.v g.c a true⟩
instance : HSub (Group B) (Ring B) (Ring B) := ⟨fun g a => addTerm2 g.v g.c a false⟩

/-- `r / s`, with `r` unchanged where Julia has no `Ring` result (see `div?`). -/
instance : Div (Ring B) := ⟨fun a b => (a.div? b).getD a⟩

/-- Evaluate at `xs` (Julia `f(x…)`, `ring.jl:75-76`, with the coefficients that
Julia drops): `∑ᵢ cᵢ ∏ⱼ xⱼ^{vᵢⱼ}` with Julia's `^` and left-to-right folds. -/
def eval (f : Ring B) (xs : Array Float) : Float :=
  let term (t : Group B) : Float :=
    let es := t.v.toExpos
    let p := (List.range B.n).foldl (fun acc j =>
      let x := xs[j]?.getD 0.0
      acc * match es[j]?.getD (.int 0) with
        | .int n => JuliaBase.F64.powInt x n
        | e => JuliaBase.F64.pow x e.toFloat) 1.0
    t.c.toFloat * p
  match f.terms.toList with
  | [] => 0.0
  | t :: ts => ts.foldl (fun acc s => acc + term s) (term t)

/-- Julia `show(io, r)` (`ring.jl:249-259`): `𝟎` for the empty ring, otherwise the
first term and every further term with a nonzero coefficient, joined by ` + `. -/
def print [GroupProduct B] (a : Ring B) : String :=
  match a.terms.toList with
  | [] => "𝟎"
  | t :: ts => ts.foldl (fun s g => if g.c.isZero then s else s ++ " + " ++ g.print) t.print

instance [GroupProduct B] : ToString (Ring B) := ⟨print⟩

end Ring

namespace Group

variable {B : Basis}

/-- Julia `a ± b` on two monomials (`ring.jl:94-107`): a two-term ring, or one
term when the monomials agree (Julia's `-` of equal monomials is a malformed call;
fixed). -/
def addGroup (a b : Group B) (plus : Bool) : Ring B :=
  if a.v.beq b.v then ⟨#[Group.mk' a.v (if plus then a.c.add b.c else a.c.sub b.c)]⟩
  else ⟨#[a, Group.mk' b.v (if plus then b.c else b.c.neg)]⟩

instance : HAdd (Group B) (Group B) (Ring B) := ⟨fun a b => a.addGroup b true⟩
instance : HSub (Group B) (Group B) (Ring B) := ⟨fun a b => a.addGroup b false⟩

end Group

end FieldAlgebra
