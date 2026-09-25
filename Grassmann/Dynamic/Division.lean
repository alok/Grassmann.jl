/-
Inverses, division and integer powers of dynamic elements with Julia's result kinds
(Grassmann.jl `src/algebra.jl:406-712`; AbstractTensors `src/AbstractTensors.jl:317-330`).

**`inv`** (`src/algebra.jl:478-559, 604-613`), kind by kind:

| element | `inv(t)` |
|---|---|
| `𝟎`, `∞` | `∞`, `𝟎` |
| `One`, a scalar `Single` | itself, `Single(1/x)` |
| a blade `e`, a term `x·e` | `Single(±1/abs2(e))`, `Single(±1/(abs2(e)·x))` (`-` when the reverse flips the grade) |
| `Chain` | `~t / value(scalar(abs2(t)))` (a `Chain`) |
| `Couple` `re + im·B` | `(re - im·B)/(re² - im²·B²)` (Julia's formula assumes `B² < 0`: defect `couple-inv-hyperbolic`, fixed) |
| `PseudoCouple` | `(~t) / abs2(t)` |
| `Spinor`, `CoSpinor`, `Multivector` | with `d = (~t)⟑t`: `~t / scalar(d)` when `d` is (numerically) a scalar, `~t / d(k)` when it is a single grade `k` (even `k` for halves), else undefined (`inv?` is `none`; Julia throws `inv(m) is undefined`, defect `inv-mixed-undefined`) |
| `Phasor` | `Phasor(1/amp, -angle)` |

**Division** `a / b = a ⟑ inv(b)` and `a \ b = inv(a) ⟑ b` (AbstractTensors
`src/AbstractTensors.jl:320-323`), with Julia's special method for a `Couple` divided by a
scalar term (both parts divide, `src/algebra.jl:552`). Two couples on one blade divide
through the inverse (Julia's real-coefficient method uses Smith's algorithm,
`src/algebra.jl:555-600`, which agrees up to rounding). A scalar `s : α` divides as a
number (`TA.divScalar`: containers entrywise, terms and couples by `1/s`).

**Powers** `t ^ i` for an integer `i` (`src/algebra.jl:406-470`): `i = 1` is `t`, `i = 0`
is `One`; a term `x·e` is `x^i·e^i`, with Julia's period-4 cycle `e, e², e³, e⁴` when `e² = ±1`
and `(e²)^⌊i/2⌋·e^(i mod 2)` otherwise (defect `term-power-period4`: the cycle is wrong for
null blades and non-unit metrics); a `Chain` in `n ≤ 3` goes through its square
`contraction(~t, t)`; a `Couple` whose blade squares to `-1` is a complex power (Julia's
`power_by_squaring`); anything else is `One⟑t⟑t⋯` (repeated for `i < 8`, by squaring
beyond). Negative powers are powers of the inverse (Julia returns `One` or throws for a
non-literal negative exponent, same defect).

Coefficient types: `inv` and `/` need a division on `α` (`Float`, `Rat`, complex types).
Julia promotes `Int64` elements to `Float64` (`inv(3v₁) = 0.333…v₁`), which a `TA V Int`
cannot hold: map the element to `Float` or `Rat` first (`TA.map`). Integer powers work at
every coefficient type.
-/
import Grassmann.Dynamic.Ops

namespace Grassmann

open DirectSum DirectSum.Bits StaticVectors AbstractTensors JuliaBase

namespace TA

variable {V : TensorBundle} {α : Type} [Coeff α] [Kernels V]

/-! ## Inverses -/

/-- Julia `parityreverse(grade(b))`: the reverse flips the blade's grade. -/
@[inline] def revSign (b : UInt64) : Bool := reverseFlips (popcount b)

/-- The scalar `B ⟑ B` of a blade. -/
@[inline] def bladeSq (V : TensorBundle) (b : UInt64) : Rat := scalarCoef V .mul b b

variable [Div α]

/-- Julia `inv(b)` of a term `x·e_b` (`src/algebra.jl:545-556`): `x⁻¹` for a scalar,
`±1/(abs2(e_b)·x)` on `e_b` otherwise. -/
def invTerm (b : UInt64) (x : α) : TA V α :=
  if b == 0 then single 0 (Coeff.one / x)
  else
    let s : α := if revSign b then -Coeff.one else Coeff.one
    single b (s / (Coeff.ofRat (abs2Inv V b) * x))

/-- `inv(re + im·e_b) = (re - im·e_b)/(re² - im²·e_b²)`: the inverse of a couple for every
blade (defect `couple-inv-hyperbolic`: Julia's formula is right only when `e_b² < 0`). A
degenerate couple (`b = 0`) is the scalar `re + im`. -/
def invCouple (b : UInt64) (re im : α) : TA V α :=
  if b == 0 then couple 0 (Coeff.one / (re + im)) Coeff.zero
  else
    let den := re * re - Coeff.ofRat (bladeSq V b) * (im * im)
    couple b (re / den) (-im / den)

variable [JNorm α]

/-- Julia's inverse of a `Spinor`, `CoSpinor` or `Multivector` (`src/algebra.jl:486-532`):
`d = (~m)⟑m`; `~m / scalar(d)` when `norm(scalar(d)) ≈ norm(d)`, else `~m / d(k)` for the
first grade `k` (even `k ≥ 2` for halves) with `norm(d(k)) ≈ norm(d)`; `none` otherwise. -/
def invContainer? (m : TA V α) (rm : TA V α := reverse m) : Option (TA V α) :=
  let d := mul rm m
  let fd := norm d
  let sd := scalar d
  if F64.isapprox (norm sd) fd then
    some (mul rm (match sd with
      | single _ x => single 0 (Coeff.one / x)
      | _ => infinity))
  else
    let halves := match m with | spinor _ | cospinor _ => true | _ => false
    (List.range (V.n + 1)).findSome? fun k =>
      if k == 0 || (halves && k % 2 == 1) then none else
      let dk := gradeProj k d
      if F64.isapprox (norm dk) fd then
        match dk with
        | chain g c =>
          let r := reverse (chain g c)
          let s := getD (contraction (chain g c) (chain g c)).toDense.v 0
          some (mul rm (divScalar r s))
        | _ => none
      else none

/-- Julia `inv(t)` with the reverse `rt = ~t` supplied: Julia computes `~t` in the element's
own coefficient type before any division promotes it (`inv(A)` of an `Int64` chain reverses
in `Int64`, so a zero entry stays `+0.0`), which a caller that promotes first passes here. -/
def invWith? (t rt : TA V α) : Option (TA V α) :=
  match t with
  | zero => some infinity
  | infinity => some zero
  | one => some one
  | blade b => some (invTerm b Coeff.one)
  | single b x => some (invTerm b x)
  | chain g c =>
    -- `~t / value(scalar(abs2(t)))`, entrywise
    let s := getD (contraction (chain g c) (chain g c)).toDense.v 0
    some (divScalar rt s)
  | couple b re im => some (invCouple b re im)
  | pseudo .. =>
    -- `(~t) / abs2(t)`: `abs2` is a scalar term or a sum of terms
    let a := mul rt t
    match a with
    | single 0 x => some (divScalar rt x)
    | _ => (invContainer? (toMultiTA a)).map (mul rt)
  | spinor _ | cospinor _ | multi _ => invContainer? t rt
  | phasor amp θ => some (phasor (Coeff.one / amp) (neg θ))

/-- Julia `inv(t)` with Julia's result kinds (module docstring), `none` where Julia's
algorithm finds no inverse. -/
def inv? (t : TA V α) : Option (TA V α) := invWith? t (reverse t)

/-- Julia `inv(t)`; panics with Julia's message where the inverse is undefined. -/
def inv (t : TA V α) : TA V α :=
  match inv? t with
  | some x => x
  | none => panic! "inv(m) is undefined (Grassmann.jl src/algebra.jl:486-532)"

instance : Inv (TA V α) := ⟨inv⟩

/-! ## Division -/

/-- Julia `a / b = a ⟑ inv(b)` (right division) with Julia's special couple methods;
`none` where `inv(b)` is undefined. -/
def div? (a b : TA V α) : Option (TA V α) :=
  match a, b with
  | couple B re im, single 0 y => some (couple B (re / y) (im / y))
  | couple B re im, one => some (couple B re im)
  | _, _ => (inv? b).map (mul a)

/-- Julia `a / b`; panics where `inv(b)` is undefined. -/
def div (a b : TA V α) : TA V α :=
  match div? a b with
  | some x => x
  | none => panic! "inv(m) is undefined (Grassmann.jl src/algebra.jl:486-532)"

/-- `a / b` with `rb = ~b` supplied (see `invWith?`). -/
def divWith? (a b rb : TA V α) : Option (TA V α) :=
  match a, b with
  | couple B re im, single 0 y => some (couple B (re / y) (im / y))
  | couple B re im, one => some (couple B re im)
  | _, _ => (invWith? b rb).map (mul a)

/-- Julia `a \ b = inv(a) ⟑ b` (left division); `none` where `inv(a)` is undefined. -/
def ldiv? (a b : TA V α) : Option (TA V α) := (inv? a).map (mul · b)

/-- Julia `a \ b`; panics where `inv(a)` is undefined. -/
def ldiv (a b : TA V α) : TA V α :=
  match ldiv? a b with
  | some x => x
  | none => panic! "inv(m) is undefined (Grassmann.jl src/algebra.jl:486-532)"

instance : Div (TA V α) := ⟨div⟩
instance : LeftDiv (TA V α) (TA V α) (TA V α) := ⟨ldiv⟩

end TA

/-! ## Powers -/

namespace TA

variable {V : TensorBundle} {α : Type} [Coeff α] [Kernels V]

/-- Julia's `power_by_squaring(x, p)` for `p ≥ 1` with the multiplication `mul`
(`base/intfuncs.jl`): the trailing factors of two are squarings, then the remaining bits
multiply in. -/
def powBySquaring {β : Type} (mul : β → β → β) (x : β) (p : Nat) : β :=
  if p ≤ 1 then x
  else
    -- `t = trailing_zeros(p) + 1`, `p >>= t`, square `t - 1` times
    let tz := (List.range 64).find? (fun k => (p >>> k) % 2 == 1) |>.getD 0
    let x := (List.range tz).foldl (fun x _ => mul x x) x
    let y := x
    go (p >>> (tz + 1)) x y 64
where
  /-- The remaining bits of `p` (fuel bounds the loop by the bit length). -/
  go (p : Nat) (x y : β) : Nat → β
    | 0 => y
    | fuel + 1 =>
      if p == 0 then y
      else
        let t := ((List.range 64).find? (fun k => (p >>> k) % 2 == 1) |>.getD 0) + 1
        let x := (List.range t).foldl (fun x _ => mul x x) x
        go (p >>> t) x (mul y x) fuel

/-- `One ⟑ t ⟑ t ⋯` (`i` factors; Julia repeats for `i < 8`, squares beyond). -/
def powGeneral (t : TA V α) (i : Nat) : TA V α :=
  if i < 8 then (List.range i).foldl (fun out _ => mul out t) one
  else
    -- Julia: `ind = indices(i)`, multiply `out` by `p` at the set bits, squaring `p` between
    let K := Nat.log2 i + 1
    let (out, _) := (List.range K).foldl (fun (out, p) k =>
      let out := if (i >>> k) % 2 == 1 then mul out p else out
      (out, if k + 1 == K then p else mul p p)) (one, t)
    out

/-- `x^i` for the coefficient (repeated multiplication, `i ≥ 0`). -/
def cpow (x : α) (i : Nat) : α := (List.range i).foldl (fun a _ => a * x) Coeff.one

/-- The power of a term `x·e_b` (`i ≥ 2`): Julia's period-4 cycle `e, e², e³, e⁴` when
`e_b² = ±1`, else `(e_b²)^⌊i/2⌋ e_b^(i mod 2)` (defect `term-power-period4`), times `x^i`
unless the term is a unit blade. -/
def powTerm (b : UInt64) (x : α) (unit : Bool) (i : Nat) : TA V α :=
  let e : TA V α := ofBlade b
  let sq := bladeSq V b
  let out : TA V α :=
    if sq == 1 || sq == -1 then
      match (i - 1) % 4 with
      | 0 => e
      | 1 => mul e e
      | 2 => mul (mul e e) e
      | _ => mul (mul (mul e e) e) e
    else if sq == 0 then zero  -- a null blade: `e² = 𝟎` (Julia's kind), every power vanishes
    else
      let c : α := cpow (Coeff.ofRat sq) (i / 2)
      if i % 2 == 0 then single 0 c else smul c e
  if unit then out else mulScalar out (cpow x i)

/-- Julia `t ^ i` for a natural exponent (module docstring). -/
def powNat (t : TA V α) (i : Nat) : TA V α :=
  if _h1 : i = 1 then t
  else if _h0 : i = 0 then
    -- `Couple{V,B}(Complex(t)^0) = 1 + 0·B` when `B² = -1`, else `One`
    match t with
    | couple b .. => if bladeSq V b == -1 then couple b Coeff.one Coeff.zero else one
    | _ => one
  else match t with
    | zero => zero
    | infinity => infinity
    | one => one
    | blade b => powTerm b Coeff.one true i
    | single b x => powTerm b x false i
    | chain g c =>
      if V.n ≤ 3 && V.diffvars == 0 then
        let sq := contraction (reverse t) (chain g c)
        let d := i / 2
        let val := if d == 1 then sq else powNat sq d
        if i % 2 == 0 then val else mul val t
      else powGeneral t i
    | couple b re im =>
      if bladeSq V b == -1 then
        -- `Couple{V,B}(Complex(t)^i)`: complex multiplication, `power_by_squaring`
        let cm := fun (z w : α × α) => (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)
        let (r, s) := powBySquaring cm (re, im) i
        couple b r s
      else powGeneral t i
    | _ => powGeneral t i
termination_by i
decreasing_by omega

instance : HPow (TA V α) Nat (TA V α) := ⟨powNat⟩

variable [Div α] [JNorm α]

/-- Julia `t ^ i` for an integer exponent: negative powers are powers of `inv(t)` (Julia's
literal `t^-1`, `t^-2`; other negative exponents are a Julia defect, see the module
docstring). -/
def powInt (t : TA V α) (i : Int) : TA V α :=
  if i ≥ 0 then powNat t i.toNat else powNat (inv t) i.natAbs

instance : HPow (TA V α) Int (TA V α) := ⟨powInt⟩

end TA

end Grassmann
