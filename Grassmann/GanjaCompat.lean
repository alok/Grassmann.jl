/-
Compatibility bridge between `Grassmann.lean` (Michael Reed / `chakravala` `Grassmann.jl`
conventions) and `ganja.js` (Steven De Keninck / `enkimute` geometric algebra conventions).

Credits:
- Michael Reed (`chakravala` / `Grassmann.jl`): space/basis/operator architecture ported here.
- Steven De Keninck (`enkimute` / `ganja.js`): CoffeeShop, Wedge, PGA/CGA operator conventions.

## Convention Alignment Summary

| Concept | `Grassmann.lean` (`Grassmann.jl`) | `ganja.js` | Bridge here |
|---|---|---|---|
| Arbitrary `Cl(p,q,r)` | `S!"..."` / `D!"..."` | `Algebra(p, q, r)` (`r` null gens first) | `TensorBundle.cl p q r` |
| Poincaré dual (`!`) | `!x` (`complementright`), metric-free | `!x` (`Dual`), metric-free | `ganjaDual` / `ganjaUndual` (never Hodge `⋆` in PGA!) |
| Regressive join (`&`) | `a ∨ b` = `complementleft (!a ∧ !b)` | `a & b` = `UnDual(Dual(a) ^ Dual(b))` | `ganjaJoin` = `a ∨ b` |
| Left contraction (`<<`) | `a < b` = `contraction(b, a)` (reversed-left) | `a << b` = Dorst `a ⌋ b` | `dorstLDot` = `Kernels.bin .contractionRevLeft` (`contraction(b, ~a)`) |
| Conjugate (`~`) | `~x` = reverse `[+,+,-,-]`; `clifford` = `[+,-,-,+]` | `~x` = Clifford conjugate `[+,-,-,+]` | `ganjaConj` (`clifford`), `ganjaRev` (`reverse`) |
| Sandwich (`>>>`) | `R >>> x = R * x * ~R` (reverse) | `R >>> x = R * x * R.Reverse` | identical! |
| CGA3 null basis | Witt `CGA3 = S!"∞∅+++"` (`∞⋅∅ = -1`) | Raw `Cl(4,1)` (`ni = e₋+e₊`, `no = ½(e₋-e₊)`) | `cgaWittToRawVec` / `cgaRawToWittVec` |
-/
module

public import Grassmann.Kernel.Runtime
public import Grassmann.Types.Convert

@[expose] public section

namespace Grassmann

open DirectSum DirectSum.Bits StaticVectors AbstractTensors

namespace GanjaCompat

/-! ## Arbitrary `Cl(p, q, r)` Space Construction -/

/-- Build the `TensorBundle` for `Cl(p, q, r)` matching `ganja.js`'s `Algebra(p, q, r)`
generator order:
* when `r > 0`: `r` degenerate (`0`) generators first, then `p` positive (`+1`), then `q`
  negative (`-1`), so `cl 2 0 1 = PGA2` (`D!"0,1,1"`) and `cl 3 0 1 = PGA3` (`D!"0,1,1,1"`).
* when `r = 0`: a `Signature` with `p` positive generators followed by `q` negative generators
  (e.g. `cl 3 0 0 = S!"+++"`, `cl 4 1 0 = S!"++++-"`, `cl 0 1 0 = S!"-"`, `cl 0 2 0 = S!"--"`). -/
def _root_.DirectSum.TensorBundle.cl (p q r : Nat) : TensorBundle :=
  if r == 0 then
    let n := p + q
    let neg : UInt64 :=
      if q == 0 then 0
      else (Bits.lowMask q) <<< p.toUInt64
    TensorBundle.sig n neg
  else
    let d : Array Rat :=
      Array.replicate r (0 : Rat) ++ Array.replicate p (1 : Rat) ++ Array.replicate q (-1 : Rat)
    TensorBundle.diag d

/-- Alias for `DirectSum.TensorBundle.cl`. -/
abbrev cl (p q r : Nat) : TensorBundle := DirectSum.TensorBundle.cl p q r

/-- Conformal Witt space `S!"∞∅+…+"` for Euclidean dimension `d` (`n = d + 2`,
`v∞² = v∅² = 0`, `v∞⋅v∅ = -1`). For `d = 2, 3` this agrees with `CGA2` and `CGA3`. -/
def cgaWitt (d : Nat) : TensorBundle :=
  { n := d + 2, metric := .signature 2, hasinf := true, hasorigin := true }

/-- Check that `cl 2 0 1 = PGA2` and `cl 3 0 1 = PGA3`. -/
theorem cl_pga2 : cl 2 0 1 = PGA2 := by decide
theorem cl_pga3 : cl 3 0 1 = PGA3 := by decide
theorem cgaWitt_2 : cgaWitt 2 = CGA2 := by decide
theorem cgaWitt_3 : cgaWitt 3 = CGA3 := by decide

/-! ## Metric-Free Poincaré Duality (Safe for Degenerate PGA) -/

section Ops

variable {V : TensorBundle} {G H : Nat} {p q : Bool} {α : Type} [Coeff α] [Kernels V]

/-- Ganja.js metric-free Poincaré dual `!x` (`complementright`, safe in PGA where Hodge `⋆e₀ = 0`). -/
@[inline] def dualChain (c : Chain V G α) : Chain V (V.n - G) α := c.complementright

/-- Ganja.js metric-free Poincaré undual (`complementleft`, exact inverse of `dualChain`). -/
@[inline] def undualChain (c : Chain V G α) : Chain V (V.n - G) α := c.complementleft

/-- Ganja.js metric-free Poincaré dual on a `Half`. -/
@[inline] def dualHalf (h : Half V p α) : Half V (p ^^ (V.n % 2 == 1)) α := h.complementright

/-- Ganja.js metric-free Poincaré undual on a `Half`. -/
@[inline] def undualHalf (h : Half V p α) : Half V (p ^^ (V.n % 2 == 1)) α := h.complementleft

/-- Ganja.js metric-free Poincaré dual on a `Multivector`. -/
@[inline] def dualMV (m : Multivector V α) : Multivector V α := m.complementright

/-- Ganja.js metric-free Poincaré undual on a `Multivector`. -/
@[inline] def undualMV (m : Multivector V α) : Multivector V α := m.complementleft

/-! ## Ganja.js Reverse vs Clifford Conjugate -/

/-- Ganja.js `.Reverse` (`[+1, +1, -1, -1]` by grade mod 4; Grassmann.jl `~x`). -/
@[inline] def revChain (c : Chain V G α) : Chain V G α := c.reverse
/-- Ganja.js `.Reverse` on a `Half`. -/
@[inline] def revHalf (h : Half V p α) : Half V p α := h.reverse
/-- Ganja.js `.Reverse` on a `Multivector`. -/
@[inline] def revMV (m : Multivector V α) : Multivector V α := m.reverse

/-- Ganja.js `~x` / `.Conjugate` (Clifford conjugate `[+1, -1, -1, +1]` by grade mod 4). -/
@[inline] def conjChain (c : Chain V G α) : Chain V G α := c.clifford
/-- Ganja.js `~x` / `.Conjugate` on a `Half`. -/
@[inline] def conjHalf (h : Half V p α) : Half V p α := h.clifford
/-- Ganja.js `~x` / `.Conjugate` on a `Multivector`. -/
@[inline] def conjMV (m : Multivector V α) : Multivector V α := m.clifford

/-! ## Dorst Left Contraction (`a ⌋ b`, ganja.js `a << b`)

In Grassmann.jl, `contraction(b, a)` (`a < b`) carries an extra `rev(|a|)` factor relative to
Dorst's left contraction `a ⌋ b`. `BinOp.contractionRevLeft` evaluates `contraction(b, ~a)`,
canceling `rev(|a|)` so it equals `⟨a * b⟩_{H - G}` (0 when `G > H`) for every grade pair. -/

/-- Dorst left contraction `a ⌋ b` (ganja.js `a << b`) on homogeneous chains: grade `H - G`
(zero when `G > H`). -/
@[inline] def dorstLDotChain (a : Chain V G α) (b : Chain V H α) : Chain V (H - G) α :=
  if G > H then Chain.zero
  else ⟨Kernels.bin .contractionRevLeft (.chain G) (.chain H) (.chain (H - G)) a.v b.v⟩

/-- Dorst left contraction `a ⌋ b` (ganja.js `a << b`) on full multivectors. -/
@[inline] def dorstLDotMV (a b : Multivector V α) : Multivector V α :=
  ⟨Kernels.bin .contractionRevLeft .full .full .full a.v b.v⟩

/-- Ganja.js regressive join `a & b = UnDual(Dual(a) ^ Dual(b))` on chains (`a ∨ b`). -/
@[inline] def joinChain (a : Chain V G α) (b : Chain V H α) : Chain V (G + H - V.n) α :=
  a ∨ b

/-- Ganja.js regressive join `a & b` on multivectors (`a ∨ b`). -/
@[inline] def joinMV (a b : Multivector V α) : Multivector V α :=
  a ∨ b

/-- Ganja.js exterior meet `a ^ b` on chains (`a ∧ b`). -/
@[inline] def meetChain (a : Chain V G α) (b : Chain V H α) : Chain V (G + H) α :=
  a ∧ b

/-- Ganja.js exterior meet `a ^ b` on multivectors (`a ∧ b`). -/
@[inline] def meetMV (a b : Multivector V α) : Multivector V α :=
  a ∧ b

end Ops

/-! ## Conformal Witt (`S!"∞∅++…+"`) ↔ Raw `Cl(d+1, 1)` (`e₊²=+1, e₋²=-1`) Vector Bridge

With ganja.js null vectors `n∞ = e₋ + e₊` and `n₀ = ½(e₋ - e₊)`:
* `n∞² = n₀² = 0` and `n∞ ⋅ n₀ = -1` (exact isometry with Grassmann's `v∞, v∅`).
* `c_∞ v∞ + c_∅ v∅ + x  ↦  x + (c_∞ - ½ c_∅) e₊ + (c_∞ + ½ c_∅) e₋`.
* `x + c₊ e₊ + c₋ e₋    ↦  ½(c₊ + c₋) v∞ + (c₋ - c₊) v∅ + x`. -/

/-- Convert a grade-1 vector from Witt conformal space `cgaWitt d` (`[v∞, v∅, e₁…e_d]`) to raw
ganja.js conformal space `cl (d + 1) 1 0` (`[e₁…e_d, e₊, e₋]`). -/
def cgaWittToRawVec {d : Nat} (v : Chain (cgaWitt d) 1 Float) : Chain (cl (d + 1) 1 0) 1 Float :=
  let cInf := v.v.get! 0
  let cOri := v.v.get! 1
  let cPlus := cInf - 0.5 * cOri
  let cMinus := cInf + 0.5 * cOri
  let rec go (i : Nat) (acc : FloatArray) : FloatArray :=
    if i < d then go (i + 1) (acc.push (v.v.get! (i + 2))) else acc
  let arr := (go 0 (FloatArray.emptyWithCapacity (d + 2))).push cPlus |>.push cMinus
  ⟨if h : arr.size = Leibniz.binomial (cl (d + 1) 1 0).n 1 then ⟨arr, h⟩ else zeroValues _⟩

/-- Convert a grade-1 vector from raw ganja.js conformal space `cl (d + 1) 1 0` (`[e₁…e_d, e₊, e₋]`)
to Witt conformal space `cgaWitt d` (`[v∞, v∅, e₁…e_d]`). -/
def cgaRawToWittVec {d : Nat} (v : Chain (cl (d + 1) 1 0) 1 Float) : Chain (cgaWitt d) 1 Float :=
  let cPlus := v.v.get! d
  let cMinus := v.v.get! (d + 1)
  let cInf := 0.5 * (cPlus + cMinus)
  let cOri := cMinus - cPlus
  let rec go (i : Nat) (acc : FloatArray) : FloatArray :=
    if i < d then go (i + 1) (acc.push (v.v.get! i)) else acc
  let init := ((FloatArray.emptyWithCapacity (d + 2)).push cInf).push cOri
  let arr := go 0 init
  ⟨if h : arr.size = Leibniz.binomial (cgaWitt d).n 1 then ⟨arr, h⟩ else zeroValues _⟩

end GanjaCompat

end Grassmann
