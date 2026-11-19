/-
  Grassmann/CABI/Alg.lean — Strictly Init-only General Clifford & Witt Conformal Engine

  Provides a complete, zero-`Lean`, zero-`Std` runtime Clifford algebra layer
  (`AlgSpace`, dense `MV`, `Layout`, `BinOp`, `PlanEntry`, `plan2`) for
  `Grassmann.Eval`, `Grassmann.Codegen.GPU`, `Grassmann.CoffeeShop`,
  `Grassmann.Wedge`, and `Grassmann.Studio`.

  Supports:
  - Arbitrary diagonal metrics `Cl(p, q, r)` (`p + q + r ≤ 6`)
  - Spacetime Algebra `STA` (`S"-+++"`, preserving `ALOK-950` exact invariants)
  - Projective Geometric Algebra `PGA2` (`D"0,1,1"`), `PGA3` (`D"0,1,1,1"`)
  - Exact Witt-basis Conformal Geometric Algebra `CGA2` (`S"∞∅++"`), `CGA3` (`S"∞∅+++"`)
    with `∞² = ∅² = 0`, `∞ · ∅ = -1` (`∞ ∅ = -1 + ∞∧∅`, `∅ ∞ = -1 - ∞∧∅`).

  Credits:
  - Michael Reed (`chakravala` / `Grassmann.jl`)
  - Steven De Keninck (`enkimute` / `ganja.js`)
-/
import Grassmann.CABI.Kernels

namespace Grassmann.CABI.Alg

open Grassmann.CABI.Kernels

/-! ### Space Descriptor (`AlgSpace`) -/

/-- Lightweight `Init`-only descriptor for any Clifford/Projective/Conformal algebra (`n ≤ 6`). -/
structure AlgSpace where
  n           : Nat
  zeroMask    : UInt32 := 0
  negMask     : UInt32 := 0
  hasInf      : Bool   := false
  hasOrigin   : Bool   := false
  displayName : String := "Cl"
  deriving DecidableEq, Repr, Inhabited

namespace AlgSpace

@[inline] def hasconformal (V : AlgSpace) : Bool := V.hasInf && V.hasOrigin
@[inline] def nulls (V : AlgSpace) : Nat := (if V.hasInf then 1 else 0) + (if V.hasOrigin then 1 else 0)
@[inline] def dim (V : AlgSpace) : Nat := (1 : Nat) <<< V.n

def V0 : AlgSpace := { n := 0, displayName := "ℝ0" }
def R2 : AlgSpace := { n := 2, displayName := "ℝ2" }
def R3 : AlgSpace := { n := 3, displayName := "ℝ3" }
def R4 : AlgSpace := { n := 4, displayName := "ℝ4" }
/-- Spacetime Algebra `S"-+++"`: bit0=`et` (`-1`), bit1..3=`ex,ey,ez` (`+1`). -/
def STA : AlgSpace := { n := 4, negMask := 1, displayName := "⟨-+++⟩" }
/-- 2D PGA `D"0,1,1"`: bit0=`e0` (`0`), bit1..2=`e1,e2` (`+1`). -/
def PGA2 : AlgSpace := { n := 3, zeroMask := 1, displayName := "⟨0++⟩" }
/-- 3D PGA `D"0,1,1,1"`: bit0=`e0` (`0`), bit1..3=`e1,e2,e3` (`+1`). -/
def PGA3 : AlgSpace := { n := 4, zeroMask := 1, displayName := "⟨0+++⟩" }
/-- 2D Witt CGA `S"∞∅++"`: bit0=`∞`, bit1=`∅`, bit2..3=`e1,e2` (`+1`). -/
def CGA2 : AlgSpace := { n := 4, hasInf := true, hasOrigin := true, displayName := "⟨∞∅++⟩" }
/-- 3D Witt CGA `S"∞∅+++"`: bit0=`∞`, bit1=`∅`, bit2..4=`e1,e2,e3` (`+1`). -/
def CGA3 : AlgSpace := { n := 5, hasInf := true, hasOrigin := true, displayName := "⟨∞∅+++⟩" }

def sig (n : Nat) (negMask : UInt32) : AlgSpace :=
  { n, negMask, displayName := s!"Cl({n})" }

/-- Construct `Cl(p, q, r)` with `r` degenerate zeros first, then `p` `+1`, then `q` `-1`. -/
def cl (p q r : Nat) : AlgSpace :=
  let (nu, zm, nm) := clMasks p.toUInt32 q.toUInt32 r.toUInt32
  { n := nu.toNat, zeroMask := zm, negMask := nm, displayName := s!"Cl({p},{q},{r})" }

instance : ToString AlgSpace where
  toString V := V.displayName

/-- Human-readable label for a basis blade bitmask `b`. -/
def bladeLabel (V : AlgSpace) (b : UInt64) : String := Id.run do
  if b == 0 then return "1"
  let mut out := "e"
  let mut started := false
  if V.hasInf && (b &&& 1) != 0 then
    out := "v∞"; started := true
  if V.hasOrigin then
    let obit : UInt64 := if V.hasInf then 2 else 1
    if (b &&& obit) != 0 then
      out := if started then out ++ "∅" else "v∅"
      started := true
  let off := V.nulls
  for i in [off:V.n] do
    if ((b >>> i.toUInt64) &&& 1) != 0 then
      if !started then out := "e"; started := true
      out := out ++ toString (i - off + 1)
  return out

end AlgSpace

/-! ### Grade-Major Basis Order & Blade Utilities -/

@[inline] def testBit (b : UInt64) (i : Nat) : Bool :=
  ((b >>> i.toUInt64) &&& 1) != 0

@[inline] def lowMask (n : Nat) : UInt64 :=
  if n >= 64 then 0xFFFFFFFFFFFFFFFF else ((1 : UInt64) <<< n.toUInt64) - 1

@[inline] def popcount64 (b : UInt64) : Nat :=
  (popcount32 (b &&& 0xFFFFFFFF).toUInt32 + popcount32 (b >>> 32).toUInt32).toNat

/-- All basis blades of grade `g` in `n` generators, in canonical ascending bitmask order. -/
def indexBasisGrade (n g : Nat) : Array UInt64 := Id.run do
  let dim := (1 : Nat) <<< n
  let mut out : Array UInt64 := #[]
  for i in [:dim] do
    let u := i.toUInt64
    if popcount64 u == g then
      out := out.push u
  return out

/-- All `2^n` basis blades of `n` generators, ordered by grade `0, 1, ..., n`. -/
def indexBasisAll (n : Nat) : Array UInt64 := Id.run do
  let mut out : Array UInt64 := Array.emptyWithCapacity ((1 : Nat) <<< n)
  for g in [:n + 1] do
    out := out ++ indexBasisGrade n g
  return out

/-! ### Exact Blade Product Terms (Diagonal + Witt Conformal `∞`/`∅`) -/

/-- Exact product of two basis blades `e_a * e_b` in `V`, returning 0, 1, or 2
`(bladeMask, coeff)` terms. Handles both arbitrary diagonal metrics AND exact
Witt conformal null pairs (`∞² = ∅² = 0`, `∞ ∅ = -1 + ∞∧∅`, `∅ ∞ = -1 - ∞∧∅`). -/
def bladeMulTerms (V : AlgSpace) (a b : UInt32) : Array (UInt32 × Float) :=
  if !V.hasconformal then
    let s := metricProductSign a b V.zeroMask V.negMask
    if s == 0.0 then #[] else #[(a ^^^ b, s)]
  else
    -- Split into Witt null pair (bits 0..1: 0=1, 1=∞, 2=∅, 3=E=∞∧∅) and non-null tail (bits >= 2)
    let an := a &&& 3
    let bn := b &&& 3
    let ae := a &&& (~~~(3 : UInt32))
    let be := b &&& (~~~(3 : UInt32))
    -- Move `bn` past `ae` (every bit of `ae` > every bit of `bn`): swaps = popcount(ae) * popcount(bn)
    let crossOdd := ((popcount32 ae * popcount32 bn) &&& 1) == 1
    let eucSign := metricProductSign ae be (V.zeroMask &&& (~~~(3 : UInt32))) (V.negMask &&& (~~~(3 : UInt32)))
    if eucSign == 0.0 then #[]
    else
      let baseSign := if crossOdd then -eucSign else eucSign
      let eMask := ae ^^^ be
      match an, bn with
      | 0, _ => #[(bn ||| eMask, baseSign)]
      | _, 0 => #[(an ||| eMask, baseSign)]
      | 1, 1 => #[]                                         -- ∞ * ∞ = 0
      | 2, 2 => #[]                                         -- ∅ * ∅ = 0
      | 1, 2 => #[(0 ||| eMask, -baseSign), (3 ||| eMask, baseSign)]   -- ∞ * ∅ = -1 + E
      | 2, 1 => #[(0 ||| eMask, -baseSign), (3 ||| eMask, -baseSign)]  -- ∅ * ∞ = -1 - E
      | 1, 3 => #[(1 ||| eMask, baseSign)]                  -- ∞ * E = +∞
      | 3, 1 => #[(1 ||| eMask, -baseSign)]                 -- E * ∞ = -∞
      | 2, 3 => #[(2 ||| eMask, -baseSign)]                 -- ∅ * E = -∅
      | 3, 2 => #[(2 ||| eMask, baseSign)]                  -- E * ∅ = +∅
      | 3, 3 => #[(0 ||| eMask, baseSign)]                  -- E * E = +1
      | _, _ => #[]

/-- Exact metric square sign `-1 / 0 / +1` of a single blade `e_b * e_b`. -/
def bladeMetricSign (V : AlgSpace) (b : UInt64) : Int8 :=
  let bu := b.toUInt32
  let terms := bladeMulTerms V bu bu
  if terms.isEmpty then 0
  else
    let c := (terms.find? fun t => t.1 == 0).map (·.2) |>.getD 0.0
    if c < -0.5 then -1 else if c > 0.5 then 1 else 0

/-! ### Dense `Init`-Only Multivector (`MV V`) -/

/-- Dense `FloatArray`-backed multivector over `V` (length `2^V.n`, indexed by bitmask). -/
structure MV (V : AlgSpace) where
  data : FloatArray
  deriving Inhabited

namespace MV

def zero {V : AlgSpace} : MV V := ⟨faZeros V.dim⟩

def one {V : AlgSpace} : MV V :=
  ⟨faAddAt (faZeros V.dim) 0 1.0⟩

def single {V : AlgSpace} (b : UInt64) (c : Float) : MV V :=
  ⟨faAddAt (faZeros V.dim) b.toNat c⟩

def blade {V : AlgSpace} (b : UInt64) : MV V := single b 1.0

@[inline] def coeff {V : AlgSpace} (x : MV V) (b : UInt64) : Float :=
  faGet x.data b.toNat

def add {V : AlgSpace} (a b : MV V) : MV V := Id.run do
  let d := V.dim
  let mut out := FloatArray.emptyWithCapacity d
  for i in [:d] do
    out := out.push (faGet a.data i + faGet b.data i)
  return ⟨out⟩

def sub {V : AlgSpace} (a b : MV V) : MV V := Id.run do
  let d := V.dim
  let mut out := FloatArray.emptyWithCapacity d
  for i in [:d] do
    out := out.push (faGet a.data i - faGet b.data i)
  return ⟨out⟩

def neg {V : AlgSpace} (a : MV V) : MV V := Id.run do
  let d := V.dim
  let mut out := FloatArray.emptyWithCapacity d
  for i in [:d] do
    out := out.push (-(faGet a.data i))
  return ⟨out⟩

def mulScalar {V : AlgSpace} (a : MV V) (s : Float) : MV V := Id.run do
  let d := V.dim
  let mut out := FloatArray.emptyWithCapacity d
  for i in [:d] do
    out := out.push (faGet a.data i * s)
  return ⟨out⟩

def mul {V : AlgSpace} (a b : MV V) : MV V := Id.run do
  let d := V.dim
  let mut out := faZeros d
  for i in [:d] do
    let ai := faGet a.data i
    if Float.abs ai > 1e-18 then
      let iu := i.toUInt32
      for j in [:d] do
        let bj := faGet b.data j
        if Float.abs bj > 1e-18 then
          let terms := bladeMulTerms V iu j.toUInt32
          for (k, c) in terms do
            out := faAddAt out k.toNat (c * ai * bj)
  return ⟨out⟩

def wedge {V : AlgSpace} (a b : MV V) : MV V :=
  ⟨metricWedge V.n.toUInt32 a.data b.data⟩

/-- Dorst left contraction `a ⌋ b` (sum of terms from `a * b` with grade `|b| - |a|`). -/
def contractionLeft {V : AlgSpace} (a b : MV V) : MV V := Id.run do
  let d := V.dim
  let mut out := faZeros d
  for i in [:d] do
    let ai := faGet a.data i
    if Float.abs ai > 1e-18 then
      let iu := i.toUInt32
      let ga := popcount32 iu
      for j in [:d] do
        let bj := faGet b.data j
        if Float.abs bj > 1e-18 then
          let ju := j.toUInt32
          let gb := popcount32 ju
          if ga <= gb then
            let wantG := gb - ga
            for (k, c) in bladeMulTerms V iu ju do
              if popcount32 k == wantG then
                out := faAddAt out k.toNat (c * ai * bj)
  return ⟨out⟩

/-- Grassmann.jl contraction `a ⨽ b` (`grade = |a| - |b|`, right-factor reversed). -/
def contraction {V : AlgSpace} (a b : MV V) : MV V := Id.run do
  let d := V.dim
  let mut out := faZeros d
  for i in [:d] do
    let ai := faGet a.data i
    if Float.abs ai > 1e-18 then
      let iu := i.toUInt32
      let ga := popcount32 iu
      for j in [:d] do
        let bj := faGet b.data j
        if Float.abs bj > 1e-18 then
          let ju := j.toUInt32
          let gb := popcount32 ju
          if gb <= ga then
            let wantG := ga - gb
            let rs := reverseSign gb
            for (k, c) in bladeMulTerms V iu ju do
              if popcount32 k == wantG then
                out := faAddAt out k.toNat (rs * c * ai * bj)
  return ⟨out⟩

def reverse {V : AlgSpace} (a : MV V) : MV V := ⟨metricReverse V.n.toUInt32 a.data⟩
def involute {V : AlgSpace} (a : MV V) : MV V := ⟨metricInvolute V.n.toUInt32 a.data⟩
def clifford {V : AlgSpace} (a : MV V) : MV V := ⟨metricCliffordConj V.n.toUInt32 a.data⟩
def complementright {V : AlgSpace} (a : MV V) : MV V := ⟨metricRightComplement V.n.toUInt32 a.data⟩
def complementleft {V : AlgSpace} (a : MV V) : MV V := ⟨metricLeftComplement V.n.toUInt32 a.data⟩

def hodge {V : AlgSpace} (a : MV V) : MV V := Id.run do
  let d := V.dim
  let fullMask : UInt32 := (d - 1).toUInt32
  let mut out := faZeros d
  for i in [:d] do
    let ai := faGet a.data i
    if Float.abs ai > 1e-18 then
      let iu := i.toUInt32
      let sq := bladeMetricSign V iu.toUInt64
      if sq != 0 then
        let comp := fullMask ^^^ iu
        let s := reorderSign iu comp * (if sq < 0 then -1.0 else 1.0)
        out := faAddAt out comp.toNat (s * ai)
  return ⟨out⟩

def gradeProj {V : AlgSpace} (g : Nat) (a : MV V) : MV V := Id.run do
  let d := V.dim
  let mut out := faZeros d
  for i in [:d] do
    if (popcount32 i.toUInt32).toNat == g then
      out := faAddAt out i (faGet a.data i)
  return ⟨out⟩

/-- Multiplicative inverse for versors/scalars (`~x / (x * ~x)` with Newton refinement for general multivectors). -/
def inv {V : AlgSpace} (x : MV V) : MV V := Id.run do
  let rx := reverse x
  let prod := mul x rx
  let s0 := prod.coeff 0
  if Float.abs s0 < 1e-15 then return zero
  let mut y := mulScalar rx (1.0 / s0)
  let two : MV V := single 0 2.0
  for _ in [:3] do
    let xy := mul x y
    y := mul y (sub two xy)
  return y

/-- Scaling-and-squaring Taylor exponential `exp(x)` for arbitrary multivectors. -/
def exp {V : AlgSpace} (x : MV V) : MV V := Id.run do
  let mut maxAbs := 0.0
  for i in [:V.dim] do
    let a := Float.abs (faGet x.data i)
    if a > maxAbs then maxAbs := a
  let mut k : Nat := 0
  let mut scale := 1.0
  while maxAbs * scale > 0.25 && k < 12 do
    scale := scale * 0.5
    k := k + 1
  let xs := mulScalar x scale
  let mut sum : MV V := one
  let mut term : MV V := one
  for n in [1:13] do
    term := mulScalar (mul term xs) (1.0 / n.toFloat)
    sum := add sum term
  for _ in [:k] do
    sum := mul sum sum
  return sum

/-- Principal logarithm `log(x)` for versors/scalars near identity (falls back to closed-form rotor log). -/
def log {V : AlgSpace} (x : MV V) : MV V :=
  let s0 := x.coeff 0
  let v := sub x (single 0 s0)
  let v2 := (mul v v).coeff 0
  if Float.abs v2 < 1e-12 then
    if s0 > 1e-12 then add (single 0 (Float.log s0)) (mulScalar v (1.0 / s0))
    else v
  else if v2 < 0.0 then
    let norm := Float.sqrt (-v2)
    let ang := Float.atan2 norm s0
    let mag := Float.sqrt (s0 * s0 - v2)
    add (single 0 (Float.log mag)) (mulScalar v (ang / norm))
  else
    let norm := Float.sqrt v2
    let ang := Float.atanh (max (-0.999999) (min 0.999999 (norm / (if Float.abs s0 < 1e-12 then 1.0 else s0))))
    mulScalar v (ang / norm)

/-- Compact float formatter (4 decimals, `Init`-only). -/
private def fmtCoeff (x : Float) : String :=
  if x.isNaN || x.isInf then "0"
  else
    let neg := x < 0.0
    let ax := if neg then -x else x
    let scaled := (ax * 10000.0 + 0.5).toUInt64.toNat
    let intP := scaled / 10000
    let frac := scaled % 10000
    let pfx := if neg && scaled > 0 then "-" else ""
    if frac == 0 then s!"{pfx}{intP}"
    else
      let d1 := frac / 1000
      let d2 := (frac / 100) % 10
      let d3 := (frac / 10) % 10
      let d4 := frac % 10
      if d4 != 0 then s!"{pfx}{intP}.{d1}{d2}{d3}{d4}"
      else if d3 != 0 then s!"{pfx}{intP}.{d1}{d2}{d3}"
      else if d2 != 0 then s!"{pfx}{intP}.{d1}{d2}"
      else s!"{pfx}{intP}.{d1}"

/-- Human-readable multivector string in grade-major basis order. -/
def showString {V : AlgSpace} (x : MV V) (zeroIndexed : Bool := false) : String := Id.run do
  let blades := indexBasisAll V.n
  let mut parts : Array String := #[]
  for b in blades do
    let c := x.coeff b
    if Float.abs c > 1e-6 then
      let lbl :=
        if b == 0 then ""
        else if zeroIndexed then
          let idxs := (List.range V.n).filter (fun i => testBit b i)
          "e" ++ String.join (idxs.map toString)
        else V.bladeLabel b
      if lbl.isEmpty then parts := parts.push (fmtCoeff c)
      else parts := parts.push s!"{fmtCoeff c}{lbl}"
  if parts.isEmpty then "0" else " + ".intercalate parts.toList

end MV

/-! ### Straight-Line Plan Generator (for `Grassmann.Codegen.GPU`) -/

inductive BinOp where
  | mul
  | wedge
  | contractionLeft
  deriving DecidableEq, Repr, Inhabited

inductive Layout where
  | chain (g : Nat)
  | even
  | odd
  | full
  deriving DecidableEq, Repr, Inhabited

def Layout.blades (V : AlgSpace) : Layout → Array UInt32
  | .chain g => (indexBasisGrade V.n g).map (·.toUInt32)
  | .even    => (indexBasisAll V.n).filter (fun b => popcount64 b % 2 == 0) |>.map (·.toUInt32)
  | .odd     => (indexBasisAll V.n).filter (fun b => popcount64 b % 2 == 1) |>.map (·.toUInt32)
  | .full    => (indexBasisAll V.n).map (·.toUInt32)

def Layout.size (V : AlgSpace) (l : Layout) : Nat := (l.blades V).size

structure PlanEntry where
  ia   : Nat
  ib   : Nat
  ic   : Nat
  coef : Float
  deriving Inhabited

/-- Generate sparse multiply-accumulate plan entries `out[ic] += coef · x[ia] · y[ib]`
for straight-line WGSL / GLSL / MSL GPU shader emission. -/
def plan2 (V : AlgSpace) (op : BinOp) (la lb lc : Layout) : Except String (Array PlanEntry) := do
  let ba := la.blades V
  let bb := lb.blades V
  let bc := lc.blades V
  let mut out : Array PlanEntry := #[]
  for ia in [:ba.size] do
    let ma := ba[ia]!
    let ga := popcount32 ma
    for ib in [:bb.size] do
      let mb := bb[ib]!
      let gb := popcount32 mb
      let terms : Array (UInt32 × Float) :=
        match op with
        | .mul => bladeMulTerms V ma mb
        | .wedge =>
          if (ma &&& mb) == 0 then #[(ma ||| mb, reorderSign ma mb)] else #[]
        | .contractionLeft =>
          if ga <= gb then
            let wantG := gb - ga
            (bladeMulTerms V ma mb).filter fun (k, _) => popcount32 k == wantG
          else #[]
      for (mc, coef) in terms do
        if Float.abs coef > 1e-12 then
          match bc.findIdx? (· == mc) with
          | some ic => out := out.push { ia, ib, ic, coef }
          | none => pure ()
  return out

end Grassmann.CABI.Alg
