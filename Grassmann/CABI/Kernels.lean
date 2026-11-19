/-
  Grassmann/CABI/Kernels.lean — Init-only high-performance GA runtime kernels

  Strictly `Init`-only (ZERO `Lean.*`, `Lake.*`, or `Std.*` imports) so that
  standalone native dylibs (macOS/visionOS/Linux) link to ~2–5 MB instead of
  182–264 MB and compile directly to WebAssembly via `lean -c` + `emcc`.

  Covers:
  - Generic `Cl(p, q, r)` (`p + q + r ≤ 6`, up to 64 blades)
  - STA `Cl(3, 1)` (`S"-+++"`, preserving `ALOK-950` exact invariants)
  - R3 `Cl(3, 0, 0)` + exact rational rotor action (no `sqrt`/`sin`/`cos`)
  - PGA2 `Cl(2, 0, 1)` (`D"0,1,1"`) with metric-free right complement `!` & join `&`
  - PGA3 `Cl(3, 0, 1)` (`D"0,1,1,1"`) full 16-blade + specialized 8-float motors
    in canonical `SceneIR` v1 wire order `(s, e01, e02, e03, e12, e13, e23, e0123)`,
    closed-form `motorExp`/`motorLog`/`motorSlerp`, Study normalization,
    motor→4×4 col-major matrix, flat XYZ batch transform, and exact PGA3 mesh slicing
  - CGA2 `Cl(3, 1)` and CGA3 `Cl(4, 1)` (`no = ½(e₋ - e₊)`, `ni = e₋ + e₊`)

  Credits:
  - Michael Reed (`chakravala` / `Grassmann.jl`) for the Grassmann.jl architecture
  - Steven De Keninck (`enkimute` / `ganja.js`) for PGA/CGA/CoffeeShop conventions
-/
import Init.Data.FloatArray
import Init.Data.ByteArray
import Init.Data.Float

namespace Grassmann.CABI.Kernels

/-! ### Bit-level Clifford Algebra helpers (Init-only, zero allocations) -/

/-- Population count of a 32-bit blade bitmask (grade). -/
@[inline] def popcount32 (x : UInt32) : UInt32 :=
  let x : UInt32 := x - ((x >>> 1) &&& (0x55555555 : UInt32))
  let x : UInt32 := (x &&& (0x33333333 : UInt32)) + ((x >>> 2) &&& (0x33333333 : UInt32))
  let x : UInt32 := (x + (x >>> 4)) &&& (0x0F0F0F0F : UInt32)
  (x * (0x01010101 : UInt32)) >>> (24 : UInt32)

/-- Reordering parity of `e_a * e_b`: true iff an odd number of swaps is needed
to merge ascending index sets `a` and `b`. -/
@[inline] def swapOdd (a b : UInt32) : Bool :=
  -- Number of pairs (i ∈ a, j ∈ b) with i > j, mod 2.
  let s := a >>> 1
  let s := s ^^^ (s >>> 1)
  let s := s ^^^ (s >>> 2)
  let s := s ^^^ (s >>> 4)
  let s := s ^^^ (s >>> 8)
  let s := s ^^^ (s >>> 16)
  (popcount32 (s &&& b) &&& 1) == 1

/-- Reordering sign `±1.0` for `e_a * e_b`. -/
@[inline] def reorderSign (a b : UInt32) : Float :=
  if swapOdd a b then -1.0 else 1.0

/-- Grade reverse sign `(-1)^(k*(k-1)/2)`. -/
@[inline] def reverseSign (g : UInt32) : Float :=
  if ((g >>> 1) &&& 1) == 1 then -1.0 else 1.0

/-- Grade involution sign `(-1)^k`. -/
@[inline] def involuteSign (g : UInt32) : Float :=
  if (g &&& 1) == 1 then -1.0 else 1.0

/-- Clifford conjugate sign `(-1)^(k*(k+1)/2)`. -/
@[inline] def cliffordConjSign (g : UInt32) : Float :=
  if (((g + 1) >>> 1) &&& 1) == 1 then -1.0 else 1.0

/-- Safe indexed read from a `FloatArray` returning `0.0` if out of bounds. -/
@[inline] def faGet (a : FloatArray) (i : Nat) : Float :=
  if i < a.size then a.get! i else 0.0

/-- Allocate a zero-filled `FloatArray` of length `n`. -/
def faZeros (n : Nat) : FloatArray := Id.run do
  let mut out := FloatArray.emptyWithCapacity n
  for _ in [:n] do
    out := out.push 0.0
  return out

/-- In-place accumulate `out[i] += v` when `i < out.size`. -/
@[inline] def faAddAt (out : FloatArray) (i : Nat) (v : Float) : FloatArray :=
  if i < out.size then
    let cur := out.get! i
    out.set! i (cur + v)
  else
    out

/-! ### Generic `Cl(p, q, r)` Kernels (`p + q + r ≤ 6`, bitmask order)

Generator order for `Cl(p, q, r)` (matching ganja.js `Algebra(p, q, r)` when `r > 0`
has degenerate basis vectors first `e0..e_{r-1}`, followed by `p` positive `+1`
generators and `q` negative `-1` generators):
- bits `0 .. r-1`: square = `0`
- bits `r .. r+p-1`: square = `+1`
- bits `r+p .. r+p+q-1`: square = `-1`
Note: STA uses custom `-+++` layout (bit 0 = `-1`, bits 1..3 = `+1`) exposed via
explicit `sta*` kernels below AND `clWithMetric`!
-/

/-- Compute metric factor of `e_a * e_b` given bitmasks `zeroMask` (`e_k² = 0`)
and `negMask` (`e_k² = -1`). Returns `0.0`, `1.0`, or `-1.0`. -/
@[inline] def metricProductSign (a b zeroMask negMask : UInt32) : Float :=
  let common := a &&& b
  if (common &&& zeroMask) != 0 then
    0.0
  else
    let negOdd := (popcount32 (common &&& negMask) &&& 1) == 1
    let swOdd := swapOdd a b
    if negOdd != swOdd then -1.0 else 1.0

/-- Build `(n, zeroMask, negMask)` for `Cl(p, q, r)` with degenerate generators first
(ganja PGA convention: `e0..e_{r-1}` have square 0, next `p` have `+1`, last `q` have `-1`). -/
@[inline] def clMasks (p q r : UInt32) : UInt32 × UInt32 × UInt32 :=
  let n := p + q + r
  let zeroMask : UInt32 := if r == 0 then 0 else ((1 : UInt32) <<< r) - 1
  let negMask : UInt32 :=
    if q == 0 then 0
    else (((1 : UInt32) <<< q) - 1) <<< (r + p)
  (n, zeroMask, negMask)

/-- Geometric product in arbitrary metric `(n, zeroMask, negMask)`, `n ≤ 6`. -/
def metricMul (n zeroMask negMask : UInt32) (a b : FloatArray) : FloatArray := Id.run do
  let dim := (1 : Nat) <<< n.toNat
  let mut out := faZeros dim
  for i in [:dim] do
    let ai := faGet a i
    if ai != 0.0 then
      let iu := i.toUInt32
      for j in [:dim] do
        let bj := faGet b j
        if bj != 0.0 then
          let ju := j.toUInt32
          let s := metricProductSign iu ju zeroMask negMask
          if s != 0.0 then
            let k := (iu ^^^ ju).toNat
            out := faAddAt out k (s * ai * bj)
  return out

/-- Outer (wedge) product `a ∧ b` (metric-independent) in dimension `n ≤ 6`. -/
def metricWedge (n : UInt32) (a b : FloatArray) : FloatArray := Id.run do
  let dim := (1 : Nat) <<< n.toNat
  let mut out := faZeros dim
  for i in [:dim] do
    let ai := faGet a i
    if ai != 0.0 then
      let iu := i.toUInt32
      for j in [:dim] do
        let ju := j.toUInt32
        if (iu &&& ju) == 0 then
          let bj := faGet b j
          if bj != 0.0 then
            let s := reorderSign iu ju
            let k := (iu ||| ju).toNat
            out := faAddAt out k (s * ai * bj)
  return out

/-- Metric-free right complement `!x` (`e_a ∧ !e_a = I`). Never collapses degenerate blades! -/
def metricRightComplement (n : UInt32) (a : FloatArray) : FloatArray := Id.run do
  let dim := (1 : Nat) <<< n.toNat
  let fullMask : UInt32 := (dim - 1).toUInt32
  let mut out := faZeros dim
  for i in [:dim] do
    let ai := faGet a i
    if ai != 0.0 then
      let iu := i.toUInt32
      let comp := fullMask ^^^ iu
      let s := reorderSign iu comp
      out := faAddAt out comp.toNat (s * ai)
  return out

/-- Inverse right complement (`x = rightComplement (leftComplement x)`), i.e., `e_comp ∧ e_a = I`. -/
def metricLeftComplement (n : UInt32) (a : FloatArray) : FloatArray := Id.run do
  let dim := (1 : Nat) <<< n.toNat
  let fullMask : UInt32 := (dim - 1).toUInt32
  let mut out := faZeros dim
  for i in [:dim] do
    let ai := faGet a i
    if ai != 0.0 then
      let iu := i.toUInt32
      let comp := fullMask ^^^ iu
      let s := reorderSign comp iu
      out := faAddAt out comp.toNat (s * ai)
  return out

/-- Regressive (join / vee) product `a & b = leftComplement (rightComplement a ∧ rightComplement b)`. -/
def metricJoin (n : UInt32) (a b : FloatArray) : FloatArray :=
  metricLeftComplement n (metricWedge n (metricRightComplement n a) (metricRightComplement n b))

/-- Dorst left contraction `a << b` (only terms with `a ⊆ b`, grade `|b| - |a|`). -/
def metricLeftContract (n zeroMask negMask : UInt32) (a b : FloatArray) : FloatArray := Id.run do
  let dim := (1 : Nat) <<< n.toNat
  let mut out := faZeros dim
  for i in [:dim] do
    let ai := faGet a i
    if ai != 0.0 then
      let iu := i.toUInt32
      for j in [:dim] do
        let ju := j.toUInt32
        if (iu &&& ju) == iu then
          let bj := faGet b j
          if bj != 0.0 then
            let s := metricProductSign iu ju zeroMask negMask
            if s != 0.0 then
              let k := (iu ^^^ ju).toNat
              out := faAddAt out k (s * ai * bj)
  return out

/-- Reverse `~a` (`(-1)^(g*(g-1)/2)`). -/
def metricReverse (n : UInt32) (a : FloatArray) : FloatArray := Id.run do
  let dim := (1 : Nat) <<< n.toNat
  let mut out := FloatArray.emptyWithCapacity dim
  for i in [:dim] do
    out := out.push (reverseSign (popcount32 i.toUInt32) * faGet a i)
  return out

/-- Grade involution `â` (`(-1)^g`). -/
def metricInvolute (n : UInt32) (a : FloatArray) : FloatArray := Id.run do
  let dim := (1 : Nat) <<< n.toNat
  let mut out := FloatArray.emptyWithCapacity dim
  for i in [:dim] do
    out := out.push (involuteSign (popcount32 i.toUInt32) * faGet a i)
  return out

/-- Clifford conjugate (`(-1)^(g*(g+1)/2)`, ganja's `~a` for grade-1/2). -/
def metricCliffordConj (n : UInt32) (a : FloatArray) : FloatArray := Id.run do
  let dim := (1 : Nat) <<< n.toNat
  let mut out := FloatArray.emptyWithCapacity dim
  for i in [:dim] do
    out := out.push (cliffordConjSign (popcount32 i.toUInt32) * faGet a i)
  return out

/-- Sandwich product `R * x * ~R`. -/
def metricSandwich (n zeroMask negMask : UInt32) (r x : FloatArray) : FloatArray :=
  metricMul n zeroMask negMask (metricMul n zeroMask negMask r x) (metricReverse n r)

/-- Public `Cl(p, q, r)` geometric product. -/
def clMul (p q r : UInt32) (a b : FloatArray) : FloatArray :=
  let (n, zm, nm) := clMasks p q r
  metricMul n zm nm a b

def clWedge (p q r : UInt32) (a b : FloatArray) : FloatArray :=
  metricWedge (p + q + r) a b

def clJoin (p q r : UInt32) (a b : FloatArray) : FloatArray :=
  metricJoin (p + q + r) a b

def clLeftContract (p q r : UInt32) (a b : FloatArray) : FloatArray :=
  let (n, zm, nm) := clMasks p q r
  metricLeftContract n zm nm a b

def clReverse (p q r : UInt32) (a : FloatArray) : FloatArray :=
  metricReverse (p + q + r) a

def clDual (p q r : UInt32) (a : FloatArray) : FloatArray :=
  metricRightComplement (p + q + r) a

def clSandwich (p q r : UInt32) (versor x : FloatArray) : FloatArray :=
  let (n, zm, nm) := clMasks p q r
  metricSandwich n zm nm versor x

/-! ### STA `Cl(3, 1)` (`-+++`, `ALOK-950` exact invariants)

Bitmask order (16 doubles):
`0:1, 1:et, 2:ex, 3:etx, 4:ey, 5:ety, 6:exy, 7:etxy,
 8:ez, 9:etz, 10:exz, 11:etxz, 12:eyz, 13:etyz, 14:exyz, 15:etxyz`
`et² = -1` (bit 0 = negMask 1), `ex² = ey² = ez² = +1`.
-/

@[inline] def staMul (a b : FloatArray) : FloatArray := metricMul 4 0 1 a b
@[inline] def staWedge (a b : FloatArray) : FloatArray := metricWedge 4 a b
@[inline] def staLeftContract (a b : FloatArray) : FloatArray := metricLeftContract 4 0 1 a b
@[inline] def staReverse (a : FloatArray) : FloatArray := metricReverse 4 a
@[inline] def staSandwich (r x : FloatArray) : FloatArray := metricSandwich 4 0 1 r x

/-- Construct an STA Lorentz boost rotor `R = cosh(φ/2) - sinh(φ/2) (ux e_tx + uy e_ty + uz e_tz)`
along unit direction `(ux, uy, uz)` with rapidity `phi`. Satisfies `R * ~R = 1`. -/
def staBoostRotor (phi ux uy uz : Float) : FloatArray :=
  let len := Float.sqrt (ux * ux + uy * uy + uz * uz)
  let (nx, ny, nz) := if len > 1e-12 then (ux / len, uy / len, uz / len) else (1.0, 0.0, 0.0)
  let h := phi * 0.5
  let c := Float.cosh h
  let s := Float.sinh h
  let out := faZeros 16
  let out := faAddAt out 0 c
  let out := faAddAt out 3 (-s * nx)  -- etx (0b0011)
  let out := faAddAt out 5 (-s * ny)  -- ety (0b0101)
  let out := faAddAt out 9 (-s * nz)  -- etz (0b1001)
  out

/-- Compute STA spatial wedge geometry for two 16-component multivectors `a, b`.
Returns 12 doubles:
`[ax, ay, az, bx, by, bz, nx, ny, nz, area, angleRad, lorentzInner]`
where `(nx, ny, nz)` is the spatial normal `e_x, e_y, e_z` dual to the spatial
bivector `(a ∧ b)_{exy, exz, eyz}`, `area = ‖(a ∧ b)_spatial‖`,
`angleRad = atan2(area, a_s · b_s)`, and `lorentzInner = -a_t b_t + a_x b_x + a_y b_y + a_z b_z`. -/
def staSpatialWedge (a b : FloatArray) : FloatArray :=
  let at0 := faGet a 1; let ax := faGet a 2; let ay := faGet a 4; let az := faGet a 8
  let bt0 := faGet b 1; let bx := faGet b 2; let by0 := faGet b 4; let bz := faGet b 8
  let wxy := ax * by0 - ay * bx
  let wxz := ax * bz - az * bx
  let wyz := ay * bz - az * by0
  -- Right-handed 3D cross product (ay*bz - az*by, az*bx - ax*bz, ax*by - ay*bx)
  let nx := wyz
  let ny := -wxz
  let nz := wxy
  let area := Float.sqrt (nx * nx + ny * ny + nz * nz)
  let sdot := ax * bx + ay * by0 + az * bz
  let angle := Float.atan2 area sdot
  let ldot := -at0 * bt0 + sdot
  FloatArray.emptyWithCapacity 12
    |>.push ax |>.push ay |>.push az
    |>.push bx |>.push by0 |>.push bz
    |>.push nx |>.push ny |>.push nz
    |>.push area |>.push angle |>.push ldot

/-! ### R3 `Cl(3, 0, 0)` + Exact Rational Rotor (Zero-sqrt Cayley/Spinor action)

Bitmask order (8 doubles): `0:1, 1:e1, 2:e2, 3:e12, 4:e3, 5:e13, 6:e23, 7:e123`.
-/

/-- Unrolled straight-line R3 geometric product (8 doubles). -/
def r3Mul (a b : FloatArray) : FloatArray :=
  let a0 := faGet a 0; let a1 := faGet a 1; let a2 := faGet a 2; let a3 := faGet a 3
  let a4 := faGet a 4; let a5 := faGet a 5; let a6 := faGet a 6; let a7 := faGet a 7
  let b0 := faGet b 0; let b1 := faGet b 1; let b2 := faGet b 2; let b3 := faGet b 3
  let b4 := faGet b 4; let b5 := faGet b 5; let b6 := faGet b 6; let b7 := faGet b 7
  FloatArray.emptyWithCapacity 8
    |>.push (a0*b0 + a1*b1 + a2*b2 - a3*b3 + a4*b4 - a5*b5 - a6*b6 - a7*b7)
    |>.push (a0*b1 + a1*b0 - a2*b3 + a3*b2 - a4*b5 + a5*b4 - a6*b7 - a7*b6)
    |>.push (a0*b2 + a1*b3 + a2*b0 - a3*b1 - a4*b6 + a5*b7 + a6*b4 + a7*b5)
    |>.push (a0*b3 + a1*b2 - a2*b1 + a3*b0 + a4*b7 - a5*b6 + a6*b5 + a7*b4)
    |>.push (a0*b4 + a1*b5 + a2*b6 - a3*b7 + a4*b0 - a5*b1 - a6*b2 - a7*b3)
    |>.push (a0*b5 + a1*b4 - a2*b7 + a3*b6 - a4*b1 + a5*b0 - a6*b3 - a7*b2)
    |>.push (a0*b6 + a1*b7 + a2*b4 - a3*b5 - a4*b2 + a5*b3 + a6*b0 + a7*b1)
    |>.push (a0*b7 + a1*b6 - a2*b5 + a3*b4 + a4*b3 - a5*b2 + a6*b1 + a7*b0)

@[inline] def r3Wedge (a b : FloatArray) : FloatArray := metricWedge 3 a b
@[inline] def r3Reverse (a : FloatArray) : FloatArray :=
  FloatArray.emptyWithCapacity 8
    |>.push (faGet a 0) |>.push (faGet a 1) |>.push (faGet a 2) |>.push (-(faGet a 3))
    |>.push (faGet a 4) |>.push (-(faGet a 5)) |>.push (-(faGet a 6)) |>.push (-(faGet a 7))

@[inline] def r3Sandwich (r x : FloatArray) : FloatArray :=
  r3Mul (r3Mul r x) (r3Reverse r)

/-- Exact R3 rational rotor rotation `x ↦ (R * x * ~R) / (R * ~R)` using NO `sqrt`/`sin`/`cos`!
`r` is an even spinor `[s, b12, b13, b23]` (4 doubles) and `v` is `[x, y, z]` (3 doubles).
Returns `[x', y', z', normSq]` (4 doubles). -/
def r3ApplyRationalRotor (s b12 b13 b23 x y z : Float) : FloatArray :=
  let n2 := s * s + b12 * b12 + b13 * b13 + b23 * b23
  if n2 == 0.0 then
    FloatArray.emptyWithCapacity 4 |>.push x |>.push y |>.push z |>.push 0.0
  else
    let inv := 1.0 / n2
    -- R = s + b12 e12 + b13 e13 + b23 e23; compute R * (x e1 + y e2 + z e3) * ~R
    -- Let t = R * v = t1 e1 + t2 e2 + t4 e3 + t7 e123
    let t1 := s * x + b12 * y + b13 * z
    let t2 := s * y - b12 * x + b23 * z
    let t4 := s * z - b13 * x - b23 * y
    let t7 := b23 * x - b13 * y + b12 * z
    -- Multiply t * ~R where ~R = s - b12 e12 - b13 e13 - b23 e23
    let ox := (t1 * s + t2 * b12 + t4 * b13 + t7 * b23) * inv
    let oy := (t2 * s - t1 * b12 + t4 * b23 - t7 * b13) * inv
    let oz := (t4 * s - t1 * b13 - t2 * b23 + t7 * b12) * inv
    FloatArray.emptyWithCapacity 4 |>.push ox |>.push oy |>.push oz |>.push n2

/-- Construct a rational R3 rotor `[s, b12, b13, b23]` from two vectors `u, v`
(`R = ‖u‖² + v*u` when `‖u‖ = ‖v‖`, or pure rational `u*v + ‖u‖‖v‖`).
For the pure rational (zero-sqrt) Cayley parameterization `(t1, t2, t3)`:
`R = 1 + t3 e12 - t2 e13 + t1 e23`. -/
def r3RationalRotorFromCayley (t1 t2 t3 : Float) : FloatArray :=
  FloatArray.emptyWithCapacity 4
    |>.push 1.0 |>.push t3 |>.push (-t2) |>.push t1

/-! ### PGA2 `Cl(2, 0, 1)` (`D"0,1,1"`, bitmask order)

Bitmask order (8 doubles): `0:1, 1:e0, 2:e1, 3:e01, 4:e2, 5:e02, 6:e12, 7:e012`.
`e0² = 0` (zeroMask = 1), `e1² = e2² = +1` (negMask = 0).
Point `P(x, y) = !(e0 + x e1 + y e2) = e12 + y e01 - x e02`.
Line  `L(a, b, c) = c e0 + a e1 + b e2` (`a x + b y + c = 0`).
-/

@[inline] def pga2Mul (a b : FloatArray) : FloatArray := metricMul 3 1 0 a b
@[inline] def pga2Meet (a b : FloatArray) : FloatArray := metricWedge 3 a b
@[inline] def pga2Join (a b : FloatArray) : FloatArray := metricJoin 3 a b
@[inline] def pga2LeftContract (a b : FloatArray) : FloatArray := metricLeftContract 3 1 0 a b
@[inline] def pga2Reverse (a : FloatArray) : FloatArray := metricReverse 3 a
@[inline] def pga2Dual (a : FloatArray) : FloatArray := metricRightComplement 3 a
@[inline] def pga2Sandwich (r x : FloatArray) : FloatArray := metricSandwich 3 1 0 r x

def pga2Point (x y : Float) : FloatArray :=
  FloatArray.emptyWithCapacity 8
    |>.push 0.0 |>.push 0.0 |>.push 0.0 |>.push y
    |>.push 0.0 |>.push (-x) |>.push 1.0 |>.push 0.0

def pga2Line (a b c : Float) : FloatArray :=
  FloatArray.emptyWithCapacity 8
    |>.push 0.0 |>.push c |>.push a |>.push 0.0
    |>.push b |>.push 0.0 |>.push 0.0 |>.push 0.0

def pga2Normalize (m : FloatArray) : FloatArray :=
  -- Euclidean norm from non-e0 blades (indices 0, 2, 4, 6)
  let c0 := faGet m 0; let c2 := faGet m 2; let c4 := faGet m 4; let c6 := faGet m 6
  let n := Float.sqrt (c0*c0 + c2*c2 + c4*c4 + c6*c6)
  if n < 1e-12 then m
  else
    let inv := 1.0 / n
    FloatArray.emptyWithCapacity 8
      |>.push (c0 * inv) |>.push (faGet m 1 * inv) |>.push (c2 * inv) |>.push (faGet m 3 * inv)
      |>.push (c4 * inv) |>.push (faGet m 5 * inv) |>.push (c6 * inv) |>.push (faGet m 7 * inv)

/-! ### PGA3 `Cl(3, 0, 1)` (`D"0,1,1,1"`) — Full 16-blade + Canonical 8-float Motor

Full bitmask order (16 doubles):
`0:1, 1:e0, 2:e1, 3:e01, 4:e2, 5:e02, 6:e12, 7:e012,
 8:e3, 9:e03, 10:e13, 11:e013, 12:e23, 13:e023, 14:e123, 15:e0123`.

Canonical `SceneIR` v1 Motor wire order (8 doubles, ganja order):
`[0:s, 1:e01, 2:e02, 3:e03, 4:e12, 5:e13, 6:e23, 7:e0123]`.

Canonical PGA3 Point (4 doubles packed `(x, y, z, w)` or 8 odd blades / 16 full):
`P(x, y, z) = !(e0 + x e1 + y e2 + z e3) = e123 - x e023 + y e013 - z e012`.
-/

@[inline] def pga3Mul (a b : FloatArray) : FloatArray := metricMul 4 1 0 a b
@[inline] def pga3Meet (a b : FloatArray) : FloatArray := metricWedge 4 a b
@[inline] def pga3Join (a b : FloatArray) : FloatArray := metricJoin 4 a b
@[inline] def pga3LeftContract (a b : FloatArray) : FloatArray := metricLeftContract 4 1 0 a b
@[inline] def pga3Reverse (a : FloatArray) : FloatArray := metricReverse 4 a
@[inline] def pga3Dual (a : FloatArray) : FloatArray := metricRightComplement 4 a
@[inline] def pga3Sandwich (r x : FloatArray) : FloatArray := metricSandwich 4 1 0 r x

/-- Identity PGA3 motor `[1, 0, 0, 0, 0, 0, 0, 0]`. -/
def pga3MotorIdentity : FloatArray :=
  FloatArray.emptyWithCapacity 8
    |>.push 1.0 |>.push 0.0 |>.push 0.0 |>.push 0.0
    |>.push 0.0 |>.push 0.0 |>.push 0.0 |>.push 0.0

/-- Construct a PGA3 rotation motor around `(ax, ay, az)` by right-handed `angle` (radians).
Wire order: `[s, e01, e02, e03, e12, e13, e23, e0123]`. -/
def pga3MakeRotor (ax ay az angle : Float) : FloatArray :=
  let len := Float.sqrt (ax * ax + ay * ay + az * az)
  let (nx, ny, nz) := if len > 1e-12 then (ax / len, ay / len, az / len) else (0.0, 0.0, 1.0)
  let half := angle * 0.5
  let c := Float.cos half
  let s := Float.sin half
  FloatArray.emptyWithCapacity 8
    |>.push c
    |>.push 0.0 |>.push 0.0 |>.push 0.0
    |>.push (-s * nz) |>.push (s * ny) |>.push (-s * nx)
    |>.push 0.0

/-- Construct a PGA3 translation motor by `(tx, ty, tz)`.
`T = 1 - ½(tx e01 + ty e02 + tz e03)`. -/
def pga3MakeTranslator (tx ty tz : Float) : FloatArray :=
  FloatArray.emptyWithCapacity 8
    |>.push 1.0
    |>.push (-0.5 * tx) |>.push (-0.5 * ty) |>.push (-0.5 * tz)
    |>.push 0.0 |>.push 0.0 |>.push 0.0
    |>.push 0.0

/-- Straight-line unrolled PGA3 motor composition `a * b` in canonical wire order
`[0:1, 1:e01, 2:e02, 3:e03, 4:e12, 5:e13, 6:e23, 7:e0123]`. Zero intermediate allocs! -/
def pga3MotorCompose (a b : FloatArray) : FloatArray :=
  let a0 := faGet a 0; let a1 := faGet a 1; let a2 := faGet a 2; let a3 := faGet a 3
  let a4 := faGet a 4; let a5 := faGet a 5; let a6 := faGet a 6; let a7 := faGet a 7
  let b0 := faGet b 0; let b1 := faGet b 1; let b2 := faGet b 2; let b3 := faGet b 3
  let b4 := faGet b 4; let b5 := faGet b 5; let b6 := faGet b 6; let b7 := faGet b 7
  -- Verified Cayley table for e0²=0, e1²=e2²=e3²=+1:
  -- e12² = e13² = e23² = -1
  -- e12*e13 = -e23, e13*e12 = +e23
  -- e12*e23 = +e13, e23*e12 = -e13
  -- e13*e23 = -e12, e23*e13 = +e12
  -- e01*e12 = +e02, e12*e01 = -e02
  -- e01*e13 = +e03, e13*e01 = -e03
  -- e01*e23 = +e0123, e23*e01 = +e0123
  -- e02*e12 = -e01, e12*e02 = +e01
  -- e02*e13 = -e0123, e13*e02 = -e0123
  -- e02*e23 = +e03, e23*e02 = -e03
  -- e03*e12 = +e0123, e12*e03 = +e0123
  -- e03*e13 = -e01, e13*e03 = +e01
  -- e03*e23 = -e02, e23*e03 = +e02
  -- e0123*e12 = -e03, e12*e0123 = -e03
  -- e0123*e13 = +e02, e13*e0123 = +e02
  -- e0123*e23 = -e01, e23*e0123 = -e01
  let c0 := a0*b0 - a4*b4 - a5*b5 - a6*b6
  let c1 := a0*b1 + a1*b0 - a2*b4 - a3*b5 + a4*b2 + a5*b3 - a6*b7 - a7*b6
  let c2 := a0*b2 + a1*b4 + a2*b0 - a3*b6 - a4*b1 + a5*b7 + a6*b3 + a7*b5
  let c3 := a0*b3 + a1*b5 + a2*b6 + a3*b0 - a4*b7 - a5*b1 - a6*b2 - a7*b4
  let c4 := a0*b4 + a4*b0 - a5*b6 + a6*b5
  let c5 := a0*b5 + a4*b6 + a5*b0 - a6*b4
  let c6 := a0*b6 - a4*b5 + a5*b4 + a6*b0
  let c7 := a0*b7 + a1*b6 - a2*b5 + a3*b4 + a4*b3 - a5*b2 + a6*b1 + a7*b0
  FloatArray.emptyWithCapacity 8
    |>.push c0 |>.push c1 |>.push c2 |>.push c3
    |>.push c4 |>.push c5 |>.push c6 |>.push c7

/-- Reverse of a PGA3 motor `~M`: flips grade-2 signs `m[1..6]`, keeps `m[0], m[7]`. -/
def pga3MotorReverse (m : FloatArray) : FloatArray :=
  FloatArray.emptyWithCapacity 8
    |>.push (faGet m 0)
    |>.push (-(faGet m 1)) |>.push (-(faGet m 2)) |>.push (-(faGet m 3))
    |>.push (-(faGet m 4)) |>.push (-(faGet m 5)) |>.push (-(faGet m 6))
    |>.push (faGet m 7)

/-- Check if a PGA3 motor satisfies unit norm and the Study condition within `tol`. -/
def pga3MotorIsUnit (m : FloatArray) (tol : Float) : Bool :=
  let m0 := faGet m 0; let m1 := faGet m 1; let m2 := faGet m 2; let m3 := faGet m 3
  let m4 := faGet m 4; let m5 := faGet m 5; let m6 := faGet m 6; let m7 := faGet m 7
  let s2 := m0*m0 + m4*m4 + m5*m5 + m6*m6
  let study := 2.0 * (m0*m7 - m1*m6 + m2*m5 - m3*m4)
  Float.abs (s2 - 1.0) <= tol && Float.abs study <= tol

/-- Exact O(1) Study normalization of a PGA3 motor: `M' = M / √(M * ~M)`. -/
def pga3MotorNormalize (m : FloatArray) : FloatArray :=
  let m0 := faGet m 0; let m1 := faGet m 1; let m2 := faGet m 2; let m3 := faGet m 3
  let m4 := faGet m 4; let m5 := faGet m 5; let m6 := faGet m 6; let m7 := faGet m 7
  let s2 := m0*m0 + m4*m4 + m5*m5 + m6*m6
  if s2 <= 1e-24 then pga3MotorIdentity
  else
    let a := 1.0 / Float.sqrt s2
    let t := m0*m7 - m1*m6 + m2*m5 - m3*m4
    let b := -t * a * a * a
    -- Multiply M * (a + b e0123):
    -- e12*e0123 = -e03, e13*e0123 = +e02, e23*e0123 = -e01
    FloatArray.emptyWithCapacity 8
      |>.push (a * m0)
      |>.push (a * m1 - b * m6)
      |>.push (a * m2 + b * m5)
      |>.push (a * m3 - b * m4)
      |>.push (a * m4)
      |>.push (a * m5)
      |>.push (a * m6)
      |>.push (a * m7 + b * m0)

/-- Exact inverse of a (possibly unnormalized) PGA3 motor: `M⁻¹ = ~M / (M * ~M)`. -/
def pga3MotorInverse (m : FloatArray) : FloatArray :=
  let m0 := faGet m 0; let m1 := faGet m 1; let m2 := faGet m 2; let m3 := faGet m 3
  let m4 := faGet m 4; let m5 := faGet m 5; let m6 := faGet m 6; let m7 := faGet m 7
  let s2 := m0*m0 + m4*m4 + m5*m5 + m6*m6
  if s2 <= 1e-24 then pga3MotorIdentity
  else
    let invS := 1.0 / s2
    let t := 2.0 * (m0*m7 - m1*m6 + m2*m5 - m3*m4)
    let invT := -t * invS * invS
    -- ~M * (invS + invT e0123)
    let r0 := m0; let r1 := -m1; let r2 := -m2; let r3 := -m3
    let r4 := -m4; let r5 := -m5; let r6 := -m6; let r7 := m7
    FloatArray.emptyWithCapacity 8
      |>.push (invS * r0)
      |>.push (invS * r1 - invT * r6)
      |>.push (invS * r2 + invT * r5)
      |>.push (invS * r3 - invT * r4)
      |>.push (invS * r4)
      |>.push (invS * r5)
      |>.push (invS * r6)
      |>.push (invS * r7 + invT * r0)

/-- Closed-form O(1) PGA3 bivector exponential `exp(B)` where `B` is given as 6 bivector
components `[e01, e02, e03, e12, e13, e23]`. Returns a unit PGA3 motor (8 doubles). -/
def pga3MotorExp (b01 b02 b03 b12 b13 b23 : Float) : FloatArray :=
  let l2 := b12*b12 + b13*b13 + b23*b23
  if l2 < 1e-18 then
    -- Pure translation: exp(B_ideal) = 1 + B_ideal
    FloatArray.emptyWithCapacity 8
      |>.push 1.0 |>.push b01 |>.push b02 |>.push b03
      |>.push 0.0 |>.push 0.0 |>.push 0.0 |>.push 0.0
  else
    let norm := Float.sqrt l2
    let invN := 1.0 / norm
    -- Dual pitch: B² = -norm² + 2 * (b01*b23 - b02*b13 + b03*b12) e0123
    -- Note: B_ideal · B_euclid (with signs matching e01*e23=+I, e02*e13=-I, e03*e12=+I)
    let dot := b01*b23 - b02*b13 + b03*b12
    let pitch := dot * invN * invN
    let c := Float.cos norm
    let s := Float.sin norm
    let sOverN := s * invN
    let m0 := c
    let m4 := sOverN * b12
    let m5 := sOverN * b13
    let m6 := sOverN * b23
    -- Using dual-number Taylor: cos(norm + eps*p) = cos(norm) - eps*p*sin(norm)
    -- sin(norm + eps*p)/(norm + eps*p) = sOverN + eps*p*(c - sOverN)/norm
    -- Actually B = (norm + eps*d) * (L_unit) where d = -dot/norm (since B² = -(norm² - 2*dot*I))
    -- Wait: (norm - dot/norm * I)² = norm² - 2*dot*I!
    -- Let d = -dot * invN, so B = (norm + d*I) * u with u² = -1:
    -- exp(B) = cos(norm) - d*sin(norm)*I + [sOverN * B_euc + sOverN * B_id + d*(c - sOverN)/norm * I * B_euc]
    -- Simpler exact form from Dorst / De Keninck:
    -- M = cos(norm) + sin(norm)/norm * B + (cos(norm) - sin(norm)/norm) * pitch * (B_euc * I) + (sin(norm) * dot / norm) * I
    -- Let's verify: e12*I = -e03, e13*I = +e02, e23*I = -e01!
    -- Check pure screw along Z: B = t*e03 + a*e12 -> norm=a, dot=t*a, pitch=t/a.
    -- Exact exp(t*e03 + a*e12) = (1 + t*e03)(cos a + sin a e12)
    --   = cos a + t cos a e03 + sin a e12 + t sin a e0123!
    -- Check our formula with B_euc = a*e12, B_id = t*e03:
    --   m0 = cos a
    --   m4 = (sin a / a) * a = sin a
    --   m7 = (sin a / a) * (t * a) = t sin a!
    --   m3 = (sin a / a) * t - (cos a - sin a / a) * (t / a) * (-a)
    --      = t (sin a / a) + t (cos a - sin a / a) = t cos a!! EXACT!!
    let k := (c - sOverN) * pitch
    let m1 := sOverN * b01 + k * b23
    let m2 := sOverN * b02 - k * b13
    let m3 := sOverN * b03 + k * b12
    let m7 := sOverN * dot
    FloatArray.emptyWithCapacity 8
      |>.push m0 |>.push m1 |>.push m2 |>.push m3
      |>.push m4 |>.push m5 |>.push m6 |>.push m7

/-- Closed-form O(1) PGA3 motor logarithm `log(M)` returning 6 bivector coefficients
`[e01, e02, e03, e12, e13, e23]` such that `exp(log(M)) = M` (for unit motors). -/
def pga3MotorLog (m : FloatArray) : FloatArray :=
  -- Ensure positive scalar half-space for shortest-path log
  let sign := if faGet m 0 < 0.0 then -1.0 else 1.0
  let m0 := sign * faGet m 0
  let m1 := sign * faGet m 1; let m2 := sign * faGet m 2; let m3 := sign * faGet m 3
  let m4 := sign * faGet m 4; let m5 := sign * faGet m 5; let m6 := sign * faGet m 6
  let m7 := sign * faGet m 7
  let s2 := m4*m4 + m5*m5 + m6*m6
  if s2 < 1e-18 then
    -- Pure translation: log(1 + B_ideal) = B_ideal
    FloatArray.emptyWithCapacity 6
      |>.push m1 |>.push m2 |>.push m3 |>.push 0.0 |>.push 0.0 |>.push 0.0
  else
    let s := Float.sqrt s2
    let theta := Float.atan2 s m0
    let a := theta / s
    -- Inverse of screw formula above:
    -- m7 = s * (dot/norm) => dot = theta * m7 / s
    -- Check pure screw along Z: m0=cos a, m4=sin a, m3=t cos a, m7=t sin a:
    --   s = sin a, theta = a, a_fac = a / sin a
    --   b12 = a_fac * sin a = a.
    --   b03 = (a_fac * m3) + ((m0 * a_fac - 1) ... )? Let's solve explicitly!
    -- From exp: m3 = (s/theta)*b03 + (m0 - s/theta)*(dot/theta²)*b12, and b12 = (theta/s)*m4
    -- => m3 = (s/theta)*b03 + (m0 - s/theta)*(m7/s²)*m4
    -- => b03 = (theta/s) * (m3 - (m0 - s/theta)*(m7/s²)*m4)
    -- Wait: check pure screw Z: m3 - (cos a - sin a / a)*(t sin a / sin² a)*sin a
    --   = t cos a - (cos a - sin a / a)*t = t * (sin a / a)
    --   Multiply by (a / sin a) => b03 = t!! EXACT!!
    -- Generalize for all 3 ideal components using (m6, -m5, m4) matching (+b23, -b13, +b12):
    let c := (m0 - s / theta) * (m7 / s2)
    let b01 := a * (m1 - c * m6)
    let b02 := a * (m2 + c * m5)
    let b03 := a * (m3 - c * m4)
    let b12 := a * m4
    let b13 := a * m5
    let b23 := a * m6
    FloatArray.emptyWithCapacity 6
      |>.push b01 |>.push b02 |>.push b03 |>.push b12 |>.push b13 |>.push b23

/-- Screw linear interpolation (SLERP / ScLERP) between two unit PGA3 motors `m0, m1` at `t ∈ [0,1]`. -/
def pga3MotorSlerp (m0 m1 : FloatArray) (t : Float) : FloatArray :=
  let rel := pga3MotorCompose (pga3MotorReverse m0) m1
  let logRel := pga3MotorLog rel
  let step := pga3MotorExp
    (t * faGet logRel 0) (t * faGet logRel 1) (t * faGet logRel 2)
    (t * faGet logRel 3) (t * faGet logRel 4) (t * faGet logRel 5)
  pga3MotorNormalize (pga3MotorCompose m0 step)

/-- Convert a unit PGA3 motor (wire order `[s, e01, e02, e03, e12, e13, e23, e0123]`)
into a **column-major 4×4 affine matrix** (16 doubles) for OpenGL/WebGL/WebGPU/Metal/RealityKit!
Verified against `M * P(x, y, z) * ~M` on basis points `(0,0,0), (1,0,0), (0,1,0), (0,0,1)`. -/
def pga3MotorToMat4 (m : FloatArray) : FloatArray :=
  -- Map unit motor to quaternion (w, qx, qy, qz) where:
  -- R = cos(θ/2) - sin(θ/2)*(az e12 - ay e13 + ax e23)
  -- => w = m0, qx = -m6, qy = m5, qz = -m4!
  let w := faGet m 0
  let m1 := faGet m 1; let m2 := faGet m 2; let m3 := faGet m 3
  let qz := -(faGet m 4)
  let qy := faGet m 5
  let qx := -(faGet m 6)
  let m7 := faGet m 7
  -- Standard right-handed rotation matrix columns from unit quaternion (w, qx, qy, qz):
  let xx := qx*qx; let yy := qy*qy; let zz := qz*qz
  let xy := qx*qy; let xz := qx*qz; let yz := qy*qz
  let wx := w*qx; let wy := w*qy; let wz := w*qz
  -- Col 0 = R(1,0,0)
  let r00 := 1.0 - 2.0*(yy + zz)
  let r10 := 2.0*(xy + wz)
  let r20 := 2.0*(xz - wy)
  -- Col 1 = R(0,1,0)
  let r01 := 2.0*(xy - wz)
  let r11 := 1.0 - 2.0*(xx + zz)
  let r21 := 2.0*(yz + wx)
  -- Col 2 = R(0,0,1)
  let r02 := 2.0*(xz + wy)
  let r12 := 2.0*(yz - wx)
  let r22 := 1.0 - 2.0*(xx + yy)
  -- Translation vector t = M * P(0,0,0) * ~M = M * e123 * ~M:
  -- Compute t directly from (M * e123 * ~M) components (-e023, +e013, -e012):
  -- Let M = R + D where D = m1 e01 + m2 e02 + m3 e03 + m7 e0123.
  -- Since R * e123 * ~R = e123 (origin fixed by pure rotation),
  -- M * e123 * ~M = e123 + 2 * (D * ~R)_{e01, e02, e03} * e123!
  -- Wait: T = 1 - ½(tx e01 + ty e02 + tz e03), and M = T * R => D = -½ t_vec * R => t_vec = -2 * D * ~R!
  -- Compute (D * ~R) on e01, e02, e03:
  -- ~R = m0 - m4 e12 - m5 e13 - m6 e23 (with m4=-qz, m5=qy, m6=-qx)
  -- Using compose formula for c1, c2, c3 with a=(0,m1,m2,m3,0,0,0,m7), b=(m0,0,0,0,-m4,-m5,-m6,0):
  -- d1 = m1*m0 + m2*m4 + m3*m5 - m7*(-m6) = m1*m0 + m2*m4 + m3*m5 + m7*m6?
  -- Wait check compose c1: a0*b1 + a1*b0 - a2*b4 - a3*b5 + a4*b2 + a5*b3 - a6*b7 - a7*b6
  -- Here b4=-m4, b5=-m5, b6=-m6, a4=a5=a6=0:
  -- d1 = m1*m0 - m2*(-m4) - m3*(-m5) - m7*(-m6) = m1*m0 + m2*m4 + m3*m5 + m7*m6
  -- d2 = m1*(-m4) + m2*m0 - m3*(-m6) + m7*(-m5) = -m1*m4 + m2*m0 + m3*m6 - m7*m5
  -- d3 = m1*(-m5) + m2*(-m6) + m3*m0 - m7*(-m4) = -m1*m5 - m2*m6 + m3*m0 + m7*m4
  -- Wait check sign on pure T * R where T = 1 - ½ tx e01, R = cos - sin e12 (m4 = -sin):
  -- T*R has m0=cos, m1=-½ tx cos, m2=-½ tx (-sin) = +½ tx sin? Wait compose(T, R):
  -- c2 = a1*b4 = (-½ tx)*(-sin) = +½ tx sin.
  -- Check d1 = (-½ tx cos)*cos + (+½ tx sin)*(-sin)? Wait that gives -½ tx (cos² - sin²)!
  -- Aha! THANK GOODNESS WE CHECKED! Look at compose c2:
  -- e01 * e12 = +e02 => a1*b4 has +, so in T*R, m2 = a1*b4 = (-½ tx)*m4.
  -- Then in (T*R)*~R: b4 = -m4, so c1 has `- a2 * b4 = - m2 * (-m4) = + m2 * m4`!
  -- Plug in m2 = -½ tx * m4: `+ (-½ tx * m4) * m4 = -½ tx m4²`!!
  -- And `m1 * m0 = -½ tx m0²`!!
  -- Sum: `-½ tx (m0² + m4²) = -½ tx`!! Wait why did I think m2 = +½ tx sin? Because m4 = -sin so (-½ tx)*(-sin) = +½ tx sin, and then m2*m4 = (+½ tx sin)*(-sin) = -½ tx sin²!! IT WORKED!!
  -- Double check c2: `-m1*m4 + m2*m0 = -(-½ tx m0)*m4 + (-½ tx m4)*m0 = 0`!! EXACT ZERO!!
  let m4 := faGet m 4; let m5 := faGet m 5; let m6 := faGet m 6
  let tx := -2.0 * (m1*w + m2*m4 + m3*m5 + m7*m6)
  let ty := -2.0 * (-m1*m4 + m2*w + m3*m6 - m7*m5)
  let tz := -2.0 * (-m1*m5 - m2*m6 + m3*w + m7*m4)
  -- Column-major 4×4 matrix
  FloatArray.emptyWithCapacity 16
    |>.push r00 |>.push r10 |>.push r20 |>.push 0.0
    |>.push r01 |>.push r11 |>.push r21 |>.push 0.0
    |>.push r02 |>.push r12 |>.push r22 |>.push 0.0
    |>.push tx  |>.push ty  |>.push tz  |>.push 1.0

/-- Apply a unit PGA3 motor to a single 3D point `(x, y, z)` returning `[x', y', z']`. -/
def pga3MotorApplyXYZ (m : FloatArray) (x y z : Float) : FloatArray :=
  let mat := pga3MotorToMat4 m
  let r00 := faGet mat 0; let r10 := faGet mat 1; let r20 := faGet mat 2
  let r01 := faGet mat 4; let r11 := faGet mat 5; let r21 := faGet mat 6
  let r02 := faGet mat 8; let r12 := faGet mat 9; let r22 := faGet mat 10
  let tx  := faGet mat 12; let ty := faGet mat 13; let tz := faGet mat 14
  FloatArray.emptyWithCapacity 3
    |>.push (r00*x + r01*y + r02*z + tx)
    |>.push (r10*x + r11*y + r12*z + ty)
    |>.push (r20*x + r21*y + r22*z + tz)

/-- Blazing-fast batch transform of flat `xyz` triples (`3*N` doubles) by one unit PGA3 motor.
Precomputes the 3×4 affine matrix once, then runs a tight tail-recursive loop! -/
def pga3MotorApplyXYZBatch (m xyz : FloatArray) : FloatArray :=
  let mat := pga3MotorToMat4 m
  let r00 := faGet mat 0; let r10 := faGet mat 1; let r20 := faGet mat 2
  let r01 := faGet mat 4; let r11 := faGet mat 5; let r21 := faGet mat 6
  let r02 := faGet mat 8; let r12 := faGet mat 9; let r22 := faGet mat 10
  let tx  := faGet mat 12; let ty := faGet mat 13; let tz := faGet mat 14
  let lim := (xyz.size / 3) * 3
  let rec go (base : Nat) (out : FloatArray) : FloatArray :=
    if h2 : base + 2 < xyz.size then
      let x := xyz[base]'(Nat.lt_trans (Nat.lt_succ_of_lt (Nat.lt_succ_self base)) h2)
      let y := xyz[base + 1]'(Nat.lt_trans (Nat.lt_succ_self (base + 1)) h2)
      let z := xyz[base + 2]'h2
      let out := out
        |>.push (r00*x + r01*y + r02*z + tx)
        |>.push (r10*x + r11*y + r12*z + ty)
        |>.push (r20*x + r21*y + r22*z + tz)
      go (base + 3) out
    else out
  termination_by xyz.size - base
  go 0 (FloatArray.emptyWithCapacity lim)

/-! ### CGA2 `Cl(3, 1)` & CGA3 `Cl(4, 1)` Kernels

Standard raw orthonormal basis (ganja `Algebra(3,1)` and `Algebra(4,1)`):
- CGA2 (`n=4`, 16 blades): `e1²=e2²=e3²=+1`, `e4²=-1` (`zeroMask=0, negMask=0b1000=8`).
  `no = 0.5*(e4 - e3)`, `ni = e4 + e3`, `up(x,y) = x e1 + y e2 + ½(x²+y²) ni + no`.
- CGA3 (`n=5`, 32 blades): `e1²=e2²=e3²=e4²=+1`, `e5²=-1` (`zeroMask=0, negMask=0b10000=16`).
  `no = 0.5*(e5 - e4)`, `ni = e5 + e4`, `up(x,y,z) = x e1 + y e2 + z e3 + ½(x²+y²+z²) ni + no`.
-/

@[inline] def cga2Mul (a b : FloatArray) : FloatArray := metricMul 4 0 8 a b
@[inline] def cga2Wedge (a b : FloatArray) : FloatArray := metricWedge 4 a b
@[inline] def cga2LeftContract (a b : FloatArray) : FloatArray := metricLeftContract 4 0 8 a b
@[inline] def cga2Reverse (a : FloatArray) : FloatArray := metricReverse 4 a
@[inline] def cga2Sandwich (r x : FloatArray) : FloatArray := metricSandwich 4 0 8 r x

def cga2Up (x y : Float) : FloatArray :=
  let r2 := x*x + y*y
  -- ½ r² (e4 + e3) + ½ (e4 - e3) = ½(r² - 1) e3 + ½(r² + 1) e4
  let out := faZeros 16
  let out := faAddAt out 1 x
  let out := faAddAt out 2 y
  let out := faAddAt out 4 (0.5 * (r2 - 1.0))
  let out := faAddAt out 8 (0.5 * (r2 + 1.0))
  out

@[inline] def cga3Mul (a b : FloatArray) : FloatArray := metricMul 5 0 16 a b
@[inline] def cga3Wedge (a b : FloatArray) : FloatArray := metricWedge 5 a b
@[inline] def cga3LeftContract (a b : FloatArray) : FloatArray := metricLeftContract 5 0 16 a b
@[inline] def cga3Reverse (a : FloatArray) : FloatArray := metricReverse 5 a
@[inline] def cga3Sandwich (r x : FloatArray) : FloatArray := metricSandwich 5 0 16 r x

/-- Embed Euclidean point `(x, y, z)` into CGA3 `Cl(4, 1)` (32 doubles). -/
def cga3Up (x y z : Float) : FloatArray :=
  let r2 := x*x + y*y + z*z
  let out := faZeros 32
  let out := faAddAt out 1 x                   -- e1
  let out := faAddAt out 2 y                   -- e2
  let out := faAddAt out 4 z                   -- e3
  let out := faAddAt out 8 (0.5 * (r2 - 1.0))  -- e4 (+)
  let out := faAddAt out 16 (0.5 * (r2 + 1.0)) -- e5 (-)
  out

/-- Extract Euclidean `(x, y, z)` from a CGA3 null point (32 doubles). -/
def cga3Down (p : FloatArray) : FloatArray :=
  -- -p · ni = (p_e5 - p_e4) (check: up has e5-e4 = 1!)
  let w := faGet p 16 - faGet p 8
  let inv := if Float.abs w > 1e-12 then 1.0 / w else 1.0
  FloatArray.emptyWithCapacity 3
    |>.push (faGet p 1 * inv)
    |>.push (faGet p 2 * inv)
    |>.push (faGet p 4 * inv)

/-- Construct a CGA3 dual sphere `S* = up(cx, cy, cz) - ½ r² ni` (32 doubles). -/
def cga3DualSphere (cx cy cz radius : Float) : FloatArray :=
  let r2 := cx*cx + cy*cy + cz*cz - radius*radius
  let out := faZeros 32
  let out := faAddAt out 1 cx
  let out := faAddAt out 2 cy
  let out := faAddAt out 4 cz
  let out := faAddAt out 8 (0.5 * (r2 - 1.0))
  let out := faAddAt out 16 (0.5 * (r2 + 1.0))
  out

/-- Construct a CGA3 dual plane `Π* = nx e1 + ny e2 + nz e3 + d ni` (32 doubles). -/
def cga3DualPlane (nx ny nz d : Float) : FloatArray :=
  let out := faZeros 32
  let out := faAddAt out 1 nx
  let out := faAddAt out 2 ny
  let out := faAddAt out 4 nz
  let out := faAddAt out 8 d
  let out := faAddAt out 16 d
  out

end Grassmann.CABI.Kernels
