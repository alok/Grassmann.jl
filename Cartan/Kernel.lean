import Cartan.Field
import Cartan.Generated

/-!
# Field kernels: Grassmann products over whole fields

A product of two `Chain` fields evaluated point by point decodes two fiber vectors, looks up the
Grassmann plan of the operation (a hash-map read), runs it and encodes the result: three small
allocations and a lookup per point. Julia's broadcast runs the product's generated code in a
tight loop instead.

Every typed Grassmann product is `Kernels.bin op (layoutOf X) (layoutOf Y) (layoutOf Z)` on the
operands' dense coefficients, and every linear unary map `Kernels.un op (layoutOf X) (layoutOf Z)`
(`Grassmann.Algebra.Products`, `Grassmann.Algebra.Unary`); at `Float` the reference kernels
evaluate DirectSum's multiply-accumulate plan (`Grassmann.Kernel.Plan`). A field kernel looks the
plan up once and evaluates it at every point directly on the flat fiber arrays, in the plan's
own accumulation order, so its results are bit-identical to the pointwise product (the property
tests check this against the pointwise lift on random fields).

For the spaces with generated kernels (`Cartan.Generated`: `ℝ2`, `ℝ3`, `ℝ4`) the plan is not
interpreted at all: the straight-line kernel of the key runs instead (same arithmetic, same
order). The planned field instances apply to fibers with a dense `Float` layout (`Chain`,
`Spinor`, `CoSpinor`, `Multivector`); everything else uses the pointwise lift.
-/

namespace Cartan

open Grassmann Grassmann.Kernel DirectSum StaticVectors AbstractTensors

namespace Kernel

/-- A Grassmann plan prepared for field evaluation: gather-form rows with `Nat` positions and
`Float` coefficients (`code`: `0` is `+1`, `1` is `-1`, `2` is `coef`). -/
structure FieldPlan where
  /-- Number of outputs per point. -/
  outputs : Nat
  /-- Row boundaries (`outputs + 1` entries). -/
  rowStart : Array Nat
  /-- First-operand position per entry. -/
  ia : Array Nat
  /-- Second-operand position per entry (`0` for unary plans). -/
  ib : Array Nat
  /-- Coefficient class per entry. -/
  code : ByteArray
  /-- The coefficient per entry, as Grassmann's `Coeff.ofRat` at `Float`. -/
  coef : FloatArray
  deriving Inhabited

/-- Prepare a plan. -/
def FieldPlan.ofPlan (p : Plan) : FieldPlan where
  outputs := p.outputs
  rowStart := p.rowStart.map (·.toNat)
  ia := p.ia.map (·.toNat)
  ib := p.ib.map (·.toNat)
  code := p.code
  coef := p.coef.foldl (fun acc r => acc.push (Coeff.ofRat r)) (FloatArray.emptyWithCapacity p.coef.size)

/-- The plan of the binary operation `op` from layouts `la × lb` into `lc` on `V` (the reference
kernel's plan, `Grassmann.Kernel.plan`); `none` when Grassmann cannot build it. -/
def binPlan (V : TensorBundle) (op : BinOp) (la lb lc : Layout) : Option FieldPlan :=
  match plan { V, op := .bin op, la, lb, lc } with
  | .ok p => some (.ofPlan p)
  | .error _ => none

/-- The plan of the unary operation `op` from layout `la` into `lc` on `V`. -/
def unPlan (V : TensorBundle) (op : UnOp) (la lc : Layout) : Option FieldPlan :=
  match plan { V, op := .un op, la, lb := la, lc } with
  | .ok p => some (.ofPlan p)
  | .error _ => none

/-- Accumulate entry `t` of a row into `o` (Grassmann `Plan.acc`: `o + v`, `o - v` or
`o + coef * v`). The three are the single form `o + coef * v`: multiplying by `±1.0` is exact and
`o + (-v)` is `o - v` in IEEE arithmetic (signed zeros included), so the results are identical. -/
@[inline] def acc (fp : FieldPlan) (t : Nat) (o v : Float) : Float :=
  o + fp.coef.get! t * v

/-- One output of a binary plan at one point: entries `t, …, t+k-1` (Grassmann `Plan.row₂`). -/
def row₂ (fp : FieldPlan) (a b : FloatArray) (oa ob : Nat) : (k t : Nat) → Float → Float
  | 0, _, o => o
  | k + 1, t, o => row₂ fp a b oa ob k (t + 1) (acc fp t o (a.get! (oa + fp.ia[t]!) * b.get! (ob + fp.ib[t]!)))

/-- One output of a unary plan at one point (Grassmann `Plan.row₁`). -/
def row₁ (fp : FieldPlan) (a : FloatArray) (oa : Nat) : (k t : Nat) → Float → Float
  | 0, _, o => o
  | k + 1, t, o => row₁ fp a oa k (t + 1) (acc fp t o (a.get! (oa + fp.ia[t]!)))

/-- The outputs `c, …, c+k-1` of a binary plan at one point, pushed onto `out`. -/
def rows₂ (fp : FieldPlan) (a b : FloatArray) (oa ob : Nat) : (k c : Nat) → FloatArray → FloatArray
  | 0, _, out => out
  | k + 1, c, out =>
    let s := fp.rowStart[c]!
    let e := fp.rowStart[c + 1]!
    rows₂ fp a b oa ob k (c + 1) (out.push (row₂ fp a b oa ob (e - s) s 0))

/-- The outputs `c, …, c+k-1` of a unary plan at one point, pushed onto `out`. -/
def rows₁ (fp : FieldPlan) (a : FloatArray) (oa : Nat) : (k c : Nat) → FloatArray → FloatArray
  | 0, _, out => out
  | k + 1, c, out =>
    let s := fp.rowStart[c]!
    let e := fp.rowStart[c + 1]!
    rows₁ fp a oa k (c + 1) (out.push (row₁ fp a oa (e - s) s 0))

/-- A binary plan at the points `i, …, i+k-1` of two flat fields (widths `wa`, `wb`). -/
def points₂ (fp : FieldPlan) (a b : FloatArray) (wa wb : Nat) : (k i : Nat) → FloatArray → FloatArray
  | 0, _, out => out
  | k + 1, i, out => points₂ fp a b wa wb k (i + 1) (rows₂ fp a b (i * wa) (i * wb) fp.outputs 0 out)

/-- A unary plan at the points `i, …, i+k-1` of a flat field (width `wa`). -/
def points₁ (fp : FieldPlan) (a : FloatArray) (wa : Nat) : (k i : Nat) → FloatArray → FloatArray
  | 0, _, out => out
  | k + 1, i, out => points₁ fp a wa k (i + 1) (rows₁ fp a (i * wa) fp.outputs 0 out)

/-- Evaluate a binary plan at all `n` points: `n * outputs` floats. -/
def evalZip (fp : FieldPlan) (a b : FloatArray) (wa wb n : Nat) : FloatArray :=
  points₂ fp a b wa wb n 0 (FloatArray.emptyWithCapacity (n * fp.outputs))

/-- Evaluate a unary plan at all `n` points. -/
def evalMap (fp : FieldPlan) (a : FloatArray) (wa n : Nat) : FloatArray :=
  points₁ fp a wa n 0 (FloatArray.emptyWithCapacity (n * fp.outputs))

end Kernel

namespace TensorField

variable {M : Type} [FrameBundle M] {m : M} {X Y Z : Type} {V : TensorBundle}
  [FlatFiber X] [FlatFiber Y] [FlatFiber Z]
  [DenseLayout X V Float] [DenseLayout Y V Float] [DenseLayout Z V Float]

/-- The binary Grassmann operation `op : X → Y → Z` over two fields, through its plan
(`Kernels.bin op (layoutOf X) (layoutOf Y) (layoutOf Z)`); `pointwise` is the same operation on
fiber values, used if the plan cannot be built or does not have `Z`'s width. -/
def planZip (op : BinOp) (pointwise : X → Y → Z) (a : TensorField m X) (b : TensorField m Y) :
    TensorField m Z :=
  let n := card m
  let fallback (_ : Unit) : TensorField m Z :=
    match Kernel.binPlan V op (layoutOf X) (layoutOf Y) (layoutOf Z) with
    | some fp =>
      let out := Kernel.evalZip fp a.data b.data (FlatFiber.width X) (FlatFiber.width Y) n
      if h : out.size = FlatFiber.width Z * n then ⟨out, h, none⟩ else zipWith pointwise a b
    | none => zipWith pointwise a b
  match Generated.bin? V op (layoutOf X) (layoutOf Y) (layoutOf Z) with
  | some k =>
    let out := k a.data b.data n
    if h : out.size = FlatFiber.width Z * n then ⟨out, h, none⟩ else fallback ()
  | none => fallback ()

/-- The linear Grassmann map `op : X → Z` over a field, through its plan
(`Kernels.un op (layoutOf X) (layoutOf Z)`); `pointwise` as for `planZip`. -/
def planMap (op : UnOp) (pointwise : X → Z) (a : TensorField m X) : TensorField m Z :=
  let n := card m
  let fallback (_ : Unit) : TensorField m Z :=
    match Kernel.unPlan V op (layoutOf X) (layoutOf Z) with
    | some fp =>
      let out := Kernel.evalMap fp a.data (FlatFiber.width X) n
      if h : out.size = FlatFiber.width Z * n then ⟨out, h, none⟩ else map pointwise a
    | none => map pointwise a
  match Generated.un? V op (layoutOf X) (layoutOf Z) with
  | some k =>
    let out := k a.data n
    if h : out.size = FlatFiber.width Z * n then ⟨out, h, none⟩ else fallback ()
  | none => fallback ()

end TensorField

end Cartan
