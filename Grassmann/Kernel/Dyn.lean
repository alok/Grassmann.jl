/-
Generated kernels for the dynamic layer (`Grassmann.TA`): `class DynKernels V`.

The dynamic products evaluate Julia's generated loops (`Grassmann.Loops`: Julia's summation
order, first-term sums, the zero metric factors of a degenerate geometric product kept) so that
`Float` results agree with Julia bit for bit, sign of zero included. Interpreted, a loop costs a
plan lookup in a process-wide `HashMap` (hashing the space) and generic, boxed coefficient
arithmetic: 200–300 ns for a small product, and the unary maps compute every entry from
DirectSum's blade rules (µs).

`grassmann_kernels`/`basis!` (`Grassmann.Kernel.Codegen.Dyn`) emit a `DynKernels V` instance for
every space it generates with at most five generators and no tangent generators. At
elaboration time it builds Julia's loop plan of every container shape the dynamic layer's fast
paths use (`dynKeys`: the four core products of two chains strictly between the scalars and the
pseudoscalar, and of two containers) and compares it entry by entry with the plan of the
space's generated kernel for the same layouts: where they are equal the loop *is* the generated
kernel (the non-degenerate diagonal spaces), otherwise (a degenerate metric, whose loop keeps
`0·x·y` terms; a conformal space) a dedicated straight-line kernel is emitted from the loop plan.
So `loop` is Julia's loop, compiled, in every such space, and the flags record which unary maps
the generated kernels compute exactly as Julia does:

| field | meaning |
|---|---|
| `loops` | `loop` covers every key of `dynKeys` (compiled) |
| `signs` | the sign maps (`reverse`, `involute`, `clifford`, `antireverse`) and the plain complements (`complementright`, `complementleft`) of every container are the generated kernels (signed permutations, Julia's `±x`) |
| `hodges` | the same for the Hodge complements (diagonal metrics without zero factors) |
| `fast` | all of the above in a non-degenerate diagonal space (`dynFastShape`): products of two terms by the blade sign too |

The default instance (every other space) sets every flag to `false`: Julia's loops,
interpreted. The operator instances of the dynamic layer read these through
`Grassmann.Dynamic.Fast`.
-/
module

public import Grassmann.Dynamic.Loops

@[expose] public section

namespace Grassmann

open DirectSum DirectSum.Bits StaticVectors AbstractTensors

/-- Whether a space's metric is diagonal and non-degenerate, not conformal, tangent or dyadic,
with at most 5 generators: there Julia's loops add no zero-factor terms, so the generated
kernels of the typed layer are Julia's loops. -/
def _root_.DirectSum.TensorBundle.dynFastShape (V : TensorBundle) : Bool :=
  V.n ≤ 5 && !V.hasconformal && !V.istangent && V.dyadmode == 0 && V.isdiag &&
    (match V.metric with
     | .diagonal d => d.all (· != 0)
     | .tensor _ => false
     | _ => true)

/-- The generated Julia loops of the space `V` for the dynamic layer (module docstring). -/
class DynKernels (V : TensorBundle) where
  /-- Products of two terms and every map below agree with Julia bit for bit (`dynFastShape`). -/
  fast : Bool := false
  /-- The sign maps and plain complements of containers are the generated kernels. -/
  signs : Bool := false
  /-- The Hodge complements of containers are the generated kernels. -/
  hodges : Bool := false
  /-- `loop` is compiled for every key of `dynKeys`. -/
  loops : Bool := false
  /-- Julia's generated loop of `op` from containers of layouts `la × lb` into `lc`, the first
  operand outermost, in its expression form (`Grassmann.Loops`). -/
  loop : {α : Type} → [Coeff α] → BinOp → (la lb lc : Layout) →
      Values α (la.size V.n) → Values α (lb.size V.n) → Values α (lc.size V.n) :=
    fun op la lb lc x y =>
      Loops.run true { V, op, a := .dense la, b := .dense lb, lc, outerFirst := true } x.data y.data

/-- Every space: Julia's loops, interpreted. -/
instance (priority := low) DynKernels.interpreted (V : TensorBundle) : DynKernels V := {}

/-- The half layout of parity `odd`. -/
@[inline] def DynKernels.halfL (odd : Bool) : Layout := if odd then .odd else .even

/-- The result layout of Julia's loop for the core product `op` of two chains of grades
`g`, `h` strictly between `0` and `n` (`none`: Julia's result is `𝟎`); a conformal contraction
of two chains is a `Multivector` (Julia's `μ`, `src/algebra.jl:1152-1450`). -/
@[inline] def dynChainOut (V : TensorBundle) (op : BinOp) (g h : Nat) : Option Layout :=
  match op with
  | .mul => some (DynKernels.halfL ((g + h) % 2 == 1))
  | .wedge => if g + h > V.n then none else some (.chain (g + h))
  | .vee => if g + h < V.n then none else some (.chain (g + h - V.n))
  | .contraction => if g < h then none else if V.hasconformal then some .full else some (.chain (g - h))
  | _ => none

/-- The result layout of Julia's loop for the core product `op` of two containers of layouts
`la`, `lb` (halves multiply by parity, `∨` shifted by the parity of `n`;
`src/products.jl:1146-1320`). -/
@[inline] def dynPairOut (n : Nat) (op : BinOp) : Layout → Layout → Layout
  | .full, _ | _, .full => .full
  | la, lb =>
    let r := (la == .odd) ^^ (lb == .odd)
    DynKernels.halfL (if op == .vee then r ^^ (n % 2 == 1) else r)

/-- The keys `(op, la, lb, lc)` of Julia's loops the dynamic layer's fast paths use in `V`:
the four core products of two chains strictly between the scalars and the pseudoscalar (where
the product is not `𝟎`), and of two containers (`Spinor`, `CoSpinor`, `Multivector`). -/
def dynKeys (V : TensorBundle) : Array (BinOp × Layout × Layout × Layout) := Id.run do
  let mut out := #[]
  for op in [BinOp.mul, .wedge, .vee, .contraction] do
    for g in [1:V.n] do
      for h in [1:V.n] do
        if let some lc := dynChainOut V op g h then out := out.push (op, .chain g, .chain h, lc)
    for la in [Layout.even, .odd, .full] do
      for lb in [Layout.even, .odd, .full] do
        out := out.push (op, la, lb, dynPairOut V.n op la lb)
  return out

end Grassmann
