/-
Fast paths of the dynamic layer: container products and unary maps through compiled kernels,
where they are bit for bit Julia's generated loops.

The dynamic products (`TA.mul`, `TA.wedge`, …) evaluate Julia's generated loops through
interpreted plans (`Grassmann.Dynamic.Loops`) so that `Float` results agree with Julia bit for
bit, sign of zero included, in *every* space; the unary maps compute each entry from DirectSum's
blade rules. Both are generic in the coefficient type and pay a plan lookup per call.

`grassmann_kernels`/`basis!` emit a `DynKernels V` instance (`Grassmann.Kernel.Dyn`) for every
space they generate with at most five generators and no tangent or dyadic generators (the
standard spaces `ℝ2` … `CGA3`, and user spaces through `basis!`): Julia's loops of the container
shapes below as compiled straight-line kernels (the typed layer's generated kernel where its plan
is Julia's loop entry for entry, a dedicated kernel from the loop plan otherwise: a degenerate
metric's zero factors, a conformal space), and flags recording which generated unary kernels are
Julia's entry-wise maps. The operator instances of `Grassmann.Dynamic.Ops` (`*`, `∧`, `∨`, `⋅`,
`~`, `⋆`, …) call the `…F` functions here, which take

* for a product of two chains strictly between the scalars and the pseudoscalar, or of two
  containers (`Spinor`, `CoSpinor`, `Multivector`), `DynKernels.loop` when `DynKernels.loops`;
* for two terms, the blade sign (`parityjoin`) with `termProd`'s exact scaling when
  `DynKernels.fast` (non-degenerate diagonal metrics);
* for a sign map (`reverse`, `involute`, `clifford`, `antireverse`) or plain complement of a
  container, the generated kernel when `DynKernels.signs`; for a Hodge complement when
  `DynKernels.hodges`;

and Julia's loops (the full lattice) for everything else. At a call site with a literal space
the flags fold and the kernel is specialized at the coefficient type (`Tests/Dynamic/Fast.lean`
and `Tests/Codegen/Kernels.lean` check the two paths agree bit for bit on random `Float`
operands with zero entries; docs/PERF.md has the timings).

Julia's result kinds are unchanged: the fast paths cover exactly the branches of Julia's
dispatch that end in a container loop and fall back to the full lattice for everything
else (terms, couples, scalar or pseudoscalar factors, grades outside the range).
-/
import Grassmann.Dynamic.Products
import Grassmann.Kernel.Dyn

namespace Grassmann

open DirectSum DirectSum.Bits StaticVectors AbstractTensors

namespace TA

variable {V : TensorBundle} {α : Type} [Coeff α] [Kernels V] [DynKernels V]

/-- A container's layout and storage (`none` for terms, chains and couples). -/
@[inline] def containerData? : TA V α → Option ((l : Layout) × Values α (l.size V.n))
  | spinor h => some ⟨.even, h.v⟩
  | cospinor h => some ⟨.odd, h.v⟩
  | multi m => some ⟨.full, m.v⟩
  | _ => none

/-- The product of two terms by the blade sign when `DynKernels.fast` (a non-degenerate
diagonal metric): DirectSum's diagonal blade product (`TensorBundle.mulDiag`), scaled exactly as
`termProd` scales its `BladeResult`: `x·y` on a positive disjoint product, `(x·y)·c` otherwise. -/
@[inline] def singleMulF (A : UInt64) (x : α) (B : UInt64) (y : α) : TA V α :=
  let d := A ^^^ B
  match V.metric with
  | .euclid | .signature _ =>
    -- a signature: the sign is Julia's `parityjoin` (reordering and shared negative
    -- generators), the factor `±1`
    let neg := parityjoin V.sigBits A B
    if A &&& B == 0 then single d (if neg then (x * y) * Coeff.ofRat (-1) else x * y)
    else single d ((x * y) * Coeff.ofRat (if neg then -1 else 1))
  | _ =>
    let (c, d) := V.mulDiag A B
    if A &&& B == 0 then single d (if c < 0 then (x * y) * Coeff.ofRat (-1) else x * y)
    else single d ((x * y) * Coeff.ofRat c)

/-- The core product `op(a, b)` (Julia's result kind), through the compiled loops where
`DynKernels` allows it (module docstring). -/
@[inline] def prodF (op : POp) (a b : TA V α) : TA V α :=
  if DynKernels.loops V then
    match a, b with
    | single A x, single B y =>
      if DynKernels.fast V && op == .mul then singleMulF A x B y else prod op a b
    | chain g x, chain h y =>
      if 0 < g && g < V.n && 0 < h && h < V.n then
        match dynChainOut V op.bin g h with
        | some lc => ofLayout lc (DynKernels.loop op.bin (.chain g) (.chain h) lc x.v y.v)
        | none => zero
      else prod op a b
    | _, _ =>
      match containerData? a, containerData? b with
      | some ⟨la, x⟩, some ⟨lb, y⟩ =>
        let lc := dynPairOut V.n op.bin la lb
        ofLayout lc (DynKernels.loop op.bin la lb lc x y)
      | _, _ => prod op a b
  else prod op a b

/-- Julia `a * b` (the geometric product) with the fast path. -/
@[inline] def mulF (a b : TA V α) : TA V α := prodF .mul a b
/-- Julia `a ∧ b` with the fast path. -/
@[inline] def wedgeF (a b : TA V α) : TA V α := prodF .wedge a b
/-- Julia `a ∨ b` with the fast path. -/
@[inline] def veeF (a b : TA V α) : TA V α := prodF .vee a b
/-- Julia `contraction(a, b)` with the fast path. -/
@[inline] def contractionF (a b : TA V α) : TA V α := prodF .contraction a b

/-- A sign map (`reverse`, `involute`, `clifford`, `antireverse`) with the fast path for
containers and chains. -/
@[inline] def signF (op : UnOp) (x : TA V α) : TA V α :=
  if DynKernels.signs V then
    match x with
    | chain g c => chain g ⟨Kernels.un op (.chain g) (.chain g) c.v⟩
    | spinor h => spinor ⟨Kernels.un op .even .even h.v⟩
    | cospinor h => cospinor ⟨Kernels.un op .odd .odd h.v⟩
    | multi m => multi ⟨Kernels.un op .full .full m.v⟩
    | _ => signMap op x
  else signMap op x

/-- Whether the generated kernels compute the complement `op` exactly as Julia does. -/
@[inline] def complementExact (V : TensorBundle) [DynKernels V] (op : UnOp) : Bool :=
  if op == .complementright || op == .complementleft then DynKernels.signs V else DynKernels.hodges V

/-- A complement (`complementright`, `complementleft`, `hodge`, `complementlefthodge`) with
the fast path for containers and chains (the grade/parity flip of Julia's kinds). -/
@[inline] def complementF (op : UnOp) (x : TA V α) : TA V α :=
  if complementExact V op then
    match x with
    | chain g c => chain (V.n - g) ⟨Kernels.un op (.chain g) (.chain (V.n - g)) c.v⟩
    | spinor h => ofHalf (p := V.n % 2 == 1) ⟨Kernels.un op .even (halfLayout (V.n % 2 == 1)) h.v⟩
    | cospinor h => ofHalf (p := V.n % 2 == 0) ⟨Kernels.un op .odd (halfLayout (V.n % 2 == 0)) h.v⟩
    | multi m => multi ⟨Kernels.un op .full .full m.v⟩
    | _ => complementMap op x
  else complementMap op x

/-- Julia `reverse(x)` with the fast path. -/
@[inline] def reverseF (x : TA V α) : TA V α := signF .reverse x
/-- Julia `involute(x)` with the fast path. -/
@[inline] def involuteF (x : TA V α) : TA V α := signF .involute x
/-- Julia `clifford(x)` with the fast path. -/
@[inline] def cliffordF (x : TA V α) : TA V α := signF .clifford x
/-- Julia `hodge(x)` with the fast path. -/
@[inline] def hodgeF (x : TA V α) : TA V α := complementF .complementrighthodge x
/-- Julia `complementright(x)` with the fast path. -/
@[inline] def complementrightF (x : TA V α) : TA V α := complementF .complementright x
/-- Julia `complementleft(x)` with the fast path. -/
@[inline] def complementleftF (x : TA V α) : TA V α := complementF .complementleft x

instance : Mul (TA V α) := ⟨mulF⟩

end TA

end Grassmann
