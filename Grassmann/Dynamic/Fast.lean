/-
Fast paths of the dynamic layer: container products and unary maps through the space's
generated kernels (DESIGN.md §5.2), where they are bit for bit Julia's generated loops.

The dynamic products (`TA.mul`, `TA.wedge`, …) evaluate Julia's generated loops through
interpreted plans (`Grassmann.Dynamic.Loops`) so that `Float` results agree with Julia bit for
bit, sign of zero included, in *every* space; the unary maps compute each entry from DirectSum's
blade rules. Both are generic in the coefficient type and pay a plan lookup per call.

In a space whose `Kernels` instance is generated and whose metric is diagonal and
non-degenerate (not conformal, tangent or dyadic, `n ≤ 5`: `ℝ2`, `ℝ3`, `ℝ4`, `STA`, and
`basis!` spaces of that shape), the generated kernel of a

* product of two chains strictly between the scalars and the pseudoscalar,
* product of two containers (`Spinor`, `CoSpinor`, `Multivector`),
* sign map (`reverse`, `involute`, `clifford`, `antireverse`) or complement of a container

is the same computation as Julia's loop: the same contributions in the same order (first
operand outermost, one term per blade pair, no zero metric factors), summed from the first
term (Julia's expression form, used below its `cache_limit` for `n ≤ 5`), entries negated
with `-x`. The class `DynKernels V` records that a space qualifies (`fast`); the operator
instances of `Grassmann.Dynamic.Ops` (`*`, `∧`, `∨`, `⋅`, `~`, `⋆`, …) call the `…F`
functions here, which take the generated kernel when `fast` holds and the Julia loop
otherwise. At a call site with a literal space the test folds and the kernel is specialized at
the coefficient type (`Tests/Dynamic/Fast.lean` checks the two paths agree bit for bit on
random `Float` operands with zero entries; docs/PERF.md has the timings).

Julia's result kinds are unchanged: the fast paths cover exactly the branches of Julia's
dispatch that end in a container loop and fall back to the full lattice for everything
else (terms, couples, scalar or pseudoscalar factors, grades outside the range).
-/
import Grassmann.Dynamic.Products

namespace Grassmann

open DirectSum DirectSum.Bits StaticVectors AbstractTensors

/-- Whether the dynamic layer may evaluate container products and unary maps of `V` through
its `Kernels V` instance (see the module docstring): `true` only for spaces whose instance is
generated for every shape used and whose metric is diagonal, non-degenerate, not conformal,
tangent or dyadic, with `n ≤ 5`. The default instance says `false` (Julia's loops). -/
class DynKernels (V : TensorBundle) where
  /-- The generated kernels agree with Julia's loops bit for bit. -/
  fast : Bool

/-- Every space: Julia's loops. -/
instance (priority := low) DynKernels.loops (V : TensorBundle) : DynKernels V := ⟨false⟩

/-- `ℝ2` has generated kernels (`Grassmann.Kernel.Generated.R2`). -/
instance : DynKernels ℝ2 := ⟨true⟩
/-- `ℝ3` has generated kernels. -/
instance : DynKernels ℝ3 := ⟨true⟩
/-- `ℝ4` has generated kernels. -/
instance : DynKernels ℝ4 := ⟨true⟩
/-- `STA` has generated kernels (a non-degenerate signature). -/
instance : DynKernels STA := ⟨true⟩

/-- Whether a space's metric allows the fast paths when its kernels are generated: diagonal
and non-degenerate, not conformal, tangent or dyadic, at most 5 generators. -/
def _root_.DirectSum.TensorBundle.dynFastShape (V : TensorBundle) : Bool :=
  V.n ≤ 5 && !V.hasconformal && !V.istangent && V.dyadmode == 0 && V.isdiag &&
    (match V.metric with
     | .diagonal d => d.all (· != 0)
     | .tensor _ => false
     | _ => true)

namespace TA

variable {V : TensorBundle} {α : Type} [Coeff α] [Kernels V] [DynKernels V]

/-- The result layout of Julia's loop for the core product `op` of two chains of grades
`g`, `h` strictly between `0` and `n` (`none`: Julia's result is `𝟎`). -/
@[inline] def chainOut (n : Nat) (op : POp) (g h : Nat) : Option Layout :=
  match op with
  | .mul => some (halfL ((g + h) % 2 == 1))
  | .wedge => if g + h > n then none else some (.chain (g + h))
  | .vee => if g + h < n then none else some (.chain (g + h - n))
  | .contraction => if g < h then none else some (.chain (g - h))

/-- The result layout of Julia's loop for the core product `op` of two containers of layouts
`la`, `lb` (halves multiply by parity, `∨` shifted by the parity of `n`). -/
@[inline] def pairOut (n : Nat) (op : POp) : Layout → Layout → Layout
  | .full, _ | _, .full => .full
  | la, lb =>
    let p := la == .odd
    let q := lb == .odd
    let r := p ^^ q
    halfL (if op == .vee then r ^^ (n % 2 == 1) else r)

/-- A container's layout and storage (`none` for terms, chains and couples). -/
@[inline] def containerData? : TA V α → Option ((l : Layout) × Values α (l.size V.n))
  | spinor h => some ⟨.even, h.v⟩
  | cospinor h => some ⟨.odd, h.v⟩
  | multi m => some ⟨.full, m.v⟩
  | _ => none

/-- The core product `op(a, b)` (Julia's result kind), through the generated kernel where
`DynKernels.fast` allows it (module docstring). -/
@[inline] def prodF (op : POp) (a b : TA V α) : TA V α :=
  if DynKernels.fast V then
    match a, b with
    | single A x, single B y =>
      -- DirectSum's diagonal blade product (`TensorBundle.mulDiag`), scaled exactly as
      -- `termProd` scales its `BladeResult`: `x·y` on a positive disjoint product,
      -- `(x·y)·c` otherwise
      if op == .mul then
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
      else prod op a b
    | chain g x, chain h y =>
      if 0 < g && g < V.n && 0 < h && h < V.n then
        match chainOut V.n op g h with
        | some lc => ofLayout lc (Kernels.bin op.bin (.chain g) (.chain h) lc x.v y.v)
        | none => zero
      else prod op a b
    | _, _ =>
      match containerData? a, containerData? b with
      | some ⟨la, x⟩, some ⟨lb, y⟩ =>
        let lc := pairOut V.n op la lb
        ofLayout lc (Kernels.bin op.bin la lb lc x y)
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
  if DynKernels.fast V then
    match x with
    | chain g c => chain g ⟨Kernels.un op (.chain g) (.chain g) c.v⟩
    | spinor h => spinor ⟨Kernels.un op .even .even h.v⟩
    | cospinor h => cospinor ⟨Kernels.un op .odd .odd h.v⟩
    | multi m => multi ⟨Kernels.un op .full .full m.v⟩
    | _ => signMap op x
  else signMap op x

/-- A complement (`complementright`, `complementleft`, `hodge`, `complementlefthodge`) with
the fast path for containers and chains (the grade/parity flip of Julia's kinds). -/
@[inline] def complementF (op : UnOp) (x : TA V α) : TA V α :=
  if DynKernels.fast V then
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
