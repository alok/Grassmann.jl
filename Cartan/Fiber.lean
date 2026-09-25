import Grassmann
import Cartan.Flat

/-!
# Fibers: flat unboxed storage of field values

A Julia `TensorField{B,F,N}` stores its fiber values in an `Array{F,N}`. For the element types that
occur in practice (`Float64`, `ComplexF64`, `Chain`, `Spinor`, `Multivector`, `Values`) Julia's
`F` is an isbits type, so the array holds the coefficients inline, one element after the other
(docs/port-notes/cartan-core.md §8.3). `FlatFiber F` is that encoding for Lean: an element of
`F` is `width F` consecutive `Float`s, and a field over `n` points is one `FloatArray` of
`width F * n` floats in point-major (Julia column-major) order. No element is boxed.

* `FlatFiber F`: `width`, `read` (decode at an offset), `push` (append), and the size law that
  lets field combinators prove their output sizes.
* `LinearFiber F`: `+`, `-`, negation and scaling by a `Float` act componentwise
  on the encoding (true for all the instances here), so fields of `F` add and scale their raw
  arrays in one loop.
* `ShowFiber F`: Julia's `show` of a fiber value, non-compact (`1.0v₁ + 2.0v₂`) and compact
  (`1.0v₁+2.0v₂`, used inside arrays and after `↦` in compact context).

`Induced` is Julia's `InducedMetric` (Grassmann `src/forms.jl:1692`): the metric of the fiber
algebra itself, a zero-size tag.
-/

namespace Cartan

open Grassmann DirectSum StaticVectors AbstractTensors JuliaBase

/-- Julia `InducedMetric` (Grassmann `src/forms.jl:1692`): "use the fiber algebra's own
metric". A Cartan base whose metric type is `Induced` stores no per-point metric. -/
structure Induced where
  deriving Repr, BEq, DecidableEq, Inhabited, Hashable

/-- Julia `isinduced(::InducedMetric) = true` (Grassmann `src/forms.jl:1699`). -/
@[inline] def Induced.isInduced (_ : Induced) : Bool := true

/-! ## Flat fibers -/

/-- `FloatArray.set!` keeps the size. -/
@[simp] theorem _root_.FloatArray.size_set!' (a : FloatArray) (i : Nat) (v : Float) :
    (a.set! i v).size = a.size := by
  cases a; simp [FloatArray.set!, FloatArray.size]

/-- `(a.set! i x).get! i = x` in range. -/
theorem _root_.FloatArray.get!_set!_self (a : FloatArray) (i : Nat) (x : Float) (h : i < a.size) :
    (a.set! i x).get! i = x := by
  cases a with | mk ds =>
  simp only [FloatArray.size] at h
  simp [FloatArray.set!, FloatArray.get!, Array.set!, h]

/-- `set!` leaves the other entries alone. -/
theorem _root_.FloatArray.get!_set!_ne (a : FloatArray) (i j : Nat) (x : Float) (h : i ≠ j) :
    (a.set! i x).get! j = a.get! j := by
  cases a with | mk ds =>
  simp [FloatArray.set!, FloatArray.get!, Array.set!, getElem!_def, h]

/-- Two float arrays with the same size and the same entries are equal. -/
theorem _root_.FloatArray.ext_get! {a b : FloatArray} (hs : a.size = b.size)
    (h : ∀ i, i < a.size → a.get! i = b.get! i) : a = b := by
  cases a with | mk xs =>
  cases b with | mk ys =>
  simp only [FloatArray.size] at hs h
  congr 1
  apply Array.ext hs
  intro i h1 h2
  have := h i h1
  simp only [FloatArray.get!, getElem!_def, Array.getElem?_eq_getElem h1,
    Array.getElem?_eq_getElem h2] at this
  exact this

/-- `a[off + j] := src[j]` for `j ∈ [j₀, j₀ + k)` (in place once unshared; the default `write`). -/
def writeFrom (src : FloatArray) (off : Nat) : (k j : Nat) → FloatArray → FloatArray
  | 0, _, a => a
  | k + 1, j, a => writeFrom src off k (j + 1) (a.set! (off + j) (src.get! j))

@[simp] theorem size_writeFrom (src : FloatArray) (off : Nat) : ∀ (k j : Nat) (a : FloatArray),
    (writeFrom src off k j a).size = a.size
  | 0, _, _ => rfl
  | k + 1, j, a => by rw [writeFrom, size_writeFrom src off k (j + 1), FloatArray.size_set!']

/-- A fiber type whose elements are `width` consecutive `Float`s in a `FloatArray` (Julia: an
isbits element type stored inline in `Array{F}`). -/
class FlatFiber (F : Type) where
  /-- Number of floats per element. -/
  width : Nat
  /-- Decode the element stored at `a[off], …, a[off + width - 1]` (reads past the end give
  `0.0`, as `FloatArray.get!`). -/
  read : FloatArray → Nat → F
  /-- Append the encoding of an element. -/
  push : FloatArray → F → FloatArray
  /-- Pushing appends exactly `width` floats. -/
  size_push (a : FloatArray) (x : F) : (push a x).size = a.size + width
  /-- Write the encoding of an element at `a[off], …` (destination passing: in place when the
  array is exclusive, entries past the end dropped). Fields are built by writing into a
  preallocated buffer (`TensorField.ofFn`), which avoids `FloatArray.push`, an out-of-line call
  per float. The default goes through `push`; the instances here write directly. -/
  write (a : FloatArray) (off : Nat) (x : F) : FloatArray :=
    let s := push FloatArray.empty x
    writeFrom s off s.size 0 a
  /-- Writing keeps the size. -/
  size_write (a : FloatArray) (off : Nat) (x : F) : (write a off x).size = a.size := by
    intros; simp

attribute [simp] FlatFiber.size_push

/-- `FloatArray.push` adds one element. -/
@[simp] theorem _root_.FloatArray.size_push' (a : FloatArray) (x : Float) :
    (a.push x).size = a.size + 1 := by
  cases a; simp [FloatArray.push, FloatArray.size]

/-- `+`, `-`, negation and scaling by a `Float` act componentwise on the flat encoding of `F`, so
fields of `F` may add and scale their raw arrays. `recipDiv` records how Julia divides by a real
`s`: Grassmann elements as `x * (1/s)` (Grassmann `src/algebra.jl:704`, `a/b = a*(1/b)` for
`TensorGraded`/`TensorMixed`), numbers componentwise `x / s`; the two differ in the last bit. -/
class LinearFiber (F : Type) [FlatFiber F] where
  /-- Julia's `x / s` is `x * (1/s)` for this fiber type. -/
  recipDiv : Bool := false

/-! ## Building flat arrays -/

/-- `f (… (f init i) …) (i+k-1)`: a tail-recursive fold over the indices `i, …, i+k-1`. -/
@[specialize] def foldRange {β : Type} (f : β → Nat → β) : (k i : Nat) → β → β
  | 0, _, acc => acc
  | k + 1, i, acc => foldRange f k (i + 1) (f acc i)

/-- Append `f i, f (i+1), …, f (i+k-1)` (tail recursive, fuelled by `k`). -/
@[specialize] def buildLoop {F : Type} [FlatFiber F] (f : Nat → F) : (k i : Nat) → FloatArray → FloatArray
  | 0, _, a => a
  | k + 1, i, a => buildLoop f k (i + 1) (FlatFiber.push a (f i))

theorem size_buildLoop {F : Type} [FlatFiber F] (f : Nat → F) : ∀ (k i : Nat) (a : FloatArray),
    (buildLoop f k i a).size = a.size + k * FlatFiber.width F
  | 0, _, a => by simp [buildLoop]
  | k + 1, i, a => by
    rw [buildLoop, size_buildLoop f k (i + 1), FlatFiber.size_push, Nat.succ_mul]; omega

/-- Write `f i, f (i+1), …, f (i+k-1)` at the offsets `off, off + w, …` (tail recursive). -/
@[specialize] def fillLoop {F : Type} [FlatFiber F] (f : Nat → F) :
    (k i off : Nat) → FloatArray → FloatArray
  | 0, _, _, a => a
  | k + 1, i, off, a => fillLoop f k (i + 1) (off + FlatFiber.width F) (FlatFiber.write a off (f i))

@[simp] theorem size_fillLoop {F : Type} [FlatFiber F] (f : Nat → F) :
    ∀ (k i off : Nat) (a : FloatArray), (fillLoop f k i off a).size = a.size
  | 0, _, _, _ => rfl
  | k + 1, i, off, a => by rw [fillLoop, size_fillLoop f k (i + 1), FlatFiber.size_write]

/-- The flat encoding of `f 0, …, f (n-1)`, written into a zero buffer (`Cartan.Flat.zeros`,
`FlatFiber.write`): no `FloatArray.push`, an out-of-line call per float. -/
@[inline] def buildFlat {F : Type} [FlatFiber F] (n : Nat) (f : Nat → F) : FloatArray :=
  fillLoop f n 0 0 (Flat.zeros (FlatFiber.width F * n))

@[simp] theorem size_buildFlat {F : Type} [FlatFiber F] (n : Nat) (f : Nat → F) :
    (buildFlat n f).size = FlatFiber.width F * n := by
  rw [buildFlat, size_fillLoop, Flat.size_zeros]

/-- `Float` fibers: one float each. -/
instance instFlatFiberFloat : FlatFiber Float where
  width := 1
  read a i := a.get! i
  push a x := a.push x
  size_push a x := by simp
  write a off x := a.set! off x
  size_write a off x := FloatArray.size_set!' a off x

instance : LinearFiber Float := ⟨false⟩

/-- `ComplexF64` fibers: `(re, im)`, as Julia stores `Complex{Float64}`. -/
instance : FlatFiber (Complex Float) where
  width := 2
  read a i := ⟨a.get! i, a.get! (i + 1)⟩
  push a z := (a.push z.re).push z.im
  size_push a z := by simp
  write a off z := (a.set! off z.re).set! (off + 1) z.im
  size_write a off z := by simp

instance : LinearFiber (Complex Float) := ⟨false⟩

/-! ## Static vectors of flat elements -/

/-- Append the entries `i, i+1, …, i+k-1` of `v` (tail recursive, fuelled by `k`). -/
@[specialize] def pushValues {α : Type} [Packed α] [Inhabited α] [FlatFiber α] {n : Nat}
    (v : Values α n) : (k i : Nat) → FloatArray → FloatArray
  | 0, _, a => a
  | k + 1, i, a => pushValues v k (i + 1) (FlatFiber.push a (v.get! i))

theorem size_pushValues {α : Type} [Packed α] [Inhabited α] [FlatFiber α] {n : Nat}
    (v : Values α n) : ∀ (k i : Nat) (a : FloatArray),
      (pushValues v k i a).size = a.size + k * FlatFiber.width α
  | 0, _, a => by simp [pushValues]
  | k + 1, i, a => by
    rw [pushValues, size_pushValues v k (i + 1), FlatFiber.size_push, Nat.succ_mul]; omega

/-- Write the entries `j, …, j+k-1` of `v` at `off + j·w` (element width `w`). -/
@[specialize] def writeValues {α : Type} [Packed α] [Inhabited α] [FlatFiber α] {n : Nat}
    (v : Values α n) (off : Nat) : (k j : Nat) → FloatArray → FloatArray
  | 0, _, a => a
  | k + 1, j, a => writeValues v off k (j + 1) (FlatFiber.write a (off + j * FlatFiber.width α) (v.get! j))

@[simp] theorem size_writeValues {α : Type} [Packed α] [Inhabited α] [FlatFiber α] {n : Nat}
    (v : Values α n) (off : Nat) : ∀ (k j : Nat) (a : FloatArray),
      (writeValues v off k j a).size = a.size
  | 0, _, _ => rfl
  | k + 1, j, a => by rw [writeValues, size_writeValues v off k (j + 1), FlatFiber.size_write]

/-- Decode `n` consecutive flat elements starting at `off`. -/
@[inline] def readValues {α : Type} [Packed α] [FlatFiber α] (n : Nat) (a : FloatArray)
    (off : Nat) : Values α n :=
  let w := FlatFiber.width α
  Values.ofFn fun i => FlatFiber.read a (off + i.1 * w)

/-- `Values α n` of flat elements (Julia `Values{n,α}`). -/
instance {α : Type} [Packed α] [Inhabited α] [FlatFiber α] {n : Nat} : FlatFiber (Values α n) where
  width := n * FlatFiber.width α
  read a off := readValues n a off
  push a v := pushValues v n 0 a
  size_push a v := size_pushValues v n 0 a
  write a off v := writeValues v off n 0 a
  size_write a off v := size_writeValues v off n 0 a

/-- Static vectors divide entrywise (StaticVectors `v / s = map(c -> c/s)`), so as their entries do. -/
instance {α : Type} [Packed α] [Inhabited α] [FlatFiber α] [LinearFiber α] {n : Nat} :
    LinearFiber (Values α n) := ⟨LinearFiber.recipDiv α⟩

/-! ## Grassmann elements -/

section Grassmann

variable {V : TensorBundle} {G : Nat} {p : Bool} {α : Type} [Coeff α] [FlatFiber α]

/-- `Chain V G α` fibers: the `binomial(n, G)` coefficients in Julia's storage order. -/
instance : FlatFiber (Chain V G α) where
  width := Leibniz.binomial V.n G * FlatFiber.width α
  read a off := ⟨readValues _ a off⟩
  push a c := pushValues c.v _ 0 a
  size_push a c := size_pushValues c.v _ 0 a
  write a off c := writeValues c.v off (Leibniz.binomial V.n G) 0 a
  size_write a off c := size_writeValues c.v off (Leibniz.binomial V.n G) 0 a

instance [LinearFiber α] : LinearFiber (Chain V G α) := ⟨true⟩

/-- `Spinor`/`CoSpinor` fibers (`Half V p α`): the half-algebra coefficients. -/
instance : FlatFiber (Half V p α) where
  width := halfDim V.n p * FlatFiber.width α
  read a off := ⟨readValues _ a off⟩
  push a h := pushValues h.v _ 0 a
  size_push a h := size_pushValues h.v _ 0 a
  write a off h := writeValues h.v off (halfDim V.n p) 0 a
  size_write a off h := size_writeValues h.v off (halfDim V.n p) 0 a

instance [LinearFiber α] : LinearFiber (Half V p α) := ⟨true⟩

/-- `Multivector` fibers: all `2^n` coefficients. -/
instance : FlatFiber (Multivector V α) where
  width := 2 ^ V.n * FlatFiber.width α
  read a off := ⟨readValues _ a off⟩
  push a m := pushValues m.v _ 0 a
  size_push a m := size_pushValues m.v _ 0 a
  write a off m := writeValues m.v off (2 ^ V.n) 0 a
  size_write a off m := size_writeValues m.v off (2 ^ V.n) 0 a

instance [LinearFiber α] : LinearFiber (Multivector V α) := ⟨true⟩

end Grassmann

/-! ## Display -/

/-- Julia `show` of a fiber value, in a non-compact or a compact (`:compact => true`) context. -/
class ShowFiber (F : Type) where
  /-- Julia `sprint(show, x; context = :compact => compact)`. -/
  showFiber : (compact : Bool) → F → String

export ShowFiber (showFiber)

instance : ShowFiber Float := ⟨F64.showIO⟩

instance : ShowFiber (Complex Float) := ⟨fun c z => JuliaShow.showIO c z⟩

instance : ShowFiber Induced := ⟨fun _ _ => "InducedMetric()"⟩

instance {α : Type} [Packed α] [ShowFiber α] {n : Nat} : ShowFiber (Values α n) where
  showFiber c v := "[" ++ ", ".intercalate (v.toList.map (showFiber c)) ++ "]"

section GrassmannShow

variable {V : TensorBundle} {G : Nat} {p : Bool} {α : Type} [Coeff α] [JuliaShow α]

/-- Julia `show` of a list of terms: Leibniz `showvalue` for the first term, Grassmann
`showterm` for the rest (`src/multivectors.jl:46-58`); coefficients go through `compactio`
(6 significant digits) and the separators are ` + ` / `+` by the caller's `:compact` flag. -/
def showTerms (labels : UInt64 → String) (compact : Bool) (ts : List (UInt64 × α)) : String :=
  String.join <| ts.zipIdx.map fun ((b, x), i) =>
    (if i == 0 then JuliaShow.showValue true x else JuliaShow.showTerm compact true x) ++ labels b

/-- Julia `show(io, ::Chain)` (`src/multivectors.jl:109-116`): every term, zeros included. -/
def showChain (compact : Bool) (c : Chain V G α) : String :=
  showTerms (V.bladeLabel ·) compact (layoutTerms V (.chain G) c.v)

/-- Julia `show(io, ::Spinor)`/`show(io, ::CoSpinor)` (`src/multivectors.jl:589-615`). -/
def showHalf (compact : Bool) (h : Half V p α) : String :=
  let ts := layoutTerms V (halfLayout p) h.v
  if p then showTerms (V.bladeLabel ·) compact ts
  else match ts with
    | (_, s) :: rest => JuliaShow.printIO true s ++ String.join (rest.map fun (b, x) =>
        JuliaShow.showTerm compact true x ++ V.bladeLabel b)
    | [] => ""

/-- Julia `show(io, ::Multivector)` (`src/multivectors.jl:340-356`): the scalar, then the
nonzero terms; `0v⃖` when only the scalar is left. -/
def showMultivector (compact : Bool) (m : Multivector V α) : String :=
  let s := getD m.v 0
  let rest := (layoutTerms V .full m.v).drop 1 |>.filter (fun (_, x) => !Coeff.isZero x)
  if rest.isEmpty then JuliaShow.printIO true s ++ JuliaShow.showStar s ++ "v⃖"
  else JuliaShow.printIO true s ++ String.join (rest.map fun (b, x) =>
    JuliaShow.showTerm compact true x ++ V.bladeLabel b)

instance : ShowFiber (Chain V G α) := ⟨showChain⟩
instance : ShowFiber (Half V p α) := ⟨showHalf⟩
instance : ShowFiber (Multivector V α) := ⟨showMultivector⟩

end GrassmannShow

/-! ## Norms of fiber values -/

/-- Julia `norm(x)` of a fiber value, as a `Float` (`LinearAlgebra.norm`; for Grassmann elements
the Euclidean norm of the coefficients, `src/multivectors.jl`). `flat` records that the norm is
`√(x₀² + x₁² + …)` of the flat encoding, summed left to right (StaticVectors `norm`), so fields
can compute it on their raw arrays. -/
class FiberNorm (F : Type) where
  /-- Julia `norm(x)`. -/
  fnorm : F → Float
  /-- `fnorm` is the left-to-right Euclidean norm of the flat encoding. -/
  flat : Bool := false

export FiberNorm (fnorm)

instance : FiberNorm Float := ⟨Float.abs, false⟩
instance : FiberNorm (Complex Float) := ⟨ComplexF64.abs, false⟩

instance {X : Type} {V : TensorBundle} {α : Type} [Coeff α] [JNorm α] [DenseLayout X V α] :
    FiberNorm X := ⟨fun x => Grassmann.norm x, false⟩

/-- Grassmann elements over `Float`: `norm` is StaticVectors' `√(Σ xᵢ²)` of the coefficients. -/
instance (priority := high) {X : Type} {V : TensorBundle} [DenseLayout X V Float] : FiberNorm X :=
  ⟨fun x => Grassmann.norm x, true⟩

end Cartan
