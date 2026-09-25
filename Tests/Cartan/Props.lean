import Tests.Cartan.Common
import Tests.Util.Random

/-!
# Property tests of the Cartan core

Deterministic random fields (SplitMix64, `Tests.Util.Random`):

* the planned Grassmann field kernels (`Cartan.Kernel`) are bit-identical to the pointwise lift of
  the fiber operation, for products and linear maps between chains of every grade, spinors,
  co-spinors and multivectors, in Euclidean, Lorentzian and degenerate spaces;
* the flat linear operations (`+`, `-`, scaling, Julia's reciprocal division, scalar fields,
  norms) agree bit for bit with the fiber operations they replace;
* lazy range fields hold exactly `JuliaBase`'s range elements, before and after range arithmetic;
* grid neighbours through the gluing agree with MeshTopology's `NeighborTable`;
* the coordinate-function constructors, components, re-basing and casts are consistent.
-/

open Lean Tests.Small Cartan JuliaBase Grassmann MeshTopology

namespace Tests.CartanTests.Props

/-- Bitwise equality of float arrays (NaNs equal). -/
def bitsEq (a b : FloatArray) : Bool :=
  a.size == b.size && (List.range a.size).all fun i =>
    a[i]!.toBits == b[i]!.toBits || (a[i]!.isNaN && b[i]!.isNaN)

/-- `k` random floats in `[-2, 2)`, with exact zeros, negative zeros and small integers mixed in
(they exercise the signed-zero and exact paths). -/
def randFloats (seed k : Nat) : FloatArray := Id.run do
  let mut g := Rng.ofSeed seed
  let mut out := FloatArray.emptyWithCapacity k
  for _ in [0:k] do
    let (u, g1) := g.nat 10
    let (x, g2) := g1.floatIn (-2) 2
    g := g2
    out := out.push (if u == 0 then 0 else if u == 1 then -0.0 else if u == 2 then Float.ofNat (x.abs.toUInt64.toNat) else x)
  return out

/-- A random field over `m`. -/
def randField {M F : Type} [FrameBundle M] [FlatFiber F] (m : M) (seed : Nat) : TensorField m F :=
  (TensorField.ofFlat? m (randFloats seed (FlatFiber.width F * card m))).get!

/-- The test grid (7 × 5 points). -/
def g : GridBundle 2 (AffinePoint 2) := .ofSpace (.ofAxes #v[Axis.colon 0 0.5 3, Axis.linRange (-1) 1 5])

/-- Compare two fields bit for bit. -/
def same {M F : Type} [FrameBundle M] [FlatFiber F] {m : M} (label : String)
    (a b : TensorField m F) : TestM Unit :=
  check label (bitsEq a.data b.data) fun _ => "fields differ"

/-- Planned products against the pointwise lift in `V`, for chains of grades `G`, `H`. -/
def productsChain (V : TensorBundle) (G H : Nat) (seed : Nat) : TestM Unit := do
  let a : TensorField g (Chain V G Float) := randField g seed
  let b : TensorField g (Chain V H Float) := randField g (seed + 1)
  let l := s!"{repr V.n} {G}×{H}"
  same s!"planned * {l}" (a * b) (TensorField.zipWith HMul.hMul a b)
  same s!"planned ∧ {l}" (a ∧ b) (TensorField.zipWith wedge a b)
  same s!"planned ∨ {l}" (a ∨ b) (TensorField.zipWith vee a b)
  same s!"planned ⋅ {l}" (a ⋅ b) (TensorField.zipWith contraction a b)
  same s!"planned ⋆ {l}" (⋆a) (TensorField.map hodge a)
  same s!"planned ! {l}" (complementRight a) (TensorField.map complementRight a)
  same s!"planned complementleft {l}" (complementLeft b) (TensorField.map complementLeft b)
  same s!"planned ~ {l}" (~a) (TensorField.map (~ ·) a)
  same s!"planned involute {l}" (involute b) (TensorField.map involute b)
  same s!"planned clifford {l}" (clifford a) (TensorField.map clifford a)

/-- Planned products of halves and multivectors against the pointwise lift. -/
def productsMixed (V : TensorBundle) (seed : Nat) : TestM Unit := do
  let s : TensorField g (Spinor V Float) := randField g seed
  let c : TensorField g (CoSpinor V Float) := randField g (seed + 1)
  let v : TensorField g (Chain V 1 Float) := randField g (seed + 2)
  let m : TensorField g (Multivector V Float) := randField g (seed + 3)
  let l := s!"{repr V.n}"
  same s!"planned spinor*spinor {l}" (s * s) (TensorField.zipWith HMul.hMul s s)
  same s!"planned spinor*cospinor {l}" (s * c) (TensorField.zipWith HMul.hMul s c)
  same s!"planned vector*spinor {l}" (v * s) (TensorField.zipWith HMul.hMul v s)
  same s!"planned cospinor*vector {l}" (c * v) (TensorField.zipWith HMul.hMul c v)
  same s!"planned spinor∧vector {l}" (s ∧ v) (TensorField.zipWith wedge s v)
  same s!"planned spinor⋅vector {l}" (s ⋅ v) (TensorField.zipWith contraction s v)
  same s!"planned multi*multi {l}" (m * m) (TensorField.zipWith HMul.hMul m m)
  same s!"planned multi∧vector {l}" (m ∧ v) (TensorField.zipWith wedge m v)
  same s!"planned vector⋅multi {l}" (v ⋅ m) (TensorField.zipWith contraction v m)
  same s!"planned ⋆spinor {l}" (⋆s) (TensorField.map hodge s)
  same s!"planned ⋆multi {l}" (⋆m) (TensorField.map hodge m)
  same s!"planned ~multi {l}" (~m) (TensorField.map (~ ·) m)
  same s!"planned clifford cospinor {l}" (clifford c) (TensorField.map clifford c)

/-- The flat linear operations against the fiber operations. -/
def linear (seed : Nat) : TestM Unit := do
  let a : TensorField g (Chain ℝ3 1 Float) := randField g seed
  let b : TensorField g (Chain ℝ3 1 Float) := randField g (seed + 1)
  let s : TensorField g Float := randField g (seed + 2)
  let x : Float := 2.5
  same "flat +" (a + b) (TensorField.zipWith (· + ·) a b)
  same "flat -" (a - b) (TensorField.zipWith (· - ·) a b)
  same "flat neg" (-a) (TensorField.map (- ·) a)
  same "flat scale" (x * a) (TensorField.map (x * ·) a)
  same "flat scale right" (a * x) (TensorField.map (· * x) a)
  same "reciprocal division" (a / (3 : Float)) (TensorField.map (· * ((1 : Float) / 3)) a)
  same "scalar field times chain" (s * a) (TensorField.zipWith HMul.hMul s a)
  same "chain times scalar field" (a * s) (TensorField.zipWith HMul.hMul a s)
  same "chain over scalar field" (a / s) (TensorField.zipWith (fun c y => c * ((1 : Float) / y)) a s)
  same "flat norm" a.norm (TensorField.map (fun c => Grassmann.norm c) a)
  same "unit" a.unit (TensorField.map (fun c => c * ((1 : Float) / Grassmann.norm c)) a)
  same "scalar division stays componentwise" (s / (3 : Float)) (TensorField.map (· / 3) s)
  same "scalar fields over scalar fields" (s / s) (TensorField.zipWith (· / ·) s s)

/-- Lazy range fields hold `JuliaBase`'s range elements. -/
def ranges (seed : Nat) : TestM Unit := do
  let mut rng := Rng.ofSeed seed
  for k in [0:40] do
    let (a, r1) := rng.floatIn (-5) 5
    let (st, r2) := r1.floatIn 0.01 1
    let (len, r3) := r2.nat 60
    let (x, r4) := r3.floatIn (-3) 3
    rng := r4
    let stop := a + st * Float.ofNat len
    let jr := JuliaBase.colon a st stop
    let ax := Axis.stepLen jr
    let t := TensorField.ofAxis ax
    check s!"range {k} elements" (bitsEq t.data jr.toFloatArray)
    match ax.scale x with
    | some (.stepLen r') =>
      check s!"range {k} x .* r" (bitsEq ((x * t).data) r'.toFloatArray)
    | _ => check s!"range {k} x .* r" false
    let lr := JuliaBase.LinRange.mk' a stop (len + 2)
    check s!"linrange {k} elements" (bitsEq (TensorField.ofAxis (.lin lr)).data lr.toFloatArray)

/-- Grid neighbours through the gluing against MeshTopology's precomputed table. -/
def neighbors : TestM Unit := do
  let base := GridBundle.ofSpace (.ofAxes #v[Axis.linRange 0 1 5, Axis.linRange 0 1 7])
  let bs : List (String × GridBundle 2 (AffinePoint 2)) :=
    [("open", base), ("torus", base.torus), ("mobius", base.mobius), ("sphere", base.sphere),
     ("klein", base.klein), ("cone", base.cone), ("geographic", base.geographic)]
  for (name, b) in bs do
    let tbl := b.top.neighborTable
    let ok := (List.range (card b)).all fun k =>
      (List.finRange 2).all fun a =>
        [false, true].all fun up =>
          let mine := b.neighbor (if up then 1 else -1) a (b.cartesian k)
          let theirs := if h : k < tbl.len then tbl.get a ⟨k, h⟩ up else 0
          match mine with
          | some l => theirs == l + 1
          | none => theirs == 0
    check s!"neighbors {name}" ok

/-- Constructors, components and casts. -/
def misc : TestM Unit := do
  let f (x y : Float) : Float := x * x - 3 * y
  same "tabulate2 = tabulatePoint" (TensorField.tabulate2 g f)
    (TensorField.tabulatePoint g fun p => f (p.get! 0) (p.get! 1))
  let a : TensorField g (Chain ℝ3 1 Float) := randField g 77
  let back := TensorField.chainOf ℝ3 1 fun j => a.component j.1
  same "chainOf ∘ component" back a
  check "split size" (a.split.size == 3)
  let g' : GridBundle 2 (AffinePoint 2) := .ofSpace (.ofAxes #v[Axis.colon 0 0.5 3, Axis.linRange (-1) 1 5])
  check "cast? to an equal base" ((a.cast? g').isSome)
  let g'' : GridBundle 2 (AffinePoint 2) := .ofSpace (.ofAxes #v[Axis.colon 0 0.5 3, Axis.linRange (-1) 2 5])
  check "cast? to another base" ((a.cast? g'').isNone)
  check "rebase? to a smaller base" ((a.rebase? (GridBundle.ofAxis (Axis.oneTo 3))).isNone)
  let s : TensorField g Float := randField g 78
  same "iszero is 0/1" s.iszero (s.map fun x => if x == 0 then 1 else 0)
  check "graph width" ((a.graph.get 3).v.toList.length == 5)
  let tf := (TensorField.ofAxis (Axis.colon 0 0.1 1))
  check "range tag of the identity field" tf.range?.isSome
  check "range tag dropped by t + 1" ((tf + (1 : Float)).range?.isNone)
  check "range tag kept by t + t" ((tf + tf).range?.isSome)

/-- `supnorm`/`infnorm` (one root after the extremum of the squared norms) against the
extremum of the norms field (a root per point), for a field of width `w`, with and without a
`NaN` fiber. -/
def extrema {F : Type} [FlatFiber F] [FiberNorm F] (label : String) (t : TensorField g F) :
    TestM Unit := do
  let ext (isMax : Bool) (u : TensorField g F) : Float :=
    u.norm.data.foldl (fun acc x => Flat.extStep isMax acc x)
      (if isMax then Float.ofBits 0xFFF0000000000000 else Float.ofBits 0x7FF0000000000000)
  let same (l : String) (x y : Float) : TestM Unit :=
    check l (x.toBits == y.toBits || (x.isNaN && y.isNaN)) fun _ => s!"{x} vs {y}"
  same s!"supnorm {label}" t.supnorm (ext true t)
  same s!"infnorm {label}" t.infnorm (ext false t)
  let tn := (TensorField.ofFlat? g (t.data.set! 7 ((0 : Float) / 0))).get!
  same s!"supnorm {label} with NaN" tn.supnorm (ext true tn)
  same s!"infnorm {label} with NaN" tn.infnorm (ext false tn)

/-- Run the property tests. -/
def run : TestM Unit := do
  extrema "Float" (randField (F := Float) g 800)
  extrema "ℝ2 vector" (randField (F := Chain ℝ2 1 Float) g 801)
  extrema "ℝ3 vector" (randField (F := Chain ℝ3 1 Float) g 802)
  extrema "ℝ2 multivector" (randField (F := Multivector ℝ2 Float) g 803)
  extrema "ℝ5 vector" (randField (F := Chain ℝ5 1 Float) g 804)
  for (G, H) in [(0, 1), (1, 1), (1, 2), (2, 1), (2, 2), (3, 1), (1, 3), (2, 3)] do
    productsChain ℝ3 G H (100 + 10 * G + H)
    productsChain ℝ4 G H (200 + 10 * G + H)
    productsChain STA G H (300 + 10 * G + H)
    productsChain PGA3 G H (400 + 10 * G + H)
  productsMixed ℝ3 500
  productsMixed ℝ4 510
  productsMixed STA 520
  productsMixed PGA3 530
  for k in [0:5] do linear (600 + 10 * k)
  ranges 700
  neighbors
  misc

end Tests.CartanTests.Props
