import Cartan.Props

/-!
# Operator-, couple- and phasor-valued fields

Julia's field kinds with algebraic fibers other than elements (Cartan.jl `src/Cartan.jl:136-142`):

| Julia alias | fiber | Lean fiber |
|---|---|---|
| `EndomorphismField` | `Endomorphism{V}` (`TensorOperator`) | `TensorOperator V ld W lc Float` |
| `DiagonalField` | `DiagonalOperator` | `DiagonalOperator V l Float` |
| `OutermorphismField` | `Outermorphism` | `Outermorphism V W Float` |
| `ComplexMap` | `Complex`, `Couple` | `Complex Float`, `Couple V Float`, `PseudoCouple V Float` |
| `PhasorField` | `Phasor` | `Phasor V Float` |
| (terms) | `Single` | `Single V G Float` |

**Encodings.** An operator is its column-major matrix (Julia's `TensorOperator(Chain(c₁, …))`
flattened column after column); a diagonal operator its diagonal; an outermorphism its compound
blocks `Λ¹F, …, Λᵏ F` one after the other (`k = min(dim V, dim W)`, each `C(m,g) × C(n,g)`
column-major). These are linear (`LinearFiber`), so fields of them add and scale on the flat
arrays, dividing by a real as Grassmann does (`x * (1/s)`).

A `Couple`, `PseudoCouple`, `Single` or `Phasor` carries its blade as data (Julia: the type
parameter `B`); the flat encoding stores the blade mask as the float `UInt64.toFloat bits`
(exact: masks are below `2⁵³`) in front of the coefficients. These fibers are not linear on
their encodings (the blade is not a coefficient), so their arithmetic goes through the generic
pointwise lifts. Float bit casts are opaque to Lean's logic, so the read-back law
(`LawfulFlatFiber`) is proved for the operator encodings only; the blade encodings are checked
by the oracle tests.

**Operations** (Julia `Cartan.jl:401-449`, each `TensorField(base(t), f.(fiber(t)))`): `det`,
`tr`, `transpose`, `inv`, `DiagonalOperator`, `outermorphism`, the complex spectrum
`eigvalscomplex`; `polarize`, `complexify`, `vectorize`, `radius`, `angle`,
`realvalue`, `imagvalue`, `amplitude` of couples, phasors and complex fields; and
`metricextensorfield`/`metrictensorfield` of grids and simplex bundles (`Cartan.jl:210-213`).

Julia returns `det`/`tr` of an operator as a grade-0 `Chain` (printed `2.0v`); here they are
scalar fields (the same value).
-/

namespace Cartan

open Grassmann DirectSum StaticVectors AbstractTensors JuliaBase Grassmann.Forms

/-! ## Operator fibers -/

section Operators

variable {V W : TensorBundle} {ld lc l : Layout}

/-- `TensorOperator` fibers: the `rows × cols` column-major entries. -/
instance : FlatFiber (TensorOperator V ld W lc Float) where
  width := FlatFiber.width (Values Float (lc.size W.n * ld.size V.n))
  read a off := ⟨⟨FlatFiber.read a off⟩⟩
  push a T := FlatFiber.push a T.mat.v
  size_push a T := FlatFiber.size_push a T.mat.v
  write a off T := FlatFiber.write a off T.mat.v
  size_write a off T := FlatFiber.size_write a off T.mat.v

instance : LinearFiber (TensorOperator V ld W lc Float) := ⟨true⟩

instance : LawfulFlatFiber (TensorOperator V ld W lc Float) where
  read_push_self a T := by
    show (⟨⟨FlatFiber.read (FlatFiber.push a T.mat.v) a.size⟩⟩ : TensorOperator V ld W lc Float) = T
    rw [LawfulFlatFiber.read_push_self]
  read_push_lt a T off h := by
    show (⟨⟨FlatFiber.read (FlatFiber.push a T.mat.v) off⟩⟩ : TensorOperator V ld W lc Float) =
      ⟨⟨FlatFiber.read a off⟩⟩
    rw [LawfulFlatFiber.read_push_lt a T.mat.v off h]
  read_write_self a off T h := by
    show (⟨⟨FlatFiber.read (FlatFiber.write a off T.mat.v) off⟩⟩ : TensorOperator V ld W lc Float) = T
    rw [LawfulFlatFiber.read_write_self a off T.mat.v h]
  read_write_other a off off' T h := by
    show (⟨⟨FlatFiber.read (FlatFiber.write a off T.mat.v) off'⟩⟩ : TensorOperator V ld W lc Float) =
      ⟨⟨FlatFiber.read a off'⟩⟩
    rw [LawfulFlatFiber.read_write_other a off off' T.mat.v h]

instance : ShowFiber (TensorOperator V ld W lc Float) := ⟨fun _ T => toString T⟩

/-- Julia `norm(T)` of an operator fiber: the Euclidean norm of its entries (Grassmann's `norm`
of the nested chain, `√(Σ |cⱼ|²)` over the columns). -/
instance : FiberNorm (TensorOperator V ld W lc Float) := ⟨fun T => T.mat.v.norm, true⟩

/-- `DiagonalOperator` fibers: the diagonal. -/
instance : FlatFiber (DiagonalOperator V l Float) where
  width := FlatFiber.width (Values Float (l.size V.n))
  read a off := ⟨FlatFiber.read a off⟩
  push a D := FlatFiber.push a D.d
  size_push a D := FlatFiber.size_push a D.d
  write a off D := FlatFiber.write a off D.d
  size_write a off D := FlatFiber.size_write a off D.d

instance : LinearFiber (DiagonalOperator V l Float) := ⟨true⟩

instance : LawfulFlatFiber (DiagonalOperator V l Float) where
  read_push_self a D := by
    show (⟨FlatFiber.read (FlatFiber.push a D.d) a.size⟩ : DiagonalOperator V l Float) = D
    rw [LawfulFlatFiber.read_push_self]
  read_push_lt a D off h := by
    show (⟨FlatFiber.read (FlatFiber.push a D.d) off⟩ : DiagonalOperator V l Float) =
      ⟨FlatFiber.read a off⟩
    rw [LawfulFlatFiber.read_push_lt a D.d off h]
  read_write_self a off D h := by
    show (⟨FlatFiber.read (FlatFiber.write a off D.d) off⟩ : DiagonalOperator V l Float) = D
    rw [LawfulFlatFiber.read_write_self a off D.d h]
  read_write_other a off off' D h := by
    show (⟨FlatFiber.read (FlatFiber.write a off D.d) off'⟩ : DiagonalOperator V l Float) =
      ⟨FlatFiber.read a off'⟩
    rw [LawfulFlatFiber.read_write_other a off off' D.d h]

instance : ShowFiber (DiagonalOperator V l Float) := ⟨fun _ D => toString D⟩

/-- The number of floats of the compound blocks `1 … k` of maps `V → W`
(`Σ_{g=1}^{k} C(dim W, g) · C(dim V, g)`, `k = min(dim V, dim W)`). -/
def outerWidth (V W : TensorBundle) : Nat :=
  (List.range (min V.n W.n)).foldl
    (fun acc g => acc + Leibniz.binomial W.n (g + 1) * Leibniz.binomial V.n (g + 1)) 0

/-- Push the blocks `g + 1, …, k` of an outermorphism (each at its static shape: a block of
another shape is written as zeros). -/
def pushOuterBlocks (O : Outermorphism V W Float) : (r g : Nat) → FloatArray → FloatArray
  | 0, _, a => a
  | r + 1, g, a =>
    let rows := Leibniz.binomial W.n (g + 1)
    let cols := Leibniz.binomial V.n (g + 1)
    let blk : Mat rows cols Float := match O.blocks[g]? with
      | some b => b.toMat rows cols
      | none => Mat.zero
    pushOuterBlocks O r (g + 1) (FlatFiber.push a blk.v)

theorem size_pushOuterBlocks (O : Outermorphism V W Float) : ∀ (r g : Nat) (a : FloatArray),
    (pushOuterBlocks O r g a).size =
      a.size + (List.range r).foldl
        (fun acc i => acc + Leibniz.binomial W.n (g + i + 1) * Leibniz.binomial V.n (g + i + 1)) 0
  | 0, _, a => by simp [pushOuterBlocks]
  | r + 1, g, a => by
    rw [pushOuterBlocks, size_pushOuterBlocks O r (g + 1), FlatFiber.size_push]
    simp only [FlatFiber.width, Nat.mul_one]
    rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    simp only [Nat.zero_add, Nat.add_zero]
    have : ∀ (l : List Nat) (c : Nat), l.foldl (fun acc i =>
        acc + Leibniz.binomial W.n (g + 1 + i + 1) * Leibniz.binomial V.n (g + 1 + i + 1)) c =
        c + l.foldl (fun acc i =>
        acc + Leibniz.binomial W.n (g + 1 + i + 1) * Leibniz.binomial V.n (g + 1 + i + 1)) 0 := by
      intro l; induction l with
      | nil => intro c; simp
      | cons x xs ih => intro c; simp only [List.foldl_cons]; rw [ih, ih (0 + _)]; omega
    have e : ∀ i, g + (i + 1) + 1 = g + 1 + i + 1 := fun i => by omega
    simp only [e]
    rw [this _ (Leibniz.binomial W.n (g + 1) * Leibniz.binomial V.n (g + 1))]
    omega

/-- Read the blocks `g + 1, …, g + r` from offset `off`. -/
def readOuterBlocks (a : FloatArray) : (r g off : Nat) → Array (DMat Float) → Array (DMat Float)
  | 0, _, _, acc => acc
  | r + 1, g, off, acc =>
    let rows := Leibniz.binomial W.n (g + 1)
    let cols := Leibniz.binomial V.n (g + 1)
    let blk : Mat rows cols Float := ⟨FlatFiber.read a off⟩
    readOuterBlocks a r (g + 1) (off + rows * cols) (acc.push (DMat.ofMat blk))

/-- `Outermorphism` fibers: the compound blocks one after the other (see the module note). -/
instance : FlatFiber (Outermorphism V W Float) where
  width := outerWidth V W
  read a off := ⟨readOuterBlocks (V := V) (W := W) a (min V.n W.n) 0 off #[]⟩
  push a O := pushOuterBlocks O (min V.n W.n) 0 a
  size_push a O := by
    rw [size_pushOuterBlocks]; simp only [Nat.zero_add]; rfl

instance : LinearFiber (Outermorphism V W Float) := ⟨true⟩

instance : ShowFiber (Outermorphism V W Float) := ⟨fun _ O => toString O⟩

end Operators

/-! ## Couples, phasors, terms -/

section Couples

variable {V : TensorBundle} {G : Nat}

/-- A blade mask as a float (exact below `2⁵³`). -/
@[inline] def bitsToFloat (b : UInt64) : Float := b.toFloat

/-- A blade mask back from its float. -/
@[inline] def floatToBits (x : Float) : UInt64 := x.toUInt64

/-- `Couple` fibers: `(blade, re, im)`. -/
instance : FlatFiber (Couple V Float) where
  width := 3
  read a off := ⟨floatToBits (a.get! off), a.get! (off + 1), a.get! (off + 2)⟩
  push a z := ((a.push (bitsToFloat z.bits)).push z.re).push z.im
  size_push a z := by simp
  write a off z := ((a.set! off (bitsToFloat z.bits)).set! (off + 1) z.re).set! (off + 2) z.im
  size_write a off z := by simp

/-- `PseudoCouple` fibers: `(blade, re, im)`. -/
instance : FlatFiber (PseudoCouple V Float) where
  width := 3
  read a off := ⟨floatToBits (a.get! off), a.get! (off + 1), a.get! (off + 2)⟩
  push a z := ((a.push (bitsToFloat z.bits)).push z.re).push z.im
  size_push a z := by simp
  write a off z := ((a.set! off (bitsToFloat z.bits)).set! (off + 1) z.re).set! (off + 2) z.im
  size_write a off z := by simp

/-- `Phasor` fibers: `(amplitude, blade, re, im)` of the angle couple. -/
instance : FlatFiber (Phasor V Float) where
  width := 4
  read a off := ⟨a.get! off, ⟨floatToBits (a.get! (off + 1)), a.get! (off + 2), a.get! (off + 3)⟩⟩
  push a z := (((a.push z.amp).push (bitsToFloat z.angle.bits)).push z.angle.re).push z.angle.im
  size_push a z := by simp
  write a off z := (((a.set! off z.amp).set! (off + 1) (bitsToFloat z.angle.bits)).set! (off + 2)
    z.angle.re).set! (off + 3) z.angle.im
  size_write a off z := by simp

/-- `Single` fibers: `(blade, value)`. -/
instance : FlatFiber (Single V G Float) where
  width := 2
  read a off := ⟨floatToBits (a.get! off), a.get! (off + 1)⟩
  push a s := (a.push (bitsToFloat s.bits)).push s.val
  size_push a s := by simp
  write a off s := (a.set! off (bitsToFloat s.bits)).set! (off + 1) s.val
  size_write a off s := by simp

instance : ShowFiber (Couple V Float) := ⟨fun _ z => toString z⟩
instance : ShowFiber (PseudoCouple V Float) := ⟨fun _ z => toString z⟩
instance : ShowFiber (Phasor V Float) := ⟨fun _ z => toString z⟩
instance : ShowFiber (Single V G Float) := ⟨fun _ s => toString s⟩

/-- Julia `norm(z::Couple)`: `√(re² + im²)` of the coefficients. -/
instance : FiberNorm (Couple V Float) := ⟨fun z => Float.sqrt (z.re * z.re + z.im * z.im), false⟩

/-- Julia `norm(t::Single) = abs(value(t))`. -/
instance : FiberNorm (Single V G Float) := ⟨fun s => s.val.abs, false⟩

end Couples

/-! ## Field operations -/

namespace TensorField

variable {M : Type} [FrameBundle M] {m : M} {V W : TensorBundle} {l : Layout}

/-- Julia `det(t)` of an endomorphism field (`Cartan.jl:449`). -/
def det (t : TensorField m (Endomorphism V (.chain 1) Float)) : TensorField m Float :=
  t.map fun T => TensorOperator.det (V := V) (W := V) T

/-- Julia `tr(t)` of an operator field (`Cartan.jl:448`). -/
def tr {ld : Layout} (t : TensorField m (TensorOperator V ld V ld Float)) : TensorField m Float :=
  t.map TensorOperator.tr

/-- Julia `transpose(t)` of an operator field (`Cartan.jl:399`). -/
def transpose {ld lc : Layout} (t : TensorField m (TensorOperator V ld W lc Float)) :
    TensorField m (TensorOperator W lc V ld Float) := t.map TensorOperator.transpose

/-- Julia `inv(t)` of a grade-1 endomorphism field (`Cartan.jl:400`, Grassmann's Cramer inverse
`inv(::Simplex)`). -/
def invOp (t : TensorField m (Endomorphism V (.chain 1) Float)) :
    TensorField m (Endomorphism V (.chain 1) Float) := t.map fun T => TensorOperator.inv (V := V) (W := V) T

/-- Julia `DiagonalOperator(t)` of an endomorphism field: the diagonals (`Cartan.jl:401`). -/
def diagonal (t : TensorField m (Endomorphism V l Float)) : TensorField m (DiagonalOperator V l Float) :=
  t.map DiagonalOperator.ofEndomorphism

/-- Julia `outermorphism(t)` of a grade-1 operator field (`Cartan.jl:401`). -/
def outermorphism (t : TensorField m (Simplex V W Float)) : TensorField m (Outermorphism V W Float) :=
  t.map TensorOperator.outermorphism

/-- Julia `TensorOperator(t)` of a diagonal field (`Cartan.jl:401`). -/
def ofDiagonal (t : TensorField m (DiagonalOperator V l Float)) :
    TensorField m (Endomorphism V l Float) := t.map DiagonalOperator.toOperator

/-- Julia `det(t)` of a diagonal field (grade-1 diagonal: the product of the entries). -/
def detDiag (t : TensorField m (DiagonalMorphism V Float)) : TensorField m Float :=
  t.map DiagonalMorphism.det

/-- Julia `tr(t)` of a diagonal field. -/
def trDiag (t : TensorField m (DiagonalOperator V l Float)) : TensorField m Float :=
  t.map DiagonalOperator.tr

/-- Julia `det(t)` of an outermorphism field (its top compound). -/
def detOuter (t : TensorField m (Outermorphism V W Float)) : TensorField m Float :=
  t.map Outermorphism.det

/-- Julia `tr(t)` of an outermorphism field (`Σ_g tr Λᵍ`, grade 0 included). -/
def trOuter (t : TensorField m (Outermorphism V V Float)) : TensorField m Float :=
  t.map Outermorphism.tr

/-- Julia `eigvals(t)` of a grade-1 endomorphism field, as complex numbers (Julia returns a real
or complex `Chain` per point; `Forms.Spectral.eigvalscomplex`). -/
def eigvalscomplex (t : TensorField m (Endomorphism V (.chain 1) Float)) :
    TensorField m (Chain V 1 (Complex Float)) :=
  t.map fun X => ⟨(TensorOperator.eigvalscomplex X).cast (by simp [Layout.size, Leibniz.choose])⟩


/-! ### Couples and phasors -/

/-- Julia `polarize(t)` of a couple field (`Cartan.jl:404`). -/
def polarize (t : TensorField m (Couple V Float)) : TensorField m (Phasor V Float) :=
  t.map Couple.polarize

/-- Julia `complexify(t)` of a phasor field (`Cartan.jl:404`). -/
def complexify (t : TensorField m (Phasor V Float)) : TensorField m (Couple V Float) :=
  t.map Phasor.complexify

/-- Julia `vectorize(t)` of a couple field: the plane coordinates `(re, im)` (`Cartan.jl:401`). -/
def vectorize (t : TensorField m (Couple V Float)) : TensorField m (Chain ℝ2 1 Float) :=
  t.map fun z => Chain.ofFn fun i => if i.1 = 0 then z.re else z.im

/-- Julia `vectorize(t)` of a complex field (`ComplexMap`): `Chain(re, im)`. -/
def vectorizeC (t : TensorField m (Complex Float)) : TensorField m (Chain ℝ2 1 Float) :=
  t.map fun z => Chain.ofFn fun i => if i.1 = 0 then z.re else z.im

/-- Julia `radius(t)` of a couple field. -/
def radius (t : TensorField m (Couple V Float)) : TensorField m Float := t.map Couple.radius

/-- Julia `angle(t)` of a couple field: the angle `θ·B` as a `Single` field. -/
def angleC (t : TensorField m (Couple V Float)) : TensorField m (Single V 2 Float) :=
  t.map fun z => ⟨z.bits, z.angleCoef⟩

/-- Julia `realvalue(t)` of a couple field. -/
def realvalue (t : TensorField m (Couple V Float)) : TensorField m Float := t.map (·.re)

/-- Julia `imagvalue(t)` of a couple field. -/
def imagvalue (t : TensorField m (Couple V Float)) : TensorField m Float := t.map (·.im)

/-- Julia `amplitude(t)` of a phasor field. -/
def amplitude (t : TensorField m (Phasor V Float)) : TensorField m Float := t.map (·.amp)

end TensorField

/-! ## Metric fields (`Cartan.jl:210-213`) -/

/-- Julia `submetric` (`fiber.jl:152-155`): the grade-1 part of a metric extensor. -/
class SubMetric (G : Type) (G' : outParam Type) where
  /-- Julia `submetric(g)`. -/
  submetric : G → G'

instance {V : TensorBundle} : SubMetric (DiagonalOperator V .full Float) (DiagonalMorphism V Float) :=
  ⟨fun D => ⟨Forms.gradeBlock V.n .full D.d 1 |>.cast (by simp [Layout.size, Leibniz.choose])⟩⟩

instance {V : TensorBundle} : SubMetric (DiagonalMorphism V Float) (DiagonalMorphism V Float) := ⟨id⟩

instance {V W : TensorBundle} :
    SubMetric (Outermorphism V W Float) (TensorOperator V (.chain 1) W (.chain 1) Float) :=
  ⟨fun O => O.block 1⟩

instance {V : TensorBundle} {l : Layout} :
    SubMetric (TensorOperator V l V l Float) (TensorOperator V l V l Float) := ⟨id⟩

namespace GridBundle

variable {N : Nat} {P G : Type}

/-- The same grid with the induced metric (Julia `GridBundle(PointArray(0, points(t)),
immersion(t))`). -/
def induced (b : GridBundle N P G) : GridBundle N P := ⟨b.space, b.top, .induced, 0, b.size_top⟩

/-- Julia `metricextensorfield(t)` (`Cartan.jl:210`): the metric of every point as a field over
the grid with the induced metric. -/
def metricextensorfield [FlatFiber G] [Inhabited G] (b : GridBundle N P G) :
    TensorField b.induced G := TensorField.ofFn b.induced b.metric.get

/-- Julia `metrictensorfield(t)` (`Cartan.jl:211`): the grade-1 metrics (`submetric`). -/
def metrictensorfield {G' : Type} [FlatFiber G'] [Inhabited G] [SubMetric G G'] (b : GridBundle N P G) :
    TensorField b.induced G' := TensorField.ofFn b.induced fun i => SubMetric.submetric (b.metric.get i)

end GridBundle

namespace SimplexBundle

variable {n : Nat} {P G : Type}

/-- The same mesh with the induced metric (Julia `SimplexBundle(PointCloud(0, points(t)),
immersion(t))`). -/
def induced (b : SimplexBundle n P G) : SimplexBundle n P := ⟨⟨b.cloud.points, .induced, 0⟩, b.top⟩

/-- Julia `metricextensorfield(t)` of a simplex bundle (`Cartan.jl:212`): the metric of every
vertex. -/
def metricextensorfield [FlatFiber G] [Inhabited G] (b : SimplexBundle n P G) :
    TensorField b.induced G := TensorField.ofFn b.induced fun i => b.cloud.metric.get (b.image i - 1)

/-- Julia `metrictensorfield(t)` of a simplex bundle (`Cartan.jl:213`). -/
def metrictensorfield {G' : Type} [FlatFiber G'] [Inhabited G] [SubMetric G G'] (b : SimplexBundle n P G) :
    TensorField b.induced G' :=
  TensorField.ofFn b.induced fun i => SubMetric.submetric (b.cloud.metric.get (b.image i - 1))

end SimplexBundle

end Cartan
