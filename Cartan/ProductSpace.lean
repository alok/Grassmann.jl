import Cartan.Axis

/-!
# `ProductSpace`: lazy Cartesian grids

Julia `ProductSpace{V,T,N}` (Cartan.jl `src/topology.jl:22-185`) is the lazy `N`-dimensional array
of the points of a tensor-product grid: `p[i₁,…,i_N] = Chain{V,1}(v[1][i₁], …, v[N][i_N])` for
1-D coordinate vectors `v` (usually ranges). Nothing is materialized; points are computed on
demand. Arrays are column-major (axis 1 fastest), as everywhere in Cartan.

The point type is `AffinePoint N`, Julia's `Chain{affinemanifold(N),1,Float64,N}`: the default
`V` of a `ProductSpace` is `affinemanifold(N) = Submanifold(N+2)(2:N+1…)` (`topology.jl:24`), so a
point prints `x v₂ + y v₃` while user `Chain(x, y)` fibers print `x v₁ + y v₂`. `AffinePoint`
keeps that distinction in the type; `toChain` gives the point as a Euclidean `Chain` for
Grassmann algebra.
-/

namespace Cartan

open Grassmann DirectSum StaticVectors AbstractTensors JuliaBase

/-! ## Affine points -/

/-- A point of an `N`-dimensional `ProductSpace` (Julia `Chain{affinemanifold(N),1,Float64,N}`,
`topology.jl:24, 77`): `N` coordinates, printed with the basis `v₂ … v_{N+1}`. -/
structure AffinePoint (N : Nat) where
  /-- The coordinates, axis 1 first. -/
  coords : Values Float N
  deriving BEq, Inhabited

namespace AffinePoint

variable {N : Nat}

/-- Build from the coordinates. -/
@[inline] def ofFn (f : Fin N → Float) : AffinePoint N := ⟨Values.ofFn f⟩

/-- Coordinate `i` (0-based; Julia `p[i+1]`). -/
instance : GetElem (AffinePoint N) Nat Float (fun _ i => i < N) where
  getElem p i h := p.coords.get ⟨i, h⟩

/-- Coordinate `i` (0-based), `0.0` out of range. -/
@[inline] def get! (p : AffinePoint N) (i : Nat) : Float := p.coords.get! i

/-- The point as a vector of the Euclidean algebra on `N` generators (Julia `Chain(value(p)...)`,
basis `v₁ … v_N`). -/
@[inline] def toChain (p : AffinePoint N) : Chain (TensorBundle.euclidean N) 1 Float :=
  ⟨p.coords.cast (by simp [TensorBundle.euclidean, Leibniz.binomial])⟩

instance : Add (AffinePoint N) := ⟨fun a b => ⟨a.coords + b.coords⟩⟩
instance : Sub (AffinePoint N) := ⟨fun a b => ⟨a.coords - b.coords⟩⟩
instance : Neg (AffinePoint N) := ⟨fun a => ⟨-a.coords⟩⟩
instance : HMul Float (AffinePoint N) (AffinePoint N) := ⟨fun s a => ⟨s * a.coords⟩⟩
instance : HMul (AffinePoint N) Float (AffinePoint N) := ⟨fun a s => ⟨a.coords * s⟩⟩
instance : HDiv (AffinePoint N) Float (AffinePoint N) := ⟨fun a s => ⟨a.coords / s⟩⟩

/-- `buf[j] := a[off + j]` for `j ∈ [j₀, j₀ + k)` (in place when `buf` is unshared). -/
def readLoop (a : FloatArray) (off : Nat) : (k j : Nat) → FloatArray → FloatArray
  | 0, _, buf => buf
  | k + 1, j, buf => readLoop a off k (j + 1) (buf.set! j (a.get! (off + j)))

@[simp] theorem size_readLoop (a : FloatArray) (off : Nat) :
    ∀ (k j : Nat) (buf : FloatArray), (readLoop a off k j buf).size = buf.size
  | 0, _, _ => rfl
  | k + 1, j, buf => by rw [readLoop, size_readLoop a off k (j + 1), FloatArray.size_set!']

theorem get!_readLoop_below (a : FloatArray) (off : Nat) :
    ∀ (k j : Nat) (buf : FloatArray) (i : Nat), i < j → (readLoop a off k j buf).get! i = buf.get! i
  | 0, _, _, _, _ => rfl
  | k + 1, j, buf, i, h => by
    rw [readLoop, get!_readLoop_below a off k (j + 1) _ i (by omega),
      FloatArray.get!_set!_ne _ j i _ (by omega)]

theorem get!_readLoop (a : FloatArray) (off : Nat) :
    ∀ (k j : Nat) (buf : FloatArray) (i : Nat), j + k ≤ buf.size → j ≤ i → i < j + k →
      (readLoop a off k j buf).get! i = a.get! (off + i)
  | 0, _, _, _, _, h1, h2 => absurd h2 (by omega)
  | k + 1, j, buf, i, hs, h1, h2 => by
    rw [readLoop]
    by_cases hij : i = j
    · subst hij
      rw [get!_readLoop_below a off k (i + 1) _ i (by omega),
        FloatArray.get!_set!_self _ i _ (by omega)]
    · exact get!_readLoop a off k (j + 1) _ i (by rw [FloatArray.size_set!']; omega) (by omega)
        (by omega)

/-- `Values.get` of a float vector is `get!` of its storage. -/
theorem _root_.StaticVectors.Values.get_float {n : Nat} (v : Values Float n) (i : Fin n) :
    v.get i = v.data.get! i.1 := by
  obtain ⟨d, hd⟩ := v
  have hd' : d.size = n := hd
  have hi : i.1 < d.size := by rw [hd']; exact i.2
  cases d with | mk xs =>
  simp only [FloatArray.size] at hi
  simp [Values.get, Packed.get, FloatArray.get!, getElem!_def, Array.getElem?_eq_getElem hi]
  rfl

/-- The point stored at `a[off …]` written into the storage of `x` (`readLoop`). -/
@[inline] def readPointInto (a : FloatArray) (off : Nat) (x : AffinePoint N) : AffinePoint N :=
  ⟨⟨readLoop a off N 0 x.coords.data, by
    show (readLoop a off N 0 x.coords.data).size = N
    rw [size_readLoop]; exact x.coords.size_eq⟩⟩

theorem readPointInto_eq (a : FloatArray) (off : Nat) (x : AffinePoint N) :
    readPointInto a off x = ⟨readValues N a off⟩ := by
  cases x with | mk xc =>
  simp only [readPointInto, AffinePoint.mk.injEq]
  apply Values.ext
  intro i
  have hx : xc.data.size = N := xc.size_eq
  rw [Values.get_float, readValues, Values.get_ofFn]
  show (readLoop a off N 0 xc.data).get! i.1 = FlatFiber.read a (off + i.1 * FlatFiber.width Float)
  rw [get!_readLoop a off N 0 _ i.1 (by omega) (Nat.zero_le _) (by omega)]
  show a.get! (off + i.1) = a.get! (off + i.1 * 1)
  rw [Nat.mul_one]

instance : FlatFiber (AffinePoint N) where
  width := N * FlatFiber.width Float
  read a off := ⟨FlatFiber.read a off⟩
  push a p := FlatFiber.push a p.coords
  size_push a p := FlatFiber.size_push a p.coords
  write a off p := FlatFiber.write a off p.coords
  size_write a off p := FlatFiber.size_write a off p.coords
  readInto := readPointInto
  readInto_eq := readPointInto_eq

instance : LinearFiber (AffinePoint N) := ⟨true⟩

/-- The display label of coordinate `j` (0-based): `v₂`, `v₃`, … (the affine manifold's basis
indices `2 … N+1`). -/
def label (j : Nat) : String := Leibniz.printIndices [Int.ofNat (j + 2)] false "v"

/-- Julia `show` of a `Chain{affinemanifold(N),1}`: `0.5v₂ + 2.0v₃` (compact: `0.5v₂+2.0v₃`). -/
def showPoint (compact : Bool) (p : AffinePoint N) : String :=
  String.join <| p.coords.toList.zipIdx.map fun (x, j) =>
    (if j == 0 then JuliaShow.showValue true x else JuliaShow.showTerm compact true x) ++ label j

instance : ShowFiber (AffinePoint N) := ⟨showPoint⟩
instance : ToString (AffinePoint N) := ⟨showPoint false⟩

/-- Julia `norm(p)`. -/
instance : FiberNorm (AffinePoint N) := ⟨fun p => p.coords.norm, true⟩

end AffinePoint

/-! ## Product spaces -/

/-- Julia `ProductSpace{V,T,N,N,S}` over `Float64` coordinates (`topology.jl:46-50`): the lazy
tensor-product grid of `N` coordinate axes. Julia computes range elements on every access; here
each axis is materialized once (`coords`, `sum(size)` floats), so decoding a point is `N` array
reads. Build with `ofAxes`. -/
structure ProductSpace (N : Nat) where
  /-- The coordinate vectors (Julia `split(p) = p.v`), axis 1 first. -/
  axes : Vector Axis N
  /-- The elements of every axis (`axes[a].toFloatArray`). -/
  coords : Vector FloatArray N

namespace ProductSpace

variable {N : Nat}

/-- Julia `ProductSpace(a…)` / `a ⊕ b ⊕ …` of 1-D vectors (`topology.jl:101, 109-110`). -/
def ofAxes (axes : Vector Axis N) : ProductSpace N := ⟨axes, axes.map Axis.toFloatArray⟩

instance : Inhabited (ProductSpace N) := ⟨ofAxes (Vector.replicate N default)⟩

/-- Julia `size(p)` (`topology.jl:76`). -/
def size (p : ProductSpace N) : Vector Nat N := p.axes.map (·.length)

/-- Julia `length(p)`: the number of points. -/
def length (p : ProductSpace N) : Nat := MeshTopology.gridLength p.size

/-- Coordinate `a` of the point with 0-based column-major linear index `k`. -/
@[inline] def coord (p : ProductSpace N) (k : Nat) (a : Fin N) : Float :=
  let c := p.coords[a]
  c.get! (k / MeshTopology.axisStride p.size a.1 % c.size)

/-- Write the coordinates `a, a+1, …, a+r-1` of the point with linear index `k` into `buf`
(`buf[a] := coords[a][k / st % size]`, `st` the stride of axis `a`: the product of the sizes
before it). -/
def pointLoop (p : ProductSpace N) (k : Nat) : (r a st : Nat) → FloatArray → FloatArray
  | 0, _, _, buf => buf
  | r + 1, a, st, buf =>
    let c := p.coords[a]!
    let n := c.size
    pointLoop p k r (a + 1) (st * n) (buf.set! a (c.get! (k / st % n)))

@[simp] theorem size_pointLoop (p : ProductSpace N) (k : Nat) :
    ∀ (r a st : Nat) (buf : FloatArray), (pointLoop p k r a st buf).size = buf.size
  | 0, _, _, _ => rfl
  | r + 1, a, st, buf => by
    simp only [pointLoop]; rw [size_pointLoop p k r, FloatArray.size_set!']

/-- The point with 0-based column-major linear index `k` written into the storage of `x`
(Julia `p[k+1]`, `topology.jl:77-94`): in place when `x` is unshared, so a loop over the points
that hands each one to a function and then reuses it allocates nothing
(`TensorField.tabulatePoint`). -/
@[inline] def pointInto (p : ProductSpace N) (k : Nat) (x : AffinePoint N) : AffinePoint N :=
  ⟨⟨pointLoop p k N 0 1 x.coords.data, by
    show (pointLoop p k N 0 1 x.coords.data).size = N
    rw [size_pointLoop]; exact x.coords.size_eq⟩⟩

/-- The point with 0-based column-major linear index `k` (Julia `p[k+1]`, `topology.jl:77-94`). -/
@[inline] def point (p : ProductSpace N) (k : Nat) : AffinePoint N := pointInto p k default

/-- `pointLoop` leaves the entries outside `[a, a + r)` alone. -/
theorem get!_pointLoop_outside (p : ProductSpace N) (k : Nat) :
    ∀ (r a st : Nat) (buf : FloatArray) (j : Nat), j < a ∨ a + r ≤ j →
      (pointLoop p k r a st buf).get! j = buf.get! j
  | 0, _, _, _, _, _ => rfl
  | r + 1, a, st, buf, j, h => by
    simp only [pointLoop]
    rw [get!_pointLoop_outside p k r (a + 1) _ _ j (by omega),
      FloatArray.get!_set!_ne _ a j _ (by omega)]

/-- The entries `pointLoop` writes do not depend on the buffer. -/
theorem get!_pointLoop_congr (p : ProductSpace N) (k : Nat) :
    ∀ (r a st : Nat) (buf buf' : FloatArray) (j : Nat), a + r ≤ buf.size → a + r ≤ buf'.size →
      a ≤ j → j < a + r → (pointLoop p k r a st buf).get! j = (pointLoop p k r a st buf').get! j
  | 0, _, _, _, _, _, _, _, h1, h2 => absurd h2 (by omega)
  | r + 1, a, st, buf, buf', j, hb, hb', h1, h2 => by
    simp only [pointLoop]
    by_cases hj : j = a
    · subst hj
      rw [get!_pointLoop_outside p k r (j + 1) _ _ j (Or.inl (by omega)),
        get!_pointLoop_outside p k r (j + 1) _ _ j (Or.inl (by omega)),
        FloatArray.get!_set!_self _ j _ (by omega), FloatArray.get!_set!_self _ j _ (by omega)]
    · exact get!_pointLoop_congr p k r (a + 1) _ _ _ _
        (by rw [FloatArray.size_set!']; omega) (by rw [FloatArray.size_set!']; omega)
        (by omega) (by omega)

/-- The point does not depend on the storage it is written into. -/
theorem pointInto_congr (p : ProductSpace N) (k : Nat) (x y : AffinePoint N) :
    pointInto p k x = pointInto p k y := by
  cases x with | mk xc =>
  cases y with | mk yc =>
  cases xc with | mk xd hx =>
  cases yc with | mk yd hy =>
  have hx' : xd.size = N := hx
  have hy' : yd.size = N := hy
  simp only [pointInto, AffinePoint.mk.injEq, Values.mk.injEq]
  apply FloatArray.ext_get! (by rw [size_pointLoop, size_pointLoop, hx', hy'])
  intro j hj
  rw [size_pointLoop] at hj
  exact get!_pointLoop_congr p k N 0 1 xd yd j (by omega) (by omega) (Nat.zero_le _) (by omega)

/-- Reusing storage does not change the point. -/
theorem pointInto_eq (p : ProductSpace N) (k : Nat) (x : AffinePoint N) :
    pointInto p k x = point p k :=
  pointInto_congr p k x default

/-- The point at the 0-based multi-index `idx` (Julia `p[i₁+1, …, i_N+1]`). -/
@[inline] def pointAt (p : ProductSpace N) (idx : Vector Nat N) : AffinePoint N :=
  ⟨Values.ofFn fun a => p.coords[a].get! idx[a]⟩

/-- Julia `isrange(p)` (`topology.jl:74`): every axis is a range. -/
def isRange (p : ProductSpace N) : Bool := p.axes.toList.all (·.isRange)

/-- Julia `widths(p)` (`topology.jl:118`): `last - first` per axis. -/
def widths (p : ProductSpace N) : Vector Float N := p.axes.map (·.width)

/-- Julia `a ⊕ b` of product spaces (`topology.jl:102-104`): the axes concatenated. -/
def append {M : Nat} (a : ProductSpace M) (b : ProductSpace N) : ProductSpace (M + N) :=
  ofAxes (a.axes ++ b.axes)

/-- Julia `p ⊕ v` with a 1-D vector (`topology.jl:102`). -/
def push (p : ProductSpace N) (v : Axis) : ProductSpace (N + 1) := ofAxes (p.axes.push v)

/-- Julia `remove(p, Val(J))` (`topology.jl:120-122`): the space without axis `a` (for `N = 2`
Julia returns the remaining range itself; see `axis`). -/
def remove (p : ProductSpace (N + 1)) (a : Fin (N + 1)) : ProductSpace N :=
  ofAxes ((p.axes.eraseIdx a.1 a.2).cast (by omega))

/-- The axes `ks` (Julia `ProductSpace(p.v[ks])`, the result of slicing with colons at `ks`,
`topology.jl:175-181`). -/
def select {K : Nat} (p : ProductSpace N) (ks : Vector (Fin N) K) : ProductSpace K :=
  ofAxes (ks.map (p.axes[·]))

/-- Julia `p(…, :, …)` with one colon at `a` (`topology.jl:125-129`): the coordinate vector of
axis `a` itself. -/
@[inline] def axis (p : ProductSpace N) (a : Fin N) : Axis := p.axes[a]

/-- Julia `resample(p, n)` (`topology.jl:185`): every axis resampled. -/
def resample (p : ProductSpace N) (n : Vector Nat N) : ProductSpace N :=
  ofAxes (Vector.ofFn fun a => p.axes[a].resample n[a])

/-- Julia `extend(p, i)` (`Cartan.jl:560`): the last axis continued to `i` points. -/
def extend (p : ProductSpace (N + 1)) (i : Nat) : Option (ProductSpace (N + 1)) := do
  let last ← p.axes[N].extend i
  return ofAxes (p.axes.set N last)

/-- Julia `==` of product spaces: equal axes. -/
instance : BEq (ProductSpace N) := ⟨fun a b => a.axes.toList == b.axes.toList⟩

/-- A default-`V` chain display `x₁v₁ + x₂v₂ + …` (Julia `Chain(xs...)`). -/
def showChainValues (xs : List Float) : String :=
  String.join <| xs.zipIdx.map fun (x, j) =>
    (if j == 0 then JuliaShow.showValue true x else JuliaShow.showTerm false true x) ++
      Leibniz.printIndices [Int.ofNat (j + 1)] false "v"

/-- Julia `show(io, p::RealRegion{V,T,N,<:AbstractRange})` (`topology.jl:63`):
`(Chain(firsts)):(Chain(steps)):(Chain(lasts))` with default basis names. Julia reads the `step`
field and throws for `LinRange`/`UnitRange` axes (B7); here their step is `step(r)`. A space with an
explicit axis prints its axes, `ProductSpace(a, b, …)`. -/
def showString (p : ProductSpace N) : String :=
  let axs := p.axes.toList
  match axs.mapM (·.step?) with
  | some steps =>
    s!"({showChainValues (axs.map (·.first))}):({showChainValues steps}):({showChainValues (axs.map (·.last))})"
  | none => "ProductSpace(" ++ ", ".intercalate (axs.map toString) ++ ")"

instance : ToString (ProductSpace N) := ⟨showString⟩

end ProductSpace

end Cartan
