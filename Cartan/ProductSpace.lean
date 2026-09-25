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

instance : FlatFiber (AffinePoint N) where
  width := N * FlatFiber.width Float
  read a off := ⟨FlatFiber.read a off⟩
  push a p := FlatFiber.push a p.coords
  size_push a p := FlatFiber.size_push a p.coords

instance : LinearFiber (AffinePoint N) := ⟨⟩

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
instance : FiberNorm (AffinePoint N) := ⟨fun p => p.coords.norm⟩

end AffinePoint

/-! ## Product spaces -/

/-- Julia `ProductSpace{V,T,N,N,S}` over `Float64` coordinates (`topology.jl:46-50`): the lazy
tensor-product grid of `N` coordinate axes. -/
structure ProductSpace (N : Nat) where
  /-- The coordinate vectors (Julia `split(p) = p.v`), axis 1 first. -/
  axes : Vector Axis N
  deriving Inhabited

namespace ProductSpace

variable {N : Nat}

/-- Julia `ProductSpace(a…)` / `a ⊕ b ⊕ …` of 1-D vectors (`topology.jl:101, 109-110`). -/
def ofAxes (axes : Vector Axis N) : ProductSpace N := ⟨axes⟩

/-- Julia `size(p)` (`topology.jl:76`). -/
def size (p : ProductSpace N) : Vector Nat N := p.axes.map (·.length)

/-- Julia `length(p)`: the number of points. -/
def length (p : ProductSpace N) : Nat := MeshTopology.gridLength p.size

/-- Coordinate `a` of the point with 0-based column-major linear index `k`. -/
@[inline] def coord (p : ProductSpace N) (k : Nat) (a : Fin N) : Float :=
  let ax := p.axes[a]
  ax.get (k / MeshTopology.axisStride p.size a.1 % ax.length)

/-- The point with 0-based column-major linear index `k` (Julia `p[k+1]`, `topology.jl:77-94`). -/
@[inline] def point (p : ProductSpace N) (k : Nat) : AffinePoint N :=
  ⟨Values.ofFnScan (fun (st : Nat) (a : Fin N) =>
    let ax := p.axes[a]
    let n := ax.length
    (st * n, ax.get (k / st % n))) 1⟩

/-- The point at the 0-based multi-index `idx` (Julia `p[i₁+1, …, i_N+1]`). -/
@[inline] def pointAt (p : ProductSpace N) (idx : Vector Nat N) : AffinePoint N :=
  ⟨Values.ofFn fun a => p.axes[a].get idx[a]⟩

/-- Julia `isrange(p)` (`topology.jl:74`): every axis is a range. -/
def isRange (p : ProductSpace N) : Bool := p.axes.toList.all (·.isRange)

/-- Julia `widths(p)` (`topology.jl:118`): `last - first` per axis. -/
def widths (p : ProductSpace N) : Vector Float N := p.axes.map (·.width)

/-- Julia `a ⊕ b` of product spaces (`topology.jl:102-104`): the axes concatenated. -/
def append {M : Nat} (a : ProductSpace M) (b : ProductSpace N) : ProductSpace (M + N) :=
  ⟨a.axes ++ b.axes⟩

/-- Julia `p ⊕ v` with a 1-D vector (`topology.jl:102`). -/
def push (p : ProductSpace N) (v : Axis) : ProductSpace (N + 1) := ⟨p.axes.push v⟩

/-- Julia `remove(p, Val(J))` (`topology.jl:120-122`): the space without axis `a` (for `N = 2`
Julia returns the remaining range itself; see `axis`). -/
def remove (p : ProductSpace (N + 1)) (a : Fin (N + 1)) : ProductSpace N :=
  ⟨(p.axes.eraseIdx a.1 a.2).cast (by omega)⟩

/-- The axes `ks` (Julia `ProductSpace(p.v[ks])`, the result of slicing with colons at `ks`,
`topology.jl:175-181`). -/
def select {K : Nat} (p : ProductSpace N) (ks : Vector (Fin N) K) : ProductSpace K :=
  ⟨ks.map (p.axes[·])⟩

/-- Julia `p(…, :, …)` with one colon at `a` (`topology.jl:125-129`): the coordinate vector of
axis `a` itself. -/
@[inline] def axis (p : ProductSpace N) (a : Fin N) : Axis := p.axes[a]

/-- Julia `resample(p, n)` (`topology.jl:185`): every axis resampled. -/
def resample (p : ProductSpace N) (n : Vector Nat N) : ProductSpace N :=
  ⟨Vector.ofFn fun a => p.axes[a].resample n[a]⟩

/-- Julia `extend(p, i)` (`Cartan.jl:560`): the last axis continued to `i` points. -/
def extend (p : ProductSpace (N + 1)) (i : Nat) : Option (ProductSpace (N + 1)) := do
  let last ← p.axes[N].extend i
  return ⟨p.axes.set N last⟩

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
