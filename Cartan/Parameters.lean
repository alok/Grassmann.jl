import Cartan.Algebra

/-!
# Parameter domains: `TorusParameter(n, m)` and friends

Julia's `XParameter(n…)` (Cartan.jl `src/quotient.jl:19-114`) is the identity field on a grid of
`LinRange`s with the matching quotient topology: the parameter space of a torus, sphere, Möbius
strip, … from which the docs build every surface (`torus.(TorusParameter(60,60))`). The chain is
`TorusParameter(Values(n…))` → `TorusTopology(LinRange(0,2π,n₁) ⊕ …)` → the grid bundle with
`TorusTopology(size)` → `TensorField(dom)` (port notes §2.8).

In Julia 0.4.16 every multi-dimensional `XParameter` throws, because the MeshTopology split
dropped `XTopology(::ProductSpace)` (B1); the port implements the intended pre-split chain, and
the oracle generates its goldens with the one-line shim restoring it.

* 1-D parameters (`XParameter(n)`) have real points (`PointArray(0, LinRange(…))`), N-D ones
  `AffinePoint`s. The 1-D fibers are the `LinRange` itself (lazy in Julia).
* `HopfParameter(n₁, n₂)` indexes `n[3]` of a 2-vector in Julia (B18); here it is
  `LinRange(0,2π,n₁) ⊕ LinRange(0,4π,n₂)`.
* `BallParameter()` and `SphereParameter()` build Tube parameters in Julia (B19); here they build
  a ball and a sphere.

| Julia | axes | topology |
|---|---|---|
| `OpenParameter` | `[0,1]^N` | open |
| `MirrorParameter` | `[0,2π] × [0,1]^(N-1)` | mirror |
| `ClampedParameter`, `TorusParameter` | `[0,2π]^N` | clamped, torus |
| `CylinderParameter`, `MobiusParameter` | `[-π,π] × [-1,1]` | cylinder, Möbius |
| `WingParameter` | `[0,1] × [-1,1]` | wing |
| `KleinParameter` | `[0,2π]²` | Klein |
| `ConeParameter` | `[0,1] × [0,2π]` | cone |
| `TubeParameter` | `[-1,1] × [-π,π]`; 3-D `[0,1] × [-1,1] × [-π,π]` | tube |
| `BallParameter` | `[-1,1]` (1-D); `[0,1] × [-π/2,π/2]^(N-2) × [-π,π]` | ball |
| `SphereParameter` | `[-π,π]` (1-D); `[-π/2,π/2]^(N-1) × [-π,π]` | sphere |
| `GeographicParameter` | `[-π,π] × [-π/2,π/2]` | geographic |
| `HopfParameter` | `[7π/16/n₁, 7π/16] × [0,2π] × [0,4π]`; 2-D `[0,2π] × [0,4π]` | Hopf |
-/

namespace Cartan

open Grassmann DirectSum StaticVectors AbstractTensors JuliaBase MeshTopology

namespace Parameter

/-! ## Bases -/

/-- The product space of the `LinRange`s `(lo a, hi a, n a)`. -/
def linSpace {N : Nat} (lo hi : Fin N → Float) (n : Vector Nat N) : ProductSpace N :=
  .ofAxes (Vector.ofFn fun a => Axis.linRange (lo a) (hi a) n[a])

/-- A 1-D parameter base: the `LinRange(lo, hi, n)` interval with real points. -/
def base1 (lo hi : Float) (n : Nat) : GridBundle 1 Float := GridBundle.ofAxis (Axis.linRange lo hi n)

/-- The open grid of an N-D parameter space. -/
def baseN {N : Nat} (lo hi : Fin N → Float) (n : Vector Nat N) : GridBundle N (AffinePoint N) :=
  GridBundle.ofSpace (linSpace lo hi n)

/-- `-π/2` for all but the last axis, `-π` for the last (the sphere's axes). -/
def sphereLo {N : Nat} (a : Fin N) : Float := if a.1 + 1 = N then -piF else -halfPiF
/-- `π/2` for all but the last axis, `π` for the last. -/
def sphereHi {N : Nat} (a : Fin N) : Float := if a.1 + 1 = N then piF else halfPiF
/-- The ball's lower bounds: `0` on the radial axis, then as the sphere. -/
def ballLo {N : Nat} (a : Fin N) : Float := if a.1 = 0 then 0 else sphereLo a
/-- The ball's upper bounds: `1` on the radial axis, then as the sphere. -/
def ballHi {N : Nat} (a : Fin N) : Float := if a.1 = 0 then 1 else sphereHi a

/-! ## 1-D parameters (real points; the fiber is the `LinRange`) -/

/-- Julia `OpenParameter(n)`: `[0,1]`, open. -/
def open1 (n : Nat) : TensorField (base1 0 1 n) Float := TensorField.identity1 _
/-- Julia `MirrorParameter(n)`: `[0,2π]`, mirror. -/
def mirror1 (n : Nat) : TensorField (base1 0 twoPiF n).mirror Float := TensorField.identity1 _
/-- Julia `ClampedParameter(n)`: `[0,2π]`, clamped. -/
def clamped1 (n : Nat) : TensorField (base1 0 twoPiF n).clamped Float := TensorField.identity1 _
/-- Julia `TorusParameter(n)`: `[0,2π]`, periodic. -/
def torus1 (n : Nat) : TensorField (base1 0 twoPiF n).torus Float := TensorField.identity1 _
/-- Julia `BallParameter(n)`: `[-1,1]`, open (the 1-ball). -/
def ball1 (n : Nat) : TensorField (base1 (-1) 1 n).ball Float := TensorField.identity1 _
/-- Julia `SphereParameter(n)`: `[-π,π]`, periodic (the circle). -/
def sphere1 (n : Nat) : TensorField (base1 (-piF) piF n).sphere Float := TensorField.identity1 _

/-! ## N-D parameters (affine points) -/

/-- Julia `OpenParameter(n…)`: `[0,1]^N`, open. -/
def «open» {N : Nat} (n : Vector Nat N) : TensorField (baseN (fun _ => 0) (fun _ => 1) n) (AffinePoint N) :=
  TensorField.identity _
/-- Julia `MirrorParameter(n…)`: `[0,2π] × [0,1]^(N-1)`, the low face of axis 1 a mirror. -/
def mirror {N : Nat} (n : Vector Nat N) :
    TensorField (baseN (fun _ => 0) (fun a => if a.1 = 0 then twoPiF else 1) n).mirror (AffinePoint N) :=
  TensorField.identity _
/-- Julia `ClampedParameter(n…)`: `[0,2π]^N`, every face a mirror. -/
def clamped {N : Nat} (n : Vector Nat N) :
    TensorField (baseN (fun _ => 0) (fun _ => twoPiF) n).clamped (AffinePoint N) := TensorField.identity _
/-- Julia `TorusParameter(n…)`: `[0,2π]^N`, every axis periodic. -/
def torus {N : Nat} (n : Vector Nat N) :
    TensorField (baseN (fun _ => 0) (fun _ => twoPiF) n).torus (AffinePoint N) := TensorField.identity _
/-- Julia `BallParameter(n…)` (`PolarParameter`): `[0,1] × [-π/2,π/2]^(N-2) × [-π,π]`. -/
def ball {N : Nat} (n : Vector Nat N) : TensorField (baseN ballLo ballHi n).ball (AffinePoint N) :=
  TensorField.identity _
/-- Julia `SphereParameter(n…)`: `[-π/2,π/2]^(N-1) × [-π,π]`. -/
def sphere {N : Nat} (n : Vector Nat N) : TensorField (baseN sphereLo sphereHi n).sphere (AffinePoint N) :=
  TensorField.identity _

/-- The bounds of a 2-D parameter space from two pairs. -/
def lo2 (a b : Float) (i : Fin 2) : Float := if i.1 = 0 then a else b

/-- Julia `CylinderParameter(n, m)`: `[-π,π] × [-1,1]`, axis 1 periodic. -/
def cylinder (n m : Nat) :
    TensorField (baseN (lo2 (-piF) (-1)) (lo2 piF 1) #v[n, m]).cylinder (AffinePoint 2) := TensorField.identity _
/-- Julia `MobiusParameter(n, m)`: `[-π,π] × [-1,1]`, axis 1 periodic with a flip. -/
def mobius (n m : Nat) :
    TensorField (baseN (lo2 (-piF) (-1)) (lo2 piF 1) #v[n, m]).mobius (AffinePoint 2) := TensorField.identity _
/-- Julia `WingParameter(n, m)`: `[0,1] × [-1,1]`, the ends of axis 1 folded. -/
def wing (n m : Nat) :
    TensorField (baseN (lo2 0 (-1)) (lo2 1 1) #v[n, m]).wing (AffinePoint 2) := TensorField.identity _
/-- Julia `KleinParameter(n, m)`: `[0,2π]²`. -/
def klein (n m : Nat) :
    TensorField (baseN (fun _ => 0) (fun _ => twoPiF) #v[n, m]).klein (AffinePoint 2) := TensorField.identity _
/-- Julia `ConeParameter(n, m)`: `[0,1] × [0,2π]`. -/
def cone (n m : Nat) :
    TensorField (baseN (fun _ => 0) (lo2 1 twoPiF) #v[n, m]).cone (AffinePoint 2) := TensorField.identity _
/-- Julia `TubeParameter(n, m)` (`RevolvedParameter`): `[-1,1] × [-π,π]`, axis 2 periodic. -/
def tube (n m : Nat) :
    TensorField (baseN (lo2 (-1) (-piF)) (lo2 1 piF) #v[n, m]).tube (AffinePoint 2) := TensorField.identity _
/-- The bounds of the 3-D tube, `[0,1] × [-1,1] × [-π,π]`. -/
def tube3Lo (i : Fin 3) : Float := if i.1 = 0 then 0 else if i.1 = 1 then -1 else -piF
/-- Upper bounds of the 3-D tube. -/
def tube3Hi (i : Fin 3) : Float := if i.1 = 0 then 1 else if i.1 = 1 then 1 else piF
/-- Julia `TubeParameter(n₁, n₂, n₃)`: `[0,1] × [-1,1] × [-π,π]`. -/
def tube3 (n : Vector Nat 3) : TensorField (baseN tube3Lo tube3Hi n).tube3 (AffinePoint 3) :=
  TensorField.identity _
/-- Julia `GeographicParameter(n, m)`: `[-π,π] × [-π/2,π/2]`. -/
def geographic (n m : Nat) :
    TensorField (baseN (lo2 (-piF) (-halfPiF)) (lo2 piF halfPiF) #v[n, m]).geographic (AffinePoint 2) :=
  TensorField.identity _
/-- Julia `HopfParameter(n, m)` with the intended axes `[0,2π] × [0,4π]` (B18). -/
def hopf (n m : Nat) :
    TensorField (baseN (fun _ => 0) (lo2 twoPiF fourPiF) #v[n, m]).hopf (AffinePoint 2) := TensorField.identity _
/-- The first axis of the 3-D Hopf parameter starts at `7π/16/n₁`. -/
def hopfLo (n1 : Nat) (i : Fin 3) : Float := if i.1 = 0 then 7 * piF / 16 / Float.ofNat n1 else 0
/-- Upper bounds of the 3-D Hopf parameter: `7π/16`, `2π`, `4π`. -/
def hopfHi (i : Fin 3) : Float := if i.1 = 0 then 7 * piF / 16 else if i.1 = 1 then twoPiF else fourPiF
/-- Julia `HopfParameter(n₁, n₂, n₃)`: `[7π/16/n₁, 7π/16] × [0,2π] × [0,4π]`. -/
def hopf3 (n : Vector Nat 3) : TensorField (baseN (hopfLo n[0]) hopfHi n).hopf3 (AffinePoint 3) :=
  TensorField.identity _

/-! ## Julia's default sizes (`quotient.jl:77-110`) -/

/-- Julia `TorusParameter()` = `TorusParameter(61, 61)`. -/
def torusDefault := torus #v[61, 61]
/-- Julia `HopfParameter()` = `HopfParameter(7, 60, 61)`. -/
def hopfDefault := hopf3 #v[7, 60, 61]
/-- Julia `ConeParameter(n = 31, m = 2n+1)`. -/
def coneDefault (n : Nat := 31) := cone n (2 * n + 1)
/-- Julia `GeographicParameter(n = 61, m = n÷2)`. -/
def geographicDefault (n : Nat := 61) := geographic n (n / 2)
/-- Julia `TubeParameter()` = `TubeParameter(20, 61)`. -/
def tubeDefault := tube 20 61
/-- Julia `BallParameter()`: Julia builds `TubeParameter(20, 61)` (B19); fixed to the ball. -/
def ballDefault := ball #v[20, 61]
/-- Julia `SphereParameter()`: Julia builds `TubeParameter(31, 61)` (B19); fixed to the sphere. -/
def sphereDefault := sphere #v[31, 61]

end Parameter

end Cartan
