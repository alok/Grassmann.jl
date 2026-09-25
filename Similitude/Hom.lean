import Similitude.Scalar

/-!
# Unit systems as homomorphisms of the dimension group

Each unit system collapses the USQ dimensions whose defining constants it sets
to one: in `Metric` (`g₀ = 1`) a force is a mass times an acceleration, so
`F ↦ ML T⁻²`; in `Gauss` a charge is `M¹ᐟ²L³ᐟ²T⁻¹`. Similitude writes these maps
as closures over `Group{:USQ}` (`derived.jl:27-99`); here each is a linear map
with *doubled* integer coefficients (`LinMap`), so the maps are data: they
evaluate on exact or floating exponent vectors, and the kernel checks that every
one of them is a projection (`LinMap.IsProjection`, `homs_idempotent`).

Similitude's fundamental isomorphism `UnitSystem(d)` (`dimension.jl:466-493`),
from USQ exponents to exponents over the eleven defining constants, is the same
kind of map (`usqMap`), checked against UnitSystems' closed form `usqToConst`.
-/

namespace Similitude

open FieldConstants FieldAlgebra UnitSystems

/-- A linear map of the eleven USQ exponents with coefficients in `½ℤ`, stored
row-sparse and doubled: output slot `i` is `Σ (j, k) ∈ rows[i], (k/2)·dⱼ`. -/
structure LinMap where
  /-- for each output slot, the `(input slot, doubled coefficient)` terms -/
  rows : List (List (Nat × Int))

namespace LinMap

/-- Doubled matrix entry `(i, j)`. -/
def entry (m : LinMap) (i j : Nat) : Int :=
  ((m.rows.getD i []).filter (·.1 == j)).foldl (fun acc t => acc + t.2) 0

/-- `(M·M)[i][j] = 2·M[i][j]` for the doubled matrix `M` means the map is idempotent. -/
def IsProjection (m : LinMap) : Prop :=
  ∀ i ∈ List.range 11, ∀ j ∈ List.range 11,
    ((List.range 11).foldl (fun acc k => acc + m.entry i k * m.entry k j) 0) = 2 * m.entry i j

instance (m : LinMap) : Decidable m.IsProjection := by unfold IsProjection; infer_instance

/-- Apply the map to exact exponents. -/
def applyRat (m : LinMap) (d : Fin 11 → Rat) : Vector Rat 11 :=
  Vector.ofFn fun i => (m.rows.getD i.1 []).foldl
    (fun acc (j, k) => acc + mkRat k 2 * (if h : j < 11 then d ⟨j, h⟩ else 0)) 0

/-- Apply the map to `Float64` exponents (Julia raises a `MethodError` for the
`//2` maps of Gauss, ESU and EMU on float exponents; the port evaluates them). -/
def applyFloat (m : LinMap) (d : Fin 11 → Float) : FVec 11 :=
  FVec.ofFn fun i => (m.rows.getD i.1 []).foldl
    (fun acc (j, k) => acc + (Float.ofInt k / 2.0) * (if h : j < 11 then d ⟨j, h⟩ else 0.0)) 0.0

/-- Apply the map to a USQ exponent vector, keeping Julia's element type. -/
def apply (m : LinMap) : Exps 11 → Exps 11
  | .exact v => .exact (m.applyRat fun i => v[i])
  | .float v => .float (m.applyFloat v.get)

/-- Apply the map to a USQ group; the image has coefficient `1` (Julia builds it
with `Group(…, 1, Val(:USQ))`). -/
def applyGroup (m : LinMap) (g : USQGroup) : USQGroup := Group.mk' (m.apply g.v) (.int 1)

end LinMap

/-! Slots: `F=0 M=1 L=2 T=3 Q=4 Θ=5 N=6 J=7 A=8 R=9 C=10`; coefficients doubled. -/

/-- `Engineering` (English, Survey): `(F,M,L,T,Q,Θ,N,J,A,0,0)` (`derived.jl:27-29`). -/
def homEngineering : LinMap := ⟨(List.range 11).map fun i => if i < 9 then [(i, 2)] else []⟩
/-- `Gravitational` (British, IPS): `(F+M,0,L−M,T+2M,Q,Θ,N,J,0,0,0)` (`derived.jl:30-32`). -/
def homGravitational : LinMap :=
  ⟨[[(0, 2), (1, 2)], [], [(2, 2), (1, -2)], [(3, 2), (1, 4)], [(4, 2)], [(5, 2)], [(6, 2)], [(7, 2)],
    [], [], []]⟩
/-- `Metric` and every system without its own map: `(0,F+M,F+L,T−2F,Q,Θ,N,J,0,0,0)`
(`derived.jl:33-35`, `dimension.jl:507`). -/
def homMetric : LinMap :=
  ⟨[[], [(0, 2), (1, 2)], [(0, 2), (2, 2)], [(3, 2), (0, -4)], [(4, 2)], [(5, 2)], [(6, 2)], [(7, 2)],
    [], [], []]⟩
/-- `MetricDegree` (and the other angle-keeping metric systems): Metric plus `A`
(`derived.jl:36-38`). -/
def homMetricDegree : LinMap :=
  ⟨[[], [(0, 2), (1, 2)], [(0, 2), (2, 2)], [(3, 2), (0, -4)], [(4, 2)], [(5, 2)], [(6, 2)], [(7, 2)],
    [(8, 2)], [], []]⟩
/-- `Gauss` (LorentzHeaviside): `(0,F+M+Q/2,F+L+3Q/2+C,T−2F−Q−C,0,Θ,N,J,0,0,0)` (`derived.jl:43-45`). -/
def homGauss : LinMap :=
  ⟨[[], [(0, 2), (1, 2), (4, 1)], [(0, 2), (2, 2), (4, 3), (10, 2)], [(3, 2), (0, -4), (4, -2), (10, -2)],
    [], [(5, 2)], [(6, 2)], [(7, 2)], [], [], []]⟩
/-- `ESU`: `(0,F+M+Q/2,F+L+3Q/2,T−2F−Q,0,Θ,N,J,0,0,0)` (`derived.jl:46-48`). -/
def homESU : LinMap :=
  ⟨[[], [(0, 2), (1, 2), (4, 1)], [(0, 2), (2, 2), (4, 3)], [(3, 2), (0, -4), (4, -2)], [], [(5, 2)],
    [(6, 2)], [(7, 2)], [], [], []]⟩
/-- `EMU`: `(0,F+M+Q/2,F+L+Q/2,T−2F,0,Θ,N,J,0,0,0)` (`derived.jl:49-51`). -/
def homEMU : LinMap :=
  ⟨[[], [(0, 2), (1, 2), (4, 1)], [(0, 2), (2, 2), (4, 1)], [(3, 2), (0, -4)], [], [(5, 2)], [(6, 2)],
    [(7, 2)], [], [], []]⟩
/-- `Stoney` and `Cosmological`: `(0,F+M+Θ+N,0,L+T−F,Q,0,0,J,0,0,0)` (`derived.jl:63-65, 94-96`). -/
def homStoney : LinMap :=
  ⟨[[], [(0, 2), (1, 2), (5, 2), (6, 2)], [], [(2, 2), (3, 2), (0, -2)], [(4, 2)], [], [], [(7, 2)],
    [], [], []]⟩
/-- `Electronic` and `Hubble`: `(0,0,0,L+T−F−J,Q,0,…)` (`derived.jl:66-68, 91-93`). -/
def homElectronic : LinMap :=
  ⟨[[], [], [], [(2, 2), (3, 2), (0, -2), (7, -2)], [(4, 2)], [], [], [], [], [], []]⟩
/-- `Planck` (QCD): `(0,M+Θ+N+2(F+J)−L−T,0,…)` (`derived.jl:72-74`). -/
def homPlanck : LinMap :=
  ⟨[[], [(1, 2), (5, 2), (6, 2), (0, 4), (7, 4), (2, -2), (3, -2)], [], [], [], [], [], [], [], [], []]⟩
/-- `PlanckGauss` (QCDGauss), `QCDoriginal`, `CosmologicalQuantum`: Planck plus `Q`
(`derived.jl:69-71, 75-77, 97-99`). -/
def homPlanckGauss : LinMap :=
  ⟨[[], [(1, 2), (5, 2), (6, 2), (0, 4), (7, 4), (2, -2), (3, -2)], [], [], [(4, 2)], [], [], [], [], [],
    []]⟩
/-- `Natural`: everything is dimensionless (`derived.jl:78-80`). -/
def homNatural : LinMap := ⟨List.replicate 11 []⟩
/-- `NaturalGauss`: only charge survives (`derived.jl:81-83`). -/
def homNaturalGauss : LinMap := ⟨[[], [], [], [], [(4, 2)], [], [], [], [], [], []]⟩
/-- `Rydberg` (Schrodinger): `(0,F+M+N,F+L,T−Θ+2(J−F),Q,0,…)` (`derived.jl:85-87`). -/
def homRydberg : LinMap :=
  ⟨[[], [(0, 2), (1, 2), (6, 2)], [(0, 2), (2, 2)], [(3, 2), (5, -2), (7, 4), (0, -4)], [(4, 2)], [], [],
    [], [], [], []]⟩
/-- `Hartree`: `(0,0,L+2(T−Θ)−3F−4J,0,Q,0,…)` (`derived.jl:88-90`). -/
def homHartree : LinMap :=
  ⟨[[], [], [(2, 2), (3, 4), (5, -4), (0, -6), (7, -8)], [], [(4, 2)], [], [], [], [], [], []]⟩

/-- The homomorphism `U(d)` of each system, with Julia's `@unitgroup` sharing
(`derived.jl:127-148`, `Similitude.jl:208`) and the Metric default for systems
without a method (`dimension.jl:507`). -/
def _root_.UnitSystems.Sys.hom : Sys → LinMap
  | .Engineering | .English | .Survey => homEngineering
  | .Gravitational | .British | .IPS => homGravitational
  | .MetricDegree | .MetricTurn | .MetricSpatian | .MetricGradian | .MetricArcminute
  | .MetricArcsecond => homMetricDegree
  | .Gauss | .LorentzHeaviside => homGauss
  | .ESU => homESU
  | .EMU => homEMU
  | .Stoney | .Cosmological => homStoney
  | .Electronic | .Hubble => homElectronic
  | .Planck | .QCD => homPlanck
  | .PlanckGauss | .QCDGauss | .QCDoriginal | .CosmologicalQuantum => homPlanckGauss
  | .Natural => homNatural
  | .NaturalGauss => homNaturalGauss
  | .Rydberg | .Schrodinger => homRydberg
  | .Hartree => homHartree
  | _ => homMetric

/-- The distinct maps. -/
def allHoms : List LinMap :=
  [homEngineering, homGravitational, homMetric, homMetricDegree, homGauss, homESU, homEMU, homStoney,
   homElectronic, homPlanck, homPlanckGauss, homNatural, homNaturalGauss, homRydberg, homHartree]

/-- Every unit-system homomorphism is a projection: applying it twice changes
nothing, so a displayed dimension is already in the system's normal form. The
kernel multiplies all fifteen 11×11 matrices. -/
theorem homs_idempotent : ∀ m ∈ allHoms, m.IsProjection := by decide

/-- Similitude's `UnitSystem(d)` (`dimension.jl:466-493`): USQ exponents to
exponents over `kB ħ 𝘤 μ₀ mₑ Mᵤ Kcd θ λ αL g₀`. -/
def usqMap : LinMap :=
  ⟨[[(5, -2)],
    [(2, 2), (3, 2), (4, 1), (0, -2), (7, -2)],
    [(0, 6), (5, 4), (7, 8), (2, -2), (3, -4), (4, -1)],
    [(4, -1)],
    [(1, 2), (5, 2), (6, 2), (0, 4), (7, 4), (2, -2), (3, -2)],
    [(6, -2)],
    [(7, 2)],
    [(2, 2), (3, 2), (8, 2), (4, 1), (0, -2), (7, -2)],
    [(9, 2), (4, -1)],
    [(4, -2), (10, -2)],
    [(2, 2), (3, 2), (5, -2), (0, -4), (7, -4)]]⟩

/-- The doubled image of an integer USQ dimension under a map, as a `HalfDim`. -/
def LinMap.halfDim (m : LinMap) (d : Dim) : HalfDim :=
  let x := d.toInts
  let e (i : Nat) : Int := (m.rows.getD i []).foldl (fun acc (j, k) => acc + k * x.getD j 0) 0
  ⟨e 0, e 1, e 2, e 3, e 4, e 5, e 6, e 7, e 8, e 9, e 10⟩

/-- `usqMap` is UnitSystems' closed-form `usqToConst` (checked on the basis, so
the two linear maps are equal). -/
theorem usqMap_eq_usqToConst :
    ∀ d ∈ [USQ.F, USQ.M, USQ.L, USQ.T, USQ.Q, USQ.Θ, USQ.N, USQ.J, USQ.A, USQ.R, USQ.C],
      usqMap.halfDim d = usqToConst d := by decide

/-- The USQ exponents of a type-level dimension as a group element. -/
def _root_.UnitSystems.Dim.toGroup (d : Dim) : USQGroup :=
  Group.mk' (.exact (Vector.ofFn fun i => d.toRats.getD i.1 0)) (.int 1)

end Similitude
