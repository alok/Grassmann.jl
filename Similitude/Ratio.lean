import Similitude.Registry
import Std.Data.HashMap

/-!
# Exact conversion ratios

Similitude never stores conversion tables. A quantity of USQ dimension `d`
converts from `U` to `S` by the exact product (`Similitude.jl:70-89`)

  `ratio(d, U, S) = ∏ₖ (cₖ(S)/cₖ(U))^eₖ`, with `e = UnitSystem(d)`,

over the eleven defining constants `kB ħ 𝘤 μ₀ mₑ Mᵤ Kcd θ λ αL g₀`. Because the
constants are exact groups, the ratio is exact too:
`ratio(energy, Metric, English) = g₀⁻¹ft⁻¹lb⁻¹`.

`ConvertUnit U S d` (Julia `ConvertUnit{U,S,D}`, `dimension.jl:225-266`) is the
conversion factor as a value; its type records the systems and the dimension,
so it can only multiply quantities it applies to.
-/

namespace Similitude

open FieldConstants FieldAlgebra UnitSystems

/-- Similitude's 48 unit systems (Julia `normal(U)`): UnitSystems' definitions
evaluated over `Scalar`, computed once. -/
def systemTable : Array (UnitSystem Scalar) := Sys.all.toArray.map (·.sys Scalar)

/-- The exact constants of a system. -/
def _root_.UnitSystems.Sys.consts (U : Sys) : UnitSystem Scalar := systemTable[U.ctorIdx]!

/-- The eleven ratios `unit(cₖ(S)/cₖ(U))` of `ratio_calc`
(`UnitSystems.boltzmann(U,S)` … `gravity(U,S)`, `Similitude.jl:76-89`). -/
def constRatios (U S : UnitSystem Scalar) : Array Scalar :=
  let f (g : UnitSystem Scalar → Scalar) : Scalar := UnitAlg.unit (g S / g U)
  #[f boltzmann, f planckreduced, f lightspeed, f permeability, f electronmass, f molarmass,
    f luminousefficacy, f radian, f rationalization, f lorentz, f gravity]

/-- Julia `x^e` with the exponent's element type (runtime `Int`, `Rational` or `Float64`). -/
def Scalar.powExpo (x : Scalar) : Expo → Scalar
  | .int n => x.ipow n
  | .rat q => x.qpow q
  | .float y => match x with
    | .grp g => .grp (g.fpow y)
    | x => .ofFloat (JuliaBase.F64.pow x.toFloat y)

/-- `ratio_calc(e, U, S)` for constant exponents `e`, from the eleven constant ratios. -/
def ratioOf (cr : Array Scalar) (e : Exps 11) : Scalar :=
  let es := e.toExpos
  let terms := (List.range 11).map fun k => (cr[k]?.getD (.ofInt 1)).powExpo (es[k]!)
  match terms with
  | [] => .ofInt 1
  | t :: ts => ts.foldl (· * ·) t

/-- Is the ratio of each base dimension between the two systems exactly one?
(Julia's `isone(ratio(usqᵢ, U, S))`, used by `convertdim`.) -/
def baseOnes (cr : Array Scalar) : Array Bool :=
  (List.finRange 11).toArray.map fun i => (ratioOf cr (usqMap.apply (Exps.unit i))).isOne

/-- Per ordered pair of systems: the eleven constant ratios and the base-ratio
flags, computed on first use and cached (`Thunk`), so repeated conversions
between two systems do the group arithmetic once. -/
def pairTable : Array (Thunk (Array Scalar × Array Bool)) :=
  let sys := Sys.all.toArray
  (List.range (sys.size * sys.size)).toArray.map fun k => Thunk.mk fun _ =>
    let cr := constRatios (sys[k / sys.size]!).consts (sys[k % sys.size]!).consts
    (cr, baseOnes cr)

/-- The cached constant ratios and base flags of a pair of systems. -/
def pairData (U S : Sys) : Array Scalar × Array Bool :=
  (pairTable[U.ctorIdx * Sys.all.length + S.ctorIdx]!).get

/-- `ratio(d, U, S)` computed from the cached constant ratios of the pair. -/
def ratioUncached (d : Exps 11) (U S : Sys) : Scalar :=
  ratioOf (pairData U S).1 (usqMap.apply d)

/-- A cache key: the exponents with their element type, and the two systems. -/
structure RatioKey where
  /-- `0` `Int`, `1` `Rational` (numerator, denominator pairs), `2` `Float64` bits -/
  kind : UInt8
  /-- the exponents -/
  e : Array Int
  /-- source system -/
  U : Nat
  /-- target system -/
  S : Nat
  deriving BEq, Hashable

/-- The cache key of `ratio d U S`. -/
def RatioKey.of (d : Exps 11) (U S : Sys) : RatioKey :=
  match d with
  | .int v => ⟨0, v.toArray, U.ctorIdx, S.ctorIdx⟩
  | .exact v => ⟨1, v.toArray.flatMap (fun q => #[q.num, (q.den : Int)]), U.ctorIdx, S.ctorIdx⟩
  | .float v => ⟨2, v.1.toList.toArray.map (fun x => (x.toBits.toNat : Int)), U.ctorIdx, S.ctorIdx⟩

private unsafe def ratioCacheImpl : IO.Ref (Std.HashMap RatioKey Scalar) :=
  unsafeBaseIO (IO.mkRef {})

/-- The process-global cache of runtime ratios. -/
@[implemented_by ratioCacheImpl]
private opaque ratioCache : IO.Ref (Std.HashMap RatioKey Scalar)

private unsafe def ratioImpl (d : Exps 11) (U S : Sys) : Scalar := unsafeBaseIO do
  let k := RatioKey.of d U S
  match (← ratioCache.get).get? k with
  | some r => return r
  | none =>
    let r := ratioUncached d U S
    ratioCache.modify (·.insert k r)
    return r

/-- Julia `ratio(d, U, S)`: the exact factor converting a quantity of USQ
dimension `d` from `U` to `S`. Julia recomputes it on every runtime call; here
it is computed once per `(d, U, S)` and cached for the process (logically
`ratioUncached d U S`, as the plan caches of `Grassmann.Kernel.Reference`). -/
@[implemented_by ratioImpl]
def ratio (d : Exps 11) (U S : Sys) : Scalar := ratioUncached d U S

/-- Would Julia throw computing `x^e`? Raising an `Int` (or a group with an `Int`
coefficient other than `±1`) to a negative runtime power is a `DomainError`
(`power_by_squaring`); it happens for FFF, whose permeability is `0`. -/
def Scalar.powThrows : Scalar → Expo → Bool
  | .grp g, .int n => n < 0 && match g.c with | .int c => c != 1 && c != -1 | _ => false
  | .num (.int c), .int n => n < 0 && c != 1 && c != -1
  | _, _ => false

/-- `ratio`, or `none` where Julia throws a `DomainError` (`Scalar.powThrows`). -/
def ratio? (d : Exps 11) (U S : Sys) : Option Scalar :=
  let cr := (pairData U S).1
  let e := usqMap.apply d
  if (List.finRange 11).any fun k => (cr[k.1]?.getD (.ofInt 1)).powThrows (e.get k) then none
  else some (ratioOf cr e)

/-- Julia `convertdim(d, U, S)` (`dimension.jl:231-234`): drop the base
dimensions whose own ratio between `U` and `S` is exactly one (for display);
`ones` are the flags of `baseOnes`. -/
def convertDim (ones : Array Bool) (d : Exps 11) : Exps 11 :=
  let keep (i : Fin 11) : Bool := !(ones[i.1]?.getD false)
  match d with
  | .int v => .int (Vector.ofFn fun i => if keep i then v[i] else 0)
  | .exact v => .exact (Vector.ofFn fun i => if keep i then v[i] else 0)
  | .float v => .float (FVec.ofFn fun i => if keep i then v.get i else 0.0)

/-- Julia `show(io, ::ConvertUnit{U,S})` for a dimension `d` (`dimension.jl:236-243`):
`ratio [S-units]/[U-units] U -> S`. -/
def showConvert (d : Exps 11) (U S : Sys) : String :=
  let (cr, ones) := pairData U S
  let d' := convertDim ones d
  s!"{ratioOf cr (usqMap.apply d)} [{S.showDim d'}]/[{U.showDim d'}] {U.name} -> {S.name}"

/-- A conversion factor between two unit systems for quantities of dimension `d`
(Julia `ConvertUnit{U,S,D}`, e.g. `energy(Metric, English)`). It carries no data:
the systems and the dimension are in its type. -/
structure ConvertUnit (U S : Sys) (d : Dim) : Type where
  mk ::

namespace ConvertUnit

variable {U S : Sys} {d : Dim}

/-- The exact factor. -/
def ratio (_ : ConvertUnit U S d) : Scalar := Similitude.ratio d.toGroup.v U S

/-- Julia `dimensions(c) = c.v` (`dimension.jl:230`): the dimension the factor
converts. -/
def dimensions (_ : ConvertUnit U S d) : USQGroup := d.toGroup

/-- The inverse conversion (Julia's `inv(::ConvertUnit)` is broken,
`dimension.jl:245`; this is the intended meaning). -/
def inv (_ : ConvertUnit U S d) : ConvertUnit S U d := ⟨⟩

instance : ToString (ConvertUnit U S d) := ⟨fun _ => showConvert d.toGroup.v U S⟩

end ConvertUnit

/-- Julia `d(U, S)`: the conversion factor for dimension `d` from `U` to `S`. -/
def _root_.UnitSystems.Dim.conv (d : Dim) (U S : Sys) : ConvertUnit U S d := ⟨⟩

end Similitude
