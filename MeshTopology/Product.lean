import MeshTopology.Basic

/-!
# ProductTopology

Julia `ProductTopology{N,S}` (MeshTopology.jl `src/MeshTopology.jl:113-208`): a lazy Cartesian
grid of integer axis vectors, `m[i₁,…,i_N] = Values(v₁[i₁], …, v_N[i_N])`. It is also the type of
the transversal gluing maps `q` of a `QuotientTopology`.

Each axis is an `AxisMap`, one constructor per Julia vector type that occurs (`OneTo`, `UnitRange`,
`StepRange`, `CrossRange`, `Vector{Int}`), because the type drives `resize`, `show` and the type
parameter `S`. Building a product from several axes follows Julia's `Values(v...)` promotion
(port-notes/meshtopology.md §3.2, checked in the oracle): ranges of different kinds are converted
to a common `UnitRange`/`StepRange`, and any other mixture keeps its axes with
`S = AbstractVector{Int64}`.
-/

namespace MeshTopology

/-- One integer axis vector of a `ProductTopology`. -/
inductive AxisMap where
  /-- `Base.OneTo(n)`: the identity `1..n`. -/
  | oneTo (n : Nat)
  /-- `start:stop`. -/
  | unitRange (start stop : Int)
  /-- `start:step:stop` with Julia's normalized `stop` (use `AxisMap.stepRange'`). -/
  | stepRange (start step stop : Int)
  /-- `CrossRange(n)` (MT:48-63). -/
  | cross (n : Nat)
  /-- An explicit `Vector{Int}`. -/
  | vec (v : Array Int)
  deriving Inhabited, Repr, BEq

/-- The Julia type of an axis, or of a promoted collection of axes. -/
inductive AxisKind where
  | oneTo | unitRange | stepRange | cross | vec
  /-- `AbstractVector{Int64}`: axes of unrelated types. -/
  | abstract
  deriving Inhabited, Repr, BEq, DecidableEq

namespace AxisKind

/-- Julia type string. -/
def typeString : AxisKind → String
  | oneTo => "Base.OneTo{Int64}"
  | unitRange => "UnitRange{Int64}"
  | stepRange => "StepRange{Int64, Int64}"
  | cross => "CrossRange"
  | vec => "Vector{Int64}"
  | abstract => "AbstractVector{Int64}"

/-- `true` for the three `AbstractRange` kinds that promote to each other. -/
def isIntRange : AxisKind → Bool
  | oneTo | unitRange | stepRange => true
  | _ => false

end AxisKind

namespace AxisMap

/-- Julia `StepRange(start, step, stop)`: normalizes `stop` to the last element
(`base/range.jl` `steprange_last`); an empty range gets `stop = start - step`. -/
def stepRange' (start step stop : Int) : AxisMap :=
  if step == 0 || stop == start then .stepRange start step stop
  else if (step > 0) != (stop > start) then .stepRange start step (start - step)
  else .stepRange start step (stop - (stop - start).tmod step)

/-- Julia type of the axis. -/
def kind : AxisMap → AxisKind
  | oneTo _ => .oneTo
  | unitRange .. => .unitRange
  | stepRange .. => .stepRange
  | cross _ => .cross
  | vec _ => .vec

/-- Julia `length`. -/
def length : AxisMap → Nat
  | oneTo n => n
  | unitRange a b => (b - a + 1).toNat
  | stepRange a s b => if s == 0 then 0 else ((b - a) / s + 1).toNat
  | cross n => n
  | vec v => v.size

/-- Julia `v[i]` for a 1-based index `i`, without bounds checks (Julia throws `BoundsError`
out of range; here ranges extrapolate and vectors read `0`). -/
@[inline] def get (m : AxisMap) (i : Int) : Int :=
  match m with
  | oneTo _ => i
  | unitRange a _ => a + i - 1
  | stepRange a s _ => a + (i - 1) * s
  | cross n => crossGet n i
  | vec v => if 1 ≤ i then v[(i - 1).toNat]?.getD 0 else 0

/-- Julia `collect`. -/
def toArray (m : AxisMap) : Array Int := (Array.range m.length).map fun (k : Nat) => m.get (Int.ofNat k + 1)

/-- Julia `first` (of a nonempty axis). -/
@[inline] def first (m : AxisMap) : Int := m.get 1

/-- Julia `last` (of a nonempty axis). -/
@[inline] def last (m : AxisMap) : Int := m.get m.length

/-- Julia `resize(v, i)` (MT:147-149): `OneTo(i)`; `1:1:i` for a `StepRange` starting at `1` and
`i:-1:1` for any other `StepRange`; `CrossRange(i)`. `UnitRange` and `Vector` have no method
(`none`). -/
def resize? (m : AxisMap) (i : Nat) : Option AxisMap :=
  match m with
  | oneTo _ => some (oneTo i)
  | stepRange a _ _ => some (if a == 1 then stepRange' 1 1 i else stepRange' i (-1) 1)
  | cross _ => some (cross i)
  | _ => none

/-- Convert a range axis to a `UnitRange` (Julia `convert(UnitRange{Int}, v)`). -/
def toUnitRange (m : AxisMap) : AxisMap :=
  match m with
  | oneTo n => unitRange 1 n
  | _ => m

/-- Convert a range axis to a `StepRange` (Julia `convert(StepRange{Int,Int}, v)`). -/
def toStepRange (m : AxisMap) : AxisMap :=
  match m with
  | oneTo n => stepRange' 1 1 n
  | unitRange a b => stepRange' a 1 b
  | _ => m

/-- Julia `isequal` of two axes as vectors (elementwise, any representation). -/
def eqv (a b : AxisMap) : Bool := a == b || a.toArray == b.toArray

end AxisMap

/-- Julia `promote_type` of a family of axis kinds, as `Values(v...)` applies it. -/
def promoteKinds (ks : List AxisKind) : AxisKind :=
  match ks with
  | [] => .vec
  | k :: rest =>
    if rest.all (· == k) then k
    else if ks.all (·.isIntRange) then
      if ks.contains .stepRange then .stepRange else .unitRange
    else .abstract

/-- Julia `ProductTopology{N,S}` (MT:129-132): one `AxisMap` per grid axis. Use
`ProductTopology.ofAxes` to build one with Julia's promotion. -/
structure ProductTopology (N : Nat) where
  /-- The axis vectors (Julia field `v`). -/
  axes : Vector AxisMap N
  deriving Inhabited, BEq, Repr

namespace ProductTopology

variable {N : Nat}

/-- Julia `ProductTopology(Values(v...))`: builds the product, converting range axes of
different kinds to their promoted type. -/
def ofAxes (axes : Vector AxisMap N) : ProductTopology N :=
  match promoteKinds (axes.toList.map (·.kind)) with
  | .stepRange => ⟨axes.map (·.toStepRange)⟩
  | .unitRange => ⟨axes.map (·.toUnitRange)⟩
  | _ => ⟨axes⟩

/-- Julia `ProductTopology(i, jk...)` with integer sizes: `OneTo` axes (MT:134). -/
def ofSizes (s : Vector Nat N) : ProductTopology N := ⟨s.map .oneTo⟩

/-- The single-axis product (Julia `ProductTopology(v::AbstractVector)`, MT:136). -/
def single (a : AxisMap) : ProductTopology 1 := ⟨#v[a]⟩

/-- The 0-dimensional product (Julia `ProductTopology()`, MT:133). -/
def empty : ProductTopology 0 := ⟨#v[]⟩

/-- Julia type parameter `S`. -/
def elKind (m : ProductTopology N) : AxisKind :=
  if N = 0 then .vec else promoteKinds (m.axes.toList.map (·.kind))

/-- Julia type string `ProductTopology{N, S}`. -/
def typeString (m : ProductTopology N) : String :=
  s!"ProductTopology\{{N}, {m.elKind.typeString}}"

/-- Julia `size` (MT:161). -/
def size (m : ProductTopology N) : Vector Nat N := m.axes.map (·.length)

/-- Julia `length` (the number of grid points). -/
def length (m : ProductTopology N) : Nat := gridLength m.size

/-- Julia `m[i₁,…,i_N]` (MT:162), without bounds checks. -/
@[inline] def get (m : ProductTopology N) (idx : Vector Int N) : Vector Int N :=
  Vector.ofFn fun k => m.axes[k].get idx[k]

/-- Julia `m[k]` for a 1-based column-major linear index (MT:168-179). -/
def getLinear (m : ProductTopology N) (k : Nat) : Vector Int N :=
  m.get ((cartesianIndex m.size k).map (Int.ofNat ·))

/-- All entries in column-major order (Julia `vec(collect(m))`). -/
def toArray (m : ProductTopology N) : Array (Vector Int N) :=
  (Array.range m.length).map fun k => m.getLinear (k + 1)

/-- Julia `resize(m, i)` (MT:150-153): resizes the **last** axis only. -/
def resize? (m : ProductTopology N) (i : Nat) : Option (ProductTopology N) :=
  match N, m with
  | 0, m => some m
  | n + 1, m => (m.axes[n].resize? i).map fun a => ofAxes (m.axes.set n a)

/-- Julia `resample(m, i)` (MT:155-159): resizes every axis. -/
def resample? (m : ProductTopology N) (s : Vector Nat N) : Option (ProductTopology N) := do
  let axes ← (Vector.ofFn fun k : Fin N => (k, m.axes[k].resize? s[k])).toList.foldlM
    (fun (acc : Vector AxisMap N) (k, a?) => a?.map (acc.set k.1 · k.2)) m.axes
  return ofAxes axes

/-- The product of the listed axes, in the given order (Julia `ProductTopology(m.v[vals])`,
which re-promotes). -/
def select {K : Nat} (m : ProductTopology N) (ks : Vector (Fin N) K) : ProductTopology K :=
  ofAxes (ks.map (m.axes[·]))

/-- `select` with 0-based axis positions given as naturals (an out-of-range position reads the
default axis `OneTo(0)`). -/
def selectIdx {K : Nat} (m : ProductTopology N) (ks : Vector Nat K) : ProductTopology K :=
  ofAxes (ks.map fun k => m.axes.toArray[k]?.getD (.oneTo 0))

/-- The axes other than `a`, ascending (Julia `exclude(m, Val(a))`, MT:183-190). -/
def exclude (m : ProductTopology N) (a : Fin N) : ProductTopology (N - 1) :=
  ofAxes (m.axes.eraseIdx a.1)

/-- Julia `exclude(m, Val(a₁), …)` for any set of axes (MT:191-202): the remaining axes,
ascending. The result dimension is the number of kept axes. -/
def excludeMany (m : ProductTopology N) (ex : List Nat) : (K : Nat) × ProductTopology K :=
  let kept := (List.finRange N).filter fun k => !ex.contains (k.1 + 1)
  ⟨kept.length, m.select (Vector.ofFn fun i => kept[i.1])⟩

/-- Julia `a × b` (MT:204): concatenated axes. -/
def cross {M : Nat} (a : ProductTopology M) (b : ProductTopology N) : ProductTopology (M + N) :=
  ofAxes (a.axes ++ b.axes)

/-- Julia `a × v` for an integer vector or range axis (MT:205, 207). -/
def crossAxis (a : ProductTopology N) (v : AxisMap) : ProductTopology (N + 1) :=
  ofAxes (a.axes.push v)

/-- Julia `v × b` (MT:206, 208). -/
def axisCross (v : AxisMap) (b : ProductTopology N) : ProductTopology (1 + N) :=
  ofAxes (#v[v] ++ b.axes)

/-- Julia `(:)(min::Values, max::Values)` (MT:141): `ProductTopology(min[k]:max[k])`. -/
def colon (lo hi : Vector Int N) : ProductTopology N :=
  ofAxes (Vector.ofFn fun k => .unitRange lo[k] hi[k])

/-- Julia `(:)(min, step, max)` on `Values` (MT:142). -/
def colonStep (lo st hi : Vector Int N) : ProductTopology N :=
  ofAxes (Vector.ofFn fun k => AxisMap.stepRange' lo[k] st[k] hi[k])

end ProductTopology

/-! ## Julia array printing -/

/-- Julia `print` of a `Values{N,Int}` / `Vector{Int}`: `[a, b, c]`. -/
def showInts (v : List Int) : String := "[" ++ ", ".intercalate (v.map toString) ++ "]"

/-- Julia's `size` string of an array summary: `3×4`, `5-element`, `0-dimensional`. -/
def dimsString (dims : List Nat) : String :=
  match dims with
  | [] => "0-dimensional"
  | [n] => s!"{n}-element"
  | ds => "×".intercalate (ds.map toString)

/-- Body of Julia's compact `show` of an N-D array (`[a b; c d;;; …]`), from the entries'
strings in column-major order. -/
partial def showArrayBody (dims : List Nat) (elems : Array String) : String :=
  match dims with
  | [] => elems[0]?.getD ""
  | [_] => ", ".intercalate elems.toList
  | [r, c] =>
    "; ".intercalate ((List.range r).map fun i =>
      " ".intercalate ((List.range c).map fun j => elems[i + j * r]!))
  | ds =>
    let d := ds.length
    let last := ds.getLast!
    let inner := ds.dropLast
    let stride := inner.foldl (· * ·) 1
    let sep := String.ofList (List.replicate d ';') ++ " "
    sep.intercalate ((List.range last).map fun k =>
      showArrayBody inner (elems.extract (k * stride) ((k + 1) * stride)))

namespace ProductTopology

variable {N : Nat}

/-- Julia `summary(m)`: `3×4 ProductTopology{2, Base.OneTo{Int64}}`. -/
def summary (m : ProductTopology N) : String :=
  s!"{dimsString m.size.toList} {m.typeString}"

/-- Julia `show(io, m)` (MT:139): `Values(first.(v)):Values(last.(v))` when every axis is an
`AbstractRange`, and Julia's compact array printing otherwise. -/
def showString (m : ProductTopology N) : String :=
  if m.axes.toList.all (·.kind.isIntRange) then
    showInts (m.axes.toList.map (·.first)) ++ ":" ++ showInts (m.axes.toList.map (·.last))
  else
    s!"Values\{{N}, Int64}[" ++
      showArrayBody m.size.toList (m.toArray.map (showInts ·.toList)) ++ "]"

instance : ToString (ProductTopology N) := ⟨showString⟩

end ProductTopology

end MeshTopology
