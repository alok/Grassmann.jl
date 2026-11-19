/-
Minimal pure-`Init` open-addressing hash map for process-global memoization caches
(`DirectSum.BladeAlgebra.mulTableCache`, `Grassmann.Kernel.planCache`).

Replaces `Std.Data.HashMap` on the core runtime path so `DirectSum.Core`,
`Grassmann.Kernel.Runtime`, `Grassmann.Projective`, `Grassmann.Conformal`, and
`Grassmann.Kernel.Generated.*` depend strictly on `Init` (zero `Std.*`, zero `Lean.*`).
-/
module

@[expose] public section

namespace DirectSum

/-- Compact power-of-two open-addressing hash map using only `Init` (`Array`, `BEq`, `Hashable`). -/
structure SmallMap (κ : Type) (β : Type) where
  /-- Backing slot array; length is always a power of two (`≥ 16`). -/
  slots : Array (Option (κ × β))
  /-- Number of occupied entries. -/
  size : Nat

namespace SmallMap

/-- Empty map with initial power-of-two capacity `cap` (default 16). -/
def empty {κ β : Type} (cap : Nat := 16) : SmallMap κ β :=
  let n := if cap < 16 then 16 else cap
  ⟨Array.replicate n none, 0⟩

instance {κ β : Type} : EmptyCollection (SmallMap κ β) := ⟨SmallMap.empty⟩
instance {κ β : Type} : Inhabited (SmallMap κ β) := ⟨SmallMap.empty⟩

/-- Linear-probing lookup loop bounded by remaining steps `rem`. -/
def getLoop {κ β : Type} [BEq κ] (slots : Array (Option (κ × β))) (mask : Nat) (k : κ)
    (idx : Nat) : Nat → Option β
  | 0 => none
  | rem + 1 =>
    match slots[idx]! with
    | none => none
    | some (k', v) =>
      if k' == k then some v
      else getLoop slots mask k ((idx + 1) &&& mask) rem

/-- Look up key `k` in `O(1)` expected time. -/
@[inline] def get? {κ β : Type} [BEq κ] [Hashable κ] (m : SmallMap κ β) (k : κ) : Option β :=
  let n := m.slots.size
  if n == 0 then none
  else
    let mask := n - 1
    let idx := (hash k).toNat &&& mask
    getLoop m.slots mask k idx n

/-- Linear-probing insertion into `slots`, returning `(newSlots, insertedNew?)`. -/
def putLoop {κ β : Type} [BEq κ] (slots : Array (Option (κ × β))) (mask : Nat) (k : κ) (v : β)
    (idx : Nat) : Nat → Array (Option (κ × β)) × Bool
  | 0 => (slots, false)
  | rem + 1 =>
    match slots[idx]! with
    | none => (slots.set! idx (some (k, v)), true)
    | some (k', _) =>
      if k' == k then (slots.set! idx (some (k, v)), false)
      else putLoop slots mask k v ((idx + 1) &&& mask) rem

/-- Rehash all entries from `src` into a fresh `dst` slot array of double capacity. -/
def rehashLoop {κ β : Type} [BEq κ] [Hashable κ] (src : Array (Option (κ × β))) (i : Nat)
    (dst : Array (Option (κ × β))) (mask : Nat) : Array (Option (κ × β)) :=
  if i < src.size then
    let dst := match src[i]! with
      | none => dst
      | some (k, v) =>
        let idx := (hash k).toNat &&& mask
        (putLoop dst mask k v idx dst.size).1
    rehashLoop src (i + 1) dst mask
  else dst
termination_by src.size - i

/-- Insert or update `k ↦ v`, doubling capacity when load exceeds 50%. -/
def insert {κ β : Type} [BEq κ] [Hashable κ] (m : SmallMap κ β) (k : κ) (v : β) : SmallMap κ β :=
  let cap := if m.slots.size < 16 then 16 else m.slots.size
  let slots := if m.slots.size < 16 then Array.replicate 16 none else m.slots
  let (slots, cap) :=
    if m.size * 2 ≥ cap then
      let newCap := cap * 2
      (rehashLoop slots 0 (Array.replicate newCap none) (newCap - 1), newCap)
    else (slots, cap)
  let mask := cap - 1
  let idx := (hash k).toNat &&& mask
  let (slots', isNew) := putLoop slots mask k v idx cap
  ⟨slots', if isNew then m.size + 1 else m.size⟩

end SmallMap

end DirectSum
