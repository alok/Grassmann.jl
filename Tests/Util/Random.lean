/-
Deterministic pseudo-random generation for property tests.

SplitMix64 (Steele, Lea, Flood 2014): a tiny, fast, statistically solid
generator whose whole state is one `UInt64`. Determinism matters more than
quality here: a failing property must reproduce from its printed seed.
-/

namespace Tests

/-- SplitMix64 generator state. -/
structure Rng where
  state : UInt64
  deriving Repr, Inhabited

namespace Rng

/-- Seed a generator. -/
def ofSeed (seed : Nat) : Rng := ⟨seed.toUInt64⟩

/-- Advance and return 64 random bits. -/
@[inline] def next (g : Rng) : UInt64 × Rng :=
  let s := g.state + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

/-- Uniform float in `[0, 1)` from the top 53 bits. -/
@[inline] def float (g : Rng) : Float × Rng :=
  let (u, g) := g.next
  ((u >>> 11).toFloat / 9007199254740992.0, g)

/-- Uniform float in `[lo, hi)`. -/
@[inline] def floatIn (g : Rng) (lo hi : Float) : Float × Rng :=
  let (u, g) := g.float
  (lo + (hi - lo) * u, g)

/-- Uniform natural number in `[0, n)` (for `n > 0`; returns 0 when `n = 0`). -/
@[inline] def nat (g : Rng) (n : Nat) : Nat × Rng :=
  let (u, g) := g.next
  (if n == 0 then 0 else u.toNat % n, g)

/-- Uniform integer in `[lo, hi]`. -/
@[inline] def int (g : Rng) (lo hi : Int) : Int × Rng :=
  let (k, g) := g.nat (hi - lo + 1).toNat
  (lo + k, g)

end Rng

/-- A state monad over `Rng` for writing generators compactly. -/
abbrev Gen := StateM Rng

namespace Gen

def float : Gen Float := modifyGet Rng.float
def floatIn (lo hi : Float) : Gen Float := modifyGet (·.floatIn lo hi)
def nat (n : Nat) : Gen Nat := modifyGet (·.nat n)
def int (lo hi : Int) : Gen Int := modifyGet (·.int lo hi)

/-- Run a generator from a seed. -/
def run {α : Type} (seed : Nat) (g : Gen α) : α := (StateT.run g (Rng.ofSeed seed)).1

/-- `n` independent draws. -/
def array {α : Type} (n : Nat) (g : Gen α) : Gen (Array α) := do
  let mut out := Array.mkEmpty n
  for _ in [0:n] do out := out.push (← g)
  return out

end Gen

end Tests
