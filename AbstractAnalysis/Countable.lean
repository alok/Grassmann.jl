import AbstractAnalysis.Show

/-!
# Countable containers

Julia's `CountableArray{T,N,F}` is a lazily evaluated array `x[i…] = f(i…)`
with a nominal (mutable) size; `FunctionArray` is a family `x ↦ f(x, i…)`
(AbstractAnalysis.jl src/AbstractAnalysis.jl:41-189).

Port decisions:
* The rank `N` is a type index (`CountableArray α N`, sizes in `Vector Nat N`),
  so pointwise operations only typecheck between arrays of equal rank, exactly
  Julia's `where N` constraint, at no runtime cost.
* `CountableVector` (rank 1, the common case) is its own structure with a
  `Nat → α` generator, so `x[i]` is a plain call.
* Julia's in-place `resize!` (which even mutates the global `Naturals`) becomes
  the pure `withLen`.
* Indices are **1-based**, like Julia: `x[i] = x.f i` for `i ≥ 1`.
-/

namespace AbstractAnalysis

/-- Julia `CountableVector{T,F}`: the sequence `f(1), f(2), …` with nominal
length `len` (Julia's default `100`). Reading past `len` is allowed, as in
Julia (there is no bounds check). -/
structure CountableVector (α : Type) where
  /-- The generator (Julia `counter(x)`), 1-based. -/
  f : Nat → α
  /-- Nominal length (Julia `length(x)`). -/
  len : Nat := 100

namespace CountableVector

variable {α β γ : Type}

/-- Julia `CountableVector(f, n)`. -/
@[inline] def mk' (f : Nat → α) (n : Nat := 100) : CountableVector α := ⟨f, n⟩

/-- 1-based element access, unchecked like Julia's `getindex`. -/
instance : GetElem (CountableVector α) Nat α (fun _ _ => True) where
  getElem x i _ := x.f i

/-- Julia `x[end]`. -/
@[inline] def last (x : CountableVector α) : α := x.f x.len

/-- Julia `x(n)` / `resize!(x, n)`: same generator, new length. -/
@[inline] def withLen (x : CountableVector α) (n : Nat) : CountableVector α := { x with len := n }

/-- Julia `collect(x)`: the first `len` terms. -/
def toArray (x : CountableVector α) : Array α := Id.run do
  let mut out := Array.mkEmpty x.len
  for i in [1:x.len + 1] do out := out.push (x.f i)
  return out

/-- Julia `x[a:b]` (materialized). -/
def slice (x : CountableVector α) (a b : Nat) : Array α := Id.run do
  let mut out := Array.mkEmpty (b + 1 - a)
  for i in [a:b + 1] do out := out.push (x.f i)
  return out

/-- Julia `map(f, x)`: lazy composition `f ∘ counter(x)`. -/
@[inline] def map (g : α → β) (x : CountableVector α) : CountableVector β := ⟨g ∘ x.f, x.len⟩

/-- Julia `binop(a, b, op)`: pointwise, length `min`. -/
@[inline] def zipWith (g : α → β → γ) (a : CountableVector α) (b : CountableVector β) :
    CountableVector γ := ⟨fun i => g (a.f i) (b.f i), min a.len b.len⟩

instance [Add α] : Add (CountableVector α) := ⟨zipWith (· + ·)⟩
instance [Sub α] : Sub (CountableVector α) := ⟨zipWith (· - ·)⟩
instance [Mul α] : Mul (CountableVector α) := ⟨zipWith (· * ·)⟩
instance [Div α] : Div (CountableVector α) := ⟨zipWith (· / ·)⟩
instance [Neg α] : Neg (CountableVector α) := ⟨map (- ·)⟩

/-- Julia `a + x` (scalar on the left): `map(Fix1(+, a), x)`. -/
instance [Add α] : HAdd α (CountableVector α) (CountableVector α) := ⟨fun a x => x.map (a + ·)⟩
/-- Julia `x + b`. -/
instance [Add α] : HAdd (CountableVector α) α (CountableVector α) := ⟨fun x b => x.map (· + b)⟩
/-- Julia `a - x`. -/
instance [Sub α] : HSub α (CountableVector α) (CountableVector α) := ⟨fun a x => x.map (a - ·)⟩
/-- Julia `x - b`. -/
instance [Sub α] : HSub (CountableVector α) α (CountableVector α) := ⟨fun x b => x.map (· - b)⟩
/-- Julia `a * x`. -/
instance [Mul α] : HMul α (CountableVector α) (CountableVector α) := ⟨fun a x => x.map (a * ·)⟩
/-- Julia `x * b`. -/
instance [Mul α] : HMul (CountableVector α) α (CountableVector α) := ⟨fun x b => x.map (· * b)⟩
/-- Julia `a / x`. -/
instance [Div α] : HDiv α (CountableVector α) (CountableVector α) := ⟨fun a x => x.map (a / ·)⟩
/-- Julia `x / b`. -/
instance [Div α] : HDiv (CountableVector α) α (CountableVector α) := ⟨fun x b => x.map (· / b)⟩
/-- Julia `x ^ p` (pointwise). -/
instance [HPow α β α] : HPow (CountableVector α) β (CountableVector α) := ⟨fun x p => x.map (· ^ p)⟩
/-- Julia `a ^ x` (`Base.:^(a::Number, x::CountableArray) = map(Fix1(^, a), x)`,
src/AbstractAnalysis.jl:103-109). -/
instance [HPow α α α] : HPow α (CountableVector α) (CountableVector α) := ⟨fun a x => x.map (a ^ ·)⟩
/-- Julia `x ^ y` for two countable vectors (pointwise, the shorter length). -/
instance [HPow α α α] : HPow (CountableVector α) (CountableVector α) (CountableVector α) :=
  ⟨zipWith (· ^ ·)⟩

/-- Julia `CountableVector(r::AbstractRange)`: `i ↦ x0 + h*(i-1)`
(src/AbstractAnalysis.jl:78-80). -/
def ofRange [Add α] [Mul α] [NatCast α] (x0 h : α) (n : Nat) : CountableVector α :=
  ⟨fun i => x0 + h * ((i - 1 : Nat) : α), n⟩

/-- Julia `residuals(x)` specialised to a countable sequence: the lazy sequence
`d(x[k+1], x[k])` of length `len - 1`. (Julia's generic method references an
undefined `d`; its special cases `Ones → Zeros`, `Naturals → Ones`,
`Integers → Naturals` agree with this definition.) -/
def residuals (x : CountableVector α) (d : α → α → Float) : CountableVector Float :=
  ⟨fun k => d (x.f (k + 1)) (x.f k), x.len - 1⟩

end CountableVector

/-- Julia `Ones(n)`: `CountableVector(one, n)`. -/
def Ones (n : Nat := 100) : CountableVector Int := ⟨fun _ => 1, n⟩
/-- Julia `Zeros(n)`: `CountableVector(zero, n)`. -/
def Zeros (n : Nat := 100) : CountableVector Int := ⟨fun _ => 0, n⟩
/-- Julia `Naturals(n)` (default length 100): `CountableVector(identity)`. -/
def Naturals (n : Nat := 100) : CountableVector Int := ⟨fun i => (i : Int), n⟩

/-- Julia `CountableArray{T,N,F}`: `x[i…] = f(i…)` over a nominal size. The rank
`N` is part of the type. -/
structure CountableArray (α : Type) (N : Nat) where
  /-- The generator on 1-based multi-indices. -/
  f : Vector Nat N → α
  /-- Nominal size (Julia `size(x)`). -/
  size : Vector Nat N

namespace CountableArray

variable {α β γ : Type} {N : Nat}

/-- Julia `x[i…]`. -/
@[inline] def get (x : CountableArray α N) (i : Vector Nat N) : α := x.f i

/-- Julia `map(f, x)`. -/
@[inline] def map (g : α → β) (x : CountableArray α N) : CountableArray β N := ⟨g ∘ x.f, x.size⟩

/-- Julia `binop` on arrays of the same rank: size is the pointwise `min`. -/
@[inline] def zipWith (g : α → β → γ) (a : CountableArray α N) (b : CountableArray β N) :
    CountableArray γ N :=
  ⟨fun i => g (a.f i) (b.f i), Vector.zipWith min a.size b.size⟩

instance [Add α] : Add (CountableArray α N) := ⟨zipWith (· + ·)⟩
instance [Mul α] : Mul (CountableArray α N) := ⟨zipWith (· * ·)⟩
instance [Sub α] : Sub (CountableArray α N) := ⟨zipWith (· - ·)⟩
/-- Julia `a / b` on arrays (src/AbstractAnalysis.jl:103-109). -/
instance [Div α] : Div (CountableArray α N) := ⟨zipWith (· / ·)⟩
/-- Julia `a ^ b` on arrays. -/
instance [HPow α α α] : HPow (CountableArray α N) (CountableArray α N) (CountableArray α N) :=
  ⟨zipWith (· ^ ·)⟩
/-- Julia `a ⊙ x` for a number `a` (`map(Fix1(⊙, a), x)`). -/
instance [Mul α] : HMul α (CountableArray α N) (CountableArray α N) := ⟨fun a x => x.map (a * ·)⟩
/-- Julia `x ⊙ b` for a number `b` (`map(Fix2(⊙, b), x)`). -/
instance [Mul α] : HMul (CountableArray α N) α (CountableArray α N) := ⟨fun x b => x.map (· * b)⟩
instance [Add α] : HAdd α (CountableArray α N) (CountableArray α N) := ⟨fun a x => x.map (a + ·)⟩
instance [Add α] : HAdd (CountableArray α N) α (CountableArray α N) := ⟨fun x b => x.map (· + b)⟩
instance [Sub α] : HSub α (CountableArray α N) (CountableArray α N) := ⟨fun a x => x.map (a - ·)⟩
instance [Sub α] : HSub (CountableArray α N) α (CountableArray α N) := ⟨fun x b => x.map (· - b)⟩
instance [Div α] : HDiv α (CountableArray α N) (CountableArray α N) := ⟨fun a x => x.map (a / ·)⟩
instance [Div α] : HDiv (CountableArray α N) α (CountableArray α N) := ⟨fun x b => x.map (· / b)⟩
instance [HPow α α α] : HPow α (CountableArray α N) (CountableArray α N) := ⟨fun a x => x.map (a ^ ·)⟩
instance [HPow α α α] : HPow (CountableArray α N) α (CountableArray α N) := ⟨fun x b => x.map (· ^ b)⟩

/-- View a vector as a rank-1 array. -/
def ofVector (x : CountableVector α) : CountableArray α 1 := ⟨fun i => x.f i[0], #v[x.len]⟩

/-- Julia `collect` of a rank-2 array (row-major list of rows, 1-based). -/
def toRows (x : CountableArray α 2) : Array (Array α) := Id.run do
  let mut rows := #[]
  for i in [1:x.size[0] + 1] do
    let mut row := #[]
    for j in [1:x.size[1] + 1] do row := row.push (x.f #v[i, j])
    rows := rows.push row
  return rows

end CountableArray

/-- Julia `countableproduct(x, y, op=*)`: `(i, j) ↦ op(x(i), y(j))`
(src/AbstractAnalysis.jl:126-128). -/
def countableProduct {α β γ : Type} (x : CountableVector α) (y : CountableVector β) (op : α → β → γ) :
    CountableArray γ 2 :=
  ⟨fun i => op (x.f i[0]) (y.f i[1]), #v[x.len, y.len]⟩

/-- Julia `countableproduct(x, y, z, op)`: rank 3. -/
def countableProduct3 {α β γ δ : Type} (x : CountableVector α) (y : CountableVector β)
    (z : CountableVector γ) (op : α → β → γ → δ) : CountableArray δ 3 :=
  ⟨fun i => op (x.f i[0]) (y.f i[1]) (z.f i[2]), #v[x.len, y.len, z.len]⟩

/-- Julia `countabletuple(x, y)`. -/
def countableTuple {α β : Type} (x : CountableVector α) (y : CountableVector β) : CountableArray (α × β) 2 :=
  countableProduct x y Prod.mk

/-- Julia `CountableArray(n, m)`: the grid of index tuples. -/
def CountableArray.grid (n m : Nat) : CountableArray (Int × Int) 2 := countableTuple (Naturals n) (Naturals m)

/-- Julia `CountableArray(n...)` of any rank: the grid of index tuples, `x[i…] = (i…)`. -/
def CountableArray.gridN {N : Nat} (size : Vector Nat N) : CountableArray (Vector Nat N) N := ⟨id, size⟩

/-- Julia `FunctionVector{T,F}`: a family `x ↦ f(x, i)` indexed by `i ≥ 1`
(src/AbstractAnalysis.jl:133-167). -/
structure FunctionVector (β α : Type) where
  /-- Julia `counter(x)`: `f(x, i)`. -/
  f : β → Nat → α
  /-- Nominal length. -/
  len : Nat := 100

namespace FunctionVector

variable {α β γ : Type}

/-- Julia `x[i] = Fix2(f, i)`: the `i`-th function. -/
@[inline] def term (x : FunctionVector β α) (i : Nat) : β → α := fun u => x.f u i

/-- Julia `(x::FunctionArray)(u)`: the countable sequence `i ↦ f(u, i)`. -/
@[inline] def eval (x : FunctionVector β α) (u : β) : CountableVector α := ⟨x.f u, x.len⟩

/-- Julia `resize!`/`x(n)`. -/
@[inline] def withLen (x : FunctionVector β α) (n : Nat) : FunctionVector β α := { x with len := n }

/-- Julia `map(f, x) = FunctionArray(f ∘ counter(x))`. -/
@[inline] def map (g : α → γ) (x : FunctionVector β α) : FunctionVector β γ := ⟨fun u i => g (x.f u i), x.len⟩

/-- Julia pointwise `binop` on function families. -/
@[inline] def zipWith (g : α → α → γ) (a b : FunctionVector β α) : FunctionVector β γ :=
  ⟨fun u i => g (a.f u i) (b.f u i), min a.len b.len⟩

instance [Add α] : Add (FunctionVector β α) := ⟨zipWith (· + ·)⟩
instance [Mul α] : Mul (FunctionVector β α) := ⟨zipWith (· * ·)⟩
instance [Mul α] : HMul α (FunctionVector β α) (FunctionVector β α) := ⟨fun a x => x.map (a * ·)⟩
/-- Julia `a - b` of function families (src/AbstractAnalysis.jl:169-175). -/
instance [Sub α] : Sub (FunctionVector β α) := ⟨zipWith (· - ·)⟩
/-- Julia `a / b` of function families. -/
instance [Div α] : Div (FunctionVector β α) := ⟨zipWith (· / ·)⟩
/-- Julia `a ^ b` of function families. -/
instance [HPow α α α] : HPow (FunctionVector β α) (FunctionVector β α) (FunctionVector β α) :=
  ⟨zipWith (· ^ ·)⟩
instance [Mul α] : HMul (FunctionVector β α) α (FunctionVector β α) := ⟨fun x b => x.map (· * b)⟩
instance [Add α] : HAdd α (FunctionVector β α) (FunctionVector β α) := ⟨fun a x => x.map (a + ·)⟩
instance [Add α] : HAdd (FunctionVector β α) α (FunctionVector β α) := ⟨fun x b => x.map (· + b)⟩
instance [Sub α] : HSub α (FunctionVector β α) (FunctionVector β α) := ⟨fun a x => x.map (a - ·)⟩
instance [Sub α] : HSub (FunctionVector β α) α (FunctionVector β α) := ⟨fun x b => x.map (· - b)⟩
instance [Div α] : HDiv α (FunctionVector β α) (FunctionVector β α) := ⟨fun a x => x.map (a / ·)⟩
instance [Div α] : HDiv (FunctionVector β α) α (FunctionVector β α) := ⟨fun x b => x.map (· / b)⟩
instance [HPow α α α] : HPow α (FunctionVector β α) (FunctionVector β α) := ⟨fun a x => x.map (a ^ ·)⟩
instance [HPow α α α] : HPow (FunctionVector β α) α (FunctionVector β α) := ⟨fun x b => x.map (· ^ b)⟩

end FunctionVector

/-- Julia `FunctionArray(n)` with the default family `^`: `x ↦ x^i`. -/
def FunctionVector.powers (n : Nat := 100) : FunctionVector Float Float :=
  ⟨fun x i => x ^ (Float.ofNat i), n⟩

/-- Julia `Series{N,C,F}`: coefficients against a function family; `Series(f)`
has `Ones` coefficients (src/AbstractAnalysis.jl:191-212). -/
structure Series (β α : Type) where
  /-- Coefficients (`none` = Julia's `Ones`, which `dot` short-circuits). -/
  coeffs : Option (CountableVector α) := none
  /-- The function family. -/
  family : FunctionVector β α

/-- Julia `Product{N,F}`: `prod(f::FunctionArray)` (src/AbstractAnalysis.jl:214-226). -/
structure Product (β α : Type) where
  /-- The function family. -/
  family : FunctionVector β α

/-- Julia `FunctionArray{T,N}` of any rank: a family `x ↦ f(x, i…)` indexed by 1-based
multi-indices over a nominal size (src/AbstractAnalysis.jl:133-167). Julia's
`FunctionMatrix{T}(f, n, m)` builds its size from `n` twice (quirk #24); `FunctionMatrix` here
takes both. -/
structure FunctionArray (β α : Type) (N : Nat) where
  /-- Julia `counter(x)`: `f(x, i…)`. -/
  f : β → Vector Nat N → α
  /-- Nominal size. -/
  size : Vector Nat N

/-- Julia `FunctionMatrix` = rank-2 `FunctionArray`. -/
abbrev FunctionMatrix (β α : Type) := FunctionArray β α 2

namespace FunctionArray

variable {α β γ : Type} {N : Nat}

/-- Julia `(x::FunctionArray)(u)`: the countable array `i… ↦ f(u, i…)`. -/
@[inline] def eval (x : FunctionArray β α N) (u : β) : CountableArray α N := ⟨x.f u, x.size⟩

/-- Julia `x[i…] = Fix2(f, i…)`: the function at a multi-index. -/
@[inline] def term (x : FunctionArray β α N) (i : Vector Nat N) : β → α := fun u => x.f u i

/-- Julia `map(f, x)`. -/
@[inline] def map (g : α → γ) (x : FunctionArray β α N) : FunctionArray β γ N :=
  ⟨fun u i => g (x.f u i), x.size⟩

/-- Julia pointwise `binop`: the size is the pointwise `min`. -/
@[inline] def zipWith (g : α → α → γ) (a b : FunctionArray β α N) : FunctionArray β γ N :=
  ⟨fun u i => g (a.f u i) (b.f u i), Vector.zipWith min a.size b.size⟩

/-- A rank-1 family as a `FunctionArray`. -/
def ofVector (x : FunctionVector β α) : FunctionArray β α 1 := ⟨fun u i => x.f u i[0], #v[x.len]⟩

instance [Add α] : Add (FunctionArray β α N) := ⟨zipWith (· + ·)⟩
instance [Sub α] : Sub (FunctionArray β α N) := ⟨zipWith (· - ·)⟩
instance [Mul α] : Mul (FunctionArray β α N) := ⟨zipWith (· * ·)⟩
instance [Div α] : Div (FunctionArray β α N) := ⟨zipWith (· / ·)⟩
instance [Mul α] : HMul α (FunctionArray β α N) (FunctionArray β α N) := ⟨fun a x => x.map (a * ·)⟩

end FunctionArray

end AbstractAnalysis
