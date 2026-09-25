import AbstractAnalysis.Show

/-!
# Finite magmas and groups

Julia's `Semimagma{T,F,G}` (src/magma.jl) is an insertion-ordered vector of
elements whose group law `F` and inverse `G` are *type parameters holding
function instances*. The Lean port keeps that design literally: the law is a
value in the type, `Semimagma T L`, so `compose G H` only typechecks when both
sides carry the same law, which is Julia's `Semimagma{T,X,Y}`/`Semimagma{S,X,Y}`
constraint.

Membership uses Julia's `gequal = ≈` (`ApproxEq`): exact equality on exact
types, `isapprox` (`rtol = √eps`) on floats.

Julia defects are reproduced under `Julia.*` for the oracle and fixed in the
clean API (Appendix A of the port notes):
* `Julia.center` returns a greedy commuting subset (#14); `center` is correct.
* `Julia.leftCosets`/`rightCosets` deduplicate by *ordered* comparison (#15);
  the clean versions compare cosets as sets.
* `Julia.isCyclic` only tries the first two generators (#16).
* `ismonoid`/`iscategory` are broken in Julia (#17); `isMonoid` takes the
  identity explicitly.
-/

namespace AbstractAnalysis

open JuliaBase

/-- Julia's `gequal(a, b) = a ≈ b` with default tolerances. -/
class ApproxEq (α : Type) where
  /-- Julia `a ≈ b`. -/
  approx : α → α → Bool

instance : ApproxEq Int := ⟨(· == ·)⟩
instance : ApproxEq Nat := ⟨(· == ·)⟩
instance : ApproxEq Rat := ⟨(· == ·)⟩
instance : ApproxEq Float := ⟨fun x y => F64.isapprox x y⟩
instance : ApproxEq (Complex Int) := ⟨(· == ·)⟩
instance : ApproxEq (Complex Rat) := ⟨(· == ·)⟩
/-- Julia `isapprox(::ComplexF64, ::ComplexF64)`: `|x-y| ≤ rtol·max(|x|, |y|)` with `abs = hypot`. -/
instance : ApproxEq (Complex Float) := ⟨fun x y => ComplexF64.isapprox x y⟩

/-- Julia `gequal` on residues: exact equality (Julia's ModsExt, `src/AbstractAnalysis.jl`). -/
instance {n : Nat} : ApproxEq (Fin n) := ⟨(· == ·)⟩

/-- Julia `iseven`/`isodd` on the elements of a semimagma (numbers, permutations). -/
class HasParity (α : Type) where
  /-- Julia `iseven(x)`. -/
  isEven : α → Bool

instance : HasParity Int := ⟨fun n => n % 2 == 0⟩
instance : HasParity Nat := ⟨fun n => n % 2 == 0⟩

/-- A binary law with its inverse: Julia's `F` and `G` type parameters. -/
structure Law (T : Type) where
  /-- Julia `grouplaw(G)`. -/
  op : T → T → T
  /-- Julia `groupinverse(G)`. -/
  inv : T → T

/-- Julia `Semimagma(v, *)`: multiplication with `inv`. -/
def Law.mul (T : Type) [Mul T] (inv : T → T) : Law T := ⟨(· * ·), inv⟩

/-- Julia `Semimagma(v, +)`: addition with `-`. -/
def Law.add (T : Type) [Add T] [Neg T] : Law T := ⟨(· + ·), (- ·)⟩

/-- Addition modulo `n` on residues (Julia's ModsExt `+` on `Mod{n}`), inverse `n - a`. -/
def Law.addMod (n : Nat) : Law (Fin (n + 1)) := ⟨(· + ·), (- ·)⟩

/-- The inverse of a unit modulo `m` (`a` itself for a non-unit, where Julia's `inv` throws). -/
def invMod (m a : Nat) : Nat :=
  if Nat.gcd a m != 1 || m ≤ 1 then a
  else ((egcd (a % m) m 1 0 m).emod m).toNat
where
  /-- Extended Euclid on `(r₀, r₁)` tracking the Bézout coefficient `s₀` with
  `s₀ * a ≡ r₀ (mod m)` (fuel-bounded). -/
  egcd (r₀ r₁ : Nat) (s₀ s₁ : Int) : Nat → Int
    | 0 => s₀
    | fuel + 1 =>
      if r₁ = 0 then s₀
      else egcd r₁ (r₀ % r₁) s₁ (s₀ - (r₀ / r₁ : Nat) * s₁) fuel

/-- Multiplication modulo `n` on residues (Julia's ModsExt `*` on `Mod{n}`), the inverse
defined on units. -/
def Law.mulMod (n : Nat) : Law (Fin (n + 1)) :=
  ⟨(· * ·), fun a => ⟨invMod (n + 1) a.1 % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩⟩

/-- Julia `Semimagma{T,F,G}`: insertion-ordered elements under the law `L`. -/
structure Semimagma (T : Type) (L : Law T) where
  /-- The elements, in order (duplicates allowed, as in Julia). -/
  v : Array T

namespace Semimagma

variable {T : Type} {L : Law T}

/-- A bound on closure loops (every loop also stops when it runs off the end). -/
def closureBound : Nat := 1 <<< 24

/-- Julia `G(a, b) = F(a, b)`. -/
@[inline] def law (_ : Semimagma T L) (a b : T) : T := L.op a b

/-- Julia `order(G) = length(G)`. -/
@[inline] def order (G : Semimagma T L) : Nat := G.v.size

/-- Julia `g ∈ G` (linear scan with `≈`). -/
def mem [ApproxEq T] (g : T) (G : Semimagma T L) : Bool := G.v.toList.any (ApproxEq.approx g)

/-- Push unless already present (the `gh ∉ out && push!(out.v, gh)` idiom). -/
@[inline] def pushNew [ApproxEq T] (out : Array T) (g : T) : Array T :=
  if out.toList.any (ApproxEq.approx g) then out else out.push g

/-- Julia `H ⊆ G`. -/
def subset [ApproxEq T] (H G : Semimagma T L) : Bool := H.v.toList.all fun h => mem h G

/-- Julia `G == H`: mutual inclusion (set equality, order ignored). -/
def setEq [ApproxEq T] (G H : Semimagma T L) : Bool := subset G H && subset H G

instance [ApproxEq T] : BEq (Semimagma T L) := ⟨setEq⟩

/-- Julia `≈` on semimagmas (as `AbstractVector`s): **ordered** elementwise
comparison of equal-length vectors. This is what makes cosets dedup by order. -/
instance [ApproxEq T] : ApproxEq (Semimagma T L) :=
  ⟨fun a b => a.v.size == b.v.size && (a.v.toList.zip b.v.toList).all fun (x, y) => ApproxEq.approx x y⟩

/-- Julia `compose(g, H, F)`: left translate, keeping order and duplicates. -/
def composeLeft (g : T) (H : Semimagma T L) (F : T → T → T := L.op) : Semimagma T L := ⟨H.v.map (F g)⟩

/-- Julia `compose(H, g, F)`: right translate. -/
def composeRight (H : Semimagma T L) (g : T) (F : T → T → T := L.op) : Semimagma T L := ⟨H.v.map (F · g)⟩

/-- Julia `compose(G, H, F)`: all products `F(g, h)`, `g` outer, deduplicated in
first-seen order (src/magma.jl:74-83). -/
def compose [ApproxEq T] (G H : Semimagma T L) (F : T → T → T := L.op) : Semimagma T L :=
  ⟨G.v.foldl (fun out g => H.v.foldl (fun out h => pushNew out (F g h)) out) #[]⟩

/-- Julia `cayley(G)`: the table `M[i, j] = G(v[i], v[j])` (rows). -/
def cayley (G : Semimagma T L) : Array (Array T) := G.v.map fun g => G.v.map (L.op g)

/-- Julia `isassociative(G)`: the `O(n³)` check with `≈`. -/
def isAssociative [ApproxEq T] (G : Semimagma T L) : Bool :=
  G.v.toList.all fun f => G.v.toList.all fun g => G.v.toList.all fun h =>
    ApproxEq.approx (L.op (L.op f g) h) (L.op f (L.op g h))

/-- Julia `ismagma(G)`: closure under the law. -/
def isMagma [ApproxEq T] (G : Semimagma T L) : Bool :=
  G.v.toList.all fun g => G.v.toList.all fun h => mem (L.op g h) G

/-- Julia `isinvertible(G)`: every inverse is present. -/
def isInvertible [ApproxEq T] (G : Semimagma T L) : Bool := G.v.toList.all fun g => mem (L.inv g) G

/-- Julia `issemigroup = ismagma && isassociative` (also `issemicategory`). -/
def isSemigroup [ApproxEq T] (G : Semimagma T L) : Bool := isMagma G && isAssociative G

/-- Julia `isgroup = isinvertible && issemigroup` (also `isgroupoid`). -/
def isGroup [ApproxEq T] (G : Semimagma T L) : Bool := isInvertible G && isSemigroup G

/-- Julia `issemicategory = issemigroup` (src/magma.jl:114). -/
def isSemicategory [ApproxEq T] (G : Semimagma T L) : Bool := isSemigroup G

/-- Julia `isgroupoid = isgroup` (src/magma.jl:113). -/
def isGroupoid [ApproxEq T] (G : Semimagma T L) : Bool := isGroup G

/-- Julia `iscategory(G) = isone(G) ∈ G && issemicategory(G)` (src/magma.jl:111, broken in
Julia, quirk #17): the identity `e` is given explicitly. -/
def isCategory [ApproxEq T] (G : Semimagma T L) (e : T) : Bool := mem e G && isSemicategory G

/-- Julia `iseven(G) = prod(iseven.(G.v))` (src/magma.jl:52): every element is even. -/
def isEven [HasParity T] (G : Semimagma T L) : Bool := G.v.all HasParity.isEven

/-- Julia `isodd(G) = prod(isodd.(G.v))` (src/magma.jl:53): every element is odd. -/
def isOdd [HasParity T] (G : Semimagma T L) : Bool := G.v.all fun g => !HasParity.isEven g

/-- `ismonoid` as intended (Julia's is broken, quirk #17): the identity `e` is
present and the magma is a semigroup. -/
def isMonoid [ApproxEq T] (G : Semimagma T L) (e : T) : Bool := mem e G && isSemigroup G

/-- Julia `isabelian(G)`: all pairs commute. -/
def isAbelian [ApproxEq T] (G : Semimagma T L) : Bool :=
  G.v.toList.all fun g => G.v.toList.all fun h => ApproxEq.approx (L.op g h) (L.op h g)

/-- Julia `magma(p, F, G)`: the cyclic semimagma `[p, p², p³, …]` until a repeat
(src/magma.jl:152-161). -/
def cyclic [ApproxEq T] (p : T) : Semimagma T L :=
  ⟨go #[p] (L.op p p) closureBound⟩
where
  /-- Keep multiplying by `p` until a power repeats. -/
  go (out : Array T) (pn : T) : Nat → Array T
    | 0 => out
    | fuel + 1 => if out.toList.any (ApproxEq.approx pn) then out else go (out.push pn) (L.op pn p) fuel

/-- Julia `magma(G, out)`: close `out` under the law, appending new products in
Julia's order (src/magma.jl:165-178). -/
def closeArray [ApproxEq T] (out : Array T) : Array T :=
  outer out 0 closureBound
where
  /-- Products `out[i] * out[j]` for the current `j` range. -/
  inner (out : Array T) (g : T) (j : Nat) : Nat → Array T
    | 0 => out
    | fuel + 1 => if h : j < out.size then inner (pushNew out (L.op g out[j])) g (j + 1) fuel else out
  /-- Row loop. -/
  outer (out : Array T) (i : Nat) : Nat → Array T
    | 0 => out
    | fuel + 1 => if h : i < out.size then outer (inner out out[i] 0 closureBound) (i + 1) fuel else out

/-- Julia `magma(G)` / `magma(p::AbstractVector)`: the closure. -/
def magma [ApproxEq T] (G : Semimagma T L) : Semimagma T L := ⟨closeArray (L := L) G.v⟩

/-- Julia `group(G, out)`: add the inverses of the initial elements, then close
(src/magma.jl:179-186). -/
def groupOf [ApproxEq T] (out : Array T) : Array T :=
  closeArray (L := L) (out.foldl (fun acc g => pushNew acc (L.inv g)) out)

/-- Julia `group(p::AbstractVector, F, G)`: the group generated by `p`. -/
def group [ApproxEq T] (gens : Array T) : Semimagma T L := ⟨groupOf (L := L) gens⟩

/-- Julia `orders(G) = order.(G, F, G⁻¹)` (src/magma.jl:48): for each element, the order of
the group it generates. Julia's version only works for scalar elements: a permutation is an
`AbstractVector`, so `order(p, *, inv)` builds `group(p.v, …)` from its image entries and
throws; this computes the intended orders for every element type. -/
def orders [ApproxEq T] (G : Semimagma T L) : Array Nat := G.v.map fun g => (group (L := L) #[g]).order

/-- Julia `g * H` / `g + H` for an element or number (`compose(g, H, *)`, src/magma.jl:90-98):
the plain operation, not the law. -/
instance [Mul T] : HMul T (Semimagma T L) (Semimagma T L) := ⟨fun g H => composeLeft g H (· * ·)⟩
/-- Julia `H * g`. -/
instance [Mul T] : HMul (Semimagma T L) T (Semimagma T L) := ⟨fun H g => composeRight H g (· * ·)⟩
/-- Julia `g + H`. -/
instance [Add T] : HAdd T (Semimagma T L) (Semimagma T L) := ⟨fun g H => composeLeft g H (· + ·)⟩
/-- Julia `H + g`. -/
instance [Add T] : HAdd (Semimagma T L) T (Semimagma T L) := ⟨fun H g => composeRight H g (· + ·)⟩

/-- Julia `subsemigroup(G, out)`: drop elements with no product back in the set
(src/magma.jl:194-209). -/
def subsemigroup [ApproxEq T] (out : Array T) : Array T :=
  go out 0 closureBound
where
  /-- Deleting scan. -/
  go (out : Array T) (i : Nat) : Nat → Array T
    | 0 => out
    | fuel + 1 =>
      if h : i < out.size then
        let g := out[i]
        if out.any fun x => out.any (ApproxEq.approx (L.op g x)) then go out (i + 1) fuel
        else go (out.eraseIdx i) i fuel
      else out

/-- Julia `subgroup(G, out)`: keep elements whose inverse is present, then
`subsemigroup` (src/magma.jl:211-225). -/
def subgroup [ApproxEq T] (G : Semimagma T L) (out : Array T := G.v) : Semimagma T L :=
  ⟨subsemigroup (L := L) (go out 0 closureBound)⟩
where
  /-- Deleting scan. -/
  go (out : Array T) (i : Nat) : Nat → Array T
    | 0 => out
    | fuel + 1 =>
      if h : i < out.size then
        if out.any (ApproxEq.approx (L.inv out[i])) then go out (i + 1) fuel else go (out.eraseIdx i) i fuel
      else out

/-- Julia `issubgroup(H, G) = H ⊆ G && isgroup(H)`. -/
def isSubgroup [ApproxEq T] (H G : Semimagma T L) : Bool := subset H G && isGroup H

/-- Julia `centralizer(H, G)`: the `g ∈ G` commuting with all of `H`. -/
def centralizer [ApproxEq T] (H G : Semimagma T L) : Semimagma T L :=
  ⟨G.v.filter fun g => H.v.toList.all fun h => ApproxEq.approx (L.op g h) (L.op h g)⟩

/-- The center `Z(G) = centralizer(G, G)` (the definition Julia comments out). -/
def center [ApproxEq T] (G : Semimagma T L) : Semimagma T L := centralizer G G

/-- Julia `isnormal(H, G)`: `gH = Hg` (as sets) for every `g`. -/
def isNormal [ApproxEq T] (H G : Semimagma T L) : Bool :=
  G.v.toList.all fun g => setEq (composeLeft g H) (composeRight H g)

/-- Julia `normalizer(H, G)`: the `g` with `gH = Hg`. -/
def normalizer [ApproxEq T] (H G : Semimagma T L) : Semimagma T L :=
  ⟨G.v.filter fun g => setEq (composeLeft g H) (composeRight H g)⟩

/-- Julia `commutator(G, H)`: the group generated by `g⁻¹h⁻¹gh`
(src/magma.jl:302-311). -/
def commutator [ApproxEq T] (G H : Semimagma T L) : Semimagma T L :=
  let out := G.v.foldl (fun out g => H.v.foldl
    (fun out h => pushNew out (L.op (L.op (L.inv g) (L.inv h)) (L.op g h))) out) #[]
  ⟨groupOf (L := L) out⟩

/-- Left cosets `gH`, deduplicated as **sets** (the intended quotient). -/
def leftCosets [ApproxEq T] (H G : Semimagma T L) : Array (Semimagma T L) :=
  G.v.foldl (fun out g => let gH := composeLeft g H; if out.any (setEq gH) then out else out.push gH) #[]

/-- Right cosets `Hg`, deduplicated as sets. -/
def rightCosets [ApproxEq T] (H G : Semimagma T L) : Array (Semimagma T L) :=
  G.v.foldl (fun out g => let Hg := composeRight H g; if out.any (setEq Hg) then out else out.push Hg) #[]

/-- Julia `iscyclic` as intended: some element generates the whole set. -/
def isCyclic [ApproxEq T] (G : Semimagma T L) : Bool :=
  G.v.toList.any fun g => setEq G (cyclic g)

/-- Display as Julia's vector `show`: `[a, b, c]`. -/
instance [JuliaRepr T] : JuliaRepr (Semimagma T L) := ⟨fun G => JuliaRepr.repr G.v, fun G => JuliaRepr.repr G.v, false⟩

end Semimagma

namespace Julia

variable {T : Type} {L : Law T}

/-- Julia `center(G)` as written (**quirk #14**): for each surviving `g` it
deletes the elements not commuting with `g`, yielding a greedy commuting
subset (`[id, (1,3,2)]` for `S₃`), src/magma.jl:240-258. -/
def center [ApproxEq T] (G : Semimagma T L) : Semimagma T L :=
  ⟨outer G.v 0 Semimagma.closureBound⟩
where
  /-- Inner deleting scan with Julia's `j < i && (i -= 1)` adjustment. -/
  inner (g : T) (out : Array T) (i j : Nat) : Nat → Array T × Nat
    | 0 => (out, i)
    | fuel + 1 =>
      if h : j < out.size then
        let x := out[j]
        if ApproxEq.approx (L.op g x) (L.op x g) then inner g out i (j + 1) fuel
        else inner g (out.eraseIdx j) (if j < i then i - 1 else i) j fuel
      else (out, i)
  /-- Outer loop over the surviving elements. -/
  outer (out : Array T) (i : Nat) : Nat → Array T
    | 0 => out
    | fuel + 1 =>
      if h : i < out.size then
        let (out', i') := inner out[i] out i 0 Semimagma.closureBound
        outer out' (i' + 1) fuel
      else out

/-- Julia `leftcosets(H, G)` as written (**quirk #15**): `gH` is pushed unless an
*ordered-equal* coset is already present (src/magma.jl:315-322). -/
def leftCosets [ApproxEq T] (H G : Semimagma T L) : Array (Semimagma T L) :=
  G.v.foldl (fun out g => Semimagma.pushNew out (Semimagma.composeLeft g H)) #[]

/-- Julia `rightcosets(H, G)` as written (ordered dedup). -/
def rightCosets [ApproxEq T] (H G : Semimagma T L) : Array (Semimagma T L) :=
  G.v.foldl (fun out g => Semimagma.pushNew out (Semimagma.composeRight H g)) #[]

/-- Julia `G / N = leftcosets(N, G)`. -/
def quotient [ApproxEq T] (G N : Semimagma T L) : Array (Semimagma T L) := leftCosets N G

/-- Julia `iscyclic(G)` as written (**quirk #16**): only `G[1]` and `G[2]` are
tried as generators. -/
def isCyclic [ApproxEq T] (G : Semimagma T L) : Bool :=
  (G.v[0]?.map fun g => Semimagma.setEq G (Semimagma.cyclic g)).getD false ||
  (G.v[1]?.map fun g => Semimagma.setEq G (Semimagma.cyclic g)).getD false

end Julia

/-- Julia `unityroots(n) = Semimagma(cis.(2π/n .* (0:n-1)))` under `*`/`inv`. -/
def unityRoots (n : Nat) : Semimagma (Complex Float) (Law.mul (Complex Float) Complex.conj) :=
  let θ := 2 * 3.141592653589793 / Float.ofNat n
  ⟨(List.range n).toArray.map fun k => cis (θ * Float.ofNat k)⟩

/-- The inverse on Gaussian units (`inv(z) = conj(z)/|z|²`, exact for units),
standing in for Julia's `inv(::Complex{Int})`, which returns a float. -/
def gaussianInvUnit (z : Complex Int) : Complex Int :=
  let n := z.re * z.re + z.im * z.im
  ⟨z.re / n, -z.im / n⟩

/-- Julia `magma(Complex(0, 1))`-style law on Gaussian integers. -/
abbrev Law.gaussian : Law (Complex Int) := Law.mul (Complex Int) gaussianInvUnit

end AbstractAnalysis
