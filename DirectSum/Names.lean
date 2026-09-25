/-
Blade lookup by name: Julia `Λ(V).v12`, `Λ(V).v21`, `Λ(62).v32a87Ng`
(`DirectSum.jl src/basis.jl:134-181, 429-458`, `Leibniz.jl src/indices.jl:230-247`).

An exact label (`labels(V)`, e.g. `v∞∅1`, `∂1v2`) resolves directly. Otherwise
the name is read as blocks `v…`, `w…`, `∂…`, `ϵ…` of index characters
(`alphanumv` for `v`/`∂`, `alphanumw` for `w`/`ϵ`; `∞`/`∅` in `v`/`w` blocks),
each index is mapped to its generator, and the generators are multiplied left
to right with the geometric product. This gives the mathematically correct
sign for permutations *and* repeated indices; Julia's `indexparity!` flips the
sign of repeated *positive* generators through `Λ(V)`, does not back up after a
cancellation and throws on out-of-order or `w`-first names (quirk Q16).
-/
import DirectSum.BladeAlgebra

namespace DirectSum

open Bits

namespace TensorBundle

variable (V : TensorBundle)

/-- 1-based position of `c` in `alphabet`, if present. -/
private def charIndex (alphabet : String) (c : Char) : Option Nat :=
  (alphabet.toList.idxOf? c).map (· + 1)

/-- The generator (1-based) named by index character `c` in a block with prefix
`p` (`'v'`, `'w'`, `'∂'`, `'ϵ'`), per the space's layout. -/
def generatorOf (p c : Char) : Option Nat :=
  let dual := V.isdual
  -- the ∞/∅ glyphs name the null generators, in a v (or, dual, w) block
  if c == '∞' || c == '∅' then
    if !((p == 'v' && !dual) || (p == 'w' && dual)) then none
    else if c == '∞' then (if V.hasinf then some 1 else none)
    else if V.hasorigin then some (if V.hasinf then 2 else 1) else none
  else
    let vecLike := p == 'v' || p == '∂'
    (charIndex (if vecLike then Leibniz.alphanumv else Leibniz.alphanumw) c).bind fun i =>
      let f := V.diffvars
      let g := V.grade
      let within := fun (ok : Bool) (x : Nat) => if ok then some x else none
      if V.isdyadic then
        let m := g / 2
        match p with
        | 'v' => within (i ≤ m) i
        | 'w' => within (i ≤ m) (m + i)
        | '∂' => within (i ≤ f) (g + i)
        | _ => within (i ≤ f) (g + f + i)
      else
        let own := if dual then (p == 'w' || p == 'ϵ') else (p == 'v' || p == '∂')
        if !own then none
        else if p == 'v' || p == 'w' then within (V.nulls + i ≤ g) (V.nulls + i)
        else within (i ≤ f) (g + i)

/-- The generators named by `s` in order, or `none` if `s` is not a blade name. -/
def generatorsOf (s : String) : Option (List Nat) := do
  let cs := s.toList
  let (p :: _) := cs | none
  guard (p == 'v' || p == 'w' || p == '∂' || p == 'ϵ')
  let (_, gens) ← cs.foldlM (init := (p, ([] : List Nat))) fun (cur, acc) c =>
    if c == 'v' || c == 'w' || c == '∂' || c == 'ϵ' then some (c, acc)
    else (V.generatorOf cur c).map fun g => (cur, g :: acc)
  pure gens.reverse

/-- The blade whose label-mode name (`labels(V)`, e.g. `v12`, `v10`, `∂1v2`,
`v∞∅1`) is exactly `s`, if any. Label mode prints indices 1–10 as decimals, so
`10` is read as one index here (Julia resolves such names through the
`Λ(V).g` dictionary before parsing). -/
def labelBlade? (s : String) : Option UInt64 := do
  let isPrefix := fun (c : Char) => c == 'v' || c == 'w' || c == '∂' || c == 'ϵ'
  -- read `10` greedily as index 10 (alphabet position 10 is the character `0`)
  let rec go (cur : Char) (mask : UInt64) : List Char → Option UInt64
    | [] => some mask
    | '1' :: '0' :: rest =>
      match V.generatorOf cur '0' with
        | some g => go cur (mask ||| bit g) rest
        | none => none
    | c :: rest =>
      if isPrefix c then go c mask rest
      else match V.generatorOf cur c with
        | some g => go cur (mask ||| bit g) rest
        | none => none
  let cs := s.toList
  let (p :: _) := cs | none
  guard (isPrefix p)
  let mask ← go p 0 cs
  -- Julia's `labels` use the default names v/w/∂/ϵ
  let lbl := if mask == 0 then "v" else Leibniz.printLabel V.labelCtx mask true Leibniz.pre
  guard (lbl == s)
  pure mask

/-- Julia `getproperty(Λ(V), name)` with correct signs: `v12 ↦ v₁₂`,
`v21 ↦ -1v₁₂`, `v11 ↦ g₁₁·v`, `v∞∅1 ↦ v∞∅₁`; `none` for a malformed name. -/
def lookup (s : String) : Option BladeResult := do
  match V.labelBlade? s with
  | some b => return .blade b
  | none =>
    let gens ← V.generatorsOf s
    let t : Terms := gens.foldl (init := #[(0, 1)]) fun acc g =>
      acc.foldl (init := #[]) fun out (a, ca) =>
        (V.mul a (bit g)).terms.foldl (fun out (k, c) => out.add k (ca * c)) out
    match (t.nonzero.sortBasis V.n) with
    | #[] => return .zero
    | #[(b, c)] => return (if c == 1 then .blade b else .single c b)
    | t => return .sum t

end TensorBundle

end DirectSum
