/-
Index printing, ported from Leibniz.jl `src/indices.jl`.

Basis blades print as a prefix followed by subscript (vectors) or
superscript (covectors) indices: `v₁₂₃`, `w¹²`, `∂₁`, `ϵ₂`. Indices 1–9 map to
subscript digits and 10 to `₀`. Indices 11–36 map to the alphanumeric
alphabets (`alphanumv` for vectors, `alphanumw` for covectors). The special
conformal indices are `-1 ↦ ∞` and `0 ↦ ∅`.

`printLabel` is the full Julia `printlabel` (`indices.jl:156-181`): it splits a
mask into its vector, covector, tangent (`∂`) and cotangent (`ϵ`) blocks
according to a `LabelCtx` describing the space, renumbers the conformal slots
through `shiftIndices`, and prints the blocks in the order `∂ ϵ v w`.
-/
import DirectSum.Bits

namespace Leibniz

open DirectSum.Bits

/-- Conformal/projective symbols: `∞` (point at infinity) and `∅` (origin). -/
def vio : Char × Char := ('∞', '∅')

/-- `"1234567890" ++ a–z ++ A–Z` : vector index alphabet. -/
def alphanumv : String := "1234567890abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
/-- `"1234567890" ++ A–Z ++ a–z` : covector index alphabet. -/
def alphanumw : String := "1234567890ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"

private def subDigits : Array Char := #['₁', '₂', '₃', '₄', '₅', '₆', '₇', '₈', '₉', '₀']
private def supDigits : Array Char := #['¹', '²', '³', '⁴', '⁵', '⁶', '⁷', '⁸', '⁹', '⁰']

/-- Subscript glyphs for indices `-1 … 36` (Julia `subs`): `∞ ∅ ₁ … ₉ ₀ a … z`. -/
private def subTable : Array Char :=
  #['∞', '∅', '₁', '₂', '₃', '₄', '₅', '₆', '₇', '₈', '₉', '₀'] ++ ("abcdefghijklmnopqrstuvwxyz".toList.toArray)

/-- Superscript glyphs for indices `-1 … 36` (Julia `sups`): `∞ ∅ ¹ … ⁹ ⁰ A … Z`. -/
private def supTable : Array Char :=
  #['∞', '∅', '¹', '²', '³', '⁴', '⁵', '⁶', '⁷', '⁸', '⁹', '⁰'] ++ ("ABCDEFGHIJKLMNOPQRSTUVWXYZ".toList.toArray)

/-- Subscript glyph for index `i` (Julia `subs[i]`), for `-1 ≤ i ≤ 36`;
`'?'` outside that range (where Julia raises a `KeyError`). -/
def subs (i : Int) : Char :=
  if i < -1 || i > 36 then '?' else subTable[(i + 1).toNat]?.getD '?'

/-- Superscript glyph for index `i` (Julia `sups[i]`), for `-1 ≤ i ≤ 36`;
`'?'` outside that range. -/
def sups (i : Int) : Char :=
  if i < -1 || i > 36 then '?' else supTable[(i + 1).toNat]?.getD '?'

-- the glyph tables agree with the alphabets `subDigits`/`alphanumv` and `supDigits`/`alphanumw`
example : (List.range 36).all (fun j => subs (j + 1 : Nat) ==
    (if j < 10 then subDigits[j]! else alphanumv.toList[j]!)) := by decide
example : (List.range 36).all (fun j => sups (j + 1 : Nat) ==
    (if j < 10 then supDigits[j]! else alphanumw.toList[j]!)) := by decide

/-- A naming scheme: prefixes for vectors, covectors, tangent derivations and
tangent functions (Julia `NTuple{4,String}`). -/
abbrev Names := String × String × String × String

/-- Vector/covector/tangent/cotangent prefixes `("v","w","∂","ϵ")`. -/
def pre : Names := ("v", "w", "∂", "ϵ")
/-- Alternate prefixes used for labels: `("X","x","Y","y")`. -/
def PRE : Names := ("X", "x", "Y", "y")

/-- Julia `namecache`: naming scheme `k` (1-based). Scheme 1 is `pre`, scheme 2
is `PRE` (`DirectSum.jl src/DirectSum.jl:87-105`); unknown indices fall back
to `pre`. -/
def nameScheme (k : Nat) : Names := if k == 2 then PRE else pre

/-- Glyph for one index (Julia `printindex(i,l,e,pre)`, `indices.jl:139-142`).

* `label` : print indices 1–10 as plain decimal digits (symbolic labels).
* `pfx` : the prefix in use. Prefixes equal to `names.1` or `names.2.2.1`
  (`v`/`∂` by default) print subscripts, every other prefix superscripts.
  Indices beyond 36 wrap by 26 and flip sub/superscript, as in Leibniz.jl. -/
def printIndex (i : Int) (label : Bool := false) (pfx : String := pre.1)
    (names : Names := pre) : String :=
  pushIndex "" i label (pfx == names.1 || pfx == names.2.2.1)
where
  /-- Append the glyph of index `i` to `s`; `vecLike` says the prefix prints subscripts. -/
  pushIndex (s : String) (i : Int) (label vecLike : Bool) : String :=
    let t := i > 36
    let j := if t then i - 26 else i
    if label && 0 < j && j ≤ 10 then
      if j == 10 then (s.push '1').push '0' else s.push (Char.ofNat (48 + j.toNat))
    -- `(e ∉ pre[[1,3]]) ⊻ t ? sups : subs`
    else if (!vecLike) != t then s.push (sups j) else s.push (subs j)

/-- Prefix followed by all index glyphs, e.g. `printIndices [1,2] = "v₁₂"`
(Julia 1-list `printindices`, `indices.jl:145`). -/
def printIndices (is : List Int) (label : Bool := false) (pfx : String := pre.1)
    (names : Names := pre) : String :=
  let vecLike := pfx == names.1 || pfx == names.2.2.1
  is.foldl (fun acc i => printIndex.pushIndex acc i label vecLike) pfx

/-- Julia 4-list `printindices(io,a,b,c,d,l,e,f,g,h)` (`indices.jl:147-154`):
blocks print in the order `c` (∂), `d` (ϵ), `a` (v), `b` (w); the vector block
prints (possibly as a bare prefix) unless it is empty while another block is
not. The sub/superscript decision compares against the *passed* names. -/
def printIndices4 (a b c d : List Int) (label : Bool) (names : Names) : String :=
  let (e, f, g, h) := names
  let s := if c.isEmpty then "" else printIndices c label g names
  let s := if d.isEmpty then s else s ++ printIndices d label h names
  let s := if (!b.isEmpty || !c.isEmpty || !d.isEmpty) && a.isEmpty then s
    else s ++ printIndices a label e names
  if b.isEmpty then s else s ++ printIndices b label f names

/-! ## Labels of basis blades -/

/-- What `printlabel` needs to know about a space (Julia reads it from the
type of the blade's space). -/
structure LabelCtx where
  /-- `mdims` of the parent manifold. -/
  n : Nat
  /-- Tangent variables `ν` of the parent. -/
  diffvars : Nat := 0
  /-- `-1` dyadic `V⊕V'`, `+1` dual, `0` plain. -/
  dyadmode : Int := 0
  /-- The parent has the point at infinity `∞` (generator 1). -/
  hasinf : Bool := false
  /-- The parent has the origin `∅` (generator 2 if `hasinf`, else 1). -/
  hasorigin : Bool := false
  /-- Mask of the handle in the parent: local bit `j` is the `j`-th set bit.
  The full space is `lowMask n`. -/
  sub : UInt64 := lowMask n
  /-- `mdims` of the handle (its rank for a proper subspace handle). -/
  hn : Nat := n
  /-- Tangent variables counted on the handle. -/
  hdiffvars : Nat := diffvars
  deriving Repr, Inhabited

namespace LabelCtx

/-- The tangent mask of the handle (Leibniz `diffmask`, `generic.jl:70-80`);
for dyadic spaces the pair `(∂ block, ϵ block)`. -/
def diffmaskPair (c : LabelCtx) : UInt64 × UInt64 :=
  let d := c.hdiffvars
  if c.dyadmode < 0 then (shl (lowMask d) (c.hn - 2 * d), shl (lowMask d) (c.hn - d))
  else (shl (lowMask d) (c.hn - d), 0)

/-- Number of null (conformal) generators `hasinf + hasorigin`. -/
@[inline] def nulls (c : LabelCtx) : Nat := (if c.hasinf then 1 else 0) + (if c.hasorigin then 1 else 0)

/-- Julia `shift_indices!` on a list of ascending 1-based parent positions
(`indices.jl:122-132`): with `∞` present position 1 becomes `-1`; with `∅`
present the next position `P` becomes `0`; the rest shift down by `P`. -/
def shiftList (c : LabelCtx) (set : List Int) : List Int :=
  if c.nulls == 0 then set else
  match set with
  | [] => []
  | x :: xs =>
    let (set, k) := if c.hasinf && x == 1 then ((-1 : Int) :: xs, 1) else (set, 0)
    let shift : Int := c.nulls
    let (set, k) := if c.hasorigin && set.length > k && set[k]! == shift then (set.set k 0, k + 1)
      else (set, k)
    (set.zipIdx.map fun (v, i) => if i ≥ k then v - shift else v)

/-- Julia `shift_indices(V,b)`: local mask → display indices (through the
handle's parent mask, then `shiftList`). -/
def shiftIndices (c : LabelCtx) (b : UInt64) : List Int :=
  let parent := if c.sub == lowMask c.n then b else pdep b c.sub
  c.shiftList ((indicesList parent).map Int.ofNat)

end LabelCtx

/-- The label of mask `x` in a plain space: the prefix `pfx`, then the glyph of every set bit,
ascending (`printIndices (indicesList x) label pfx`, without the intermediate lists). -/
def plainLabel (x : UInt64) (pfx : String) (label vecLike : Bool) : String :=
  go x pfx 64
where
  /-- Consume the set bits of `x` from the lowest. -/
  go (x : UInt64) (acc : String) : Nat → String
    | 0 => acc
    | fuel + 1 => if x == 0 then acc else
        go (x &&& (x - 1)) (printIndex.pushIndex acc (Int.ofNat (ctz x + 1)) label vecLike) fuel

/-- Julia `printlabel(io,V,e,label,vec,cov,duo,dif)` (`indices.jl:156-181`):
the name of basis blade `e` (a mask local to the handle). `label = true` gives
the ASCII label form (`v12`, `∂1v1`). -/
def printLabel (c : LabelCtx) (e : UInt64) (label : Bool := false) (names : Names := pre) :
    String :=
  -- fast path: a whole plain space (no null, tangent or dual generators) prints `vec` and one
  -- glyph per set bit, in ascending order
  if c.dyadmode == 0 && c.diffvars == 0 && !c.hasinf && !c.hasorigin && c.sub == lowMask c.n then
    -- as `printIndices … vec` below, the sub/superscript choice compares with the default `pre`
    plainLabel e names.1 label (names.1 == pre.1 || names.1 == pre.2.2.1)
  else
  let (vec, cov, duo, dif) := names
  let nn : Int := c.n
  let d : Int := c.diffvars
  let p : Int := c.nulls
  let shift := c.shiftIndices
  if c.dyadmode < 0 then
    let (db1, db2) := c.diffmaskPair
    let es := e &&& ~~~(db1 ||| db2)
    let m := (c.n - 2 * c.diffvars) / 2
    let eps := (shift (e &&& db1)).map (· - (nn - 2 * d - p))
    let par := (shift (e &&& db2)).map (· - (nn - d - p))
    printIndices4 (shift (es &&& lowMask m)) (shift (shr es m)) eps par label names
  else
    let db := c.diffmaskPair.1
    let es := e &&& ~~~db
    let eps := (shift (e &&& db)).map (· - (nn - d - p))
    if !eps.isEmpty then
      if c.dyadmode > 0 then printIndices4 (shift es) [] [] eps label (cov, cov, dif, dif)
      else printIndices4 (shift es) [] eps [] label (vec, cov, duo, dif)
    else
      printIndices (shift es) label (if c.dyadmode > 0 then cov else vec)


/-- Julia `indexstring(V,D)` (`indices.jl:205-209`): the label with `PRE` names
in label mode, e.g. `X13`. -/
def indexString (c : LabelCtx) (e : UInt64) : String := printLabel c e true PRE

example : printIndices [1, 2, 3] = "v₁₂₃" := by decide
example : printIndices [1, 2] (pfx := "w") = "w¹²" := by decide
example : printIndices [-1, 0, 1] = "v∞∅₁" := by decide
example : printIndices [10, 11, 12] = "v₀ab" := by decide
example : printIndices [] = "v" := by decide

end Leibniz
