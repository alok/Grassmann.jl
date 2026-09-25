/-
Julia's display of `Values` (Julia's `AbstractVector` printing; port-notes
abstracttensors-staticvectors.md §5), and the `vals![…]` literal (Julia `Values(x…)`).

* `JuliaShow (Values α n)`: `repr`/`show`/`print` give the compact array form
  `[e1, e2, …]`, prefixed by the element type unless it is `Int64` or `Float64`
  (`Float32[1.5, 2.0]`, `Bool[1, 0]`, `Rational{Int64}[1//2]`, `ComplexF64[1.0 + 2.0im]`,
  `Values{2, Int64}[[1, 2], [3, 4]]`, `Int64[]`); elements print as inside a typed
  container (`Bool` as `1`/`0`, `Float32` without `f0`).
* `Values.showPlain` is the `text/plain` display: the header
  `3-element Values{3, Int64} with indices SOneTo(3):` and one element per line, aligned as
  Base's `alignment` does (numbers split before the first `.`, `e`, `E`, `f`, `F`; complex
  numbers after the sign of the imaginary part; the left parts right-justified).
-/
import StaticVectors.Values
import JuliaBase.Show

universe u

namespace StaticVectors

open JuliaBase

/-- Julia's name of an element type and how it prints inside a typed container. -/
class JuliaEltype (α : Type u) where
  /-- The type as Julia prints it (`Int64`, `Float32`, `Rational{Int64}`, `ComplexF64`). -/
  name : String
  /-- Whether Julia omits the eltype prefix in `[…]` (`Int64`, `Float64`). -/
  implicit : Bool := false
  /-- An element as printed inside a typed container (`:typeinfo` set). -/
  showElem : α → String
  /-- Julia `Base.alignment` of an element: the widths of its left and right parts. -/
  align : α → Nat × Nat

namespace JuliaEltype

/-- Base `alignment(io, x::Real)`: split before the first `.`, `e`, `E`, `f` or `F`. -/
def alignReal (s : String) : Nat × Nat :=
  let cs := s.toList
  let k := (cs.findIdx? fun c => c == '.' || c == 'e' || c == 'E' || c == 'f' || c == 'F').getD cs.length
  (k, cs.length - k)

/-- Base `alignment(io, x::Complex)`: the left part ends with the sign of the imaginary part
(`r"^(.*[^ef][\+\-])(.*)$"`, the last `+`/`-` not preceded by `e`/`f`). -/
def alignComplex (s : String) : Nat × Nat :=
  let cs := s.toList.toArray
  let rec go (i : Nat) : Nat → Option Nat
    | 0 => none
    | fuel + 1 =>
      if i == 0 then none
      else
        let c := cs[i]!
        let p := cs[i - 1]!
        if (c == '+' || c == '-') && p != 'e' && p != 'f' then some (i + 1) else go (i - 1) fuel
  match go (cs.size - 1) cs.size with
  | some k => (k, cs.size - k)
  | none => (0, cs.size)

end JuliaEltype

instance : JuliaEltype Int where
  name := "Int64"
  implicit := true
  showElem x := toString x
  align x := (toString x).length |> fun k => (k, 0)

instance : JuliaEltype Nat where
  name := "Int64"
  implicit := true
  showElem x := toString x
  align x := ((toString x).length, 0)

instance : JuliaEltype Float where
  name := "Float64"
  implicit := true
  showElem x := F64.showString x
  align x := JuliaEltype.alignReal (F64.showString x)

instance : JuliaEltype Float32 where
  name := "Float32"
  showElem x := F32.printString x
  align x := JuliaEltype.alignReal (F32.printString x)

instance : JuliaEltype Bool where
  name := "Bool"
  showElem x := if x then "1" else "0"
  align _ := (1, 0)

instance : JuliaEltype Rat where
  name := "Rational{Int64}"
  showElem x := JuliaShow.showString x
  align x := JuliaEltype.alignReal (JuliaShow.showString x)

instance : JuliaEltype UInt8 where
  name := "UInt8"
  showElem x := JuliaShow.showString x
  align x := ((JuliaShow.showString x).length, 0)

instance : JuliaEltype UInt16 where
  name := "UInt16"
  showElem x := JuliaShow.showString x
  align x := ((JuliaShow.showString x).length, 0)

instance : JuliaEltype UInt32 where
  name := "UInt32"
  showElem x := JuliaShow.showString x
  align x := ((JuliaShow.showString x).length, 0)

instance : JuliaEltype UInt64 where
  name := "UInt64"
  showElem x := JuliaShow.showString x
  align x := ((JuliaShow.showString x).length, 0)

/-- `ComplexF64`. -/
instance : JuliaEltype (Complex Float) where
  name := "ComplexF64"
  showElem z := JuliaShow.showString z
  align z := JuliaEltype.alignComplex (JuliaShow.showString z)

/-- `Complex{Int64}`. -/
instance : JuliaEltype (Complex Int) where
  name := "Complex{Int64}"
  showElem z := JuliaShow.showString z
  align z := JuliaEltype.alignComplex (JuliaShow.showString z)

namespace Values

variable {α : Type u} [Packed α] {n : Nat}

/-- Julia's type of a `Values`: `Values{3, Int64}`. -/
def typeName (α : Type u) [JuliaEltype α] (n : Nat) : String :=
  "Values{" ++ toString n ++ ", " ++ JuliaEltype.name α ++ "}"

/-- Julia `repr(v)`: `[e1, e2, …]` with the eltype prefix unless `Int64`/`Float64`. -/
def showRepr [JuliaEltype α] (v : Values α n) : String :=
  (if JuliaEltype.implicit α && n != 0 then "" else JuliaEltype.name α) ++
    "[" ++ ", ".intercalate (v.toList.map JuliaEltype.showElem) ++ "]"

/-- Julia's `text/plain` display (`display(v)` in the REPL). -/
def showPlain [JuliaEltype α] (v : Values α n) : String :=
  if n == 0 then showRepr v
  else
    let es := v.toList
    let al := es.map JuliaEltype.align
    let left := al.foldl (fun m (l, _) => max m l) 0
    let lines := es.zip al |>.map fun (x, (l, _)) =>
      " " ++ String.ofList (List.replicate (left - l) ' ') ++ JuliaEltype.showElem x
    toString n ++ "-element " ++ typeName α n ++ " with indices SOneTo(" ++ toString n ++ "):\n" ++
      "\n".intercalate lines

end Values

/-- Nested vectors: `Values{2, Int64}[[1, 2], [3, 4]]`. -/
instance {α : Type u} [Packed α] {n : Nat} [JuliaEltype α] : JuliaEltype (Values α n) where
  name := Values.typeName α n
  showElem v := Values.showRepr v
  align v := (0, (Values.showRepr v).length)

/-- Julia `show`/`print`/`repr` of a `Values`: the compact array form. -/
instance {α : Type u} [Packed α] {n : Nat} [JuliaEltype α] : JuliaShow (Values α n) where
  showIO _ v := Values.showRepr v
  needsParens _ := true

/-- `vals![a, b, c]`: the `Values` with these entries, its length taken from the list (Julia
`Values(a, b, c)`). -/
syntax "vals![" term,* "]" : term

macro_rules
  | `(vals![$xs,*]) => do
    let n := Lean.Syntax.mkNumLit (toString xs.getElems.size)
    `(StaticVectors.Values.ofFn (n := $n) fun i => ([$xs,*] : List _)[i.1]!)

/-- Julia `ones(Values{n,T})`. -/
@[inline] def Values.ones {α : Type u} [Packed α] [OfNat α 1] {n : Nat} : Values α n := Values.replicate 1

end StaticVectors
