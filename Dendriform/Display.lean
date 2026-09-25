import Dendriform.Grove
import Dendriform.Float16

/-!
# Display and `GroveBin`

Julia source: DF/Dendriform.jl:390-453 (printing) and :61-66, :142-144 (`GroveBin`).
Julia's global `grovedisplay()` toggle (DF/Dendriform.jl:397-400) is an explicit `display`
argument here. The progress lines Julia prints to stdout whenever its total-grove cache
grows are not reproduced (port-notes §5.1).
-/

namespace Dendriform

namespace Tree

/-- Julia `print(io, υ::PBTree)` (DF/Dendriform.jl:404-425): the name as `[1, 2, 3]`
followed by a newline; with `display`, also `↦ μ ↦ index/Cn or TI`. The empty tree prints
`∅` (with display `∅ ↦ [∅] ↦ 0/1 or 0`) and **no newline**. -/
def print (t : Tree) (display : Bool := false) : String :=
  match t with
  | leaf => "∅" ++ (if display then " ↦ [∅] ↦ 0/1 or 0" else "")
  | _ =>
    t.nameString ++
      (if display then
        s!" ↦ {t.muString} ↦ {t.treeIndex}/{catalan t.deg} or {t.treeInteger}"
      else "") ++ "\n"

end Tree

/-- Julia `GroveBin` (DF/Dendriform.jl:61-66): a grove compressed to its degree, size and
grove index; the position `ppos` is derived. Equality is Julia's (DF/Dendriform.jl:149):
`degr`, `size` and `gbin`. -/
structure GroveBin where
  /-- the degree -/
  degr : Nat
  /-- the number of rows of the grove it came from -/
  size : Nat
  /-- the grove index (Julia `groveindex`, with multiplicity) -/
  gbin : Nat
  deriving DecidableEq, Repr, Inhabited

namespace GroveBin

/-- Julia `GroveBin(g::Grove)` (DF/Dendriform.jl:142). -/
def ofGrove {n : Nat} (g : Grove n) : GroveBin := ⟨n, g.size, g.index⟩

/-- Julia `ppos = Float16(100 i // (2^Cn(d) - 1))` (DF/Dendriform.jl:144): the grove's
position as a percentage of the total grove's index. -/
def ppos (g : GroveBin) : Float16 := Float16.ofRat (100 * g.gbin) (2 ^ catalan g.degr - 1)

/-- Julia `Grove(g::GroveBin)` (DF/Dendriform.jl:126, 171): decode the index. -/
def toGrove (g : GroveBin) : Grove g.degr := Grove.ofIndex g.degr g.gbin

/-- Julia `print(io, k::GroveBin)` (DF/Dendriform.jl:451-453):
`"$(gbin) Y$(degr) #$(size)/$(Cn(degr)) [$(ppos)%]"`. -/
protected def toString (g : GroveBin) : String :=
  s!"{g.gbin} Y{g.degr} #{g.size}/{catalan g.degr} [{g.ppos}%]"

instance : ToString GroveBin := ⟨GroveBin.toString⟩

end GroveBin

namespace Grove

/-- Julia `print(io, Y::Grove)` (DF/Dendriform.jl:428-437): each row printed as a tree, then
`Y$(degr) #$(size)/$(Cn(degr))` (or, with `display`, the `GroveBin`), without a trailing
newline. -/
def print {n : Nat} (g : Grove n) (display : Bool := false) : String :=
  String.join (g.rows.map (·.print display)) ++
    (if display then toString (GroveBin.ofGrove g) else s!"Y{n} #{g.size}/{catalan n}")

instance {n : Nat} : ToString (Grove n) := ⟨(·.print)⟩
instance {n : Nat} : Repr (Grove n) := ⟨fun g _ => g.print⟩

end Grove

/-- Julia `print` of a runtime-degree grove. -/
def SomeGrove.print (g : SomeGrove) (display : Bool := false) : String := g.2.print display

-- goldens (port-notes §6.4)
#guard (Grove.ofIndex 3 7).print == "[1, 2, 3]\n[2, 1, 3]\n[1, 3, 1]\nY3 #3/5"
#guard toString (GroveBin.ofGrove (Grove.ofIndex 3 7)) == "7 Y3 #3/5 [22.58%]"
#guard toString (GroveBin.ofGrove (Grove.total 2)) == "3 Y2 #2/2 [100.0%]"
#guard toString (GroveBin.ofGrove (Grove.total 5)) == "4398046511103 Y5 #42/42 [100.0%]"
#guard toString (GroveBin.ofGrove (Grove.ofIndex 4 1)) == "1 Y4 #1/14 [0.006104%]"
#guard (Grove.ofTree PBTree.leaf).print == "∅Y0 #1/1"
#guard (Grove.ofIndex 3 0).print == "Y3 #0/5"

end Dendriform
