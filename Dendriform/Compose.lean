import Dendriform.Display

/-!
# Grove compositions

Julia source: DF/Dendriform.jl:320-388. `Compose(n)` lists every ordered tuple
`(γ₁, …, γ_k)`, `k ≥ 2`, of non-empty groves with degrees summing to `n`, each with its
right-nested sum `γ₁ + (γ₂ + (… + γ_k))`; `grovecomposition(d, ind)` prints the grove
`Grove(d, ind)` and every composition whose sum is that grove.

Julia caches `Compose(n)` in a global store keyed by `n` alone, although the top-level call
(no singletons) and the recursive calls (with singletons) differ, so results depend on
the call history (port-notes §4.4.9, Appendix A #9: `grovecomposition(3, 31)` returns 3
instead of 4 after `grovecomposition(2, 3)`). This port implements the fresh-process
semantics and has no cache.
-/

namespace Dendriform

/-- One composition: the parts and the `GroveBin` of their right-nested sum. -/
structure Composition where
  /-- the parts `γ₁, …, γ_k` -/
  parts : List GroveBin
  /-- `GroveBin(γ₁ + (γ₂ + (… + γ_k)))` -/
  total : GroveBin
  deriving Repr, Inhabited

/-- Julia `Compose(n, η)` (DF/Dendriform.jl:322-354) without its cache. With `n < η`
(recursive calls) the singletons `[γ]` are included; the top-level call has `η = n`. -/
def compose : (fuel n η : Nat) → List Composition
  | 0, _, _ => []
  | fuel + 1, n, η =>
    let singles : List Composition :=
      if n != 0 && n < η then
        (List.range (2 ^ catalan n - 1)).map fun i =>
          let g := GroveBin.ofGrove (Grove.ofIndex n (i + 1))
          ⟨[g], g⟩
      else []
    let longer := (List.range (n - 1)).reverse.flatMap fun s' =>
      let s := s' + 1
      let rest := compose fuel (n - s) η
      (List.range (2 ^ catalan s - 1)).flatMap fun i =>
        let gsi := Grove.ofIndex s (i + 1)
        rest.map fun e =>
          let sm := gsi + e.total.toGrove
          ⟨GroveBin.ofGrove gsi :: e.parts, GroveBin.ofGrove sm⟩
    singles ++ longer

/-- Julia `Compose(d)` at top level (fresh process). -/
def compositions (d : Nat) : List Composition := compose (d + 1) d d

/-- Julia `grovecomposition(d, ind)` (DF/Dendriform.jl:366-388): the printed text and the
returned count. -/
def groveComposition (d ind : Nat) : String × Nat :=
  let head := toString (GroveBin.ofGrove (Grove.ofIndex d ind))
  let hits := (compositions d).filter (·.total.gbin == ind)
  if hits.isEmpty then (head ++ " has 1 composition (itself)\n", 1)
  else
    (head ++ s!" has {hits.length + 1} compositions\n" ++
      String.join (hits.map fun c => "(" ++ ") + (".intercalate (c.parts.map toString) ++ ")\n"),
      hits.length + 1)

-- port-notes §6.4
#guard (groveComposition 3 31).2 == 4
#guard (groveComposition 3 31).1 == "31 Y3 #5/5 [100.0%] has 4 compositions
(3 Y2 #2/2 [100.0%]) + (1 Y1 #1/1 [100.0%])
(1 Y1 #1/1 [100.0%]) + (3 Y2 #2/2 [100.0%])
(1 Y1 #1/1 [100.0%]) + (1 Y1 #1/1 [100.0%]) + (1 Y1 #1/1 [100.0%])
"
#guard groveComposition 3 6 == ("6 Y3 #2/5 [19.36%] has 1 composition (itself)\n", 1)
#guard groveComposition 3 1 == ("1 Y3 #1/5 [3.227%] has 1 composition (itself)\n", 1)

end Dendriform
