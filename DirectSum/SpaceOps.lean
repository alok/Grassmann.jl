/-
Space algebra (DirectSum.jl `src/generic.jl:128-162`, `src/operations.jl:19-87`):
dual (adjoint), direct sum `⊕`, powers, tangent bundles.

Operations Julia rejects at run time (`'` of a dyadic space, `⊕` of conformal or
dyadic spaces) return `Except String`. The notations `V′` and `V ⊕ W` use the
total variants `dual` (Julia `dual`, identity on dyadic spaces) and `oplus!`
(panics with Julia's message).
-/
import DirectSum.Show

namespace DirectSum

open Bits

namespace TensorBundle

variable (V : TensorBundle)

/-- Julia `adjoint(V)` = `V'` (`DirectSum.jl src/generic.jl:146-162`): toggle the
dual flag. A `Signature` negates every metric bit (`flipsign`, tangent and null
slots included); a `DiagonalForm`/`MetricTensor` keeps its primal values (they
are negated on read). An `Int` space first becomes a `Signature` (Julia
`Signature(M)'`). Polymode and the naming scheme reset (quirk Q6). Dyadic spaces
have no adjoint. -/
def adjoint : Except String TensorBundle :=
  if V.isdyadic then
    .error s!"{V} is the direct sum of a vector space and its dual space"
  else
    let dm : Int := if V.isdual then 0 else 1
    let m := match V.metric with
      | .euclid => .signature (flipsign V.n 0)
      | .signature s => .signature (flipsign V.n s)
      | other => other
    .ok { V with metric := m, dyadmode := dm, polymode := true, name := 1 }

/-- Julia `dual(V) = isdyadic(V) ? V : V'` (`DirectSum.jl src/generic.jl:143`). -/
def dual : TensorBundle :=
  match V.adjoint with
  | .ok W => W
  | .error _ => V

/-- Postfix dual: `V′` (U+2032) is `V.dual`. -/
postfix:max "′" => TensorBundle.dual

/-- The metric of the non-tangent generators as a diagonal (for `⊕` of a
`DiagonalForm` with a `Signature`, Julia's intended semantics, quirk Q8). -/
private def asDiag : Array Rat :=
  match V.metric with
  | .diagonal _ => V.diagValues
  | .signature s => (List.range V.grade).toArray.map fun k => if testBit s k then -1 else 1
  | _ => (List.range V.grade).toArray.map fun _ => 1

/-- Julia `combine_options`/`oplus` option table (`DirectSum.jl
src/operations.jl:19-54`): the result's `dyadmode`, or an error. `exact` says
`b` is exactly the dual of `a` (same size and metric). -/
private def oplusMode (a b : TensorBundle) (exact : Bool) : Except String Int :=
  if a.nulls != 0 || b.nulls != 0 || a.isdyadic || b.isdyadic || !a.polymode || !b.polymode then
    .error "arbitrary TensorBundle direct-sums not yet implemented"
  else match a.dyadmode, b.dyadmode with
    | 0, 0 => .ok 0
    | 1, 1 => .ok 1
    | _, _ => .ok (if exact then -1 else 0)

/-- Julia `a ⊕ b` for spaces (`DirectSum.jl src/operations.jl:36-68`).

* Both spaces need the same `diffvars`/`diffmode`.
* `V ⊕ V'` is dyadic (printed `*`) only when the dual half is exactly `V'`;
  otherwise the dual flag is silently dropped (quirk Q7, replicated), and
  `V' ⊕ V` puts the dual half first.
* A non-dyadic sum of tangent spaces is rejected (Julia builds an inconsistent
  space, quirk Q9).
* `Int ⊕ Int` stays `Int`; `Int` with anything else converts to `Signature`;
  a `DiagonalForm` with a `Signature` gives a `DiagonalForm` (Julia intends this
  but throws, quirk Q8). `MetricTensor` sums are unsupported. -/
def oplus (a b : TensorBundle) : Except String TensorBundle := do
  if a.diffvars != b.diffvars || a.diffmode != b.diffmode then
    throw s!"MethodError: no method matching ⊕({a}, {b}) (tangent orders differ)"
  let tangentOk := fun (dm : Int) =>
    if a.diffvars != 0 && dm != -1 then
      throw "direct sum of tangent spaces is only supported as V ⊕ V' (Julia quirk Q9)"
    else pure ()
  match a.metric, b.metric with
  | .euclid, .euclid =>
    tangentOk 0
    return { n := a.n + b.n, metric := .euclid }
  | .tensor _, _ | _, .tensor _ => throw "direct sums of MetricTensor spaces are not implemented"
  | .diagonal _, _ | _, .diagonal _ =>
    let exact := a.n == b.n && a.metric == b.metric
    let dm ← oplusMode a b exact
    tangentOk dm
    let vals := asDiag a ++ asDiag b
    -- stored values are primal: a dual result stores the negation (Julia `diagsig`)
    let stored := if dm > 0 then vals.map (- ·) else vals
    return { n := a.n + b.n, metric := .diagonal stored, dyadmode := dm,
             diffvars := a.diffvars, diffmode := a.diffmode }
  | ma, mb =>
    let sa := match ma with | .signature s => s | _ => 0
    let sb := match mb with | .signature s => s | _ => 0
    let exact := a.n == b.n &&
      (if b.isdual && !a.isdual then sb == flipsign a.n sa
       else if a.isdual && !b.isdual then sa == flipsign b.n sb else false)
    let dm ← oplusMode a b exact
    tangentOk dm
    -- concatenate the non-tangent metric bits (Julia `bit2int([a[:]; b[:]])`)
    let bits := (sa &&& lowMask a.grade) ||| shl (sb &&& lowMask b.grade) a.grade
    return { n := a.n + b.n, metric := .signature bits, dyadmode := dm,
             diffvars := a.diffvars, diffmode := a.diffmode }

/-- Total `⊕` for notation: panics with Julia's message on an unsupported sum
and then returns `a`. -/
def oplus! (a b : TensorBundle) : TensorBundle :=
  match oplus a b with
  | .ok v => v
  | .error e => panic! e

/-- `V ⊕ W`: direct sum of spaces (overloads `Sum`'s notation, same precedence). -/
infixr:30 " ⊕ " => TensorBundle.oplus!

/-- Julia `V^i` (`DirectSum.jl src/operations.jl:75-87`): `V ⊕ V ⊕ … ⊕ V`
(`i` copies), `V0` for `i = 0`; only plain and dual spaces (options 0 or 4). -/
def pow (i : Nat) : Except String TensorBundle :=
  if V.options != 0 && V.options != 4 then .error s!"MethodError: no method matching ^({V}, {i})"
  else match i with
    | 0 => .ok V0
    | k + 1 => (List.range k).foldlM (fun acc _ => oplus acc V) V

/-- Julia `tangent(V, μ = 1, ν = (diffvars ≠ 0 ? diffvars : 1))`
(`DirectSum.jl src/generic.jl:128-129`): add `ν` tangent variables (`2ν` slots
for a dyadic space) and raise the order by `μ`. `n` grows on every call, even
when `ν` is unchanged, so `tangent(tangent(ℝ^3)) = T²⟨++++₁⟩` (quirk Q10,
replicated: the README relies on it). An `Int` space becomes a `Signature`. -/
def tangent (mu : Nat := 1) (nu : Nat := if V.diffvars != 0 then V.diffvars else 1) :
    TensorBundle :=
  let m := match V.metric with | .euclid => .signature 0 | other => other
  { V with n := V.n + (if V.isdyadic then 2 * nu else nu), metric := m,
           diffvars := nu, diffmode := V.diffmode + mu }

end TensorBundle

end DirectSum
