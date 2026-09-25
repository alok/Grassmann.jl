import MeshTopology

/-!
Compile-time checks for MeshTopology: dimensions live in the types, small tables are decided by
the kernel, and a few port-notes examples are `#guard`ed at elaboration time.
-/

open MeshTopology

namespace Tests.MeshTopology.Static

/-! Dimensions in the types: these only typecheck because the arithmetic works out. -/

example (m : QuotientTopology 2) (n : QuotientTopology 3) : QuotientTopology 5 := m.cross n
example (m : QuotientTopology 2) : QuotientTopology 3 := m.crossInt 7
example (m : QuotientTopology 2) : QuotientTopology 1 := m.axisTopology 1
example (p : ProductTopology 4) (a : Fin 4) : ProductTopology 3 := p.exclude a
example (t : SimplexTopology 4) : SimplexTopology 6 := t.edgesIndices
example (t : SimplexTopology 3) : SimplexTopology 3 := t.edgesIndices
example (t : SimplexTopology 4) : SimplexTopology 3 × SimplexTopology 4 := t.facetsIndices

/-! Kernel-checked tables (port-notes §4.1, §6). -/

-- CrossRange(n) for n = 5, 6, 7
example : (List.range 5).map (fun (i : Nat) => crossGet 5 (Int.ofNat i + 1)) = [3, 4, 1, 2, 3] := by decide
example : (List.range 6).map (fun (i : Nat) => crossGet 6 (Int.ofNat i + 1)) = [3, 4, 1, 2, 3, 4] := by decide
example : (List.range 7).map (fun (i : Nat) => crossGet 7 (Int.ofNat i + 1)) = [4, 5, 6, 1, 2, 3, 4] := by decide
-- Lagrange counts per element: 3 corners + 3(M-1) edge nodes + center nodes
example : (List.range 6).all (fun M => 3 + 3 * M + centerSimplex 3 (M + 1) == lagrangeSimplex 3 (M + 1)) := by
  decide
example : (List.range 6).all (fun M =>
    4 + 6 * M + 4 * facetSimplex 4 (M + 1) + centerSimplex 4 (M + 1) == lagrangeSimplex 4 (M + 1)) := by
  decide
-- ∂ of the pseudoscalar
#guard boundarySigns 3 == #[1, -1, 1]
#guard boundarySigns 4 == #[-1, 1, -1, 1]

/-! Port-notes examples, evaluated at elaboration time. -/

-- Torus(4,5): K = 0 lookups of the padded grid (§4.4)
#guard (QuotientTopology.torus #v[4, 5]).get #v[0, 2] == #v[3, 2]
#guard (QuotientTopology.torus #v[4, 5]).get #v[1, 2] == #v[4, 2]
#guard (QuotientTopology.torus #v[4, 5]).get #v[2, 0] == #v[2, 4]
#guard (QuotientTopology.torus #v[4, 5]).get #v[0, 0] == #v[0, 0]
#guard (QuotientTopology.torus #v[4, 5]).ghost 1 #v[1, 1] == #v[4, 1]
#guard (QuotientTopology.torus #v[4, 5]).ghost 2 #v[1, 1] == #v[1, 5]
#guard (QuotientTopology.mobius #v[4, 5]).get #v[0, 2] == #v[3, 4]
#guard (QuotientTopology.sphere #v[4, 5]).get #v[0, 2] == #v[2, 4]
-- 5-D Torus: fixed vs upstream Q11
#guard (QuotientTopology.torus #v[3, 4, 5, 6, 7]).get #v[2, 2, 3, 4, 7] == #v[2, 2, 3, 4, 1]
#guard (QuotientTopology.torus #v[3, 4, 5, 6, 7]).ghost 0 #v[2, 2, 3, 4, 7] (q11 := true) == #v[2, 2, 3, 4, 2]
-- elementfuns / vertices of Torus(4,5) and Sphere(4,5) (§4.6)
#guard (QuotientTopology.torus #v[4, 5]).elementfuns ==
  #[1, 2, 3, 1, 5, 6, 7, 5, 9, 10, 11, 9, 13, 14, 15, 13, 1, 2, 3, 1]
#guard (QuotientTopology.sphere #v[4, 5]).vertices ==
  #[1, 2, 3, 4, 1, 5, 6, 4, 1, 7, 8, 4, 1, 9, 10, 4, 1, 2, 3, 4]
-- tri8 (§6): edges are colex, and the P3 node list of element 1
#guard let t : SimplexTopology 3 := .ofElements #[#v[1, 2, 5], #v[1, 5, 4], #v[2, 3, 6], #v[2, 6, 5],
    #v[4, 5, 8], #v[4, 8, 7], #v[5, 6, 9], #v[5, 9, 8]]
  (t.edgeList.map (·.toArray)).take 6 == #[#[1, 2], #[2, 3], #[1, 4], #[1, 5], #[2, 5], #[4, 5]] &&
  (LagrangeTriangles.ofCorners (M := 3) t).get 1 == #[1, 2, 5, 18, 19, 17, 16, 10, 11, 42]

end Tests.MeshTopology.Static
