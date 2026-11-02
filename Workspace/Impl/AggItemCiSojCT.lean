import Workspace.Impl.AggItemCiSojTW
import Workspace.Impl.PolyBd

/-!
# The component-table function table, with every precondition discharged

The only library code used is ranges, maps, transposition tables, and the proved
orbit-table program. The palette bound gives one polynomial weight budget for all
intermediates. This file closes the component-table program contract.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)

/-- Indices of the component-table program and its callees. -/
structure itcsCompIdx where
  c1 : ItC1Idx
  (f mp sq eg et orb : ℕ)

/-- The actual component-table bodies installed at these indices. -/
structure itcsCompOk (Pg : Program) (Ii : itcsCompIdx) : Prop where
  c1 : ItC1Ok Pg Ii.c1
  f : Pg.funs[Ii.f]? = some (itcsCompF Ii.c1.rng Ii.mp Ii.orb)
  mp : Pg.HasAt Ii.mp (mapFuns Ii.mp Ii.sq)
  sq : Pg.funs[Ii.sq]? = some (itcsSqGF Ii.eg)
  eg : Pg.funs[Ii.eg]? = some (itcsEdgeGF Ii.et Ii.c1.swt)
  et : Pg.funs[Ii.et]? = some itcsEdgeT
  orb : Pg.HasAt Ii.orb (orbitFuns Ii.orb)

/-- Total component-table cost at a palette bound. -/
def itcsCompTotal (q B : ℕ) : ℕ :=
  itcsCompC q (itcsCompW q B) (200 * (itcsCompW q B + 1) + 10 ^ 5 * (q + 1) ^ 3)

/-- The component-table program, requiring only an explicit bound on input colors. -/
theorem itcs_comp_prog {q B : ℕ} {Pg : Program} {Ii : itcsCompIdx}
    (hi : itcsCompOk Pg Ii) (X : PairCfg q) (x₀ : Fin q) (v : ℕ)
    (hcol : itCfColsLe (.pair X x₀) B) (hv : v ≤ B) :
    FunDet Pg Ii.f (.list [rcColVal X, .nat X.j, .nat v, .nat q])
      (encFun (itcsLab X v)) (itcsCompTotal q B) := by
  have hw := itcs_comp_weights X x₀ v hcol hv
  have hg : ∀ a b : Fin q, FunDet Pg Ii.eg
      (.list [.list [rcColVal X, .nat X.j, .nat v, .nat a, .nat b], natList (List.range q)])
      (GI.Cited.encPerm (itcsEdge X v a b))
      (200 * (itcsCompW q B + 1) + 10 ^ 5 * (q + 1) ^ 3) := by
    intro a b
    exact itcs_edge_gen hi.eg hi.et (fun u z => it_swTab_spec hi.c1.swt hi.c1.sb u z)
      X v a b (hw.edge a b) (hw.swap a) (fun z => hw.perm _) (by have := hw.qle; omega)
  exact itcs_component_prog_full hi.f hi.c1.rng hi.mp hi.sq hi.orb X v hw hg

/-- The component-table cost stays polynomial after substituting the round's palette bound. -/
theorem itcs_comp_pbu : PBU fun _ W _ => itcsCompTotal (2 * W + 3) (2 * (2 * W + 3) ^ 64) := by
  simp only [itcsCompTotal, itcsCompC, itcsSqMapC, itcsCompW, itCfObjB, itcsGenW, mapK, orbitK]
  norm_poly

end GI.Impl
