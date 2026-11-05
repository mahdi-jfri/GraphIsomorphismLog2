module

public import Workspace.Impl.LinObjectBasisEval
public import Workspace.Impl.LinMapEncoded

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset

theorem linObjectAffineEval_move_spec {P : Program} {b jsci jder jmem jm jh n C : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership} {hc : ConstructiveMembership}
    (h : linObjectAffineEvalAt P b jsci jder jmem jm jh hs hd hm hc)
    (as : List (Equiv.Perm (Fin n))) (Y : List (TmRiO n)) (hok : TmRiOK C Y)
    (z : Fin (as.length * (tmRiPcsO (gens as) Y).length) → ℤ) (g : Equiv.Perm (Fin n)) :
    let input := Val.list [encPerm g,.list ((linObjectWordPieces as Y z).map tmGlObjsVal)]
    FunDet P (b + 114) input (.list ((linObjectMovedPieces as Y z g).map tmGlObjsVal))
      (linMapBudget input.wt (tmRiMapShC n C Y.length)) := by
  have hs' (S : List (TmRiO n)) (hS : S ∈ linObjectWordPieces as Y z) :
      FunDet P (b + 198) (.list [encPerm g,tmGlObjsVal S])
        (tmGlObjsVal (S.map (tmRiSh g))) (tmRiMapShC n C Y.length) := by
    have hOrig : linObjectOrigins Y S := by
      intro o ho
      exact linObjectOrigins_wordPieces as Y z o (List.mem_flatten.mpr ⟨S,hS,ho⟩)
    have hh := tmRi_mapShift_spec h.offsets.table.orbit.inner g
      (linObjectOrigins_tmRiOK Y S hOrig hok)
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hS
    have hlen : (((tmRiPcsO (gens as) Y).get i).map
        (tmRiSh (linGroupWord (fun j => as.get j) (linObjectUnflatten _ _ z i)))).length ≤ Y.length := by
      rw [List.length_map]
      obtain ⟨o,ho,he⟩ := tmRiPcsO_mem (List.get_mem (tmRiPcsO (gens as) Y) i)
      rw [he]
      exact List.length_filter_le _ _
    exact hh.mono (linObjectShiftCost_mono hlen)
  have hh := linMapEncoded_spec h.move tmGlObjsVal (fun _ _ he => tmRi_objsVal_inj he)
    (fun S => tmGlObjsVal (S.map (tmRiSh g))) (encPerm g) (linObjectWordPieces as Y z)
    (tmRiMapShC n C Y.length) hs'
  simpa only [linObjectMovedPieces,List.map_map,Function.comp_def] using hh

end GI.Impl
