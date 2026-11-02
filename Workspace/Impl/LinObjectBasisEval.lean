import Workspace.Impl.LinObjectMovedMath
import Workspace.Impl.LinObjectAffineEval

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset

theorem linObjectShiftCost_mono {n C a b : ℕ} (h : a ≤ b) :
    tmRiMapShC n C a ≤ tmRiMapShC n C b := by
  unfold tmRiMapShC
  gcongr

theorem linObjectAffineEval_build_spec {P : Program} {b jsci jder jmem jm jh n C : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership} {hc : ConstructiveMembership}
    (h : linObjectAffineEvalAt P b jsci jder jmem jm jh hs hd hm hc)
    (as : List (Equiv.Perm (Fin n))) (Y : List (TmRiO n)) (hok : TmRiOK C Y)
    (z : Fin (as.length * (tmRiPcsO (gens as) Y).length) → ℤ) :
    let input := Val.list [encGroup as,.list ((tmRiPcsO (gens as) Y).map tmGlObjsVal),linVecVal z]
    FunDet P (b + 61) input (.list ((linObjectWordPieces as Y z).map tmGlObjsVal))
      (linObjectBasisConfigCost input.wt (tmRiMapShC n C Y.length)) := by
  let refs := tmRiPcsO (gens as) Y
  have hshift (i : Fin refs.length) (a : Equiv.Perm (Fin n)) :
      FunDet P (b + 198) (.list [encPerm a,tmGlObjsVal (refs.get i)])
        (tmGlObjsVal ((refs.get i).map (tmRiSh a))) (tmRiMapShC n C Y.length) := by
    have hsub := linObjectOrigins_reference as Y (refs.get i) (List.get_mem refs i)
    have hh := tmRi_mapShift_spec h.offsets.table.orbit.inner a (linObjectOrigins_tmRiOK Y _ hsub hok)
    have hlen : (refs.get i).length ≤ Y.length := by
      obtain ⟨o,ho,he⟩ := tmRiPcsO_mem (List.get_mem refs i)
      rw [he]
      exact List.length_filter_le _ _
    exact hh.mono (linObjectShiftCost_mono hlen)
  have hb := linObjectBasisConfig_spec h.build as z (fun i : Fin refs.length => tmGlObjsVal (refs.get i))
    (fun i a => tmGlObjsVal ((refs.get i).map (tmRiSh a))) hshift
  have henc : (List.finRange refs.length).map (fun i => tmGlObjsVal (refs.get i)) = refs.map tmGlObjsVal := by
    simpa only [List.map_ofFn,List.ofFn_eq_map,List.map_map,Function.comp_def] using
      congrArg (List.map tmGlObjsVal) (List.ofFn_get refs)
  have hout : (List.finRange refs.length).map (fun i =>
      tmGlObjsVal ((refs.get i).map (tmRiSh
        (linGroupWord (fun j => as.get j) (linObjectUnflatten _ _ z i))))) =
      (linObjectWordPieces as Y z).map tmGlObjsVal := by
    simp only [linObjectWordPieces,List.map_ofFn,List.ofFn_eq_map,List.map_map,Function.comp_def,refs]
  dsimp only [refs] at henc hout hb
  simpa only [henc,hout] using hb

end GI.Impl
