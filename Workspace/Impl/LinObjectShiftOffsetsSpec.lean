import Workspace.Impl.LinObjectShiftOffsetsCost

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset

set_option maxHeartbeats 300000 in
set_option maxRecDepth 2000 in
theorem linObjectShiftOffsets_spec {P : Program} {b jsci jder jmem jm n : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership} {hc : ConstructiveMembership}
    (h : linObjectShiftOffsetsAt P b jsci jder jmem jm hs hd hm hc)
    {Q : Type*} [CommGroup Q] (as ns : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (Y : List (TmRiO n)) (hok : TmRecObjOK Y.length Y)
    (hsol : IsSolvable (gens as)) (hNA : gens ns ≤ gens as)
    (H : Subgroup (Equiv.Perm (Fin n))) (hAH : gens as ≤ H)
    (hA : GI.Multicoset.Normalizes H (gens as)) (hN : GI.Multicoset.Normalizes H (gens ns))
    (hcomm : ∀ a ∈ gens as, ∀ b ∈ gens as, a * b * a⁻¹ * b⁻¹ ∈ gens ns)
    (hal : as.length ≤ n ^ 2) (hf : Fixes (gens ns) (tmGlMs Y))
    (g : Equiv.Perm (Fin n)) (hg : g ∈ H)
    (hy : Conf (gens as) (tmGlMs Y) (tmGlMs Y ↼ g)) :
    let refs := tmRiPcsO (gens as) Y
    let input := Val.list [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),encPerm g]
    FunAll P b input (fun out cost => linObjectOffsetsOut as π refs (tmGlMs Y ↼ g) out ∧
      cost ≤ linObjectShiftOffsetsCost hs hm hc input.wt) := by
  let refs := tmRiPcsO (gens as) Y
  let targets := refs.map (List.map (tmRiSh g))
  let input := Val.list [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),encPerm g]
  let W := input.wt
  let MB := linObjectShiftMapBudget W
  let OB := linObjectShiftOffsetsBudget hs hm hc W
  let C := linObjectShiftSource hs hm hc W
  have wa : (encGroup as).wt ≤ W := (wt_le_wt_list (by simp [input,W])).le
  have wn : (encGroup ns).wt ≤ W := (wt_le_wt_list (by simp [input,W])).le
  have wr : (Val.list (refs.map tmGlObjsVal)).wt ≤ W := (wt_le_wt_list (by simp [input,W])).le
  have wg : (encPerm g).wt ≤ W := (wt_le_wt_list (by simp [input,W])).le
  have hn : n ≤ W := by
    have hh := S_le_wt_encGroup as
    have hmul : n + 1 ≤ (as.length + 2) * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hl : Y.length ≤ W := by
    have hh := linObjectPieces_wt refs
    rw [linObjectReference_length] at hh
    omega
  have hokRi : TmRiOK (2 * Y.length) Y := fun o ho => ⟨(hok o ho).1,(hok o ho).2.1.le,(hok o ho).2.2⟩
  have hsh (S : List (TmRiO n)) (hS : S ∈ refs) :
      FunDet P (b + 85) (.list [encPerm g,tmGlObjsVal S]) (tmGlObjsVal (S.map (tmRiSh g)))
        (tmRiMapShC n (2 * Y.length) Y.length) := by
    have hOkS := linObjectOrigins_tmRiOK Y S (linObjectOrigins_reference as Y S hS) hokRi
    have hr := tmRi_mapShift_spec h.offsets.table.orbit.inner g hOkS
    have hlen : S.length ≤ Y.length := by
      obtain ⟨o,ho,rfl⟩ := tmRiPcsO_mem hS
      exact List.length_filter_le _ _
    exact hr.mono (linObjectShiftCost_mono hlen)
  have hshB : tmRiMapShC n (2 * Y.length) Y.length ≤ linObjectShiftShiftBudget W :=
    linPolyEnvelope_bound linObjectEvalShiftPoly (hn.trans (by omega)) (by omega) (by omega)
  have hmArg : (Val.list [encPerm g,.list (refs.map tmGlObjsVal)]).wt ≤ linObjectShiftMapArg W := by
    have hh := wt_list2_le (encPerm g) (.list (refs.map tmGlObjsVal))
    have hp : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by decide) _
    unfold linObjectShiftMapArg
    omega
  have hmap : FunDet P (b + 1) (.list [encPerm g,.list (refs.map tmGlObjsVal)])
      (.list (targets.map tmGlObjsVal)) MB := by
    have hr := linMapEncoded_spec h.move tmGlObjsVal (fun _ _ he => tmRi_objsVal_inj he)
      (fun S => tmGlObjsVal (S.map (tmRiSh g))) (encPerm g) refs (tmRiMapShC n (2 * Y.length) Y.length) hsh
    have hb : linMapBudget (Val.list [encPerm g,.list (refs.map tmGlObjsVal)]).wt
        (tmRiMapShC n (2 * Y.length) Y.length) ≤ MB :=
      linPolyEnvelope_bound linObjectEvalMapPoly (Nat.zero_le _) (hmArg.trans (by omega)) (hshB.trans (by omega))
    simpa only [targets,List.map_map,Function.comp_def] using hr.mono hb
  have wm := hmap.wt_lt.le
  have hoArg : (Val.list [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),.list (targets.map tmGlObjsVal)]).wt ≤
      linObjectShiftOffsetsArg W := linObjectEvalArg4 _ _ _ _ W MB (by omega) (by omega) (by omega) wm
  have ho : FunAll P (b + 4) (.list [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),.list (targets.map tmGlObjsVal)])
      (fun out cost => linObjectOffsetsOut as π refs (tmGlMs Y ↼ g) out ∧ cost ≤ OB) := by
    have hr := linObjectOffsets_moved_spec h.offsets as ns π Y hok hsol hNA H hAH hA hN hcomm hal hf
      (0 : Fin (as.length * refs.length) → ℤ) g hg hy
    have hr' : FunAll P (b + 4) (.list [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),.list (targets.map tmGlObjsVal)])
        (fun out cost => linObjectOffsetsOut as π refs (tmGlMs Y ↼ g) out ∧
          cost ≤ linObjectOffsetsCost hs hm hc (Val.list [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),
            .list (targets.map tmGlObjsVal)]).wt) := by
      simpa only [linObjectMovedPieces,linObjectWordPieces_zero,linObjectMs_shiftPieces,linObjectReference_ms] using hr
    exact hr'.mono fun out cost hout => ⟨hout.1,hout.2.trans
      (linPolyEnvelope_bound (linObjectOffsetsCost_poly hs hm hc) (Nat.zero_le _) hoArg (Nat.zero_le _))⟩
  have hp : W + MB + OB + 1 ≤ (W + MB + OB + 1) ^ 2 := Nat.le_self_pow (by decide) _
  have wC : W ≤ C := by change W ≤ 100 * (W + MB + OB + 1) ^ 2; omega
  have mC : MB ≤ C := by change MB ≤ 100 * (W + MB + OB + 1) ^ 2; omega
  have oC : OB ≤ C := by change OB ≤ 100 * (W + MB + OB + 1) ^ 2; omega
  have hC : 100 ≤ C := by change 100 ≤ 100 * (W + MB + OB + 1) ^ 2; omega
  exact linObjectShiftOffsets_comp h.entry (encGroup as) (encGroup ns) (.list (refs.map tmGlObjsVal))
    (encPerm g) (.list (targets.map tmGlObjsVal)) (fun out => linObjectOffsetsOut as π refs (tmGlMs Y ↼ g) out)
    hC wC (hmap.mono mC) (ho.mono fun out cost hout => ⟨hout.1,hout.2.trans oC⟩)

end GI.Impl
