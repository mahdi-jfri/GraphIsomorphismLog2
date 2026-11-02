import Workspace.Impl.LinObjectOffsetsEval

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset

set_option maxHeartbeats 400000 in
/-- Source and target configurations may have different local pieces.
The joint metadata bound is the number of listed input objects. -/
theorem linObjectOffsets_source_spec {P : Program} {b jsci jder jmem jm n : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership} {hc : ConstructiveMembership}
    (h : linObjectOffsetsAt P b jsci jder jmem jm hs hd hm hc)
    {Q : Type*} [CommGroup Q] (as ns : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (Y X : List (TmRiO n)) (hok : TmRecObjOK (Y.length+X.length) (Y++X))
    (hsol : IsSolvable (gens as)) (hNA : gens ns ≤ gens as)
    (H : Subgroup (Equiv.Perm (Fin n))) (hAH : gens as ≤ H)
    (hA : GI.Multicoset.Normalizes H (gens as)) (hN : GI.Multicoset.Normalizes H (gens ns))
    (hcomm : ∀ a ∈ gens as, ∀ b ∈ gens as, a*b*a⁻¹*b⁻¹ ∈ gens ns)
    (hal : as.length ≤ n^2) (hfY : Fixes (gens ns) (tmGlMs Y)) (hfX : Fixes (gens ns) (tmGlMs X))
    (g : Equiv.Perm (Fin n)) (hg : g ∈ H)
    (hZ : Conf (gens as) (tmGlMs Y) (tmGlMs X ↼ g)) :
    let refs := tmRiPcsO (gens as) Y
    let targets := (tmRiPcsO (gens as) X).map (List.map (tmRiSh g))
    let input := Val.list [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),.list (targets.map tmGlObjsVal)]
    FunAll P b input (fun out cost => linObjectOffsetsOut as π refs (tmGlMs X ↼ g) out ∧
      cost ≤ linObjectOffsetsCost hs hm hc input.wt) := by
  let refs := tmRiPcsO (gens as) Y
  let targets := linObjectMovedPieces as X (0 : Fin (as.length*(tmRiPcsO (gens as) X).length) → ℤ) g
  let M := Y.length+X.length
  have htms : tmGlMs targets.flatten = tmGlMs X ↼ g := by
    simp only [targets,linObjectMovedPieces,linObjectWordPieces_zero,linObjectMs_shiftPieces,linObjectReference_ms]
  have hpc : ∀ S ∈ refs++targets, TmRiPc as ns M S := by
    intro S hS
    rcases List.mem_append.mp hS with hS | hS
    · exact (tmRiPcsO_pc (show Y.length ≤ M by omega) hfY hS).1
    · exact linObjectMovedPieces_pc as ns X _ H hAH hA hN (show X.length ≤ M by omega) hfX g hg S hS
  have hlen : (refs++targets).length ≤ M := by
    have hr := tmRiPcsO_length_le (gens as) Y
    have ht := tmRiPcsO_length_le (gens as) X
    simp only [refs,targets,linObjectMovedPieces,linObjectWordPieces,List.length_append,List.length_map,List.length_ofFn]
    omega
  have horig : linObjectOrigins (Y++X) (refs++targets).flatten := by
    intro o ho
    rw [List.flatten_append] at ho
    rcases List.mem_append.mp ho with ho | ho
    · obtain ⟨S,hS,ho⟩ := List.mem_flatten.mp ho
      obtain ⟨o',ho',hc',hg'⟩ := linObjectOrigins_reference as Y S hS o ho
      exact ⟨o',List.mem_append_left _ ho',hc',hg'⟩
    · obtain ⟨o',ho',hc',hg'⟩ := linObjectOrigins_movedPieces as X _ g o ho
      exact ⟨o',List.mem_append_right _ ho',hc',hg'⟩
  have hOK := linObjectOrigins_ok (Y++X) _ horig hok
  have hRef : ∀ S ∈ refs, tmGlMs S ∈ pieces (gens as) (tmGlMs Y) := by
    intro S hS
    have hh : tmGlMs S ∈ (((tmRiPcsO (gens as) Y).map tmGlMs : List _) : Multiset _) := by
      simp only [Multiset.mem_coe,List.mem_map]
      exact ⟨S,hS,rfl⟩
    rwa [tmRiPcsO_ms] at hh
  have hTar : ∀ S ∈ targets, tmGlMs S ∈ pieces (gens as) (tmGlMs X ↼ g) := by
    intro S hS
    rw [← htms]
    exact linObjectMovedPieces_piece as X _ H hA g hg S hS
  have hCover := linObjectPieces_cover (gens as) targets (tmGlMs X ↼ g) hTar htms
  have hMsize : M ≤ (Val.list [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),.list (targets.map tmGlObjsVal)]).wt := by
    have hr := linObjectPieces_wt refs
    have ht := linObjectPieces_wt targets
    rw [linObjectReference_length] at hr
    rw [linObjectMovedPieces_length] at ht
    have hs' := sum_wt_lt_wt_list [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),.list (targets.map tmGlObjsVal)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hs'
    omega
  have hr := linObjectOffsets_spec h as ns π (tmGlMs Y) (tmGlMs X ↼ g) hZ refs targets
    hsol hNA (hN.mono hAH) hcomm hal hpc hlen hOK hRef hTar hCover hMsize
  simpa only [targets,linObjectMovedPieces,linObjectWordPieces_zero] using hr

end GI.Impl
