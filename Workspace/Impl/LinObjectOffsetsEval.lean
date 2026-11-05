module

public import Workspace.Impl.LinObjectPieceSize
public import Workspace.Impl.LinObjectAffineEval

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset

theorem linObjectPc_mono {n M M' : ℕ} {as ns : List (Equiv.Perm (Fin n))}
    {S : List (TmRiO n)} (h : TmRiPc as ns M S) (hM : M ≤ M') : TmRiPc as ns M' S :=
  ⟨h.1,h.2.1.trans hM,h.2.2⟩

theorem linObjectMeta_mono {n M M' : ℕ} {Y : List (TmRiO n)}
    (h : TmRecObjOK M Y) (hM : M ≤ M') : TmRecObjOK M' Y := by
  intro o ho
  exact ⟨(h o ho).1,lt_of_lt_of_le (h o ho).2.1 (Nat.mul_le_mul_left 2 hM),(h o ho).2.2⟩

/-- The computed moved pieces meet every precondition of the zero-fuel offset collector. -/
theorem linObjectOffsets_moved_spec {P : Program} {b jsci jder jmem jm n : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership} {hc : ConstructiveMembership}
    (h : linObjectOffsetsAt P b jsci jder jmem jm hs hd hm hc)
    {Q : Type*} [CommGroup Q] (as ns : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (Y : List (TmRiO n)) (hok : TmRecObjOK Y.length Y)
    (hsol : TmRiListNorm (gens as) Y) (hNA : gens ns ≤ gens as)
    (H : Subgroup (Equiv.Perm (Fin n))) (hAH : gens as ≤ H)
    (hA : GI.Multicoset.Normalizes H (gens as)) (hN : GI.Multicoset.Normalizes H (gens ns))
    (hcomm : ∀ a ∈ gens as, ∀ b ∈ gens as, a * b * a⁻¹ * b⁻¹ ∈ gens ns)
    (hal : as.length ≤ n ^ 2) (hf : Fixes (gens ns) (tmGlMs Y))
    (z : Fin (as.length * (tmRiPcsO (gens as) Y).length) → ℤ)
    (g : Equiv.Perm (Fin n)) (hg : g ∈ H)
    (hy : Conf (gens as) (tmGlMs Y) (tmGlMs Y ↼ g)) :
    let refs := tmRiPcsO (gens as) Y
    let targets := linObjectMovedPieces as Y z g
    let input := Val.list [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),.list (targets.map tmGlObjsVal)]
    FunAll P b input (fun out cost =>
      linObjectOffsetsOut as π refs (tmGlMs targets.flatten) out ∧ cost ≤ linObjectOffsetsCost hs hm hc input.wt) := by
  classical
  let refs := tmRiPcsO (gens as) Y
  let targets := linObjectMovedPieces as Y z g
  have hZ := linObjectMovedPieces_conf as Y z H hA g hg hy
  have hpc : ∀ S ∈ refs ++ targets, TmRiPc as ns (2 * Y.length) S := by
    intro S hS
    rcases List.mem_append.mp hS with hS | hS
    · exact linObjectPc_mono (tmRiPcsO_pc le_rfl hf hS).1 (by omega)
    · exact linObjectPc_mono (linObjectMovedPieces_pc as ns Y z H hAH hA hN le_rfl hf g hg S hS) (by omega)
  have hlen : (refs ++ targets).length ≤ 2 * Y.length := by
    have hr : refs.length ≤ Y.length := tmRiPcsO_length_le (gens as) Y
    have ht : targets.length = refs.length := by
      simp only [targets,refs,linObjectMovedPieces,linObjectWordPieces,List.length_map,List.length_ofFn]
    simp only [List.length_append]
    omega
  have horig : linObjectOrigins Y (refs ++ targets).flatten := by
    intro o ho
    rw [List.flatten_append] at ho
    rcases List.mem_append.mp ho with ho | ho
    · obtain ⟨S,hS,ho⟩ := List.mem_flatten.mp ho
      exact linObjectOrigins_reference as Y S hS o ho
    · exact linObjectOrigins_movedPieces as Y z g o ho
  have hok' := linObjectMeta_mono (linObjectOrigins_ok Y _ horig hok) (show Y.length ≤ 2 * Y.length by omega)
  have hRef : ∀ S ∈ refs, tmGlMs S ∈ pieces (gens as) (tmGlMs Y) := by
    intro S hS
    have hh : tmGlMs S ∈ (((tmRiPcsO (gens as) Y).map tmGlMs : List _) : Multiset _) := by
      simp only [Multiset.mem_coe,List.mem_map]
      exact ⟨S,hS,rfl⟩
    rw [tmRiPcsO_ms] at hh
    exact hh
  have hTar : ∀ S ∈ targets, tmGlMs S ∈ pieces (gens as) (tmGlMs targets.flatten) :=
    linObjectMovedPieces_piece as Y z H hA g hg
  have hCover := linObjectPieces_cover (gens as) targets (tmGlMs targets.flatten) hTar rfl
  have hnorm : TmRiListNorm (gens as) (refs ++ targets).flatten := by
    intro o ho
    rw [List.flatten_append] at ho
    rcases List.mem_append.mp ho with ho | ho
    · obtain ⟨S, hS, ho⟩ := List.mem_flatten.mp ho
      exact linObjectReference_norm as Y hsol S hS o ho
    · exact linObjectMovedPieces_norm as Y hsol z H hA g hg o ho
  exact linObjectOffsets_spec h as ns π (tmGlMs Y) (tmGlMs targets.flatten) hZ refs targets
    hnorm hNA (hN.mono hAH) hcomm hal hpc hlen hok' hRef hTar hCover
    (linObjectOffsets_size as ns Y z g)

theorem linObjectAffineEval_offsets_spec {P : Program} {b jsci jder jmem jm jh n : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership} {hc : ConstructiveMembership}
    (h : linObjectAffineEvalAt P b jsci jder jmem jm jh hs hd hm hc)
    {Q : Type*} [CommGroup Q] (as ns : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (Y : List (TmRiO n)) (hok : TmRecObjOK Y.length Y)
    (hsol : TmRiListNorm (gens as) Y) (hNA : gens ns ≤ gens as)
    (H : Subgroup (Equiv.Perm (Fin n))) (hAH : gens as ≤ H)
    (hA : GI.Multicoset.Normalizes H (gens as)) (hN : GI.Multicoset.Normalizes H (gens ns))
    (hcomm : ∀ a ∈ gens as, ∀ b ∈ gens as, a * b * a⁻¹ * b⁻¹ ∈ gens ns)
    (hal : as.length ≤ n ^ 2) (hf : Fixes (gens ns) (tmGlMs Y))
    (z : Fin (as.length * (tmRiPcsO (gens as) Y).length) → ℤ)
    (g : Equiv.Perm (Fin n)) (hg : g ∈ H)
    (hy : Conf (gens as) (tmGlMs Y) (tmGlMs Y ↼ g)) :
    let refs := tmRiPcsO (gens as) Y
    let targets := linObjectMovedPieces as Y z g
    let input := Val.list [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),.list (targets.map tmGlObjsVal)]
    FunAll P (b + 117) input (fun out cost =>
      linObjectOffsetsOut as π refs (tmGlMs targets.flatten) out ∧ cost ≤ linObjectOffsetsCost hs hm hc input.wt) := by
  exact linObjectOffsets_moved_spec h.offsets as ns π Y hok hsol hNA H hAH hA hN hcomm hal hf z g hg hy

end GI.Impl
