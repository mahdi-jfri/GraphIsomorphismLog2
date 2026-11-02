import Workspace.Impl.LinObjectBasisMath

namespace GI.Impl
open GI.Cited GI.Multicoset

noncomputable def linObjectMovedPieces {n : ℕ} (as : List (Equiv.Perm (Fin n)))
    (Y : List (TmRiO n)) (z : Fin (as.length * (tmRiPcsO (gens as) Y).length) → ℤ)
    (g : Equiv.Perm (Fin n)) : List (List (TmRiO n)) :=
  (linObjectWordPieces as Y z).map (List.map (tmRiSh g))

theorem linObjectMs_shiftPieces {n : ℕ} (Ps : List (List (TmRiO n))) (g : Equiv.Perm (Fin n)) :
    tmGlMs (Ps.map (List.map (tmRiSh g))).flatten = tmGlMs Ps.flatten ↼ g := by
  have he : (Ps.map (List.map (tmRiSh g))).flatten = Ps.flatten.map (tmRiSh g) := by
    induction Ps with
    | nil => rfl
    | cons S Ps ih => simp only [List.map_cons, List.flatten_cons, List.map_append, ih]
  rw [he,tmRi_ms_shift]

theorem linObjectMovedPieces_piece {n : ℕ} (as : List (Equiv.Perm (Fin n))) (Y : List (TmRiO n))
    (z : Fin (as.length * (tmRiPcsO (gens as) Y).length) → ℤ)
    (H : Subgroup (Equiv.Perm (Fin n))) (hn : Normalizes H (gens as))
    (g : Equiv.Perm (Fin n)) (hg : g ∈ H)
    (S : List (TmRiO n)) (hS : S ∈ linObjectMovedPieces as Y z g) :
    tmGlMs S ∈ pieces (gens as) (tmGlMs (linObjectMovedPieces as Y z g).flatten) := by
  classical
  obtain ⟨T,hT,rfl⟩ := List.mem_map.mp hS
  rw [linObjectMovedPieces,linObjectMs_shiftPieces,pieces_act hn hg]
  exact Finset.mem_image.mpr ⟨tmGlMs T,linObjectWordPieces_piece as Y z T hT,tmRi_ms_shift g T |>.symm⟩

theorem linObjectMovedPieces_conf {n : ℕ} (as : List (Equiv.Perm (Fin n))) (Y : List (TmRiO n))
    (z : Fin (as.length * (tmRiPcsO (gens as) Y).length) → ℤ)
    (H : Subgroup (Equiv.Perm (Fin n))) (hn : Normalizes H (gens as))
    (g : Equiv.Perm (Fin n)) (hg : g ∈ H)
    (hy : Conf (gens as) (tmGlMs Y) (tmGlMs Y ↼ g)) :
    Conf (gens as) (tmGlMs Y) (tmGlMs (linObjectMovedPieces as Y z g).flatten) := by
  rw [linObjectMovedPieces,linObjectMs_shiftPieces]
  exact (affine_law hn hg hy (linObjectWordPieces_conf as Y z)).2.2

/-- Shifting a piece preserves the table precondition under the two normality hypotheses. -/
theorem linObjectPc_shift {n M : ℕ} (as ns : List (Equiv.Perm (Fin n)))
    (H : Subgroup (Equiv.Perm (Fin n))) (hA : Normalizes H (gens as)) (hN : Normalizes H (gens ns))
    (S : List (TmRiO n)) (hS : TmRiPc as ns M S)
    (g : Equiv.Perm (Fin n)) (hg : g ∈ H) : TmRiPc as ns M (S.map (tmRiSh g)) := by
  refine ⟨by simpa using hS.1, by simpa using hS.2.1, ?_, ?_⟩
  · rw [tmRi_ms_shift]
    intro x hx y hy
    rw [mem_act] at hx hy
    have hh := hS.2.2.1 _ hx _ hy
    have hh' := (sameOrb_act_iff hA hg).mpr hh
    simpa using hh'
  · rw [tmRi_ms_shift]
    exact hS.2.2.2.act hN hg

/-- Every stored subgroup and color still comes from the original target. -/
def linObjectOrigins {n : ℕ} (Y Z : List (TmRiO n)) : Prop :=
  ∀ o ∈ Z, ∃ o' ∈ Y, o.1 = o'.1 ∧ o.2.1 = o'.2.1

theorem linObjectOrigins_shift {n : ℕ} (Y Z : List (TmRiO n))
    (h : linObjectOrigins Y Z) (g : Equiv.Perm (Fin n)) :
    linObjectOrigins Y (Z.map (tmRiSh g)) := by
  intro o ho
  obtain ⟨o₀,ho₀,rfl⟩ := List.mem_map.mp ho
  exact h o₀ ho₀

theorem linObjectOrigins_ok {n M : ℕ} (Y Z : List (TmRiO n))
    (h : linObjectOrigins Y Z) (hok : TmRecObjOK M Y) : TmRecObjOK M Z := by
  intro o ho
  obtain ⟨o₀,ho₀,hc,hg⟩ := h o ho
  refine ⟨by simpa only [hg] using (hok o₀ ho₀).1,
    by simpa only [hc] using (hok o₀ ho₀).2.1, ?_⟩
  intro o' ho' he
  obtain ⟨o₁,ho₁,hc',hg'⟩ := h o' ho'
  rw [hg,hg']
  exact (hok o₀ ho₀).2.2 o₁ ho₁ (hc.symm.trans (he.trans hc'))

theorem linObjectOrigins_reference {n : ℕ} (as : List (Equiv.Perm (Fin n))) (Y : List (TmRiO n))
    (S : List (TmRiO n)) (hS : S ∈ tmRiPcsO (gens as) Y) : linObjectOrigins Y S := by
  obtain ⟨a,ha,rfl⟩ := tmRiPcsO_mem hS
  intro o ho
  exact ⟨o,(List.mem_filter.mp ho).1,rfl,rfl⟩

theorem linObjectOrigins_wordPieces {n : ℕ} (as : List (Equiv.Perm (Fin n))) (Y : List (TmRiO n))
    (z : Fin (as.length * (tmRiPcsO (gens as) Y).length) → ℤ) :
    linObjectOrigins Y (linObjectWordPieces as Y z).flatten := by
  intro o ho
  obtain ⟨S,hS,ho⟩ := List.mem_flatten.mp ho
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hS
  exact linObjectOrigins_shift Y _
    (linObjectOrigins_reference as Y _ (List.get_mem _ i)) _ o ho

theorem linObjectOrigins_movedPieces {n : ℕ} (as : List (Equiv.Perm (Fin n))) (Y : List (TmRiO n))
    (z : Fin (as.length * (tmRiPcsO (gens as) Y).length) → ℤ) (g : Equiv.Perm (Fin n)) :
    linObjectOrigins Y (linObjectMovedPieces as Y z g).flatten := by
  intro o ho
  obtain ⟨S,hS,ho⟩ := List.mem_flatten.mp ho
  obtain ⟨T,hT,rfl⟩ := List.mem_map.mp hS
  obtain ⟨o₀,ho₀,rfl⟩ := List.mem_map.mp ho
  exact linObjectOrigins_wordPieces as Y z o₀ (List.mem_flatten.mpr ⟨T,hT,ho₀⟩)

theorem linObjectWordPieces_pc {n M : ℕ} (as ns : List (Equiv.Perm (Fin n))) (Y : List (TmRiO n))
    (z : Fin (as.length * (tmRiPcsO (gens as) Y).length) → ℤ)
    (H : Subgroup (Equiv.Perm (Fin n))) (hAH : gens as ≤ H)
    (hA : Normalizes H (gens as)) (hN : Normalizes H (gens ns))
    (hy : Y.length ≤ M) (hf : Fixes (gens ns) (tmGlMs Y)) :
    ∀ S ∈ linObjectWordPieces as Y z, TmRiPc as ns M S := by
  intro S hS
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hS
  exact linObjectPc_shift as ns H hA hN _
    (tmRiPcsO_pc hy hf (List.get_mem _ i)).1 _ (hAH (linPermWord_mem as _))

theorem linObjectMovedPieces_pc {n M : ℕ} (as ns : List (Equiv.Perm (Fin n))) (Y : List (TmRiO n))
    (z : Fin (as.length * (tmRiPcsO (gens as) Y).length) → ℤ)
    (H : Subgroup (Equiv.Perm (Fin n))) (hAH : gens as ≤ H)
    (hA : Normalizes H (gens as)) (hN : Normalizes H (gens ns))
    (hy : Y.length ≤ M) (hf : Fixes (gens ns) (tmGlMs Y))
    (g : Equiv.Perm (Fin n)) (hg : g ∈ H) :
    ∀ S ∈ linObjectMovedPieces as Y z g, TmRiPc as ns M S := by
  intro S hS
  obtain ⟨T,hT,rfl⟩ := List.mem_map.mp hS
  exact linObjectPc_shift as ns H hA hN T
    (linObjectWordPieces_pc as ns Y z H hAH hA hN hy hf T hT) g hg

theorem linObjectOrigins_tmRiOK {n C : ℕ} (Y Z : List (TmRiO n))
    (h : linObjectOrigins Y Z) (hok : TmRiOK C Y) : TmRiOK C Z := by
  intro o ho
  obtain ⟨o₀,ho₀,hc,hg⟩ := h o ho
  refine ⟨by simpa only [hg] using (hok o₀ ho₀).1,
    by simpa only [hc] using (hok o₀ ho₀).2.1, ?_⟩
  intro o' ho' he
  obtain ⟨o₁,ho₁,hc',hg'⟩ := h o' ho'
  rw [hg,hg']
  exact (hok o₀ ho₀).2.2 o₁ ho₁ (hc.symm.trans (he.trans hc'))

end GI.Impl
