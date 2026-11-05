module

public import Workspace.Compat
public import Workspace.BochertRelation
public import Workspace.BochertThreeCycle

@[expose] public section

open scoped commutatorElement

/-! An elementary proof of the three-cycle case of Jordan's theorem.
The support-connectivity and overlapping-cycle arguments are proved here. -/

namespace GI.Bochert
open Equiv Equiv.Perm MulAction
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem support_eq_triple {g : Perm α} (ht : g.IsThreeCycle) {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∈ g.support) (hb : b ∈ g.support) (hc : c ∈ g.support) :
    g.support = {a, b, c} := by
  apply (Finset.eq_of_subset_of_card_le
    (show ({a, b, c} : Finset α) ⊆ g.support by
      simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using
        And.intro ha (And.intro hb hc)) _).symm
  simp [ht.card_support, hab, hac, hbc]

theorem exists_threeCycle_support (G : Subgroup (Perm α))
    (hrel : ∀ a b, TripleRel G a b) {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ g ∈ G, g.IsThreeCycle ∧ g.support = {a, b, c} := by
  obtain hab' | ⟨g, hg, ht, hb, ha⟩ := hrel b a
  · exact (hab hab'.symm).elim
  obtain ⟨g, hg, ht, hgs, hgba⟩ := orient_threeCycle hg ht hb ha hab.symm
  have hgb : g b ≠ b := by rwa [hgba]
  have hgs : g.support = {b, a, g⁻¹ b} := by
    rw [threeCycle_support ht hgb, hgba]
  by_cases hgc : c ∈ g.support
  · exact ⟨g, hg, ht, support_eq_triple ht hab hac hbc
      (by rw [hgs]; simp) (by rw [hgs]; simp) hgc⟩
  obtain hbc' | ⟨h, hh, hu, hb', hc⟩ := hrel b c
  · exact (hbc hbc').elim
  obtain ⟨h, hh, hu, hhs, hhbc⟩ := orient_threeCycle hh hu hb' hc hbc
  have hhb : b ∈ h.support := hhs ▸ hb'
  have hhc : c ∈ h.support := hhs ▸ hc
  by_cases hha : a ∈ h.support
  · exact ⟨h, hh, hu, support_eq_triple hu hab hac hbc hha hhb hhc⟩
  have hhfa : h a = a := by simpa only [mem_support, not_not] using hha
  have hxb : g⁻¹ b ≠ b := by
    intro he
    exact hgb (by simpa only [apply_inv_self] using congrArg g he.symm)
  by_cases hhx : g⁻¹ b ∈ h.support
  · have hxc : g⁻¹ b ≠ c := by
      intro he
      apply hgc
      rw [hgs]
      simp [he]
    have hs : h.support = {b, c, g⁻¹ b} :=
      support_eq_triple hu hbc hxb.symm hxc.symm hhb hhc hhx
    have hxval : h (g⁻¹ b) = b := by
      have hm := apply_mem_support.mpr hhx
      rw [hs] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with he | he | he
      · exact he
      · exact (hxb (h.injective (he.trans hhbc.symm))).elim
      · exact (mem_support.mp hhx he).elim
    refine ⟨h * g * h⁻¹, G.mul_mem (G.mul_mem hh hg) (G.inv_mem hh),
      threeCycle_conj ht h, ?_⟩
    simp only [support_conj, hgs, Finset.map_insert, Finset.map_singleton,
      Equiv.toEmbedding_apply, hhbc, hhfa, hxval]
    ext d
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · have huniq : ∀ d : α, d ≠ b → g d = d ∨ h d = d := by
      intro d hdb
      by_cases hgd : g d = d
      · exact Or.inl hgd
      · right
        have hm := mem_support.mpr hgd
        rw [hgs] at hm
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with he | rfl | rfl
        · exact (hdb he).elim
        · exact hhfa
        · simpa only [mem_support, not_not] using hhx
    have hhb' : h b ≠ b := by rw [hhbc]; exact hbc.symm
    refine ⟨⁅g, h⁆, ?_, isThreeCycle_commutator_of_unique_common_moved hgb hhb' huniq, ?_⟩
    · rw [commutatorElement_def]
      exact G.mul_mem (G.mul_mem (G.mul_mem hg hh) (G.inv_mem hg)) (G.inv_mem hh)
    · rw [support_commutator_of_unique_common_moved hgb hhb' huniq, hgba, hhbc]
      exact Finset.insert_comm _ _ _

theorem alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem
    {G : Subgroup (Perm α)} (hG : IsPreprimitive G α) {g : Perm α}
    (ht : g.IsThreeCycle) (hg : g ∈ G) : alternatingGroup α ≤ G := by
  letI := hG
  rw [← closure_three_cycles_eq_alternating]
  apply (Subgroup.closure_le G).mpr
  intro h hu
  change h.IsThreeCycle at hu
  obtain ⟨a, ha, _⟩ := hu.isCycle
  have hi : h⁻¹ a ≠ a := by
    intro he
    exact ha (by simpa only [apply_inv_self] using congrArg h he.symm)
  obtain ⟨q, hq, hqt, hqs⟩ := exists_threeCycle_support G
    (tripleRel_universal G hg ht) ha.symm hi.symm (threeCycle_images_ne hu ha)
  exact threeCycle_mem_of_support hq hqt hu
    (hqs.trans (threeCycle_support hu ha).symm)

end GI.Bochert
