import Workspace.Compat
import Workspace.BochertCommutator
import Mathlib.GroupTheory.SpecificGroups.Alternating

namespace GI.Bochert
open Equiv Equiv.Perm
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem threeCycle_apply_apply {g : Perm α} (ht : g.IsThreeCycle) (a : α) :
    g (g a) = g⁻¹ a := by
  have hp : g ^ 3 = 1 := by simpa only [ht.orderOf] using pow_orderOf_eq_one g
  apply g.injective
  rw [apply_inv_self]
  simpa [pow_succ, pow_two, mul_apply] using congrArg (fun p : Perm α => p a) hp

theorem threeCycle_images_ne {g : Perm α} (ht : g.IsThreeCycle) {a : α}
    (ha : g a ≠ a) : g a ≠ g⁻¹ a := by
  intro h
  have hh : g (g a) = a := by rw [h, apply_inv_self]
  have hi : g⁻¹ a = a := (threeCycle_apply_apply ht a).symm.trans hh
  exact ha (by simpa only [apply_inv_self] using congrArg g hi.symm)

theorem threeCycle_support {g : Perm α} (ht : g.IsThreeCycle) {a : α}
    (ha : g a ≠ a) : g.support = {a, g a, g⁻¹ a} := by
  have hi : g⁻¹ a ≠ a := by
    intro h
    exact ha (by simpa only [apply_inv_self] using congrArg g h.symm)
  have hs : ({a, g a, g⁻¹ a} : Finset α) ⊆ g.support := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨mem_support.mpr ha, apply_mem_support.mpr (mem_support.mpr ha),
      by simpa only [mem_support, apply_inv_self, ne_eq, eq_comm] using hi⟩
  apply (Finset.eq_of_subset_of_card_le hs _).symm
  rw [ht.card_support]
  simp [-Equiv.Perm.coe_inv, ha.symm, hi.symm, threeCycle_images_ne ht ha]

theorem threeCycle_formula {g : Perm α} (ht : g.IsThreeCycle) {a : α}
    (ha : g a ≠ a) : g = swap a (g⁻¹ a) * swap a (g a) := by
  have hi : g⁻¹ a ≠ a := by
    intro h
    exact ha (by simpa only [apply_inv_self] using congrArg g h.symm)
  have hh := threeCycle_images_ne ht ha
  ext b
  by_cases hb : b ∈ g.support
  · rw [threeCycle_support ht ha] at hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl
    · rw [mul_apply, swap_apply_left, swap_apply_of_ne_of_ne ha hh]
    · rw [mul_apply, swap_apply_right, swap_apply_left, threeCycle_apply_apply ht a]
    · rw [mul_apply, swap_apply_of_ne_of_ne hi hh.symm, swap_apply_right, apply_inv_self]
  · have hf : g b = b := by simpa only [mem_support, not_not] using hb
    rw [threeCycle_support ht ha] at hb
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
    simp [-Equiv.Perm.coe_inv, mul_apply, swap_apply_of_ne_of_ne hb.1 hb.2.1,
      swap_apply_of_ne_of_ne hb.1 hb.2.2, hf]

theorem orient_threeCycle {G : Subgroup (Perm α)} {g : Perm α}
    (hg : g ∈ G) (ht : g.IsThreeCycle) {a b : α}
    (ha : a ∈ g.support) (hb : b ∈ g.support) (hab : a ≠ b) :
    ∃ h ∈ G, h.IsThreeCycle ∧ h.support = g.support ∧ h a = b := by
  rw [threeCycle_support ht (mem_support.mp ha)] at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with hb | hb | hb
  · exact (hab hb.symm).elim
  · exact ⟨g, hg, ht, rfl, hb.symm⟩
  · exact ⟨g⁻¹, G.inv_mem hg, ht.inv, support_inv g, hb.symm⟩

theorem threeCycle_mem_of_support {G : Subgroup (Perm α)} {g h : Perm α}
    (hg : g ∈ G) (ht : g.IsThreeCycle) (hu : h.IsThreeCycle)
    (hs : g.support = h.support) : h ∈ G := by
  obtain ⟨a, ha, _⟩ := hu.isCycle
  have hga : a ∈ g.support := hs ▸ mem_support.mpr ha
  have hgb : h a ∈ g.support := hs ▸ apply_mem_support.mpr (mem_support.mpr ha)
  obtain ⟨q, hq, hqt, hqs, hqa⟩ := orient_threeCycle hg ht hga hgb ha.symm
  have hqm : q a ≠ a := by rwa [hqa]
  have hqi : q⁻¹ a ≠ a := by
    intro he
    exact hqm (by simpa only [apply_inv_self] using congrArg q he.symm)
  have hqim : q⁻¹ a ∈ h.support := by
    rw [← hs, ← hqs, mem_support, apply_inv_self]
    exact hqi.symm
  rw [threeCycle_support hu ha] at hqim
  simp only [Finset.mem_insert, Finset.mem_singleton] at hqim
  have hi : q⁻¹ a = h⁻¹ a := by
    rcases hqim with he | he | he
    · exact (hqi he).elim
    · exact (threeCycle_images_ne hqt hqm (hqa.trans he.symm)).elim
    · exact he
  have he : q = h := by rw [threeCycle_formula hqt hqm,
    threeCycle_formula hu ha, hqa, hi]
  exact he ▸ hq

end GI.Bochert
