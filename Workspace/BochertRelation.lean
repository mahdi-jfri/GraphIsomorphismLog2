import Workspace.Compat
import Workspace.BochertCommutator
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.SpecificGroups.Alternating

/-! Elementary support connectivity for three-cycles in a primitive permutation group.
This proof uses only mathlib; it does not assume Jordan's theorem. -/

namespace GI.Bochert
open Equiv Equiv.Perm MulAction
open scoped Pointwise
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem threeCycle_conj {g : Perm α} (h : g.IsThreeCycle) (q : Perm α) :
    (q * g * q⁻¹).IsThreeCycle := by
  apply card_support_eq_three_iff.mp
  rw [card_support_conj, h.card_support]

theorem conj_mem_support {g q : Perm α} {a : α} (ha : a ∈ g.support) :
    q a ∈ (q * g * q⁻¹).support := by
  rw [mem_support]
  simpa only [mul_apply, inv_apply_self, q.injective.ne_iff] using mem_support.mp ha

def TripleRel (G : Subgroup (Perm α)) (a b : α) : Prop :=
  a = b ∨ ∃ g ∈ G, g.IsThreeCycle ∧ a ∈ g.support ∧ b ∈ g.support

theorem tripleRel_refl (G : Subgroup (Perm α)) (a : α) : TripleRel G a a :=
  Or.inl rfl

theorem tripleRel_symm {G : Subgroup (Perm α)} {a b : α}
    (h : TripleRel G a b) : TripleRel G b a := by
  rcases h with h | ⟨g, hg, ht, ha, hb⟩
  · exact Or.inl h.symm
  · exact Or.inr ⟨g, hg, ht, hb, ha⟩

theorem tripleRel_conj {G : Subgroup (Perm α)} {a b : α}
    (q : G) (h : TripleRel G a b) : TripleRel G (q.val a) (q.val b) := by
  rcases h with rfl | ⟨g, hg, ht, ha, hb⟩
  · exact tripleRel_refl _ _
  · exact Or.inr ⟨q.val * g * q.val⁻¹,
      G.mul_mem (G.mul_mem q.property hg) (G.inv_mem q.property),
      threeCycle_conj ht q.val, conj_mem_support ha, conj_mem_support hb⟩

theorem tripleRel_trans {G : Subgroup (Perm α)} {a b c : α}
    (hab : TripleRel G a b) (hbc : TripleRel G b c) : TripleRel G a c := by
  rcases hab with rfl | ⟨g, hg, ht, ha, hb⟩
  · exact hbc
  rcases hbc with rfl | ⟨h, hh, hu, hb', hc⟩
  · exact Or.inr ⟨g, hg, ht, ha, hb⟩
  by_cases ha' : a ∈ h.support
  · exact Or.inr ⟨h, hh, hu, ha', hc⟩
  have hfix : h a = a := by simpa only [mem_support, not_not] using ha'
  obtain ⟨n, hn⟩ := (hu.isCycle.sameCycle (mem_support.mp hb')
    (mem_support.mp hc)).exists_nat_pow_eq
  have hpa : (h ^ n) a = a := pow_apply_eq_self_of_apply_eq_self hfix n
  have hr := tripleRel_conj (⟨h ^ n, G.pow_mem hh n⟩ : G)
    (Or.inr ⟨g, hg, ht, ha, hb⟩ : TripleRel G a b)
  simpa only [hpa, hn] using hr

theorem tripleRel_isBlock (G : Subgroup (Perm α)) (a : α) :
    IsBlock G {b | TripleRel G a b} := by
  rw [isBlock_iff_smul_eq_of_mem]
  intro q b hb hqb
  change TripleRel G a b at hb
  change TripleRel G a (q.val b) at hqb
  have haq : TripleRel G a (q.val a) :=
    tripleRel_trans hqb (tripleRel_symm (tripleRel_conj q hb))
  ext c
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact tripleRel_trans haq (tripleRel_conj q hd)
  · intro hc
    refine ⟨q.val⁻¹ c, ?_, ?_⟩
    · have hr := tripleRel_conj q⁻¹ (tripleRel_trans (tripleRel_symm haq) hc)
      simpa using hr
    · change q.val (q.val⁻¹ c) = c
      exact q.val.apply_symm_apply c

theorem tripleRel_universal (G : Subgroup (Perm α)) [IsPreprimitive G α]
    {g : Perm α} (hg : g ∈ G) (ht : g.IsThreeCycle) (a b : α) :
    TripleRel G a b := by
  obtain ⟨u, hu, _⟩ := ht.isCycle
  have huu : TripleRel G u (g u) := Or.inr
    ⟨g, hg, ht, mem_support.mpr hu, by simpa using mem_support.mpr hu⟩
  have heq : {v | TripleRel G u v} = Set.univ := by
    rcases (tripleRel_isBlock G u).subsingleton_or_eq_univ with h | h
    · exact (hu (h huu (tripleRel_refl G u))).elim
    · exact h
  have hua : TripleRel G u a := by
    change a ∈ {v | TripleRel G u v}
    rw [heq]; trivial
  have hub : TripleRel G u b := by
    change b ∈ {v | TripleRel G u v}
    rw [heq]; trivial
  exact tripleRel_trans (tripleRel_symm hua) hub

end GI.Bochert
