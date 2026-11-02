import Workspace.AlternatingSimple
import Mathlib.GroupTheory.Commutator.Basic

open scoped commutatorElement

namespace GI.NaturalGiant

open Equiv Equiv.Perm Subgroup

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
theorem exists_outside (s : Finset α) (hs : s.card < Fintype.card α) :
    ∃ a : α, a ∉ s := by
  by_contra hn
  push Not at hn
  have he : s = Finset.univ := Finset.eq_univ_iff_forall.mpr hn
  rw [he, Finset.card_univ] at hs
  exact (lt_irrefl _ hs)

/-- Even permutations detect every nonidentity permutation. The detecting
element is an actual three-cycle on a moved point, its image, and a third point. -/
theorem exists_alternating_noncommute (h5 : 5 ≤ Fintype.card α)
    (f : Perm α) (hf : f ≠ 1) :
    ∃ t : alternatingGroup α, f * (t : Perm α) ≠ (t : Perm α) * f := by
  have hm : ∃ a : α, f a ≠ a := by
    by_contra hn
    push Not at hn
    apply hf
    ext a
    exact hn a
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := exists_outside ({a, f a, f (f a)} : Finset α)
    (by have hc := Finset.card_le_three (a := a) (b := f a) (c := f (f a)); omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
  let t₀ : Perm α := swap a b * swap a (f a)
  have ht : IsThreeCycle t₀ := isThreeCycle_swap_mul_swap_same (Ne.symm hb.1) ha.symm hb.2.1
  have hta : t₀ a = f a := by
    change swap a b (swap a (f a) a) = f a
    rw [swap_apply_left, swap_apply_of_ne_of_ne ha (Ne.symm hb.2.1)]
  have htfa : t₀ (f a) = b := by simp [t₀]
  refine ⟨⟨t₀, ht.mem_alternatingGroup⟩, ?_⟩
  intro he
  have h := congrArg (fun p : Perm α => p a) he
  change f (t₀ a) = t₀ (f a) at h
  rw [hta, htfa] at h
  exact hb.2.2 h.symm

/-- The centralizer of the natural alternating group in the full symmetric
group is trivial. -/
theorem centralizer_eq_one (h5 : 5 ≤ Fintype.card α) (f : Perm α)
    (hc : ∀ t : alternatingGroup α, f * (t : Perm α) = (t : Perm α) * f) : f = 1 := by
  by_contra hf
  obtain ⟨t, ht⟩ := exists_alternating_noncommute h5 f hf
  exact ht (hc t)

/-- A normal subgroup of the natural symmetric group is trivial or contains
the natural alternating group. This uses proved alternating simplicity and
the proved centralizer assertion, not a classification premise. -/
theorem normal_symm_dichotomy (h5 : 5 ≤ Fintype.card α)
    (N : Subgroup (Perm α)) [N.Normal] : N = ⊥ ∨ alternatingGroup α ≤ N := by
  letI : IsSimpleGroup (alternatingGroup α) := AlternatingSimple.isSimple h5
  let K := N.comap (alternatingGroup α).subtype
  haveI : K.Normal := (inferInstance : N.Normal).comap (alternatingGroup α).subtype
  rcases (inferInstance : K.Normal).eq_bot_or_eq_top with hb | ht
  · left
    apply (Subgroup.eq_bot_iff_forall N).mpr
    intro g hg
    apply centralizer_eq_one h5 g
    intro t
    have hm : ⁅g, (t : Perm α)⁆ ∈ N ⊓ alternatingGroup α :=
      Subgroup.commutator_le_inf N (alternatingGroup α)
        (Subgroup.commutator_mem_commutator hg t.property)
    let c : alternatingGroup α := ⟨⁅g, (t : Perm α)⁆, hm.2⟩
    have hc : c ∈ K := hm.1
    rw [hb, Subgroup.mem_bot] at hc
    have he : ⁅g, (t : Perm α)⁆ = 1 := congrArg Subtype.val hc
    exact commutatorElement_eq_one_iff_mul_comm.mp he
  · right
    intro g hg
    have hm : (⟨g, hg⟩ : alternatingGroup α) ∈ K := by rw [ht]; exact Subgroup.mem_top _
    exact hm

/-- There are exactly two natural giant subgroups. -/
theorem giant_eq_alt_or_top (h5 : 5 ≤ Fintype.card α)
    {H : Subgroup (Perm α)} (hgiant : alternatingGroup α ≤ H) :
    H = alternatingGroup α ∨ H = ⊤ := by
  letI : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hd := Subgroup.index_dvd_of_le hgiant
  rw [alternatingGroup.index_eq_two] at hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
  · exact Or.inr (Subgroup.index_eq_one.mp h1)
  · exact Or.inl (Equiv.Perm.eq_alternatingGroup_of_index_eq_two h2)

/-- At least one even permutation moves each natural point. -/
theorem alternating_moves_point (h5 : 5 ≤ Fintype.card α) (a : α) :
    ∃ t : alternatingGroup α, (t : Perm α) a ≠ a := by
  obtain ⟨b, hb⟩ := exists_outside ({a} : Finset α) (by simp; omega)
  have hba : b ≠ a := by simpa only [Finset.mem_singleton] using hb
  obtain ⟨c, hc⟩ := exists_outside ({a, b} : Finset α)
    (by have hcard := Finset.card_le_two (a := a) (b := b); omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  let t₀ : Perm α := swap a c * swap a b
  have ht : IsThreeCycle t₀ := isThreeCycle_swap_mul_swap_same (Ne.symm hc.1) hba.symm hc.2
  have he : t₀ a = b := by
    change swap a c (swap a b a) = b
    rw [swap_apply_left, swap_apply_of_ne_of_ne hba (Ne.symm hc.2)]
  exact ⟨⟨t₀, ht.mem_alternatingGroup⟩, by change t₀ a ≠ a; rwa [he]⟩

theorem normal_symm_fin {n : ℕ} (hn : 5 ≤ n)
    (N : Subgroup (Perm (Fin n))) [N.Normal] : N = ⊥ ∨ alternatingGroup (Fin n) ≤ N :=
  normal_symm_dichotomy (by simpa using hn) N

end GI.NaturalGiant
