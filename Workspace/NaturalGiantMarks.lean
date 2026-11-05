module

public import Workspace.NaturalGiantCentralizer

@[expose] public section

open scoped commutatorElement

namespace GI.NaturalGiant

open Equiv Equiv.Perm Subgroup

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- No nontrivial alternating quotient with a transitive kernel starts in
the natural alternating action. -/
theorem no_alternating_step (h5 : 5 ≤ Fintype.card α) {a : α}
    {L : Subgroup (Perm α)} {k : ℕ} (hk : 5 ≤ k)
    (s : VisibleStep a (alternatingGroup α) L k) : False := by
  letI : IsSimpleGroup (alternatingGroup α) := AlternatingSimple.isSimple h5
  letI : IsSimpleGroup (alternatingGroup (Fin k)) := AlternatingSimple.isSimple_fin hk
  rcases (inferInstance : s.quotient.ker.Normal).eq_bot_or_eq_top with hb | ht
  · obtain ⟨t, hmove⟩ := alternating_moves_point h5 a
    obtain ⟨l, hl⟩ := s.transitiveKernel t
    have hlker : Subgroup.inclusion s.lower l ∈ s.quotient.ker := (s.kernel _).mpr l.property
    rw [hb, Subgroup.mem_bot] at hlker
    have hlone : (l : Perm α) = 1 := congrArg Subtype.val hlker
    rw [hlone] at hl
    exact hmove hl.symm
  · obtain ⟨z, hz⟩ := exists_ne (1 : alternatingGroup (Fin k))
    obtain ⟨h, hh⟩ := s.onto z
    have hker : h ∈ s.quotient.ker := by rw [ht]; exact Subgroup.mem_top h
    change s.quotient h = 1 at hker
    rw [hh] at hker
    exact hz hker

/-- Killing all even permutations forces a symmetric-group quotient to be
abelian, because every commutator has sign one. -/
theorem quotient_commutes_of_kills_alternating {S : Type*} [Group S]
    (q : Perm α →* S) (onto : Function.Surjective q)
    (kills : alternatingGroup α ≤ q.ker) : ∀ x y : S, x * y = y * x := by
  intro x y
  obtain ⟨f, rfl⟩ := onto x
  obtain ⟨g, rfl⟩ := onto y
  have heven : ⁅f, g⁆ ∈ alternatingGroup α := by
    rw [mem_alternatingGroup, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  have hq : q ⁅f, g⁆ = 1 := kills heven
  rw [map_commutatorElement] at hq
  exact commutatorElement_eq_one_iff_mul_comm.mp hq

/-- No nonabelian alternating quotient with a transitive kernel starts in
the natural symmetric action. -/
theorem no_symmetric_step (h5 : 5 ≤ Fintype.card α) {a : α}
    {L : Subgroup (Perm α)} {k : ℕ} (hk : 5 ≤ k)
    (s : VisibleStep a (⊤ : Subgroup (Perm α)) L k) : False := by
  let q : Perm α →* alternatingGroup (Fin k) :=
    s.quotient.comp (Subgroup.topEquiv (G := Perm α)).symm.toMonoidHom
  have hq : Function.Surjective q := s.onto.comp Subgroup.topEquiv.symm.surjective
  have hker : q.ker = L := by
    ext g
    exact s.kernel ⟨g, Subgroup.mem_top g⟩
  rcases normal_symm_dichotomy h5 q.ker with hb | hAlt
  · obtain ⟨t, hmove⟩ := alternating_moves_point h5 a
    obtain ⟨l, hl⟩ := s.transitiveKernel ⟨t, Subgroup.mem_top _⟩
    have hlker : (l : Perm α) ∈ q.ker := by rw [hker]; exact l.property
    rw [hb, Subgroup.mem_bot] at hlker
    rw [hlker] at hl
    exact hmove hl.symm
  · obtain ⟨x, y, hxy⟩ := AlternatingSimple.nonabelian_fin hk
    exact hxy (quotient_commutes_of_kills_alternating q hq hAlt x y)

/-- The natural giant case contributes no marks before a nongiant restriction. -/
theorem no_giant_step (h5 : 5 ≤ Fintype.card α) {a : α}
    {H L : Subgroup (Perm α)} (hgiant : alternatingGroup α ≤ H)
    {k : ℕ} (hk : 5 ≤ k) (s : VisibleStep a H L k) : False := by
  rcases giant_eq_alt_or_top h5 hgiant with rfl | rfl
  · exact no_alternating_step h5 hk s
  · exact no_symmetric_step h5 hk s

/-- Skipping only giant unmarked restrictions retains the chain's entire
weight at the first nongiant subgroup, unless the chain has zero weight. -/
theorem first_nongiant_restriction {cutoff w : ℕ} (hcutoff : 5 ≤ cutoff)
    (h5 : 5 ≤ Fintype.card α) {a : α} {H : Subgroup (Perm α)}
    (chain : MarkedChain cutoff a H w) (hgiant : alternatingGroup α ≤ H) :
    w = 0 ∨ ∃ L : Subgroup (Perm α), L ≤ H ∧ ¬ alternatingGroup α ≤ L ∧
      MarkedChain cutoff a L w := by
  induction chain with
  | stop H => exact Or.inl rfl
  | @restrict H L w hle tail ih =>
      by_cases hL : alternatingGroup α ≤ L
      · rcases ih hL with hz | ⟨K, hK, hn, hw⟩
        · exact Or.inl hz
        · exact Or.inr ⟨K, hK.trans hle, hn, hw⟩
      · exact Or.inr ⟨L, hle, hL, tail⟩
  | mark hk s _ _ => exact (no_giant_step h5 hgiant (hcutoff.trans hk) s).elim

/-- Even the zero-weight case can be represented on a nongiant subgroup. -/
theorem weight_retained_nongiant {cutoff w : ℕ} (hcutoff : 5 ≤ cutoff)
    (h5 : 5 ≤ Fintype.card α) {a : α} {H : Subgroup (Perm α)}
    (chain : MarkedChain cutoff a H w) (hgiant : alternatingGroup α ≤ H) :
    ∃ L : Subgroup (Perm α), L ≤ H ∧ ¬ alternatingGroup α ≤ L ∧
      MarkedChain cutoff a L w := by
  rcases first_nongiant_restriction hcutoff h5 chain hgiant with rfl | h
  · refine ⟨⊥, bot_le, ?_, .stop _⟩
    intro hbot
    obtain ⟨t, ht⟩ := alternating_moves_point h5 a
    have htone := hbot t.property
    rw [Subgroup.mem_bot] at htone
    rw [htone] at ht
    exact ht rfl
  · exact h

/-- The complete budget of a natural giant is achieved in a nongiant
subgroup; no logarithmic budget or primitive classification is assumed. -/
theorem exists_nongiant_same_sigma {cutoff : ℕ} (hcutoff : 5 ≤ cutoff)
    (h5 : 5 ≤ Fintype.card α) (a : α) (H : Subgroup (Perm α))
    (hgiant : alternatingGroup α ≤ H) :
    ∃ L : Subgroup (Perm α), L ≤ H ∧ ¬ alternatingGroup α ≤ L ∧
      sigma cutoff a L = sigma cutoff a H := by
  obtain ⟨L, hle, hn, hw⟩ := weight_retained_nongiant hcutoff h5
    (sigma_achieved hcutoff a H) hgiant
  exact ⟨L, hle, hn, (sigma_subgroup_mono hcutoff a hle).antisymm (sigma_bounds_chain hcutoff hw)⟩

theorem exists_nongiant_same_sigma_fin {n cutoff : ℕ} (hcutoff : 5 ≤ cutoff)
    (hn : 5 ≤ n) (a : Fin n) (H : Subgroup (Perm (Fin n)))
    (hgiant : alternatingGroup (Fin n) ≤ H) :
    ∃ L : Subgroup (Perm (Fin n)), L ≤ H ∧ ¬ alternatingGroup (Fin n) ≤ L ∧
      sigma cutoff a L = sigma cutoff a H :=
  exists_nongiant_same_sigma hcutoff (by simpa using hn) a H hgiant

end GI.NaturalGiant
