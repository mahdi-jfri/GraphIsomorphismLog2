import Workspace.JohnsonOrbits

namespace GI.AlternatingActions

open scoped Pointwise

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- An actual natural orbit is fixed setwise by each group element. -/
theorem orbitFinset_smul (K : Subgroup (Equiv.Perm A)) (x : A) (k : K) :
    (k : Equiv.Perm A) • Johnson.orbitFinset K x = Johnson.orbitFinset K x := by
  apply Finset.eq_of_subset_of_card_le ?_ ?_
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_smul_finset.mp hy
    obtain ⟨l, hl⟩ := Johnson.mem_orbitFinset.mp hz
    exact Johnson.mem_orbitFinset.mpr ⟨k * l, congrArg (fun u => (k : Equiv.Perm A) u) hl⟩
  · rw [Finset.card_smul_finset]

/-- Complementing an invariant finite subset preserves invariance. -/
theorem invariant_finset_compl (K : Subgroup (Equiv.Perm A)) (s : Finset A)
    (hinvariant : ∀ k : K, (k : Equiv.Perm A) • s = s) :
    ∀ k : K, (k : Equiv.Perm A) • sᶜ = sᶜ := by
  intro k
  apply Finset.coe_injective
  rw [Finset.coe_smul_finset, Finset.coe_compl, Set.smul_set_compl,
    ← Finset.coe_smul_finset, hinvariant]

/-- Natural intransitivity supplies an actual nonempty invariant subset
of at most half the degree, by taking an orbit or its complement. -/
theorem exists_small_invariant_finset (K : Subgroup (Equiv.Perm A))
    (intransitive : ¬ MulAction.IsPretransitive K A) :
    ∃ s : Finset A, 1 ≤ s.card ∧ 2 * s.card ≤ Fintype.card A ∧
      ∀ k : K, (k : Equiv.Perm A) • s = s := by
  classical
  have hpair : ∃ x y : A, ¬ ∃ k : K, (k : Equiv.Perm A) x = y := by
    by_contra hn
    apply intransitive
    constructor
    intro x y
    exact not_not.mp (fun hh => hn ⟨x, y, hh⟩)
  obtain ⟨x, y, hxy⟩ := hpair
  let s := Johnson.orbitFinset K x
  have hx : x ∈ s := Johnson.self_mem_orbitFinset K x
  have hy : y ∉ s := fun h => hxy (Johnson.mem_orbitFinset.mp h)
  have hpos : 1 ≤ s.card := Finset.card_pos.mpr ⟨x, hx⟩
  have hsmall : s.card < Fintype.card A := by
    by_contra hn
    have he : s = Finset.univ := Finset.eq_of_subset_of_card_le (Finset.subset_univ s)
      (by simpa using (le_of_not_gt hn))
    exact hy (he ▸ Finset.mem_univ y)
  have hinv : ∀ k : K, (k : Equiv.Perm A) • s = s := orbitFinset_smul K x
  by_cases hhalf : 2 * s.card ≤ Fintype.card A
  · exact ⟨s, hpos, hhalf, hinv⟩
  · refine ⟨sᶜ, ?_, ?_, invariant_finset_compl K s hinv⟩
    · rw [Finset.card_compl]
      omega
    · rw [Finset.card_compl]
      omega

end GI.AlternatingActions
