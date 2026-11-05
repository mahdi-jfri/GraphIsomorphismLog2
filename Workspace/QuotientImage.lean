module

public import Workspace.QuotientChains
public import Workspace.OrbitBudget

@[expose] public section

namespace GI.QuotientImage

variable {K P : Type*} [Group K] [Group P] {k : ℕ}

theorem range_surjective (p : K →* P) : Function.Surjective p.rangeRestrict := by
  rintro ⟨p, h⟩
  obtain ⟨h, rfl⟩ := h
  exact ⟨h, rfl⟩

theorem restricted_kernel_le (p : K →* P) (q : K →* alternatingGroup (Fin k))
    (kills : p.ker ≤ q.ker) : p.rangeRestrict.ker ≤ q.ker := by
  intro h hh
  apply kills
  exact congrArg Subtype.val hh

/-- Descend the actual alternating quotient to a supplied homomorphism's
image once its kernel is killed. No action-transitivity premise is needed. -/
noncomputable def step (p : K →* P) (q : K →* alternatingGroup (Fin k))
    (N : Subgroup K) (onto : Function.Surjective q)
    (kernel : ∀ h : K, q h = 1 ↔ h ∈ N) (kills : p.ker ≤ q.ker) :
    AlternatingQuotientStep p.range (N.map p) k where
  lower := by
    rintro h ⟨n, _, rfl⟩
    exact ⟨n, rfl⟩
  quotient := HomDescent.factor p.rangeRestrict (range_surjective p) q
    (restricted_kernel_le p q kills)
  onto := HomDescent.factor_surjective _ _ _ _ onto
  kernel := by
    intro h
    obtain ⟨x, rfl⟩ := range_surjective p h
    rw [HomDescent.factor_apply]
    constructor
    · intro hx
      exact ⟨x, (kernel x).mp hx, rfl⟩
    · rintro ⟨n, hn, hnx⟩
      have heq : p.rangeRestrict n = p.rangeRestrict x := Subtype.ext hnx
      rw [← HomDescent.eq_of_eq _ q (restricted_kernel_le p q kills) heq]
      exact (kernel n).mpr hn

end GI.QuotientImage
