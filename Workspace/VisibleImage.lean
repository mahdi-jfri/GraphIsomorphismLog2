module

public import Workspace.OrbitBudget

@[expose] public section

namespace GI

namespace VisibleImage

variable {K W : Type*} [Group K] {k : ℕ}

theorem range_surjective (p : K →* Equiv.Perm W) :
    Function.Surjective p.rangeRestrict := by
  rintro ⟨p, h⟩
  obtain ⟨h, rfl⟩ := h
  exact ⟨h, rfl⟩

theorem kernel_le (p : K →* Equiv.Perm W) (q : K →* alternatingGroup (Fin k))
    (b : W)
    (visible : ∀ h : K, (∀ g : K, p h (p g b) = p g b) → q h = 1) :
    p.rangeRestrict.ker ≤ q.ker := by
  intro h hh
  apply visible h
  intro g
  have hp : p h = 1 := congrArg Subtype.val hh
  rw [hp]
  rfl

/-- A visible simple quotient descends to the actual image permutation group.
No faithfulness assumption on the source representation is needed. -/
noncomputable def step (p : K →* Equiv.Perm W)
    (q : K →* alternatingGroup (Fin k)) (N : Subgroup K)
    (onto : Function.Surjective q) (kernel : ∀ h : K, q h = 1 ↔ h ∈ N)
    (b : W)
    (transitiveKernel : ∀ h : K, ∃ n : N, p n b = p h b)
    (visible : ∀ h : K, (∀ g : K, p h (p g b) = p g b) → q h = 1) :
    VisibleStep b p.range (N.map p) k where
  lower := by
    rintro h ⟨n, _, rfl⟩
    exact ⟨n, rfl⟩
  quotient := HomDescent.factor p.rangeRestrict (range_surjective p) q
    (kernel_le p q b visible)
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
      rw [← HomDescent.eq_of_eq _ q (kernel_le p q b visible) heq]
      exact (kernel n).mpr hn
  transitiveKernel := by
    intro h
    obtain ⟨x, rfl⟩ := range_surjective p h
    obtain ⟨n, hn⟩ := transitiveKernel x
    exact ⟨⟨p n, Subgroup.mem_map_of_mem p n.property⟩, hn⟩
  visible := by
    intro h hh
    obtain ⟨x, rfl⟩ := range_surjective p h
    rw [HomDescent.factor_apply]
    apply visible x
    intro g
    exact hh (p.rangeRestrict g)

end VisibleImage

end GI
