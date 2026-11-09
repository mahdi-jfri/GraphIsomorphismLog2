module

public import Workspace.Degree.JohnsonWreath
public import Maroti.Statement

/-!
# Maróti's product action type as a wreath structure
-/

@[expose] public section

namespace GI.Degree

open Equiv

/-- Maróti's product action type is `WreathStructure`. -/
theorem wreathStructure_of_productAction {α : Type} (G : Subgroup (Perm α))
    (h : Maroti.IsProductActionType G) :
    ∃ (m k r : ℕ) (e : α ≃ JohnsonTuple m k r), 5 ≤ m ∧ 1 ≤ k ∧ 2 * k < m ∧ 1 ≤ r ∧
      WreathStructure G e := by
  obtain ⟨m, k, r, e, hm, hk, hkm, hr, hwr, halt⟩ := h
  refine ⟨m, k, r, e, hm, hk, hkm, hr, ⟨fun g hg => ?_, ?_⟩⟩
  · obtain ⟨σ, a, hgh⟩ := hwr g hg
    refine ⟨σ⁻¹, a, fun x => ?_⟩
    have := congrArg (· (e x)) hgh
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply] at this
    rw [this]
    funext i
    rfl
  · rintro _ ⟨a, ha, rfl⟩
    convert halt fun i => ⟨a i, ha i (Set.mem_univ i)⟩ using 1
    apply Equiv.ext
    intro x
    apply e.injective
    simp only [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
    rw [coordHom_apply]
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    funext i
    rfl

end GI.Degree
