import Workspace.Impl.LinPrimePass
import Workspace.Impl.LinPrimeEval

namespace GI.Impl
open GI.Cited GI.Lang

noncomputable def linPrimePassOut {n d p : ℕ} (gs : List (Equiv.Perm (Fin n)))
    (m : Fin d → ℕ) (D : linPrimeSplitData m p)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m)
    (x : linFiniteVec m) (acc : Equiv.Perm (Fin n)) (out : Val) : Prop :=
  (out = .list [] ∧ ¬∃ g : gens gs, linPrimeProjection D (linFiniteEval ρ c g x) = 0) ∨
  ∃ (ks : List (Equiv.Perm (Fin n))) (hle : gens ks ≤ gens gs) (g : gens gs),
    out = .list [linActionContext ks m (ρ.comp (Subgroup.inclusion hle))
      (c ∘ Subgroup.inclusion hle), linFinitePointVal m (linFiniteEval ρ c g x), encPerm (g.val * acc)] ∧
    ks.length ≤ n ^ 2 ∧ linPrimeProjection D (linFiniteEval ρ c g x) = 0 ∧
    (∀ h : gens gs, h.val ∈ gens ks ↔ linPrimeProjection D (c h) = 0) ∧
    (∀ h : gens gs, linPrimeProjection D (linFiniteEval ρ c h x) = 0 ↔ h.val * g.val⁻¹ ∈ gens ks)

end GI.Impl
