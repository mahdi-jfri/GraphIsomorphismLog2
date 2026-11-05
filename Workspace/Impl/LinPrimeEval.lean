module

public import Workspace.Impl.LinPrimeAction
public import Workspace.Impl.LinAffineResidual

@[expose] public section

/-! Primary projection commutes with full affine evaluation. Thus later
passes preserve all primary equations already imposed. -/
namespace GI.Impl

variable {G : Type*} [Group G] {d p : ℕ} {m : Fin d → ℕ}

@[simp] theorem linPrimeProjection_eval (D : linPrimeSplitData m p) (hm : ∀ i, 0 < m i)
    (ρ : G →* (linFiniteVec m ≃+ linFiniteVec m)) (c : G → linFiniteVec m)
    (g : G) (x : linFiniteVec m) :
    linPrimeProjection D (linFiniteEval ρ c g x) =
      linFiniteEval (linPrimeAction D hm ρ) (fun g => linPrimeProjection D (c g)) g
        (linPrimeProjection D x) := by
  simp only [linFiniteEval, map_add, linPrimeAction_image]

theorem linPrimeProjection_preserve_zero (D : linPrimeSplitData m p) (hm : ∀ i, 0 < m i)
    (ρ : G →* (linFiniteVec m ≃+ linFiniteVec m)) (c : G → linFiniteVec m)
    (g : G) (x : linFiniteVec m) (hx : linPrimeProjection D x = 0)
    (hc : linPrimeProjection D (c g) = 0) :
    linPrimeProjection D (linFiniteEval ρ c g x) = 0 := by
  rw [linPrimeProjection_eval D hm]
  simp only [linFiniteEval, hx, hc, map_zero, add_zero]

theorem linPrimeAction_comp {K : Type*} [Group K] (D : linPrimeSplitData m p)
    (hm : ∀ i, 0 < m i) (ρ : G →* (linFiniteVec m ≃+ linFiniteVec m)) (f : K →* G) :
    linPrimeAction D hm (ρ.comp f) = (linPrimeAction D hm ρ).comp f := by
  ext k y
  obtain ⟨x, rfl⟩ := linPrimeProjection_surjective D y
  simp only [linPrimeAction_image, MonoidHom.comp_apply]

end GI.Impl
