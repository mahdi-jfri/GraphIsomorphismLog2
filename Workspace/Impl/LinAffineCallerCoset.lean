import Workspace.Impl.LinAffineCallerMath

namespace GI.Impl
open GI.Cited GI.Lang
open scoped Pointwise

theorem linAffineTrans_left {n d : ℕ} (gs ks : List (Equiv.Perm (Fin n)))
    (hle : gens ks ≤ gens gs) (m : Fin d → ℕ)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m)
    (v w : linFiniteVec m) (r : gens gs)
    (hres : ∀ h : gens gs,
      linFiniteEval ρ (linFiniteRecenter ρ c w) h (v - w) = 0 ↔ h.val * r.val⁻¹ ∈ gens ks) :
    tmGLAffTrans gs ρ c v w = r.val • (gens (linConjugateGenerators ks r.val) : Set (Equiv.Perm (Fin n))) := by
  have he : tmGLAffTrans gs ρ c v w = (fun k => k * r.val) '' (gens ks : Set (Equiv.Perm (Fin n))) := by
    ext t
    constructor
    · rintro ⟨h, hh, rfl⟩
      change linFiniteEval ρ c h v = w at hh
      have hz := (linFiniteRecenter_transport ρ c w v h).mpr hh
      exact ⟨h.val * r.val⁻¹, (hres h).mp hz, by group⟩
    · rintro ⟨k, hk, rfl⟩
      let h : gens gs := ⟨k * r.val, (gens gs).mul_mem (hle hk) r.property⟩
      refine ⟨h, ?_, rfl⟩
      change linFiniteEval ρ c h v = w
      apply (linFiniteRecenter_transport ρ c w v h).mp
      apply (hres h).mpr
      change k * r.val * r.val⁻¹ ∈ gens ks
      simpa only [mul_assoc, mul_inv_cancel, mul_one] using hk
  rw [he, linRightCoset_left, ← linConjugateGenerators_gens]
  rfl

theorem linAffineSmallCover_bot {n : ℕ} (gs : List (Equiv.Perm (Fin n))) (hn : n ≤ 1) : gens gs = ⊥ := by
  letI : Subsingleton (Fin n) := Fintype.card_le_one_iff_subsingleton.mp (by simpa using hn)
  exact Subgroup.eq_bot_of_subsingleton _

end GI.Impl
