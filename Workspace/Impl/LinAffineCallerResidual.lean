module

public import Workspace.Impl.LinAffineCallerCoset

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang
open scoped Pointwise

theorem linAffineCaller_no_transport {n d : ℕ} (gs bs : List (Equiv.Perm (Fin n)))
    (hsame : gens bs = gens gs) (hle : gens bs ≤ gens gs) (m : Fin d → ℕ)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m)
    (v w : linFiniteVec m)
    (hno : ¬∃ h : gens bs, linFiniteEval (ρ.comp (Subgroup.inclusion hle))
      (linFiniteRecenter ρ c w ∘ Subgroup.inclusion hle) h (v - w) = 0) :
    tmGLAffTrans gs ρ c v w = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro t ht
  obtain ⟨h, hh, rfl⟩ := ht
  let hb : gens bs := ⟨h.val, hsame.symm ▸ h.property⟩
  have he : Subgroup.inclusion hle hb = h := Subtype.ext rfl
  apply hno
  refine ⟨hb, ?_⟩
  change linFiniteEval ρ (linFiniteRecenter ρ c w) (Subgroup.inclusion hle hb) (v - w) = 0
  rw [he]
  exact (linFiniteRecenter_transport ρ c w v h).mpr hh

theorem linAffineCaller_transport_coset {n d : ℕ} (gs bs ks : List (Equiv.Perm (Fin n)))
    (hsame : gens bs = gens gs) (hle : gens bs ≤ gens gs) (hks : gens ks ≤ gens bs)
    (m : Fin d → ℕ) (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m))
    (c : gens gs → linFiniteVec m) (v w : linFiniteVec m) (r : gens bs)
    (hres : ∀ h : gens bs,
      linFiniteEval (ρ.comp (Subgroup.inclusion hle))
        (linFiniteRecenter ρ c w ∘ Subgroup.inclusion hle) h (v - w) = 0 ↔ h.val * r.val⁻¹ ∈ gens ks) :
    tmGLAffTrans gs ρ c v w = r.val • (gens (linConjugateGenerators ks r.val) : Set (Equiv.Perm (Fin n))) := by
  have hf (h : gens gs) :
      linFiniteEval ρ (linFiniteRecenter ρ c w) h (v - w) = 0 ↔ h.val * r.val⁻¹ ∈ gens ks := by
    let hb : gens bs := ⟨h.val, hsame.symm ▸ h.property⟩
    have he : Subgroup.inclusion hle hb = h := Subtype.ext rfl
    have hh := hres hb
    change linFiniteEval ρ (linFiniteRecenter ρ c w) (Subgroup.inclusion hle hb) (v - w) = 0 ↔ _ at hh
    simpa only [he] using hh
  exact linAffineTrans_left gs ks (hks.trans hle) m ρ c v w (Subgroup.inclusion hle r) hf

end GI.Impl
