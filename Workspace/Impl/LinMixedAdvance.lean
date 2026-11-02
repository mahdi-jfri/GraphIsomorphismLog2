import Workspace.Impl.LinMixedInvariant
import Workspace.Impl.LinPrimePassOut

namespace GI.Impl
open GI.Cited GI.Lang

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 8000 in
theorem linMixedLoopInv_advance {n d : ℕ} (gs ks : List (Equiv.Perm (Fin n)))
    (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m)
    (hc : ∀ g k, c (g * k) = ρ g (c k) + c g)
    (x : linFiniteVec m) (acc0 : Equiv.Perm (Fin n)) (j : ℕ) (hp : (j + 1).Prime)
    (hle : gens ks ≤ gens gs) (r : gens gs)
    (hpoint : linMixedFiber m hm j (linFiniteEval ρ c r x))
    (hofs : ∀ k : gens ks, linMixedFiber m hm j (c (Subgroup.inclusion hle k)))
    (hcover : ∀ h : gens gs, linFiniteEval ρ c h x = 0 → h.val * r.val⁻¹ ∈ gens ks)
    (out : Val)
    (hout : linPrimePassOut ks m (linTrialPrimaryData m (j + 1) hp hm)
      (ρ.comp (Subgroup.inclusion hle)) (c ∘ Subgroup.inclusion hle)
      (linFiniteEval ρ c r x) (r.val * acc0) out) :
    linMixedLoopInv gs m hm ρ c x acc0 (j + 1) out := by
  let D := linTrialPrimaryData m (j + 1) hp hm
  let ρ' := ρ.comp (Subgroup.inclusion hle)
  let c' := c ∘ Subgroup.inclusion hle
  let point := linFiniteEval ρ c r x
  have residual (h : gens gs) (hh : linFiniteEval ρ c h x = 0) :
      ∃ k : gens ks, k.val = h.val * r.val⁻¹ ∧ linFiniteEval ρ' c' k point = 0 := by
    let k : gens ks := ⟨h.val * r.val⁻¹, hcover h hh⟩
    have he : Subgroup.inclusion hle k = h * r⁻¹ := Subtype.ext rfl
    refine ⟨k, rfl, ?_⟩
    change linFiniteEval ρ c (Subgroup.inclusion hle k) (linFiniteEval ρ c r x) = 0
    rw [he, linFiniteEval_residual ρ c hc]
    exact hh
  rcases hout with ⟨rfl, hno⟩ | ⟨ts, hts, g, rfl, hlen, hg, hstab, htrans⟩
  · refine Or.inl ⟨rfl, ?_⟩
    rintro ⟨h, hh⟩
    obtain ⟨k, _, hk⟩ := residual h hh
    apply hno
    refine ⟨k, ?_⟩
    change linPrimeProjection D (linFiniteEval ρ' c' k point) = 0
    rw [hk, map_zero]
  · let hnew : gens ts ≤ gens gs := hts.trans hle
    let rnew : gens gs := Subgroup.inclusion hle g * r
    have hρ : ρ'.comp (Subgroup.inclusion hts) = ρ.comp (Subgroup.inclusion hnew) := by
      ext k
      rfl
    have hcnew : c' ∘ Subgroup.inclusion hts = c ∘ Subgroup.inclusion hnew := by
      funext k
      rfl
    have hepoint : linFiniteEval ρ c rnew x = linFiniteEval ρ' c' g point := by
      change linFiniteEval ρ c (Subgroup.inclusion hle g * r) x = _
      rw [linFiniteEval_mul ρ c hc]
      rfl
    have hrval : rnew.val * acc0 = g.val * (r.val * acc0) := mul_assoc g.val r.val acc0
    refine Or.inr ⟨ts, hnew, rnew, ?_, hlen, ?_, ?_, ?_⟩
    · change (Val.list [linActionContext ts m (ρ'.comp (Subgroup.inclusion hts))
        (c' ∘ Subgroup.inclusion hts), linFinitePointVal m (linFiniteEval ρ' c' g point),
        encPerm (g.val * (r.val * acc0))]) = _
      rw [hρ, hcnew, hepoint, hrval]
    · rw [hepoint]
      exact linMixedFiber_next m hm
        (linMixedFiber_eval m hm j ρ' c' g point hpoint (hofs g)) (fun _ => hg)
    · intro k
      apply linMixedFiber_next m hm (hofs (Subgroup.inclusion hts k))
      intro hp'
      exact (hstab (Subgroup.inclusion hts k)).mp k.property
    · intro h hh
      obtain ⟨k, hkval, hk⟩ := residual h hh
      have hproj : linPrimeProjection D (linFiniteEval ρ' c' k point) = 0 := by rw [hk, map_zero]
      have hmem : k.val * g.val⁻¹ ∈ gens ts := (htrans k).mp hproj
      have he : h.val * rnew.val⁻¹ = k.val * g.val⁻¹ := by
        change h.val * (g.val * r.val)⁻¹ = k.val * g.val⁻¹
        rw [hkval]
        group
      rw [he]
      exact hmem

end GI.Impl
