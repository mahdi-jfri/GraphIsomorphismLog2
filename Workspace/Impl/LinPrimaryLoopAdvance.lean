import Workspace.Impl.LinPrimaryLoopInvariant

namespace GI.Impl
open GI.Cited GI.Lang

theorem linPrimaryCover_solvable {n : ℕ} (gs ks : List (Equiv.Perm (Fin n)))
    (hs : IsSolvable (gens gs)) (hle : gens ks ≤ gens gs) : IsSolvable (gens ks) := by
  letI : IsSolvable (gens gs) := hs
  exact solvable_of_solvable_injective (Subgroup.inclusion_injective hle)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 8000 in
theorem linPrimaryLoopInv_advance {n p d : ℕ} (gs ks : List (Equiv.Perm (Fin n)))
    (hks : IsSolvable (gens ks)) (hp : p.Prime) (hpn : p ≤ n) (ν : Fin d → ℕ)
    (ρ : gens gs →* (linFiniteVec (linPrimaryOrders p ν) ≃+ linFiniteVec (linPrimaryOrders p ν)))
    (c : gens gs → linFiniteVec (linPrimaryOrders p ν))
    (hc : ∀ g k, c (g * k) = ρ g (c k) + c g)
    (x : linFiniteVec (linPrimaryOrders p ν)) (acc0 : Equiv.Perm (Fin n)) (j : ℕ)
    (hle : gens ks ≤ gens gs) (r : gens gs)
    (hpoint : linPrimaryFiber p ν j (linFiniteEval ρ c r x))
    (hofs : ∀ k : gens ks, linPrimaryFiber p ν j (c (Subgroup.inclusion hle k)))
    (hcover : ∀ h : gens gs, linFiniteEval ρ c h x = 0 → h.val * r.val⁻¹ ∈ gens ks)
    (out : Val)
    (hout : linPrimaryStepOut ks hks hp hpn ν j (ρ.comp (Subgroup.inclusion hle))
      (c ∘ Subgroup.inclusion hle)
      (linActionRestricted_cocycle (linPrimaryOrders p ν) ρ c hc (Subgroup.inclusion hle))
      hofs (linFiniteEval ρ c r x) (r.val * acc0) out) :
    linPrimaryLoopInv gs ν ρ c x acc0 (j + 1) out := by
  let m := linPrimaryOrders p ν
  let ρ' := ρ.comp (Subgroup.inclusion hle)
  let c' := c ∘ Subgroup.inclusion hle
  let hc' := linActionRestricted_cocycle m ρ c hc (Subgroup.inclusion hle)
  let point := linFiniteEval ρ c r x
  have residual (h : gens gs) (hh : linFiniteEval ρ c h x = 0) :
      ∃ k : gens ks, k.val = h.val * r.val⁻¹ ∧ linFiniteEval ρ' c' k point = 0 := by
    let k : gens ks := ⟨h.val * r.val⁻¹, hcover h hh⟩
    have he : Subgroup.inclusion hle k = h * r⁻¹ := Subtype.ext rfl
    refine ⟨k, rfl, ?_⟩
    change linFiniteEval ρ c (Subgroup.inclusion hle k) (linFiniteEval ρ c r x) = 0
    rw [he, linFiniteEval_residual ρ c hc]
    exact hh
  rcases hout with ⟨rfl, hno⟩ | ⟨g, ts, hts, hlen, heq, rfl, hg⟩
  · refine Or.inl ⟨rfl, ?_⟩
    rintro ⟨h, hh⟩
    obtain ⟨k, _, hk⟩ := residual h hh
    apply hno
    refine ⟨k, ?_⟩
    change linPrimaryFiber p ν (j + 1) (linFiniteEval ρ' c' k point)
    rw [hk]
    exact linPrimaryFiber_zero p ν (j + 1)
  · let hnew : gens ts ≤ gens gs := hts.trans hle
    let rnew : gens gs := Subgroup.inclusion hle g * r
    have hρ : ρ'.comp (Subgroup.inclusion hts) = ρ.comp (Subgroup.inclusion hnew) := by
      apply MonoidHom.ext
      intro k
      rfl
    have hcnew : c' ∘ Subgroup.inclusion hts = c ∘ Subgroup.inclusion hnew := by
      funext k
      rfl
    have hepoint : linFiniteEval ρ c rnew x = ρ' g point + c' g := by
      change linFiniteEval ρ c (Subgroup.inclusion hle g * r) x = _
      rw [linFiniteEval_mul ρ c hc]
      rfl
    have hrval : rnew.val * acc0 = g.val * (r.val * acc0) := mul_assoc g.val r.val acc0
    refine Or.inr ⟨ts, hnew, rnew, ?_, hlen, ?_, ?_, ?_⟩
    · change (Val.list [linActionContext ts m (ρ'.comp (Subgroup.inclusion hts))
        (c' ∘ Subgroup.inclusion hts), linFinitePointVal m (ρ' g point + c' g),
        encPerm (g.val * (r.val * acc0))]) = _
      rw [hρ, hcnew, hepoint, hrval]
    · rw [hepoint]
      exact hg
    · intro k
      have hk : (Subgroup.inclusion hts k).val ∈ linPrimaryNextTarget ks hks hp hpn ν j ρ' c' hc' hofs point := by
        rw [← heq]
        exact k.property
      exact (linPrimaryLayerTarget_mem ks hks hp hpn ν j ρ' c' hc' hofs point (Subgroup.inclusion hts k)).mp hk
    · intro h hh
      obtain ⟨k, hkval, hk⟩ := residual h hh
      have hf := linPrimaryResidual_factor hp.pos ν (j + 1) ρ' c' hc' point k g hk hg
      have hmem : (k * g⁻¹).val ∈ gens ts := by
        rw [heq]
        exact (linPrimaryLayerTarget_mem ks hks hp hpn ν j ρ' c' hc' hofs point (k * g⁻¹)).mpr hf
      have he : h.val * rnew.val⁻¹ = (k * g⁻¹).val := by
        change h.val * (g.val * r.val)⁻¹ = k.val * g.val⁻¹
        rw [hkval]
        group
      rw [he]
      exact hmem

end GI.Impl
