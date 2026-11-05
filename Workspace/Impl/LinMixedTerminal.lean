module

public import Workspace.Impl.LinMixedInvariant

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

set_option maxHeartbeats 1000000 in
theorem linMixedLoopInv_terminal {n d : ℕ} (gs : List (Equiv.Perm (Fin n)))
    (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (hbound : ∀ i p, p.Prime → p ∣ m i → p ≤ n)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m)
    (hc : ∀ g k, c (g * k) = ρ g (c k) + c g)
    (x : linFiniteVec m) (acc0 : Equiv.Perm (Fin n)) (a : Val)
    (ha : linMixedLoopInv gs m hm ρ c x acc0 n a) :
    (a = .list [] ∧ ¬∃ h : gens gs, linFiniteEval ρ c h x = 0) ∨
    ∃ (ks : List (Equiv.Perm (Fin n))) (hle : gens ks ≤ gens gs) (r : gens gs),
      a = .list [linActionContext ks m (ρ.comp (Subgroup.inclusion hle))
        (c ∘ Subgroup.inclusion hle), linFinitePointVal m 0, encPerm (r.val * acc0)] ∧
      ks.length ≤ n ^ 2 ∧ linFiniteEval ρ c r x = 0 ∧
      (∀ k : gens ks, c (Subgroup.inclusion hle k) = 0) ∧
      (∀ h : gens gs, h.val ∈ gens ks ↔ c h = 0) ∧
      (∀ h : gens gs, linFiniteEval ρ c h x = 0 ↔ h.val * r.val⁻¹ ∈ gens ks) := by
  rcases ha with hno | ⟨ks, hle, r, rfl, hlen, hpnt, hofs, hcover⟩
  · exact Or.inl hno
  have hr : linFiniteEval ρ c r x = 0 := linMixedFiber_terminal m hm n hbound _ hpnt
  have hof : ∀ k : gens ks, c (Subgroup.inclusion hle k) = 0 :=
    fun k => linMixedFiber_terminal m hm n hbound _ (hofs k)
  refine Or.inr ⟨ks, hle, r, ?_, hlen, hr, hof, ?_, ?_⟩
  · rw [hr]
  · intro h
    constructor
    · intro hh
      let k : gens ks := ⟨h.val, hh⟩
      have he : Subgroup.inclusion hle k = h := Subtype.ext rfl
      simpa only [he] using hof k
    · intro hh
      have hs : linFiniteEval ρ c (h * r) x = 0 := by
        rw [linFiniteEval_mul ρ c hc, hr]
        simpa only [linFiniteEval, map_zero, zero_add] using hh
      simpa only [Subgroup.coe_mul, mul_assoc, mul_inv_cancel, mul_one] using hcover (h * r) hs
  · intro h
    constructor
    · exact hcover h
    · intro hh
      let k : gens ks := ⟨h.val * r.val⁻¹, hh⟩
      have he : Subgroup.inclusion hle k * r = h := by
        apply Subtype.ext
        change (h.val * r.val⁻¹) * r.val = h.val
        group
      rw [← he, linFiniteEval_mul ρ c hc, hr]
      simpa only [linFiniteEval, map_zero, zero_add] using hof k

end GI.Impl
