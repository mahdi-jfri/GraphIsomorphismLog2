import Workspace.Impl.LinPrimaryLoopAdvance

namespace GI.Impl
open GI.Cited GI.Lang

set_option maxHeartbeats 1500000 in
theorem linPrimaryLoopInv_terminal {n p d : ℕ} (gs : List (Equiv.Perm (Fin n)))
    (hp : p.Prime) (ν : Fin d → ℕ)
    (ρ : gens gs →* (linFiniteVec (linPrimaryOrders p ν) ≃+ linFiniteVec (linPrimaryOrders p ν)))
    (c : gens gs → linFiniteVec (linPrimaryOrders p ν))
    (hc : ∀ g k, c (g * k) = ρ g (c k) + c g)
    (x : linFiniteVec (linPrimaryOrders p ν)) (acc0 : Equiv.Perm (Fin n)) (a : Val)
    (ha : linPrimaryLoopInv gs ν ρ c x acc0 (linPrimaryHeight ν) a) :
    (a = .list [] ∧ ¬∃ h : gens gs, linFiniteEval ρ c h x = 0) ∨
    ∃ (ks : List (Equiv.Perm (Fin n))) (hle : gens ks ≤ gens gs) (r : gens gs),
      a = .list [linActionContext ks (linPrimaryOrders p ν) (ρ.comp (Subgroup.inclusion hle))
        (c ∘ Subgroup.inclusion hle), linFinitePointVal (linPrimaryOrders p ν) 0, encPerm (r.val * acc0)] ∧
      ks.length ≤ n ^ 2 ∧ linFiniteEval ρ c r x = 0 ∧
      (∀ k : gens ks, c (Subgroup.inclusion hle k) = 0) ∧
      (∀ h : gens gs, h.val ∈ gens ks ↔ c h = 0) ∧
      (∀ h : gens gs, linFiniteEval ρ c h x = 0 ↔ h.val * r.val⁻¹ ∈ gens ks) := by
  rcases ha with hno | ⟨ks, hle, r, rfl, hlen, hpnt, hofs, hcover⟩
  · exact Or.inl hno
  have hr : linFiniteEval ρ c r x = 0 := (linPrimaryFiber_height_iff hp ν _).mp hpnt
  have hof : ∀ k : gens ks, c (Subgroup.inclusion hle k) = 0 :=
    fun k => (linPrimaryFiber_height_iff hp ν _).mp (hofs k)
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
