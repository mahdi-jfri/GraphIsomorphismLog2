import Workspace.Impl.LinMixedFiber
import Workspace.Impl.LinPrimaryLoopInvariant

namespace GI.Impl
open GI.Cited GI.Lang

noncomputable def linMixedLoopInv {n d : ℕ} (gs : List (Equiv.Perm (Fin n)))
    (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m)
    (x : linFiniteVec m) (acc0 : Equiv.Perm (Fin n)) (j : ℕ) (a : Val) : Prop :=
  (a = .list [] ∧ ¬∃ h : gens gs, linFiniteEval ρ c h x = 0) ∨
  ∃ (ks : List (Equiv.Perm (Fin n))) (hle : gens ks ≤ gens gs) (r : gens gs),
    a = .list [linActionContext ks m (ρ.comp (Subgroup.inclusion hle)) (c ∘ Subgroup.inclusion hle),
      linFinitePointVal m (linFiniteEval ρ c r x), encPerm (r.val * acc0)] ∧ ks.length ≤ n ^ 2 ∧
    linMixedFiber m hm j (linFiniteEval ρ c r x) ∧
    (∀ k : gens ks, linMixedFiber m hm j (c (Subgroup.inclusion hle k))) ∧
    ∀ h : gens gs, linFiniteEval ρ c h x = 0 → h.val * r.val⁻¹ ∈ gens ks

theorem linMixedLoopInv_init {n d : ℕ} (gs : List (Equiv.Perm (Fin n)))
    (hlen : gs.length ≤ n ^ 2) (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m)
    (hc : ∀ g h, c (g * h) = ρ g (c h) + c g)
    (x : linFiniteVec m) (acc0 : Equiv.Perm (Fin n)) :
    linMixedLoopInv gs m hm ρ c x acc0 0
      (.list [linActionContext gs m ρ c, linFinitePointVal m x, encPerm acc0]) := by
  have hi : Subgroup.inclusion (show gens gs ≤ gens gs from le_rfl) = MonoidHom.id (gens gs) := by
    ext g
    rfl
  refine Or.inr ⟨gs, le_rfl, 1, ?_, hlen, ?_, ?_, ?_⟩
  · simp only [hi, MonoidHom.comp_id, MonoidHom.coe_id, Function.comp_id,
      linFiniteEval_one ρ c hc, Subgroup.coe_one, one_mul]
  · exact linMixedFiber_start m hm _
  · intro k
    exact linMixedFiber_start m hm _
  · intro h _
    simpa only [Subgroup.coe_one, inv_one, mul_one] using h.property

theorem linMixedLoopInv_skip {n d : ℕ} (gs : List (Equiv.Perm (Fin n)))
    (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m)
    (x : linFiniteVec m) (acc0 : Equiv.Perm (Fin n)) (j : ℕ) (hj : ¬ (j + 1).Prime)
    (a : Val) (ha : linMixedLoopInv gs m hm ρ c x acc0 j a) :
    linMixedLoopInv gs m hm ρ c x acc0 (j + 1) a := by
  rcases ha with hno | ⟨ks, hle, r, he, hlen, hpt, hof, hcover⟩
  · exact Or.inl hno
  · exact Or.inr ⟨ks, hle, r, he, hlen, linMixedFiber_skip m hm hj hpt,
      fun k => linMixedFiber_skip m hm hj (hof k), hcover⟩

end GI.Impl
