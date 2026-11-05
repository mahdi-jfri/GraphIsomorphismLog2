module

public import Workspace.Impl.LinPrimaryResidual

@[expose] public section

/-! The accumulator retains a cover subgroup and a representative of the
remaining transporter coset. Full transporters stay in that coset at every
layer; both the point and all target offsets lie in the current fiber. -/
namespace GI.Impl
open GI.Cited GI.Lang

theorem linFiniteEval_one {G V : Type*} [Group G] [AddCommGroup V]
    (ρ : G →* (V ≃+ V)) (c : G → V) (hc : ∀ g h, c (g * h) = ρ g (c h) + c g) (x : V) :
    linFiniteEval ρ c 1 x = x := by
  unfold linFiniteEval
  rw [map_one, linFiniteCocycle_one ρ c hc]
  exact add_zero x

noncomputable def linPrimaryLoopInv {n p d : ℕ} (gs : List (Equiv.Perm (Fin n)))
    (ν : Fin d → ℕ)
    (ρ : gens gs →* (linFiniteVec (linPrimaryOrders p ν) ≃+ linFiniteVec (linPrimaryOrders p ν)))
    (c : gens gs → linFiniteVec (linPrimaryOrders p ν)) (x : linFiniteVec (linPrimaryOrders p ν))
    (acc0 : Equiv.Perm (Fin n)) (j : ℕ) (a : Val) : Prop :=
  (a = .list [] ∧ ¬∃ h : gens gs, linFiniteEval ρ c h x = 0) ∨
  ∃ (ks : List (Equiv.Perm (Fin n))) (hle : gens ks ≤ gens gs) (r : gens gs),
    a = .list [linActionContext ks (linPrimaryOrders p ν) (ρ.comp (Subgroup.inclusion hle))
      (c ∘ Subgroup.inclusion hle), linFinitePointVal (linPrimaryOrders p ν) (linFiniteEval ρ c r x),
      encPerm (r.val * acc0)] ∧ ks.length ≤ n ^ 2 ∧
    linPrimaryFiber p ν j (linFiniteEval ρ c r x) ∧
    (∀ k : gens ks, linPrimaryFiber p ν j (c (Subgroup.inclusion hle k))) ∧
    ∀ h : gens gs, linFiniteEval ρ c h x = 0 → h.val * r.val⁻¹ ∈ gens ks

theorem linPrimaryLoopInv_init {n p d : ℕ} (gs : List (Equiv.Perm (Fin n)))
    (hlen : gs.length ≤ n ^ 2) (ν : Fin d → ℕ)
    (ρ : gens gs →* (linFiniteVec (linPrimaryOrders p ν) ≃+ linFiniteVec (linPrimaryOrders p ν)))
    (c : gens gs → linFiniteVec (linPrimaryOrders p ν))
    (hc : ∀ g k, c (g * k) = ρ g (c k) + c g)
    (x : linFiniteVec (linPrimaryOrders p ν)) (acc0 : Equiv.Perm (Fin n)) :
    linPrimaryLoopInv gs ν ρ c x acc0 0
      (.list [linActionContext gs (linPrimaryOrders p ν) ρ c, linFinitePointVal (linPrimaryOrders p ν) x, encPerm acc0]) := by
  have hi : (Subgroup.inclusion (show gens gs ≤ gens gs from le_rfl)) = MonoidHom.id (gens gs) := by
    apply MonoidHom.ext
    intro g
    rfl
  refine Or.inr ⟨gs, le_rfl, 1, ?_, hlen, ?_, ?_, ?_⟩
  · simp only [hi, MonoidHom.comp_id, MonoidHom.coe_id, Function.comp_id,
      linFiniteEval_one ρ c hc, Subgroup.coe_one, one_mul]
  · intro i
    simp [linPrimaryFiber]
  · intro k i
    simp [linPrimaryFiber]
  · intro h _
    simpa only [Subgroup.coe_one, inv_one, mul_one] using h.property

theorem linPrimaryLoopInv_wt {n p d W : ℕ} (gs : List (Equiv.Perm (Fin n))) (hp : p.Prime)
    (ν : Fin d → ℕ) (hn : n ≤ W) (hd : d ≤ W)
    (hwm : (linVecVal (fun i => (linPrimaryOrders p ν i : ℤ))).wt ≤ W)
    (ρ : gens gs →* (linFiniteVec (linPrimaryOrders p ν) ≃+ linFiniteVec (linPrimaryOrders p ν)))
    (c : gens gs → linFiniteVec (linPrimaryOrders p ν)) (x : linFiniteVec (linPrimaryOrders p ν))
    (acc0 : Equiv.Perm (Fin n)) (j : ℕ) (a : Val) (ha : linPrimaryLoopInv gs ν ρ c x acc0 j a) :
    a.wt ≤ linPrimaryAccumulatorWeight W := by
  rcases ha with ⟨rfl, _⟩ | ⟨ks, hle, r, rfl, hlen, _, _, _⟩
  · change 4 ≤ linPrimaryAccumulatorWeight W
    unfold linPrimaryAccumulatorWeight
    omega
  · exact linPrimaryAccumulator_wt ks hlen hn hd (linPrimaryOrders p ν) (fun i => Nat.pow_pos hp.pos)
      hwm (ρ.comp (Subgroup.inclusion hle)) (c ∘ Subgroup.inclusion hle) (linFiniteEval ρ c r x) (r.val * acc0)

end GI.Impl
