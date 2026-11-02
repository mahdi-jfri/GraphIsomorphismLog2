import Workspace.Impl.LinPrimaryLoopStepSpec

/-! The complete primary filtration program has a uniform polynomial bit cost
and returns its terminal transporter-coset invariant. -/
namespace GI.Impl
open GI.Cited GI.Lang
set_option maxRecDepth 16000

set_option maxHeartbeats 3000000 in
theorem linPrimaryLoop_spec (hm : ConstructiveMembership) (hv : VectorStabilizer)
    {P : Program} {b jm jv n p d : ℕ} (hat : linPrimaryLoopAt P b jm jv hm hv)
    (gs : List (Equiv.Perm (Fin n))) (hlen : gs.length ≤ n ^ 2)
    (hs : IsSolvable (gens gs)) (hp : p.Prime) (hpn : p ≤ n) [NeZero n] (ν : Fin d → ℕ)
    (ρ : gens gs →* (linFiniteVec (linPrimaryOrders p ν) ≃+ linFiniteVec (linPrimaryOrders p ν)))
    (c : gens gs → linFiniteVec (linPrimaryOrders p ν))
    (hc : ∀ g k, c (g * k) = ρ g (c k) + c g)
    (x : linFiniteVec (linPrimaryOrders p ν)) (acc0 : Equiv.Perm (Fin n)) :
    let a := linPrimaryLoopInputVal gs ν ρ c x acc0
    FunAll P b a (fun out cost => linPrimaryLoopInv gs ν ρ c x acc0 (linPrimaryHeight ν) out ∧
      cost ≤ linPrimaryLoopCost hm hv a.wt) := by
  let m := linPrimaryOrders p ν
  let a := linPrimaryLoopInputVal gs ν ρ c x acc0
  let W := a.wt
  obtain ⟨hn, hd, hwm, hheight, hν⟩ := linPrimaryLoop_source_bounds gs hp ν ρ c x acc0
  have hk := linPrimaryLoop_count_det hat.max (linActionContext gs m ρ c) (linFinitePointVal m x) (encPerm acc0) p ν hν hd
  have hacc := linPrimaryLoop_start_det (P := P) (linActionContext gs m ρ c) (linFinitePointVal m x) (encPerm acc0) p ν
  have h0 := linPrimaryLoopInv_init gs hlen ν ρ c hc x acc0
  have hM (i : ℕ) (v : Val) (_ : i ≤ linPrimaryHeight ν) (hv : linPrimaryLoopInv gs ν ρ c x acc0 i v) : v.wt ≤ linPrimaryAccumulatorWeight W :=
    linPrimaryLoopInv_wt gs hp ν hn hd hwm ρ c x acc0 i v hv
  have run := linLoopBddInit_spec hat.loop hk hacc (M := (linPrimaryAccumulatorWeight W))
    (Inv := linPrimaryLoopInv gs ν ρ c x acc0) h0 hM (D := fun _ => (linPrimaryLoopStepBudget hm hv W)) (by
      intro i v hi hInv
      have he := linPrimaryLoop_step_spec hm hv hat gs hs hp hpn ν ρ c hc x acc0 i hi v hInv
      refine he.mono fun out cost ho => ⟨ho.1, ho.2.trans (Nat.le_add_right (linPrimaryLoopStepBudget hm hv W) _)⟩)
  refine run.mono fun out cost ho => ⟨ho.1, ?_⟩
  have hcost := ho.2
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, loopModK] at hcost
  exact linPrimaryLoop_collected_budget hm hv W _ cost hheight hcost

set_option maxHeartbeats 1500000 in
theorem linPrimaryLoop_spec_poly (hm : ConstructiveMembership) (hv : VectorStabilizer) :
    ∃ K D : ℕ, ∀ {P : Program} {b jm jv n p d : ℕ}, linPrimaryLoopAt P b jm jv hm hv →
      ∀ (gs : List (Equiv.Perm (Fin n))), gs.length ≤ n ^ 2 →
      ∀ (_hs : IsSolvable (gens gs)) (_hp : p.Prime), p ≤ n → ∀ [NeZero n] (ν : Fin d → ℕ)
        (ρ : gens gs →* (linFiniteVec (linPrimaryOrders p ν) ≃+ linFiniteVec (linPrimaryOrders p ν)))
        (c : gens gs → linFiniteVec (linPrimaryOrders p ν)),
      (∀ g k, c (g * k) = ρ g (c k) + c g) →
      ∀ (x : linFiniteVec (linPrimaryOrders p ν)) (acc0 : Equiv.Perm (Fin n)),
      let a := linPrimaryLoopInputVal gs ν ρ c x acc0
      FunAll P b a (fun out cost => linPrimaryLoopInv gs ν ρ c x acc0 (linPrimaryHeight ν) out ∧
        cost ≤ K * (a.wt + 1) ^ D) := by
  obtain ⟨K, D, hKD⟩ := linPoly_source_bound (linPrimaryLoopCost_poly hm hv)
  refine ⟨K, D, ?_⟩
  intro P b jm jv n p d hat gs hlen hs hp hpn hn ν ρ c hc x acc0
  exact FunAll.mono (linPrimaryLoop_spec hm hv hat gs hlen hs hp hpn ν ρ c hc x acc0)
    (fun out cost ho => ⟨ho.1, ho.2.trans (hKD 0 _ _ (Nat.zero_le _) le_rfl)⟩)

end GI.Impl
