import Workspace.Impl.LinMixedStepSpec
import Workspace.Impl.LinMixedTerminal

namespace GI.Impl
open GI.Cited GI.Lang
set_option maxRecDepth 16000

private theorem linMixedLoopCollect {W A B I n cost : ℕ} (hn : n ≤ W)
    (hc : cost ≤ I + I + n * B + 1000 * (n + 1) * (W + n + A + 1)) :
    cost ≤ 1000000 * (I + W * B + 1000 * (W + 1) * (2 * W + A + 1) + 1) := by
  have hm := Nat.mul_le_mul_right B hn
  have ho := Nat.mul_le_mul
    (Nat.mul_le_mul_left 1000 (Nat.add_le_add_right hn 1))
    (show W + n + A + 1 ≤ 2 * W + A + 1 by omega)
  omega

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 16000 in
theorem linMixedLoop_spec (hm : ConstructiveMembership) (hv : VectorStabilizer)
    {P : Program} {b jm jv n d : ℕ} (hat : linMixedLoopAt P b jm jv hm hv)
    (gs : List (Equiv.Perm (Fin n))) (hlen : gs.length ≤ n ^ 2) (hs : IsSolvable (gens gs))
    (m : Fin d → ℕ) (hmpos : ∀ i, 0 < m i)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m)
    (hc : ∀ g k, c (g * k) = ρ g (c k) + c g)
    (x : linFiniteVec m) (acc0 : Equiv.Perm (Fin n)) :
    let a := linMixedLoopInputVal gs m ρ c x acc0
    FunAll P b a (fun out cost => linMixedLoopInv gs m hmpos ρ c x acc0 n out ∧
      cost ≤ linMixedLoopCost hm hv a.wt) := by
  let a := linMixedLoopInputVal gs m ρ c x acc0
  let W := a.wt
  obtain ⟨hn, hd, hwm⟩ := linMixedLoop_source_bounds gs m ρ c x acc0
  have hk := linMixedLoop_count_det (P := P) gs m ρ c x acc0
  have hacc := linMixedLoop_start_det (P := P) (linActionContext gs m ρ c)
    (linFinitePointVal m x) (encPerm acc0) (linVecVal (fun i => (m i : ℤ)))
  have h0 := linMixedLoopInv_init gs hlen m hmpos ρ c hc x acc0
  have hM (j : ℕ) (v : Val) (_ : j ≤ n) (hv : linMixedLoopInv gs m hmpos ρ c x acc0 j v) :
      v.wt ≤ linPrimaryAccumulatorWeight W := linMixedLoopInv_wt gs m hmpos hn hd hwm ρ c x acc0 j v hv
  have run := linLoopBddInit_spec hat.loop hk hacc (M := linPrimaryAccumulatorWeight W)
    (Inv := linMixedLoopInv gs m hmpos ρ c x acc0) h0 hM
    (D := fun _ => linMixedStepBudget hm hv W) (by
      intro j v hj hInv
      have he := linMixedLoop_step_spec hm hv hat gs hs m hmpos ρ c hc x acc0 j hj v hInv
      exact he.mono fun out cost ho => ⟨ho.1, ho.2.trans (Nat.le_add_right _ _)⟩)
  refine run.mono fun out cost ho => ⟨ho.1, ?_⟩
  have hcost := ho.2
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, loopModK] at hcost
  exact linMixedLoopCollect (W := W) (A := linPrimaryAccumulatorWeight W)
    (B := linMixedStepBudget hm hv W) (I := linMixedInitBudget W) hn hcost

set_option maxHeartbeats 1000000 in
theorem linMixedLoop_spec_poly (hm : ConstructiveMembership) (hv : VectorStabilizer) :
    ∃ K D : ℕ, ∀ {P : Program} {b jm jv n d : ℕ}, linMixedLoopAt P b jm jv hm hv →
      ∀ (gs : List (Equiv.Perm (Fin n))), gs.length ≤ n ^ 2 → IsSolvable (gens gs) →
      ∀ (m : Fin d → ℕ) (hmpos : ∀ i, 0 < m i)
        (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m),
      (∀ g k, c (g * k) = ρ g (c k) + c g) →
      ∀ (x : linFiniteVec m) (acc0 : Equiv.Perm (Fin n)),
      let a := linMixedLoopInputVal gs m ρ c x acc0
      FunAll P b a (fun out cost => linMixedLoopInv gs m hmpos ρ c x acc0 n out ∧
        cost ≤ K * (a.wt + 1) ^ D) := by
  obtain ⟨K, D, hKD⟩ := linPoly_source_bound (linMixedLoopCost_poly hm hv)
  refine ⟨K, D, ?_⟩
  intro P b jm jv n d hat gs hlen hs m hmpos ρ c hc x acc0
  exact FunAll.mono (linMixedLoop_spec hm hv hat gs hlen hs m hmpos ρ c hc x acc0)
    (fun out cost ho => ⟨ho.1, ho.2.trans (hKD 0 _ _ (Nat.zero_le _) le_rfl)⟩)

end GI.Impl
