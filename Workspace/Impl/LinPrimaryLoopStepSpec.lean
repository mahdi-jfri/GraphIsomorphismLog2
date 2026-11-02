import Workspace.Impl.LinPrimaryLoopCost

namespace GI.Impl
open GI.Cited GI.Lang
set_option maxRecDepth 16000

private theorem linPrimaryLoopSourceBound {s W j a M : ℕ}
    (hs : s ≤ 2 * (W + j + a) + 11) (hj : j ≤ W) (ha : a ≤ M) : s ≤ 4 * W + 2 * M + 11 := by omega

private theorem linPrimaryLoopGuardBound {S cc : ℕ} (h : cc ≤ 2 * S + 13) : cc ≤ 2 * S + 20 := by omega

set_option maxHeartbeats 3000000 in
theorem linPrimaryLoop_step_spec (hm : ConstructiveMembership) (hv : VectorStabilizer)
    {P : Program} {b jm jv n p d : ℕ} (hat : linPrimaryLoopAt P b jm jv hm hv)
    (gs : List (Equiv.Perm (Fin n))) (hs : IsSolvable (gens gs)) (hp : p.Prime) (hpn : p ≤ n)
    [NeZero n] (ν : Fin d → ℕ)
    (ρ : gens gs →* (linFiniteVec (linPrimaryOrders p ν) ≃+ linFiniteVec (linPrimaryOrders p ν)))
    (c : gens gs → linFiniteVec (linPrimaryOrders p ν))
    (hc : ∀ g k, c (g * k) = ρ g (c k) + c g)
    (x : linFiniteVec (linPrimaryOrders p ν)) (acc0 : Equiv.Perm (Fin n))
    (j : ℕ) (hj : j < linPrimaryHeight ν) (cur : Val)
    (hinv : linPrimaryLoopInv gs ν ρ c x acc0 j cur) :
    let a := linPrimaryLoopInputVal gs ν ρ c x acc0
    EvalAll P [.list [a, .nat j, cur]] (linPrimaryLoopStepF (b + 8))
      (fun out cost => linPrimaryLoopInv gs ν ρ c x acc0 (j + 1) out ∧
        cost ≤ linPrimaryLoopStepBudget hm hv a.wt) := by
  let m := linPrimaryOrders p ν
  let orig := linPrimaryLoopInputVal gs ν ρ c x acc0
  let W := orig.wt
  obtain ⟨hn, hd, hwm, hheight, hν⟩ := linPrimaryLoop_source_bounds gs hp ν ρ c x acc0
  have hjW : j ≤ W := hj.le.trans hheight
  have wcur : cur.wt ≤ (linPrimaryAccumulatorWeight W) := linPrimaryLoopInv_wt gs hp ν hn hd hwm ρ c x acc0 j cur hinv
  have hsource : (Val.list [orig, .nat j, cur]).wt ≤ 4 * W + 2 * (linPrimaryAccumulatorWeight W) + 11 :=
    linPrimaryLoopSourceBound (wt_stepArg_le orig j cur) hjW wcur
  rcases hinv with ⟨rfl, hno⟩ | ⟨ks, hle, r, rfl, hlen, hpoint, hofs, hcover⟩
  · have dl := Det.length (Det.arg' (P := P) (vs := [orig, .nat j, .list []]) (rest := []) (j := 2) rfl)
    have dd := Det.ite_zero (t := .call (b + 8) linPrimaryLoopArgE) dl (Det.nil (P := P) (env := [.list [orig, .nat j, .list []]]))
    refine dd.post fun cost hcost => ⟨Or.inl ⟨rfl, hno⟩, ?_⟩
    norm_num only [List.length_nil, wt_list_nil, Nat.add_assoc] at hcost
    exact hcost.trans (linPrimaryLoop_failure_budget hm hv W _ hsource)
  · let ρ' := ρ.comp (Subgroup.inclusion hle)
    let c' := c ∘ Subgroup.inclusion hle
    let hc' := linActionRestricted_cocycle m ρ c hc (Subgroup.inclusion hle)
    let point := linFiniteEval ρ c r x
    let accum := r.val * acc0
    let state := Val.list [linActionContext ks m ρ' c', linFinitePointVal m point, encPerm accum]
    let S := (Val.list [orig, .nat j, state]).wt
    have hks := linPrimaryCover_solvable gs ks hs hle
    have hi : (linPrimaryIterationVal ks m ρ' c' point accum p ν j).wt ≤ linPrimaryIterationWeight W :=
      linPrimaryIteration_wt ks hlen hn hd m (fun i => Nat.pow_pos hp.pos) hwm ρ' c' point accum ν hν (hpn.trans hn) j hjW
    have hstep : FunAll P (b + 8) (linPrimaryIterationVal ks m ρ' c' point accum p ν j)
        (fun out cost => linPrimaryStepOut ks hks hp hpn ν j ρ' c' hc' hofs point accum out ∧ cost ≤ (linPrimaryLoopCallBudget hm hv W)) :=
      FunAll.mono (linPrimaryStep_spec hm hv hat.step ks hks hp hpn ν j ρ' c' hc' hofs point hpoint accum)
        (fun out cost ho => ⟨ho.1, ho.2.trans (linPrimaryLoopCallBudget_bound hm hv hi hjW)⟩)
    have da := linPrimaryLoopArg_spec (P := P) (linActionContext gs m ρ c) (linFinitePointVal m x) (encPerm acc0)
      (linActionContext ks m ρ' c') (linFinitePointVal m point) (encPerm accum) p ν j
    have call := normBound_call da hstep
    have dl := Det.length (Det.arg' (P := P) (vs := [orig, .nat j, state]) (rest := []) (j := 2) rfl)
    apply EvalAll.ite dl (fun v cost ho => ⟨3, ho.1⟩)
    intro q cc hq
    obtain ⟨hq, hcc⟩ := hq
    have hq' : q = 3 := Val.nat.inj hq
    subst q
    change EvalAll P [.list [orig, .nat j, state]] (.call (b + 8) linPrimaryLoopArgE) _
    refine call.mono fun out cb ho => ?_
    have hnext := linPrimaryLoopInv_advance gs ks hks hp hpn ν ρ c hc x acc0 j hle r hpoint hofs hcover out ho.1
    have wn := linPrimaryLoopInv_wt gs hp ν hn hd hwm ρ c x acc0 (j + 1) out hnext
    refine ⟨hnext, ?_⟩
    norm_num only [List.length_cons, List.length_nil, Nat.add_assoc] at hcc
    have hcBound : cc ≤ 2 * S + 20 := linPrimaryLoopGuardBound hcc
    have cbBound := ho.2.2
    exact linPrimaryLoop_success_budget hm hv W S cc cb out.wt hsource hcBound cbBound wn

end GI.Impl
