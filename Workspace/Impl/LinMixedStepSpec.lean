module

public import Workspace.Impl.LinMixedCost
public import Workspace.Impl.LinMixedAdvance

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang
set_option maxRecDepth 24000

private theorem linMixedStepWholeCost {W A C Q S cc ct cb out : ℕ}
    (hS : S ≤ 4 * W + 2 * A + 11) (hcc : cc ≤ 2 * S + 20)
    (hct : ct ≤ 100000 * (S + W + Q + 1))
    (hcb : cb ≤ 100000 * (S + W + 1) + 2 * C + 1) (hout : out ≤ A) :
    cc + (ct + cb + out + 1) + out + 1 ≤ 10000000000 * (W + A + C + Q + 1) := by omega

set_option maxHeartbeats 1500000 in
theorem linMixedLoop_step_spec (hm : ConstructiveMembership) (hv : VectorStabilizer)
    {P : Program} {b jm jv n d : ℕ} (hat : linMixedLoopAt P b jm jv hm hv)
    (gs : List (Equiv.Perm (Fin n)))
    (m : Fin d → ℕ) (hmpos : ∀ i, 0 < m i)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m))
    (hs : IsSolvable ρ.range)
    (c : gens gs → linFiniteVec m)
    (hc : ∀ g k, c (g * k) = ρ g (c k) + c g)
    (x : linFiniteVec m) (acc0 : Equiv.Perm (Fin n)) (j : ℕ) (hj : j < n) (cur : Val)
    (hinv : linMixedLoopInv gs m hmpos ρ c x acc0 j cur) :
    let a := linMixedLoopInputVal gs m ρ c x acc0
    EvalAll P [.list [a, .nat j, cur]] (linMixedLoopStepF (b + 3) (b + 11))
      (fun out cost => linMixedLoopInv gs m hmpos ρ c x acc0 (j + 1) out ∧
        cost ≤ linMixedStepBudget hm hv a.wt) := by
  let orig := linMixedLoopInputVal gs m ρ c x acc0
  let W := orig.wt
  let A := linPrimaryAccumulatorWeight W
  let C := linMixedCallBudget hm hv W
  let Q := linMixedPrimeBudget W
  obtain ⟨hn, hd, hwm⟩ := linMixedLoop_source_bounds gs m ρ c x acc0
  have hjW : j + 1 ≤ W := (Nat.succ_le_of_lt hj).trans hn
  have wcur : cur.wt ≤ A := linMixedLoopInv_wt gs m hmpos hn hd hwm ρ c x acc0 j cur hinv
  have hsource : (Val.list [orig, .nat j, cur]).wt ≤ 4 * W + 2 * A + 11 := by
    have hh := wt_stepArg_le orig j cur
    change (Val.list [orig, .nat j, cur]).wt ≤ 2 * (W + j + cur.wt) + 11 at hh
    omega
  rcases hinv with ⟨rfl, hno⟩ | ⟨ks, hle, r, rfl, hlen, hpoint, hofs, hcover⟩
  · have dl := Det.length (Det.arg' (P := P) (vs := [orig, .nat j, .list []]) (rest := []) (j := 2) rfl)
    have dd := Det.ite_zero (t := .ite (.call (b + 3) (.arith .add (arg 1) (.nat 1)))
      (.call (b + 11) linMixedPassArgE) (arg 2)) dl (Det.nil (P := P) (env := [.list [orig, .nat j, .list []]]))
    refine dd.post fun cost hcst => ⟨Or.inl ⟨rfl, hno⟩, ?_⟩
    norm_num only [List.length_nil, wt_list_nil, Nat.add_assoc] at hcst
    change cost ≤ linMixedStepBudget hm hv W
    unfold linMixedStepBudget
    change cost ≤ 10000000000 * (W + A + C + Q + 1)
    omega
  · let ρ' := ρ.comp (Subgroup.inclusion hle)
    let c' := c ∘ Subgroup.inclusion hle
    let point := linFiniteEval ρ c r x
    let accum := r.val * acc0
    let state := Val.list [linActionContext ks m ρ' c', linFinitePointVal m point, encPerm accum]
    let S := (Val.list [orig, .nat j, state]).wt
    have hcur : linMixedLoopInv gs m hmpos ρ c x acc0 j state :=
      Or.inr ⟨ks, hle, r, rfl, hlen, hpoint, hofs, hcover⟩
    have hks := linPrimaryRange_solvable gs ks ρ hs hle
    have dl := Det.length (Det.arg' (P := P) (vs := [orig, .nat j, state]) (rest := []) (j := 2) rfl)
    apply EvalAll.ite dl (fun v cost ho => ⟨3, ho.1⟩)
    intro q cc hq
    obtain ⟨hq, hcc⟩ := hq
    have hq' : q = 3 := Val.nat.inj hq
    subst q
    norm_num only [List.length_cons, List.length_nil, Nat.add_assoc] at hcc
    have hcc' : cc ≤ 2 * S + 20 := by omega
    have hpTest := (linPrimeTest_spec hat.prime (j + 1)).mono (show
      linPrimeTestCost (j + 1) ≤ Q by unfold Q linMixedPrimeBudget linPrimeTestCost; gcongr)
    have dj := Det.arg' (P := P) (vs := [orig, .nat j, state]) (rest := []) (j := 1) rfl
    have dtest0 := Det.call (Det.arith (op := .add) dj (Det.nat 1)) hpTest
    have dtest := dtest0.mono (show _ ≤ linMixedPrimeCallBudget W S by
      have wj := wt_nat_le j
      have wp := wt_nat_le (j + 1)
      have wb := wt_boolVal_le (decide (j + 1).Prime)
      simp only [GI.Machine.BinOp.eval_add]
      unfold linMixedPrimeCallBudget
      change _ ≤ 100000 * (S + W + Q + 1)
      omega)
    by_cases hp : (j + 1).Prime
    · simp only [hp, decide_true, boolVal, Bool.toNat_true] at dtest
      apply EvalAll.ite dtest (fun v cost ho => ⟨1, ho.1⟩)
      intro q ct hq
      obtain ⟨hq, hct⟩ := hq
      have hq' : q = 1 := Val.nat.inj hq
      subst q
      letI : NeZero n := ⟨by omega⟩
      let hc' := linActionRestricted_cocycle m ρ c hc (Subgroup.inclusion hle)
      have hi := linMixedPassInput_wt ks hlen hn hd m hmpos hwm ρ' c' point accum (j + 1) hjW
      have hpass : FunAll P (b + 11) (linPrimePrepareInputVal ks m ρ' c' point accum (j + 1))
          (fun out cost => linPrimePassOut ks m (linTrialPrimaryData m (j + 1) hp hmpos)
            ρ' c' point accum out ∧ cost ≤ C) :=
        FunAll.mono (linPrimePass_spec hm hv hat.pass ks hlen m hp (by omega) hmpos ρ' hks c' hc' point accum)
          (fun out cost ho => ⟨ho.1, ho.2.trans (linMixedCallBudget_bound hm hv hi)⟩)
      have da := linMixedPassArg_spec (P := P) (linActionContext gs m ρ c) (linFinitePointVal m x)
        (encPerm acc0) (linVecVal (fun i => (m i : ℤ)))
        (linActionContext ks m ρ' c') (linFinitePointVal m point) (encPerm accum) j
      have call := normBound_call da hpass
      refine call.mono fun out cb ho => ?_
      have hnext := linMixedLoopInv_advance gs ks m hmpos ρ c hc x acc0 j hp hle r hpoint hofs hcover out ho.1
      have wn : out.wt ≤ A := linMixedLoopInv_wt gs m hmpos hn hd hwm ρ c x acc0 (j + 1) out hnext
      refine ⟨hnext, ?_⟩
      have hcb : cb ≤ 100000 * (S + W + 1) + 2 * C + 1 := by
        have hh := ho.2.2
        change cb ≤ 100000 * (S + j + 1) + 2 * C + 1 at hh
        omega
      change _ ≤ linMixedStepBudget hm hv W
      exact linMixedStepWholeCost (W := W) (A := A) (C := C) (Q := Q) hsource hcc' hct hcb wn
    · simp only [hp, decide_false, boolVal, Bool.toNat_false] at dtest
      have dc := Det.arg' (P := P) (vs := [orig, .nat j, state]) (rest := []) (j := 2) rfl
      have dd := Det.ite_zero (t := .call (b + 11) linMixedPassArgE) dtest dc
      refine dd.post fun cb hcb => ⟨linMixedLoopInv_skip gs m hmpos ρ c x acc0 j hp state hcur, ?_⟩
      have hb : 2 * S + 7 ≤ 100000 * (S + W + 1) + 2 * C + 1 := by omega
      have hw : state.wt ≤ A := wcur
      have hh := linMixedStepWholeCost (W := W) (A := A) (C := C) (Q := Q)
        hsource hcc' (show linMixedPrimeCallBudget W S ≤ 100000 * (S + W + Q + 1) from le_rfl) hb hw
      change _ ≤ linMixedStepBudget hm hv W
      unfold linMixedStepBudget
      change _ ≤ 10000000000 * (W + A + C + Q + 1)
      change cb ≤ linMixedPrimeCallBudget W S + (2 * S + 2 + 5) + state.wt + 1 at hcb
      omega

end GI.Impl
