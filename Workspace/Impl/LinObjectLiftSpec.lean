import Workspace.Impl.LinObjectLiftPositive

namespace GI.Impl
open GI.Cited GI.Lang

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 3000 in
theorem linObjectLift_spec (hH : HermiteFullRank) {P : Program} {b jh n p r : ℕ}
    (h : linObjectLiftAt P b jh) (hj : P.prims[jh]? = some (linHermitePrim hH))
    {Q : Type*} [CommGroup Q] (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (B : Fin p → Submodule ℤ (Additive Q)) (hf : Function.Surjective (linObjectLiftCoord as π))
    (L : Fin p → Matrix (Fin r) (Fin as.length) ℤ) (hdr : as.length ≤ r)
    (hfull : ∀ i, Function.Injective (L i).mulVec)
    (hL : ∀ i, LinearMap.ker ((B i).mkQ.comp (linObjectLiftCoord as π)) = linRelations (L i))
    (w : Fin (as.length * p) → ℤ) :
    let a := Val.list [encGroup as, linObjectBlockInput L, linVecVal w]
    FunAll P b a (fun out cost => linObjectLiftAnswer as π B w out ∧
      cost ≤ linObjectLiftCost hH a.wt) := by
  let a := Val.list [encGroup as, linObjectBlockInput L, linVecVal w]
  let W := a.wt
  have ww : (linVecVal w).wt < W := wt_le_wt_list (by simp [a, W])
  have wg : (encGroup as).wt < W := wt_le_wt_list (by simp [a, W])
  have hc : as.length * p ≤ W := by
    have hh := length_lt_wt_list ((List.finRange (as.length * p)).map fun i => encInt (w i))
    simp only [List.length_map, List.length_finRange] at hh
    change as.length * p < (linVecVal w).wt at hh
    omega
  have dt := Det.length (Det.arg' (P := P)
    (vs := [encGroup as, linObjectBlockInput L, linVecVal w]) (rest := []) (j := 2) rfl)
  simp only [linVecVal, List.length_map, List.length_finRange] at dt
  apply FunAll.intro h.entry
  apply EvalAll.ite dt (fun v cost ho => ⟨as.length * p, ho.1⟩)
  intro q cc hq
  obtain ⟨hq, hcc⟩ := hq
  have hq' : q = as.length * p := Val.nat.inj hq
  subst q
  by_cases hz : as.length * p = 0
  · rw [if_pos hz]
    have dg := Det.arg' (P := P)
      (vs := [encGroup as, linObjectBlockInput L, linVecVal w]) (rest := []) (j := 0) rfl
    have di := Det.get' (Det.get' dg (Det.nat 1) rfl) (Det.nat 0)
      (show ((1 :: as).map encPerm)[0]? = some (encPerm (1 : Equiv.Perm (Fin n))) by rfl)
    have dout := Det.mk2 (Det.nat 1) di
    refine dout.post fun cost hcost => ⟨linObjectLift_empty as π B w hz, ?_⟩
    have wi : (encPerm (1 : Equiv.Perm (Fin n))).wt < (encGroup as).wt := by
      have h1 : (encPerm (1 : Equiv.Perm (Fin n))).wt < (Val.list ((1 :: as).map encPerm)).wt :=
        wt_le_wt_list (by simp [encPerms])
      have h2 : (Val.list ((1 :: as).map encPerm)).wt < (encGroup as).wt :=
        wt_le_wt_list (by simp [encGroup, encPerms])
      omega
    have wraw : (Val.list ((1 :: as).map encPerm)).wt < (encGroup as).wt :=
      wt_le_wt_list (by simp [encGroup, encPerms])
    have wo := wt_list2_le (.nat 1) (encPerm (1 : Equiv.Perm (Fin n)))
    change _ ≤ linObjectLiftCost hH W
    unfold linObjectLiftCost
    dsimp only [a, W, linVecVal] at *
    have hnat : (Val.nat 1).wt = 3 := rfl
    omega
  · rw [if_neg hz]
    apply EvalAll.call_funAll (Det.var' (P := P) (env := [a]) (i := 0) rfl)
    intro v ca hv
    obtain ⟨rfl, hca⟩ := hv
    refine (linObjectLift_positive_spec hH h hj as π B hf L hdr hfull hL w
      (Nat.pos_of_ne_zero hz)).wt_lt.mono fun out cost ho => ⟨ho.1.1, ?_⟩
    have hw := ho.2
    have hcost := ho.1.2
    change _ ≤ linObjectLiftCost hH W
    unfold linObjectLiftCost linObjectLiftPositiveCost at *
    dsimp only [a, W, linVecVal] at *
    omega

theorem linObjectLift_spec_poly (hH : HermiteFullRank) :
    ∃ K D : ℕ, ∀ {P : Program} {b jh n p r : ℕ}, linObjectLiftAt P b jh →
      P.prims[jh]? = some (linHermitePrim hH) →
      ∀ {Q : Type} [CommGroup Q] (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
      (B : Fin p → Submodule ℤ (Additive Q)), Function.Surjective (linObjectLiftCoord as π) →
      ∀ (L : Fin p → Matrix (Fin r) (Fin as.length) ℤ), as.length ≤ r →
      (∀ i, Function.Injective (L i).mulVec) →
      (∀ i, LinearMap.ker ((B i).mkQ.comp (linObjectLiftCoord as π)) = linRelations (L i)) →
      ∀ w : Fin (as.length * p) → ℤ,
      let a := Val.list [encGroup as, linObjectBlockInput L, linVecVal w]
      FunAll P b a (fun out cost => linObjectLiftAnswer as π B w out ∧ cost ≤ K * (a.wt + 1) ^ D) := by
  obtain ⟨K, D, hKD⟩ := linPoly_source_bound (linObjectLiftCost_poly hH)
  refine ⟨K, D, ?_⟩
  intro P b jh n p r h hj Q _ as π B hf L hdr hfull hL w
  exact (linObjectLift_spec hH h hj as π B hf L hdr hfull hL w).mono fun out cost ho =>
    ⟨ho.1, ho.2.trans (hKD 0 _ _ (by omega) le_rfl)⟩

end GI.Impl
