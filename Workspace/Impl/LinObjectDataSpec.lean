import Workspace.Impl.LinObjectDataTail

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset

set_option maxHeartbeats 300000 in
set_option maxRecDepth 500 in
theorem linObjectData_spec (ho : GroupOrder) (hh : HermiteFullRank) (hn : SmithNonsingular)
    {P : Program} {b jsci jder jmem jo jm jh js n M : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership} {hc : ConstructiveMembership}
    (h : linObjectDataAt P b jsci jder jmem jo jm jh js hs hd hm hc)
    (hjo : P.prims[jo]? = some (groupOrderPrim ho)) (hjm : P.prims[jm]? = some (linMembershipPrim hc))
    (hjh : P.prims[jh]? = some (linHermitePrim hh)) (hjs : P.prims[js]? = some (linSmithPrim hn))
    {Q : Type*} [CommGroup Q] (as ns : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (X Y : List (TmRiO n)) (hsol : IsSolvable (gens as)) (hNA : gens ns ≤ gens as)
    (hNn : GI.Multicoset.Normalizes (gens as) (gens ns))
    (hcomm : ∀ a ∈ gens as, ∀ b ∈ gens as, a * b * a⁻¹ * b⁻¹ ∈ gens ns)
    (hal : as.length ≤ n ^ 2) (hYlen : Y.length ≤ M)
    (hfix : Fixes (gens ns) (tmGlMs Y)) (hok : TmRecObjOK M Y)
    (hMsize : M ≤ (Val.list [encGroup as, encGroup ns, tmGlObjsVal X, tmGlObjsVal Y]).wt) :
    let input := Val.list [encGroup as, encGroup ns, tmGlObjsVal X, tmGlObjsVal Y]
    FunAll P b input (fun out cost => linObjectDataOut as ns Y π out ∧
      cost ≤ linObjectDataCost hs hm ho hc hh hn input.wt) := by
  let input := Val.list [encGroup as, encGroup ns, tmGlObjsVal X, tmGlObjsVal Y]
  let W := input.wt
  let PB := linObjectDataPiecesBudget hs hm W
  let AB := linObjectDataAbelianBudget ho hc W
  have wa : (encGroup as).wt < W := wt_le_wt_list (by simp [input, W])
  have wn : (encGroup ns).wt < W := wt_le_wt_list (by simp [input, W])
  have wy : (tmGlObjsVal Y).wt < W := wt_le_wt_list (by simp [input, W])
  have hdegree : n ≤ W := by have hw := S_le_wt_encGroup as; nlinarith
  have hmW : M ≤ W := hMsize
  have hpiecesArg : (Val.list [encGroup as, encGroup ns, tmGlObjsVal Y]).wt ≤ 100 * (W + 1) := by
    have hw := wt_list3_le (encGroup as) (encGroup ns) (tmGlObjsVal Y)
    omega
  have hpieces : FunAll P (b + 1) (.list [encGroup as, encGroup ns, tmGlObjsVal Y])
      (fun out cost => (∃ groups, out = .list [.list ((tmRiPcsO (gens as) Y).map tmGlObjsVal), .list groups] ∧
        List.Forall₂ (fun S v => GroupValC n v (Aut (gens as) (tmGlMs S))) (tmRiPcsO (gens as) Y) groups) ∧
        cost ≤ PB) :=
    (linObjectPieces_spec h.pieces as ns Y hsol hNA hNn hcomm hal hYlen hfix hok).mono
      fun out cost ho' => ⟨ho'.1, ho'.2.trans (linPolyEnvelope_bound (linObjectPiecesCost_poly hs hm)
        (hdegree.trans (by omega)) (hmW.trans (by omega)) hpiecesArg)⟩
  have habArg : (Val.list [encGroup ns, encGroup as]).wt ≤ 100 * (W + 1) := by
    have hw := wt_list2_le (encGroup ns) (encGroup as)
    omega
  have hab : FunAll P (b + 103) (.list [encGroup ns, encGroup as])
      (fun out cost => (∃ M : Matrix (Fin as.length) (Fin as.length) ℤ,
        out = encIntMatrix M ∧ linPermPresentation ns as M) ∧ cost ≤ AB) := by
    have ht := (linCoordinateSource_bounds ns as).2.2
    refine (linAbelianCoordinates_spec ho hc h.abel hjo hjm ns as hNA hcomm).mono
      fun out cost ho' => ⟨ho'.1, ho'.2.trans ?_⟩
    exact (linAbelianCoordinatesCost_mono_t ho hc _ ht).trans
      (linPolyEnvelope_bound (linAbelianCoordinatesBudget_poly ho hc) (Nat.zero_le _) habArg (Nat.zero_le _))
  have da (k : ℕ) {v : Val} (hv : [encGroup as, encGroup ns, tmGlObjsVal X, tmGlObjsVal Y][k]? = some v) :=
    Det.arg' (P := P) (vs := [encGroup as, encGroup ns, tmGlObjsVal X, tmGlObjsVal Y]) (rest := []) (j := k) hv
  apply FunAll.intro h.entry
  apply EvalAll.letE (normBound_call (Det.mk3 (da 0 rfl) (da 1 rfl) (da 3 rfl)) hpieces)
  intro pv cp hpv
  obtain ⟨⟨groups, rfl, hgroups⟩, wp, hcp⟩ := hpv
  let pv := Val.list [.list ((tmRiPcsO (gens as) Y).map tmGlObjsVal), .list groups]
  have dn := Det.arg' (P := P) (vs := [encGroup as, encGroup ns, tmGlObjsVal X, tmGlObjsVal Y])
    (rest := [pv]) (j := 1) rfl
  have dA := Det.arg' (P := P) (vs := [encGroup as, encGroup ns, tmGlObjsVal X, tmGlObjsVal Y])
    (rest := [pv]) (j := 0) rfl
  apply EvalAll.letE (normBound_call (Det.mk2 dn dA) hab)
  intro mv cm hmv
  obtain ⟨⟨M, rfl, hM⟩, wm, hcm⟩ := hmv
  refine (linObjectData_tail_spec ho hh hn h hjh hjs as ns π X Y M hM groups hgroups wp wm).wt_lt.mono
    fun out cost ho' => ⟨ho'.1.1, ?_⟩
  have hcost := ho'.1.2
  have wout := ho'.2
  have whp := wt_list3_le (encGroup as) (encGroup ns) (tmGlObjsVal Y)
  have wha := wt_list2_le (encGroup ns) (encGroup as)
  change _ ≤ linObjectDataCost hs hm ho hc hh hn W
  unfold linObjectDataCost linObjectDataTailCost at *
  dsimp only [input, W, PB, AB, pv] at *
  omega

theorem linObjectData_uniform (hs : SolvableCosetIntersection) (hm : Membership)
    (ho : GroupOrder) (hc : ConstructiveMembership) (hh : HermiteFullRank) (hn : SmithNonsingular) :
    ∃ K D : ℕ, ∀ W, linObjectDataCost hs hm ho hc hh hn W ≤ K * (W + 1) ^ D := by
  obtain ⟨K, D, hKD⟩ := linPoly_source_bound (linObjectDataCost_poly hs hm ho hc hh hn)
  exact ⟨K, D, fun W => hKD 0 W W (Nat.zero_le _) le_rfl⟩

end GI.Impl
