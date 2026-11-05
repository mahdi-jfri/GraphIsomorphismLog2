module

public import Workspace.Impl.LinObjectStabilizerCompose

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset

noncomputable def linObjectStabilizerMapBudget (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (hh : HermiteFullRank) (W : ℕ) : ℕ :=
  linPolyEnvelope (linObjectCorrectMapCost_poly hs hm hc hh) (100*(W+1)^2)
noncomputable def linObjectStabilizerKernelBudget (hs : SolvableCosetIntersection) (W : ℕ) : ℕ :=
  linPolyEnvelope (linObjectKernelCost_poly hs) (100*(W+1)^2)
noncomputable def linObjectStabilizerAdjoinArg (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (hh : HermiteFullRank) (W : ℕ) : ℕ :=
  100*(W+linObjectStabilizerMapBudget hs hm hc hh W+linObjectStabilizerKernelBudget hs W+1)^2
noncomputable def linObjectStabilizerAdjoinBudget (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (hh : HermiteFullRank) (W : ℕ) : ℕ :=
  linPolyEnvelope (linObjectAdjoinCost_poly hm) (linObjectStabilizerAdjoinArg hs hm hc hh W)
noncomputable def linObjectStabilizerSource (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (hh : HermiteFullRank) (W : ℕ) : ℕ :=
  100*(W+linObjectStabilizerMapBudget hs hm hc hh W+linObjectStabilizerKernelBudget hs W+
    linObjectStabilizerAdjoinBudget hs hm hc hh W+1)^2
noncomputable def linObjectStabilizerCost (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (hh : HermiteFullRank) (W : ℕ) : ℕ :=
  100000000*(linObjectStabilizerSource hs hm hc hh W+2)^2

theorem linObjectStabilizerCost_poly (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (hh : HermiteFullRank) : PBU (fun _ W _ => linObjectStabilizerCost hs hm hc hh W) := by
  unfold linObjectStabilizerCost linObjectStabilizerSource linObjectStabilizerAdjoinBudget
    linObjectStabilizerAdjoinArg linObjectStabilizerKernelBudget linObjectStabilizerMapBudget linPolyEnvelope
  norm_poly

set_option maxHeartbeats 600000 in
set_option maxRecDepth 3000 in
theorem linObjectStabilizer_spec {P : Program} {b jsci jder jmem jm jh n r : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership} {hc : ConstructiveMembership}
    (hh : HermiteFullRank) (h : linObjectStabilizerAt P b jsci jder jmem jm jh hs hd hm hc)
    (hjmem : P.prims[jmem]? = some (membershipPrim hm))
    (hjh : P.prims[jh]? = some (linHermitePrim hh))
    {Q : Type*} [CommGroup Q] (as ns : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (hπ : Function.Surjective π) (hf : Function.Surjective (linObjectLiftCoord as π))
    (Y : List (TmRiO n)) (hok : TmRecObjOK Y.length Y)
    (hsol : TmRiListNorm (gens as) Y) (hNA : gens ns ≤ gens as)
    (H : Subgroup (Equiv.Perm (Fin n))) (hAH : gens as ≤ H)
    (hA : GI.Multicoset.Normalizes H (gens as)) (hN : GI.Multicoset.Normalizes H (gens ns))
    (hcomm : ∀ a ∈ gens as, ∀ b ∈ gens as, a*b*a⁻¹*b⁻¹ ∈ gens ns)
    (hal : as.length ≤ n^2) (hfix : Fixes (gens ns) (tmGlMs Y))
    (hker : ∀ T ∈ pieces (gens as) (tmGlMs Y), π.ker ≤ (Aut (gens as) T).subgroupOf (gens as))
    (L : Fin (tmRiPcsO (gens as) Y).length → Matrix (Fin r) (Fin as.length) ℤ)
    (hdr : as.length ≤ r) (hfull : ∀ i, Function.Injective (L i).mulVec)
    (hL : ∀ i, LinearMap.ker ((linObjectLocalImages as π Y i).mkQ.comp (linObjectLiftCoord as π)) = linRelations (L i))
    (groups : List Val)
    (hgroups : List.Forall₂ (fun S v => GroupValC n v (Aut (gens as) (tmGlMs S)))
      (tmRiPcsO (gens as) Y) groups)
    (gs : List (Equiv.Perm (Fin n))) (hgs : ∀ g ∈ gs, g ∈ H)
    (hy : ∀ g ∈ gs, Conf (gens as) (tmGlMs Y) (tmGlMs Y ↼ g))
    (hex : ∀ g ∈ gs, ∃ a ∈ gens as, (tmGlMs Y ↼ g) ↼ a = tmGlMs Y)
    (hcover : Aut H (tmGlMs Y) ≤ gens gs) :
    let ctx := Val.list [encGroup as,encGroup ns,.list ((tmRiPcsO (gens as) Y).map tmGlObjsVal),linObjectBlockInput L]
    let input := Val.list [ctx,.list groups,.list (gs.map encPerm)]
    FunAll P b input (fun out cost => GroupValC n out (Aut H (tmGlMs Y)) ∧
      cost ≤ linObjectStabilizerCost hs hm hc hh input.wt) := by
  let ctx := Val.list [encGroup as,encGroup ns,.list ((tmRiPcsO (gens as) Y).map tmGlObjsVal),linObjectBlockInput L]
  let input := Val.list [ctx,.list groups,.list (gs.map encPerm)]
  let W := input.wt
  let MB := linObjectStabilizerMapBudget hs hm hc hh W
  let KB := linObjectStabilizerKernelBudget hs W
  let AB := linObjectStabilizerAdjoinBudget hs hm hc hh W
  let C := linObjectStabilizerSource hs hm hc hh W
  have wc : ctx.wt ≤ W := (wt_le_wt_list (by simp [input,W])).le
  have wg : (Val.list (gs.map encPerm)).wt ≤ W := (wt_le_wt_list (by simp [input,W])).le
  have wgroups : (Val.list groups).wt ≤ W := (wt_le_wt_list (by simp [input,W])).le
  have wa : (encGroup as).wt ≤ W := (wt_le_wt_list (by simp [ctx])).le.trans wc
  have wn : (Val.nat n).wt ≤ W := (wt_le_wt_list (by simp [encGroup])).le.trans wa
  have hn : n ≤ W := by
    have hh' := S_le_wt_encGroup as
    have hm' : n+1 ≤ (as.length+2)*(n+1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hmArg : (Val.list [ctx,.list (gs.map encPerm)]).wt ≤ 100*(W+1)^2 := by
    have ht := wt_list2_le ctx (.list (gs.map encPerm))
    have hp : W+1 ≤ (W+1)^2 := Nat.le_self_pow (by decide) _
    omega
  have hkArg : (Val.list [encGroup as,.list groups]).wt ≤ 100*(W+1)^2 := by
    have ht := wt_list2_le (encGroup as) (.list groups)
    have hp : W+1 ≤ (W+1)^2 := Nat.le_self_pow (by decide) _
    omega
  have hm0 := linObjectCorrectMap_object_spec hh h.correct hjh as ns π hπ hf Y hok hsol hNA H hAH hA hN
    hcomm hal hfix hker L hdr hfull hL gs hgs hy hex
  have hmCall : FunAll P (b+1) (.list [ctx,.list (gs.map encPerm)])
      (fun raw cost => (∃ ks,raw = .list (ks.map encPerm) ∧ List.Forall₂
        (linObjectCorrectPair (gens as) (tmGlMs Y)) gs ks) ∧ cost ≤ MB) :=
    hm0.mono fun out cost hout => ⟨hout.1,hout.2.trans (linPolyEnvelope_bound
      (linObjectCorrectMapCost_poly hs hm hc hh) (Nat.zero_le _) hmArg (Nat.zero_le _))⟩
  have hnB : n ≤ 100*(W+1)^2 := by
    have hpW : W+1 ≤ (W+1)^2 := Nat.le_self_pow (by decide) _
    omega
  have hk : FunAll P (b+320) (.list [encGroup as,.list groups])
      (fun v cost => GroupValC n v (Aut (gens as) (tmGlMs Y)) ∧ cost ≤ KB) :=
    (linObjectKernel_aut_spec h.kernel as Y groups hgroups ns hNA hcomm hfix hal).mono fun out cost hout =>
      ⟨hout.1,hout.2.trans (linPolyEnvelope_bound (linObjectKernelCost_poly hs)
        hnB hkArg (Nat.zero_le _))⟩
  have hp : W+MB+KB+AB+1 ≤ (W+MB+KB+AB+1)^2 := Nat.le_self_pow (by decide) _
  have wC : W ≤ C := by change W ≤ 100*(W+MB+KB+AB+1)^2; omega
  have mC : MB ≤ C := by change MB ≤ 100*(W+MB+KB+AB+1)^2; omega
  have kC : KB ≤ C := by change KB ≤ 100*(W+MB+KB+AB+1)^2; omega
  have aC : AB ≤ C := by change AB ≤ 100*(W+MB+KB+AB+1)^2; omega
  have hC : 100 ≤ C := by change 100 ≤ 100*(W+MB+KB+AB+1)^2; omega
  have hm' : FunAll P (b+1) (.list [ctx,.list (gs.map encPerm)])
      (fun out cost => ((∃ ks,out = .list (ks.map encPerm) ∧ List.Forall₂
        (linObjectCorrectPair (gens as) (tmGlMs Y)) gs ks) ∧ out.wt ≤ MB) ∧ cost ≤ C) := hmCall.wt_lt.mono fun out cost hout =>
    ⟨⟨hout.1.1,hout.2.le.trans hout.1.2⟩,hout.1.2.trans mC⟩
  have hk' : FunAll P (b+320) (.list [encGroup as,.list groups])
      (fun out cost => (GroupValC n out (Aut (gens as) (tmGlMs Y)) ∧ out.wt ≤ KB) ∧ cost ≤ C) := hk.wt_lt.mono fun out cost hout =>
    ⟨⟨hout.1.1,hout.2.le.trans hout.1.2⟩,hout.1.2.trans kC⟩
  apply linObjectStabilizer_comp h.entry ctx (.list groups) (.list (gs.map encPerm)) (encGroup as) (.nat n)
    _ _ (GroupValC n · (Aut H (tmGlMs Y))) hC wC rfl rfl hm' hk'
  intro raw hr wr kv hv wkv
  obtain ⟨⟨ks,rfl,hks⟩,wks⟩ := hr
  obtain ⟨hkv,wk⟩ := hv
  have harg : (Val.list [.nat n,.list (ks.map encPerm),kv]).wt ≤
      linObjectStabilizerAdjoinArg hs hm hc hh W := by
    have ht := wt_list3_le (.nat n) (.list (ks.map encPerm)) kv
    have hp' : W+MB+KB+1 ≤ (W+MB+KB+1)^2 := Nat.le_self_pow (by decide) _
    change _ ≤ 100*(W+MB+KB+1)^2
    omega
  have hgen := linObjectCorrectedList_eq H (gens as) hAH hA (tmGlMs Y) gs ks hgs hcover hks
  refine (linObjectAdjoin_spec hm h.adjoin hjmem ks kv _ hkv.groupVal).mono
    fun out cost hout => ⟨?_,hout.2.trans ((linPolyEnvelope_bound (linObjectAdjoinCost_poly hm)
      (Nat.zero_le _) harg (Nat.zero_le _)).trans aC)⟩
  simpa only [hgen] using hout.1

end GI.Impl
