module

public import Workspace.Impl.LinObjectCallerCost

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset

set_option maxHeartbeats 300000 in
set_option maxRecDepth 2000 in
theorem linObjectAffineCaller_object_spec (hh : HermiteFullRank)
    {P : Program} {b jsci jder jmem jm jh jv n : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership} {hc : ConstructiveMembership} {hv : VectorStabilizer}
    (h : linObjectAffineCallerAt P b jsci jder jmem jm jh jv hs hd hm hc hv)
    (hjh : P.prims[jh]? = some (linHermitePrim hh))
    {Q R : Type*} [CommGroup Q] [AddCommGroup R]
    (as ns : List (Equiv.Perm (Fin n))) (π : gens as →* Q) (hπ : Function.Surjective π)
    (Y : List (TmRiO n)) (hok : TmRecObjOK Y.length Y)
    (hsol : TmRiListNorm (gens as) Y) (hNA : gens ns ≤ gens as)
    (gs : List (Equiv.Perm (Fin n))) (hAH : gens as ≤ gens gs)
    (hA : GI.Multicoset.Normalizes (gens gs) (gens as)) (hN : GI.Multicoset.Normalizes (gens gs) (gens ns))
    (hcomm : ∀ a ∈ gens as, ∀ b ∈ gens as, a * b * a⁻¹ * b⁻¹ ∈ gens ns)
    (hal : as.length ≤ n ^ 2) (hf : Fixes (gens ns) (tmGlMs Y))
    (hker : ∀ T ∈ pieces (gens as) (tmGlMs Y), π.ker ≤ (Aut (gens as) T).subgroupOf (gens as))
    (hy : ∀ g ∈ (gens gs), Conf (gens as) (tmGlMs Y) (tmGlMs Y ↼ g))
    (q : linObjectIndexedProduct as π Y →+ R)
    (V D : Matrix (Fin (as.length * (tmRiPcsO (gens as) Y).length))
      (Fin (as.length * (tmRiPcsO (gens as) Y).length)) ℤ)
    (hV : IsUnit V.det) (hpos : ∀ i, 0 < D i i)
    (E : R ≃+ tmGLVec (tmGLQMod D))
    (hE : ∀ z, E (q (linObjectProductMap
      (fun i => linObjectGroupImage (gens as) π (Aut (gens as) (tmGlMs ((tmRiPcsO (gens as) Y).get i))))
      (linObjectLiftCoord as π) (linObjectUnflatten _ _ z))) = tmGLQMap V D z)
    (ρ : (gens gs) →* (tmGLVec (tmGLQMod D) ≃+ tmGLVec (tmGLQMod D))) (c : (gens gs) → tmGLVec (tmGLQMod D))
    (hAct : ∀ k : (gens gs), ∀ Z (hZ : Conf (gens as) (tmGlMs Y) Z),
      ρ k (E (q (linObjectIndexedConfigEquiv as π hπ Y hker ⟨Z,hZ⟩))) + c k =
        E (q (linObjectIndexedConfigEquiv as π hπ Y hker
          ⟨Z ↼ k.val⁻¹,(affine_law hA ((gens gs).inv_mem k.property) (hy _ ((gens gs).inv_mem k.property)) hZ).2.2⟩)))
    (hsolB : IsSolvable ρ.range)
    (hprime : ∀ i p, p.Prime → p ∣ tmGLQMod D i → p ≤ max n 2)
    (hcocycle : ∀ g k, c (g * k) = ρ g (c k) + c g)
    (v w : tmGLVec (tmGLQMod D)) :
    let refs := tmRiPcsO (gens as) Y
    let ctx := Val.list [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),encIntMatrix V,
      linVecVal (fun i => D i i)]
    let input := Val.list [ctx,encGroup gs,linFiniteIntVecVal (tmGLQMod D) v,linFiniteIntVecVal (tmGLQMod D) w]
    FunAll P b input (fun out cost => CosetC n out (tmGLAffTrans gs ρ c v w) ∧
      cost ≤ linObjectCallerCost hs hm hc hh hv input.wt) := by
  let refs := tmRiPcsO (gens as) Y
  let ctx := Val.list [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),encIntMatrix V,
    linVecVal (fun i => D i i)]
  let input := Val.list [ctx,encGroup gs,linFiniteIntVecVal (tmGLQMod D) v,linFiniteIntVecVal (tmGLQMod D) w]
  let W := input.wt
  let SB := linObjectCallerSliceBudget W
  let RB := linObjectCallerRecordsBudget hs hm hc hh W
  let AB := linObjectCallerAffineBudget hs hm hc hh hv W
  let C := linObjectCallerSource hs hm hc hh hv W
  let rval := Val.list (gs.map fun a => linObjectAffineRecord (tmGLQMod D) ρ c (linIntoSubgroup (gens gs) a))
  let ain := Val.list [encGroup gs,linVecVal (fun i => D i i),rval,
    linFiniteIntVecVal (tmGLQMod D) v,linFiniteIntVecVal (tmGLQMod D) w]
  have wc : ctx.wt ≤ W := (wt_le_wt_list (by simp [input,W])).le
  have wg : (encGroup gs).wt ≤ W := (wt_le_wt_list (by simp [input,W])).le
  have wv : (linFiniteIntVecVal (tmGLQMod D) v).wt ≤ W := (wt_le_wt_list (by simp [input,W])).le
  have ww : (linFiniteIntVecVal (tmGLQMod D) w).wt ≤ W := (wt_le_wt_list (by simp [input,W])).le
  have worders : (linVecVal (fun i => D i i)).wt ≤ W := by
    have hh : (linVecVal (fun i => D i i)).wt < ctx.wt := wt_le_wt_list (by simp [ctx])
    omega
  have ws : (Val.list ((1 :: gs).map encPerm)).wt ≤ W := by
    have hh : (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt := wt_le_wt_list (by simp [encGroup,encPerms])
    omega
  have hl : gs.length ≤ W := by
    have hh := length_lt_wt_list ((1 :: gs).map encPerm)
    simp only [List.length_map,List.length_cons] at hh
    omega
  have hnl := wt_nat_le gs.length
  have wn1 : (Val.nat 1).wt = 3 := rfl
  have hsarg : (Val.list [.nat 1,.nat gs.length,.list ((1 :: gs).map encPerm)]).wt ≤ 100 * (W + 1) ^ 2 := by
    have hh := wt_list3_le (.nat 1) (.nat gs.length) (.list ((1 :: gs).map encPerm))
    have hp : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by decide) _
    omega
  have hslice : FunDet P (b + 1) (.list [.nat 1,.nat gs.length,.list ((1 :: gs).map encPerm)])
      (.list (gs.map encPerm)) SB := by
    have hr := linSlice_spec h.slice ((1 :: gs).map encPerm) 1 gs.length (by simp; omega)
    have hb := linPolyEnvelope_bound linSliceCost_poly (Nat.zero_le _) hsarg (Nat.zero_le _)
    simpa only [SB,linObjectCallerSliceBudget,List.map_cons,List.drop_succ_cons,List.drop_zero,← List.map_take,List.take_length] using hr.mono hb
  have wraw := hslice.wt_lt.le
  have hrarg : (Val.list [ctx,.list (gs.map encPerm)]).wt ≤ linObjectCallerRecordsArg W := by
    have hh := wt_list2_le ctx (.list (gs.map encPerm))
    have hp : W + SB + 1 ≤ (W + SB + 1) ^ 2 := Nat.le_self_pow (by decide) _
    change _ ≤ 100 * (W + SB + 1) ^ 2
    omega
  have hrecords : FunDet P (b + 4) (.list [ctx,.list (gs.map encPerm)]) rval RB :=
    (linObjectAffineRecords_object_spec hh h.records hjh as ns π hπ Y hok hsol hNA (gens gs) hAH hA hN
      hcomm hal hf hker hy q V D hV hpos E hE ρ c hAct gs (fun a ha => Subgroup.subset_closure ha)).mono
      (linPolyEnvelope_bound (linObjectRecordsCost_poly hs hm hc hh) (Nat.zero_le _) hrarg (Nat.zero_le _))
  have wrec := hrecords.wt_lt.le
  have haarg : ain.wt ≤ linObjectCallerAffineArg hs hm hc hh W := by
    have hh := wt_list_le [encGroup gs,linVecVal (fun i => D i i),rval,
      linFiniteIntVecVal (tmGLQMod D) v,linFiniteIntVecVal (tmGLQMod D) w]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil] at hh
    have hp : W + RB + 1 ≤ (W + RB + 1) ^ 2 := Nat.le_self_pow (by decide) _
    change _ ≤ 100 * (W + RB + 1) ^ 2
    change (Val.list [encGroup gs,linVecVal (fun i => D i i),rval,
      linFiniteIntVecVal (tmGLQMod D) v,linFiniteIntVecVal (tmGLQMod D) w]).wt ≤ _
    omega
  have hdiag : (fun i => ((tmGLQMod D i : ℕ) : ℤ)) = (fun i => D i i) := by
    funext i
    exact Int.toNat_of_nonneg (hpos i).le
  have hencoding : ain = tmGLAffIn gs (tmGLQMod D) ρ c v w := by
    dsimp only [ain,rval]
    rw [linObjectAffineRecords_encoding]
    unfold tmGLAffIn tmGLModZ
    rw [hdiag]
    rfl
  have hmpos : ∀ i, 0 < tmGLQMod D i := by intro i; have hp := hpos i; dsimp only [tmGLQMod]; omega
  have haffine : FunAll P (b + 417) ain (fun out cost => CosetC n out (tmGLAffTrans gs ρ c v w) ∧ cost ≤ AB) := by
    have hr := linAffineTransportAll_spec hm hc hv h.affine gs (tmGLQMod D) ρ c v w hsolB hmpos hprime hcocycle
    rw [← hencoding] at hr
    exact hr.mono fun out cost hout => ⟨hout.1,hout.2.trans
      (linPolyEnvelope_bound (linAffineCallerCost_poly hm hc hv) (Nat.zero_le _) haarg (Nat.zero_le _))⟩
  have hp : W + SB + RB + AB + 1 ≤ (W + SB + RB + AB + 1) ^ 2 := Nat.le_self_pow (by decide) _
  have wC : W ≤ C := by change W ≤ 100 * (W + SB + RB + AB + 1) ^ 2; omega
  have sC : SB ≤ C := by change SB ≤ 100 * (W + SB + RB + AB + 1) ^ 2; omega
  have rC : RB ≤ C := by change RB ≤ 100 * (W + SB + RB + AB + 1) ^ 2; omega
  have aC : AB ≤ C := by change AB ≤ 100 * (W + SB + RB + AB + 1) ^ 2; omega
  have hC : 100 ≤ C := by change 100 ≤ 100 * (W + SB + RB + AB + 1) ^ 2; omega
  exact linObjectAffineCaller_comp h.entry ctx (.nat n) (encPerm (1 : Equiv.Perm (Fin n)))
    (linVecVal (fun i => D i i)) (linFiniteIntVecVal (tmGLQMod D) v) (linFiniteIntVecVal (tmGLQMod D) w)
    rval (gs.map encPerm) (fun out => CosetC n out (tmGLAffTrans gs ρ c v w)) rfl hC wC
    (by simpa only [List.length_map,List.map_cons] using hslice.mono sC)
    (hrecords.mono rC) (haffine.mono fun out cost hout => ⟨hout.1,hout.2.trans aC⟩)

theorem linObjectCaller_uniform (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (hh : HermiteFullRank) (hv : VectorStabilizer) :
    ∃ K D : ℕ, ∀ W, linObjectCallerCost hs hm hc hh hv W ≤ K * (W + 1) ^ D := by
  obtain ⟨K,D,hKD⟩ := linPoly_source_bound (linObjectCallerCost_poly hs hm hc hh hv)
  exact ⟨K,D,fun W => hKD 0 W W (Nat.zero_le _) le_rfl⟩

end GI.Impl
