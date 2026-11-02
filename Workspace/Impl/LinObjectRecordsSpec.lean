import Workspace.Impl.LinObjectAffineRecords

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset

set_option maxHeartbeats 300000 in
set_option maxRecDepth 2000 in
theorem linObjectAffineRecords_object_spec (hh : HermiteFullRank)
    {P : Program} {b jsci jder jmem jm jh n : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership} {hc : ConstructiveMembership}
    (h : linObjectAffineRecordsAt P b jsci jder jmem jm jh hs hd hm hc)
    (hjh : P.prims[jh]? = some (linHermitePrim hh))
    {Q R : Type*} [CommGroup Q] [AddCommGroup R]
    (as ns : List (Equiv.Perm (Fin n))) (π : gens as →* Q) (hπ : Function.Surjective π)
    (Y : List (TmRiO n)) (hok : TmRecObjOK Y.length Y)
    (hsol : IsSolvable (gens as)) (hNA : gens ns ≤ gens as)
    (H : Subgroup (Equiv.Perm (Fin n))) (hAH : gens as ≤ H)
    (hA : GI.Multicoset.Normalizes H (gens as)) (hN : GI.Multicoset.Normalizes H (gens ns))
    (hcomm : ∀ a ∈ gens as, ∀ b ∈ gens as, a * b * a⁻¹ * b⁻¹ ∈ gens ns)
    (hal : as.length ≤ n ^ 2) (hf : Fixes (gens ns) (tmGlMs Y))
    (hker : ∀ T ∈ pieces (gens as) (tmGlMs Y), π.ker ≤ (Aut (gens as) T).subgroupOf (gens as))
    (hy : ∀ g ∈ H, Conf (gens as) (tmGlMs Y) (tmGlMs Y ↼ g))
    (q : linObjectIndexedProduct as π Y →+ R)
    (V D : Matrix (Fin (as.length * (tmRiPcsO (gens as) Y).length))
      (Fin (as.length * (tmRiPcsO (gens as) Y).length)) ℤ)
    (hV : IsUnit V.det) (hpos : ∀ i, 0 < D i i)
    (E : R ≃+ tmGLVec (tmGLQMod D))
    (hE : ∀ z, E (q (linObjectProductMap
      (fun i => linObjectGroupImage (gens as) π (Aut (gens as) (tmGlMs ((tmRiPcsO (gens as) Y).get i))))
      (linObjectLiftCoord as π) (linObjectUnflatten _ _ z))) = tmGLQMap V D z)
    (ρ : H →* (tmGLVec (tmGLQMod D) ≃+ tmGLVec (tmGLQMod D))) (c : H → tmGLVec (tmGLQMod D))
    (hAct : ∀ k : H, ∀ Z (hZ : Conf (gens as) (tmGlMs Y) Z),
      ρ k (E (q (linObjectIndexedConfigEquiv as π hπ Y hker ⟨Z,hZ⟩))) + c k =
        E (q (linObjectIndexedConfigEquiv as π hπ Y hker
          ⟨Z ↼ k.val⁻¹,(affine_law hA (H.inv_mem k.property) (hy _ (H.inv_mem k.property)) hZ).2.2⟩)))
    (gs : List (Equiv.Perm (Fin n))) (hgs : ∀ g ∈ gs, g ∈ H) :
    let refs := tmRiPcsO (gens as) Y
    let ctx := Val.list [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),encIntMatrix V,
      linVecVal (fun i => D i i)]
    let input := Val.list [ctx,.list (gs.map encPerm)]
    FunDet P b input (.list (gs.map fun g => linObjectAffineRecord (tmGLQMod D) ρ c (linIntoSubgroup H g)))
      (linObjectRecordsCost hs hm hc hh input.wt) := by
  let refs := tmRiPcsO (gens as) Y
  let ctx := Val.list [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),encIntMatrix V,
    linVecVal (fun i => D i i)]
  let input := Val.list [ctx,.list (gs.map encPerm)]
  let W := input.wt
  let B := linObjectRecordsItemBudget hs hm hc hh W
  have wctx : ctx.wt ≤ W := (wt_le_wt_list (by simp [input,W])).le
  have wgs : (Val.list (gs.map encPerm)).wt ≤ W := (wt_le_wt_list (by simp [input,W])).le
  have hi (a : Equiv.Perm (Fin n)) (ha : a ∈ gs) :
      FunDet P (b + 3) (.list [ctx,encPerm a]) (linObjectAffineRecord (tmGLQMod D) ρ c (linIntoSubgroup H a)) B := by
    let k := linIntoSubgroup H a
    have hk : k.val = a := linIntoSubgroup_val H a (hgs a ha)
    have wa : (encPerm a).wt ≤ W :=
      (wt_le_wt_list (List.mem_map.mpr ⟨a,ha,rfl⟩)).le.trans wgs
    have harg : (Val.list [ctx,encPerm a]).wt ≤ 100 * (W + 1) ^ 2 := by
      have hw := wt_list2_le ctx (encPerm a)
      have hp : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by decide) _
      omega
    have hr := linObjectAffineItem_object_spec hh h.item hjh as ns π hπ Y hok hsol hNA H hAH hA hN
      hcomm hal hf hker hy q V D hV hpos E hE ρ c hAct k
    rw [hk] at hr
    exact hr.mono
      (linPolyEnvelope_bound (linObjectItemActualCost_poly hs hm hc hh) (Nat.zero_le _) harg (Nat.zero_le _))
  exact linMapEncoded_spec h.map encPerm encPerm_injective
    (fun g => linObjectAffineRecord (tmGLQMod D) ρ c (linIntoSubgroup H g)) ctx gs B hi

theorem linObjectRecords_uniform (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (hh : HermiteFullRank) :
    ∃ K D : ℕ, ∀ W, linObjectRecordsCost hs hm hc hh W ≤ K * (W + 1) ^ D := by
  obtain ⟨K,D,hKD⟩ := linPoly_source_bound (linObjectRecordsCost_poly hs hm hc hh)
  exact ⟨K,D,fun W => hKD 0 W W (Nat.zero_le _) le_rfl⟩

end GI.Impl
