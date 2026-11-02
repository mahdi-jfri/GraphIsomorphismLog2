import Workspace.Impl.LinObjectItemCost

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset

set_option maxHeartbeats 300000 in
set_option maxRecDepth 2000 in
theorem linObjectAffineItem_object_spec (hh : HermiteFullRank)
    {P : Program} {b jsci jder jmem jm jh n : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership} {hc : ConstructiveMembership}
    (h : linObjectAffineItemAt P b jsci jder jmem jm jh hs hd hm hc)
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
    (g : H) :
    let refs := tmRiPcsO (gens as) Y
    let ctx := Val.list [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),encIntMatrix V,
      linVecVal (fun i => D i i)]
    let input := Val.list [ctx,encPerm g.val]
    FunDet P b input (linObjectAffineRecord (tmGLQMod D) ρ c g)
      (linObjectItemActualCost hs hm hc hh input.wt) := by
  let refs := tmRiPcsO (gens as) Y
  let ctx := Val.list [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),encIntMatrix V,
    linVecVal (fun i => D i i)]
  let input := Val.list [ctx,encPerm g.val]
  let W := input.wt
  let IB := linObjectItemInvBudget W
  let MB := linObjectItemMatrixBudget hs hm hc hh W
  let C := linObjectItemSource hs hm hc hh W
  have wc : ctx.wt ≤ W := (wt_le_wt_list (by simp [input,W])).le
  have wg : (encPerm g.val).wt ≤ W := (wt_le_wt_list (by simp [input,W])).le
  have hn : n ≤ W := by
    have hh := length_lt_wt_list ((List.finRange n).map fun i => Val.nat (g.val i).val)
    simp only [List.length_map,List.length_finRange] at hh
    change n < (encPerm g.val).wt at hh
    omega
  have hi : FunDet P (b + 398) (encPerm g.val) (encPerm g.val⁻¹) IB :=
    (inv_spec h.inv g.val).mono (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 4))
  have wi := hi.wt_lt.le
  have hpArg : W + IB + 1 ≤ (W + IB + 1) ^ 2 := Nat.le_self_pow (by decide) _
  have harg : (Val.list [ctx,encPerm g.val⁻¹]).wt ≤ linObjectItemMatrixArg W := by
    have hw := wt_list2_le ctx (encPerm g.val⁻¹)
    change _ ≤ 100 * (W + IB + 1) ^ 2
    omega
  have hwArg : W ≤ linObjectItemMatrixArg W := by change W ≤ 100 * (W + IB + 1) ^ 2; omega
  have hmat : FunDet P (b + 1) (.list [ctx,encPerm g.val])
      (.list [encIntMatrix (tmGLMat (tmGLQMod D) (ρ g).toAddMonoidHom),linFiniteIntVecVal (tmGLQMod D) (c g)]) MB :=
    (linObjectAffineMatrix_object_spec hh h.matrix hjh as ns π hπ Y hok hsol hNA H hAH hA hN hcomm hal hf hker
      hy q V D hV hpos E hE g.val g.property (ρ g).toAddMonoidHom (c g) (hAct g)).mono
        (linPolyEnvelope_bound (linObjectMatrixActualCost_poly hs hm hc hh) (Nat.zero_le _) hwArg (Nat.zero_le _))
  have hmi : FunDet P (b + 1) (.list [ctx,encPerm g.val⁻¹])
      (.list [encIntMatrix (tmGLMat (tmGLQMod D) (ρ g⁻¹).toAddMonoidHom),linFiniteIntVecVal (tmGLQMod D) (c g⁻¹)]) MB :=
    (linObjectAffineMatrix_object_spec hh h.matrix hjh as ns π hπ Y hok hsol hNA H hAH hA hN hcomm hal hf hker
      hy q V D hV hpos E hE g.val⁻¹ (H.inv_mem g.property) (ρ g⁻¹).toAddMonoidHom (c g⁻¹) (hAct g⁻¹)).mono
        (linPolyEnvelope_bound (linObjectMatrixActualCost_poly hs hm hc hh) (Nat.zero_le _) harg (Nat.zero_le _))
  have hp : W + IB + MB + 1 ≤ (W + IB + MB + 1) ^ 2 := Nat.le_self_pow (by decide) _
  have wC : W ≤ C := by change W ≤ 100 * (W + IB + MB + 1) ^ 2; omega
  have iC : IB ≤ C := by change IB ≤ 100 * (W + IB + MB + 1) ^ 2; omega
  have mC : MB ≤ C := by change MB ≤ 100 * (W + IB + MB + 1) ^ 2; omega
  have hC : 100 ≤ C := by change 100 ≤ 100 * (W + IB + MB + 1) ^ 2; omega
  exact linObjectAffineItem_comp h.entry ctx (encPerm g.val) (encPerm g.val⁻¹)
    (encIntMatrix (tmGLMat (tmGLQMod D) (ρ g).toAddMonoidHom)) (linFiniteIntVecVal (tmGLQMod D) (c g))
    (encIntMatrix (tmGLMat (tmGLQMod D) (ρ g⁻¹).toAddMonoidHom)) (linFiniteIntVecVal (tmGLQMod D) (c g⁻¹))
    hC wC (hmat.mono mC) (hi.mono iC) (hmi.mono mC)

end GI.Impl
