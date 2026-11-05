module

public import Workspace.Impl.LinObjectMatrixActualCost

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset

set_option maxHeartbeats 300000 in
set_option maxRecDepth 2000 in
theorem linObjectAffineMatrix_object_spec (hh : HermiteFullRank)
    {P : Program} {b jsci jder jmem jm jh n : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership} {hc : ConstructiveMembership}
    (h : linObjectAffineMatrixAt P b jsci jder jmem jm jh hs hd hm hc)
    (hjh : P.prims[jh]? = some (linHermitePrim hh))
    {Q R : Type*} [CommGroup Q] [AddCommGroup R]
    (as ns : List (Equiv.Perm (Fin n))) (π : gens as →* Q) (hπ : Function.Surjective π)
    (Y : List (TmRiO n)) (hok : TmRecObjOK Y.length Y)
    (hsol : TmRiListNorm (gens as) Y) (hNA : gens ns ≤ gens as)
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
    (g : Equiv.Perm (Fin n)) (hg : g ∈ H)
    (L : tmGLVec (tmGLQMod D) →+ tmGLVec (tmGLQMod D)) (c : tmGLVec (tmGLQMod D))
    (hAct : ∀ Z (hZ : Conf (gens as) (tmGlMs Y) Z),
      L (E (q (linObjectIndexedConfigEquiv as π hπ Y hker ⟨Z,hZ⟩))) + c =
        E (q (linObjectIndexedConfigEquiv as π hπ Y hker
          ⟨Z ↼ g⁻¹,(affine_law hA (H.inv_mem hg) (hy _ (H.inv_mem hg)) hZ).2.2⟩))) :
    let refs := tmRiPcsO (gens as) Y
    let ctx := Val.list [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),encIntMatrix V,
      linVecVal (fun i => D i i)]
    let input := Val.list [ctx,encPerm g]
    FunDet P b input (.list [encIntMatrix (tmGLMat (tmGLQMod D) L),linFiniteIntVecVal (tmGLQMod D) c])
      (linObjectMatrixActualCost hs hm hc hh input.wt) := by
  let refs := tmRiPcsO (gens as) Y
  let d := as.length * refs.length
  let m := tmGLQMod D
  let ctx := Val.list [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),encIntMatrix V,
    linVecVal (fun i => D i i)]
  let input := Val.list [ctx,encPerm g]
  let W := input.wt
  let EB := linObjectMatrixEvalBudget hs hm hc hh W
  let C := linObjectMatrixActualSource hs hm hc hh W
  have wc : ctx.wt ≤ W := (wt_le_wt_list (by simp [input,W])).le
  have wg : (encPerm g).wt ≤ W := (wt_le_wt_list (by simp [input,W])).le
  have wm : (linVecVal (fun i => D i i)).wt ≤ W := by
    have hh : (linVecVal (fun i => D i i)).wt < ctx.wt := wt_le_wt_list (by simp [ctx])
    omega
  have hdW : d ≤ W := by
    have hl := length_lt_wt_list ((List.finRange d).map fun i => encInt (D i i))
    simp only [List.length_map,List.length_finRange] at hl
    change d < (linVecVal (fun i => D i i)).wt at hl
    omega
  have hdiag : (fun i => ((m i : ℕ) : ℤ)) = (fun i => D i i) := by
    funext i
    exact Int.toNat_of_nonneg (hpos i).le
  have horders : normReadVal ctx [4] = some (linVecVal (fun i => (m i : ℤ))) := by rw [hdiag]; rfl
  have hmpos : ∀ i, 0 < m i := by intro i; have hp := hpos i; dsimp only [m,tmGLQMod]; omega
  have hp : W + EB + 1 ≤ (W + EB + 1) ^ 2 := Nat.le_self_pow (by decide) _
  have wC : W ≤ C := by change W ≤ 100 * (W + EB + 1) ^ 2; omega
  have eC : EB ≤ C := by change EB ≤ 100 * (W + EB + 1) ^ 2; omega
  have hC : 100 ≤ C := by change 100 ≤ 100 * (W + EB + 1) ^ 2; omega
  have evalSeed (x : Fin d → ℤ) (hx : (linVecVal x).wt ≤ 100 * (W + 1)) :
      FunDet P (b + 51) (.list [ctx,encPerm g,linVecVal x])
        (linFiniteIntVecVal m (L (fun i => (x i : ZMod (m i))) + c)) EB := by
    have harg : (Val.list [ctx,encPerm g,linVecVal x]).wt ≤ linObjectMatrixEvalArg W := by
      have hw := wt_list3_le ctx (encPerm g) (linVecVal x)
      have hp : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by decide) _
      unfold linObjectMatrixEvalArg
      omega
    have hbound : linObjectEvalCost hs hm hc hh (Val.list [ctx,encPerm g,linVecVal x]).wt ≤ EB :=
      linPolyEnvelope_bound (linObjectEvalCost_poly hs hm hc hh) (Nat.zero_le _) harg (Nat.zero_le _)
    have hr := (linObjectAffineEval_spec hh h.eval hjh as ns π hπ Y hok hsol hNA H hAH hA hN
      hcomm hal hf hker hy q V D hV hpos E hE g hg x).mono hbound
    have he := linObjectFrame_actionPoint as π hπ Y hker q V D hV E hE H hA g hg
      (hy _ (H.inv_mem hg)) (fun x => L x + c) hAct x
    simpa only [he] using hr
  have hz : FunDet P (b + 51) (.list [ctx,encPerm g,linVecVal (0 : Fin d → ℤ)])
      (linFiniteIntVecVal m c) C := by
    have hb := (linObjectMatrixSeed_zero d).trans (Nat.mul_le_mul_left 100 (Nat.add_le_add_right hdW 1))
    have hr := (evalSeed 0 hb).mono eC
    rw [linObjectFiniteZero_cast,map_zero,zero_add] at hr
    exact hr

  have hb (j : Fin d) : FunDet P (b + 51) (.list [ctx,encPerm g,linVecVal (Pi.single j (1 : ℤ))])
      (linFiniteIntVecVal m (L (Pi.single j 1) + c)) C := by
    have hw := (linObjectMatrixSeed_basis j).trans (Nat.mul_le_mul_left 100 (Nat.add_le_add_right hdW 1))
    simpa only [linObjectFiniteBasis_cast] using (evalSeed (Pi.single j (1 : ℤ)) hw).mono eC
  exact linObjectAffineMatrix_spec h ctx (encPerm g) m hmpos L c (fun x => L x + c) (fun _ => rfl)
    hC (hdW.trans wC) horders wC hz hb

end GI.Impl
