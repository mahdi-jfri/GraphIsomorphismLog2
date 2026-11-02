import Workspace.Impl.LinObjectEvalWeights
import Workspace.Impl.LinObjectOffsetsEval
import Workspace.Impl.LinObjectFrameMath

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset

set_option maxHeartbeats 100000 in
set_option maxRecDepth 2000 in
theorem linObjectAffineEval_spec (hh : HermiteFullRank)
    {P : Program} {b jsci jder jmem jm jh n : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership} {hc : ConstructiveMembership}
    (h : linObjectAffineEvalAt P b jsci jder jmem jm jh hs hd hm hc)
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
    (g : Equiv.Perm (Fin n)) (hg : g ∈ H)
    (x : Fin (as.length * (tmRiPcsO (gens as) Y).length) → ℤ) :
    let refs := tmRiPcsO (gens as) Y
    let z := Matrix.vecMul x V⁻¹
    let targets := linObjectMovedPieces as Y z g⁻¹
    let input := Val.list [.list [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),encIntMatrix V,
      linVecVal (fun i => D i i)],encPerm g,linVecVal x]
    let target := E (q (linObjectIndexedConfigEquiv as π hπ Y hker
      ⟨tmGlMs targets.flatten,linObjectMovedPieces_conf as Y z H hA g⁻¹ (H.inv_mem hg) (hy _ (H.inv_mem hg))⟩))
    FunDet P b input (linFiniteIntVecVal (tmGLQMod D) target)
      (linObjectEvalCost hs hm hc hh input.wt) := by
  let refs := tmRiPcsO (gens as) Y
  let d := as.length * refs.length
  let z := Matrix.vecMul x V⁻¹
  let targets := linObjectMovedPieces as Y z g⁻¹
  let input := Val.list [.list [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),encIntMatrix V,
    linVecVal (fun i => D i i)],encPerm g,linVecVal x]
  let W := input.wt
  let C := linObjectEvalStageBound hs hm hc hh W
  let UB := linObjectEvalLiftBudget hh W
  let BB := linObjectEvalBuildBudget hh W
  let IB := linObjectEvalInvBudget W
  let MB := linObjectEvalMoveBudget hh W
  let OB := linObjectEvalOffsetsBudget hs hm hc hh W
  let RB := linObjectEvalRowBudget hs hm hc hh W
  let FB := linObjectEvalReduceBudget hs hm hc hh W
  let SB := linObjectEvalShiftBudget W
  obtain ⟨hC,wC,sC,uC,bC,iC,mC,oC,rC,fC⟩ := linObjectEvalStage_bounds hs hm hc hh W
  have wctx : (Val.list [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),encIntMatrix V,
      linVecVal (fun i => D i i)]).wt < W := wt_le_wt_list (by simp [W,input])
  have wa : (encGroup as).wt ≤ W :=
    (wt_le_wt_list (by simp : encGroup as ∈ [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),
      encIntMatrix V,linVecVal (fun i => D i i)])).le.trans wctx.le
  have wn : (encGroup ns).wt ≤ W :=
    (wt_le_wt_list (by simp : encGroup ns ∈ [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),
      encIntMatrix V,linVecVal (fun i => D i i)])).le.trans wctx.le
  have wr : (Val.list (refs.map tmGlObjsVal)).wt ≤ W :=
    (wt_le_wt_list (by simp : Val.list (refs.map tmGlObjsVal) ∈ [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),
      encIntMatrix V,linVecVal (fun i => D i i)])).le.trans wctx.le
  have wv : (encIntMatrix V).wt ≤ W :=
    (wt_le_wt_list (by simp : encIntMatrix V ∈ [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),
      encIntMatrix V,linVecVal (fun i => D i i)])).le.trans wctx.le
  have wm : (linVecVal (fun i => D i i)).wt ≤ W :=
    (wt_le_wt_list (by simp : linVecVal (fun i => D i i) ∈ [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),
      encIntMatrix V,linVecVal (fun i => D i i)])).le.trans wctx.le
  have wx : (linVecVal x).wt ≤ W := (wt_le_wt_list (by simp [W,input])).le
  have hn : n ≤ W := by
    have ha := S_le_wt_encGroup as
    have hp : n + 1 ≤ (as.length + 2) * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hdW : d ≤ W := by
    have hl := length_lt_wt_list ((List.finRange d).map fun i => encInt (D i i))
    simp only [List.length_map,List.length_finRange] at hl
    change d < (linVecVal (fun i => D i i)).wt at hl
    omega
  have wd : (Val.nat d).wt ≤ W + 2 := (wt_nat_le d).trans (by omega)
  have hyl : Y.length ≤ W := by
    have hr := linObjectPieces_wt refs
    rw [linObjectReference_length] at hr
    omega
  have hokRi : TmRiOK (2 * Y.length) Y :=
    fun o ho => ⟨(hok o ho).1,(hok o ho).2.1.le,(hok o ho).2.2⟩
  have hsCost : tmRiMapShC n (2 * Y.length) Y.length ≤ SB :=
    linPolyEnvelope_bound linObjectEvalShiftPoly (hn.trans (by omega)) (by omega) (by omega)
  have hlArg : (Val.list [.nat d,encIntMatrix V,linVecVal x]).wt ≤ linObjectEvalLiftArg W := by
    have hw := wt_list3_le (.nat d) (encIntMatrix V) (linVecVal x)
    have hp : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by decide) _
    unfold linObjectEvalLiftArg
    omega
  have hl : FunDet P (b + 1) (.list [.nat d,encIntMatrix V,linVecVal x]) (linVecVal z) UB :=
    (linUnimodular_spec hh h.lift hjh V hV x).mono
      (fun out cost hout => ⟨hout.1,hout.2.trans
        (linPolyEnvelope_bound (linUnimodularCost_poly hh) (Nat.zero_le _) hlArg (Nat.zero_le _))⟩)
  have wz : (linVecVal z).wt ≤ UB := hl.wt_lt.le
  have hbArg : (Val.list [encGroup as,.list (refs.map tmGlObjsVal),linVecVal z]).wt ≤
      linObjectEvalBuildArg hh W := linObjectEvalArg3 _ _ _ W UB (by omega) (by omega) wz
  have hb : FunDet P (b + 61) (.list [encGroup as,.list (refs.map tmGlObjsVal),linVecVal z])
      (.list ((linObjectWordPieces as Y z).map tmGlObjsVal)) BB :=
    (linObjectAffineEval_build_spec h as Y hokRi z).mono
      (linPolyEnvelope_bound linObjectBasisConfigCost_poly (Nat.zero_le _) (by
        exact hbArg.trans (by unfold linObjectEvalBuildArg; omega)) (by
        exact hsCost.trans (by omega)))
  have wb := hb.wt_lt.le
  have hi : FunDet P (b + 102) (encPerm g) (encPerm g⁻¹) IB :=
    (inv_spec h.inv g).mono (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 4))
  have wi := hi.wt_lt.le
  have hmArg : (Val.list [encPerm g⁻¹,.list ((linObjectWordPieces as Y z).map tmGlObjsVal)]).wt ≤
      linObjectEvalMoveArg hh W := by
    have hw := wt_list2_le (encPerm g⁻¹) (.list ((linObjectWordPieces as Y z).map tmGlObjsVal))
    have hp : W + IB + BB + 1 ≤ (W + IB + BB + 1) ^ 2 := Nat.le_self_pow (by decide) _
    change _ ≤ 100 * (W + IB + BB + 1) ^ 2
    omega
  have hmv : FunDet P (b + 114) (.list [encPerm g⁻¹,.list ((linObjectWordPieces as Y z).map tmGlObjsVal)])
      (.list (targets.map tmGlObjsVal)) MB :=
    (linObjectAffineEval_move_spec h as Y hokRi z g⁻¹).mono
      (linPolyEnvelope_bound linObjectEvalMapPoly (Nat.zero_le _) (hmArg.trans (by omega)) (hsCost.trans (by omega)))
  have wmv := hmv.wt_lt.le
  have hoArg : (Val.list [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),.list (targets.map tmGlObjsVal)]).wt ≤
      linObjectEvalOffsetsArg hh W := linObjectEvalArg4 _ _ _ _ W MB (by omega) (by omega) (by omega) wmv
  have hZ := linObjectMovedPieces_conf as Y z H hA g⁻¹ (H.inv_mem hg) (hy _ (H.inv_mem hg))
  let target := E (q (linObjectIndexedConfigEquiv as π hπ Y hker ⟨tmGlMs targets.flatten,hZ⟩))
  let Rw : Val → Prop := fun out => ∃ w, out = linVecVal w ∧ tmGLQMap V D w = target ∧ out.wt ≤ OB
  have ho : FunAll P (b + 117) (.list [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),.list (targets.map tmGlObjsVal)])
      (fun out cost => Rw out ∧ cost ≤ OB) :=
    (linObjectAffineEval_offsets_spec h as ns π Y hok hsol hNA H hAH hA hN hcomm hal hf z g⁻¹
      (H.inv_mem hg) (hy _ (H.inv_mem hg))).wt_lt.mono fun out cost hout => by
        have hbnd : cost ≤ OB := hout.1.2.trans
          (linPolyEnvelope_bound (linObjectOffsetsCost_poly hs hm hc) (Nat.zero_le _) hoArg (Nat.zero_le _))
        obtain ⟨w,he,hframe⟩ := linObjectFrame_offsets as π hπ Y hker q V D E hE _ hZ hout.1.1
        exact ⟨⟨w,he,hframe,hout.2.le.trans hbnd⟩,hbnd⟩
  have hrows (out : Val) (hout : Rw out) :
      FunDet P (b + 297) (.list [.nat d,out,encIntMatrix V]) (linObjectEvalRowImage V out) RB := by
    obtain ⟨w,rfl,hw,ww⟩ := hout
    have harg : (Val.list [.nat d,linVecVal w,encIntMatrix V]).wt ≤ linObjectEvalRowArg hs hm hc hh W :=
      linObjectEvalArg3Middle _ _ _ W OB wd ww (by omega)
    have hraw := linRowMul_spec h.dense.ints h.dense.row h.dense.column h.dense.dot w V
    simpa only [linObjectEvalRowImage_vec] using hraw.mono
      (linPolyEnvelope_bound linObjectEvalRowPoly (hdW.trans (by omega)) (harg.trans (by omega)) (Nat.zero_le _))
  have hdiag : (fun i => ((tmGLQMod D i : ℕ) : ℤ)) = (fun i => D i i) := by
    funext i
    exact Int.toNat_of_nonneg (hpos i).le
  have hreduces (out : Val) (hout : Rw out) :
      FunDet P (b + 325) (.list [linObjectEvalRowImage V out,linVecVal (fun i => D i i)])
        (linFiniteIntVecVal (tmGLQMod D) target) FB := by
    obtain ⟨w,rfl,hw,ww⟩ := hout
    have hrowwt : (linVecVal (Matrix.vecMul w V)).wt ≤ RB := by
      simpa only [linObjectEvalRowImage_vec] using (hrows (linVecVal w) ⟨w,rfl,hw,ww⟩).wt_lt.le
    have harg : (Val.list [linVecVal (Matrix.vecMul w V),linVecVal (fun i => D i i)]).wt ≤
        linObjectEvalReduceArg hs hm hc hh W := linObjectEvalArg2 _ _ W RB hrowwt (by omega)
    have hraw := linFiniteReduce_spec h.reduce (tmGLQMod D) (fun i => by have hp := hpos i; dsimp only [tmGLQMod]; omega) (Matrix.vecMul w V)
    rw [hdiag] at hraw
    have hcst : linFiniteReduceCost (Val.list [linVecVal (Matrix.vecMul w V),
        linVecVal (fun i => D i i)]).wt d ≤ FB := linPolyEnvelope_bound linFiniteReduceCost_poly (hdW.trans (by omega))
      (harg.trans (by omega)) (Nat.zero_le _)
    have heq : (fun i => ((Matrix.vecMul w V) i : ZMod (tmGLQMod D i))) = target := hw
    simpa only [linObjectEvalRowImage_vec,heq] using hraw.mono hcst
  have hfinal := linObjectAffineEval_comp h.entry (encGroup as) (encGroup ns)
    (.list (refs.map tmGlObjsVal)) (encIntMatrix V) ((List.finRange d).map fun i => encInt (D i i))
    (encPerm g) (encPerm g⁻¹) (linVecVal x) (linVecVal z)
    (.list ((linObjectWordPieces as Y z).map tmGlObjsVal)) (.list (targets.map tmGlObjsVal))
    (linFiniteIntVecVal (tmGLQMod D) target) Rw (linObjectEvalRowImage V) hC wC
    (by simpa only [List.length_map,List.length_finRange] using hl.mono uC)
    (hb.mono bC) (hi.mono iC) (hmv.mono mC)
    (ho.mono fun out cost hout => ⟨hout.1,hout.2.trans oC⟩)
    (fun out hout => by simpa only [List.length_map,List.length_finRange] using (hrows out hout).mono rC)
    (fun out hout => (hreduces out hout).mono fC)
  exact hfinal

theorem linObjectEval_uniform (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (hh : HermiteFullRank) :
    ∃ K D : ℕ, ∀ W, linObjectEvalCost hs hm hc hh W ≤ K * (W + 1) ^ D := by
  obtain ⟨K,D,hKD⟩ := linPoly_source_bound (linObjectEvalCost_poly hs hm hc hh)
  exact ⟨K,D,fun W => hKD 0 W W (Nat.zero_le _) le_rfl⟩

end GI.Impl
