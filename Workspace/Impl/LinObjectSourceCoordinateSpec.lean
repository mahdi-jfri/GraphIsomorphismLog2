module

public import Workspace.Impl.LinObjectSourceCoordinateCost

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset

set_option maxHeartbeats 600000 in
set_option maxRecDepth 2500 in
theorem linObjectSourceCoordinate_spec {P : Program} {b jsci jder jmem jm n : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership} {hc : ConstructiveMembership}
    (h : linObjectSourceCoordinateAt P b jsci jder jmem jm hs hd hm hc)
    {Q R : Type*} [CommGroup Q] [AddCommGroup R]
    (as ns : List (Equiv.Perm (Fin n))) (π : gens as →* Q) (hπ : Function.Surjective π)
    (Y X : List (TmRiO n)) (hok : TmRecObjOK (Y.length+X.length) (Y++X))
    (hsol : TmRiListNorm (gens as) (Y++X)) (hNA : gens ns ≤ gens as)
    (H : Subgroup (Equiv.Perm (Fin n))) (hAH : gens as ≤ H)
    (hA : GI.Multicoset.Normalizes H (gens as)) (hN : GI.Multicoset.Normalizes H (gens ns))
    (hcomm : ∀ a ∈ gens as, ∀ b ∈ gens as, a*b*a⁻¹*b⁻¹ ∈ gens ns)
    (hal : as.length ≤ n^2) (hfY : Fixes (gens ns) (tmGlMs Y)) (hfX : Fixes (gens ns) (tmGlMs X))
    (hker : ∀ T ∈ pieces (gens as) (tmGlMs Y), π.ker ≤ (Aut (gens as) T).subgroupOf (gens as))
    (g : Equiv.Perm (Fin n)) (hg : g ∈ H)
    (hy : Conf (gens as) (tmGlMs Y) (tmGlMs X ↼ g))
    (q : linObjectIndexedProduct as π Y →+ R)
    (V D : Matrix (Fin (as.length*(tmRiPcsO (gens as) Y).length))
      (Fin (as.length*(tmRiPcsO (gens as) Y).length)) ℤ)
    (hpos : ∀ i,0 < D i i) (E : R ≃+ tmGLVec (tmGLQMod D))
    (hE : ∀ z : Fin (as.length*(tmRiPcsO (gens as) Y).length) → ℤ,
      E (q (linObjectProductMap (fun i => linObjectGroupImage (gens as) π
        (Aut (gens as) (tmGlMs ((tmRiPcsO (gens as) Y).get i)))) (linObjectLiftCoord as π)
      (linObjectUnflatten _ _ z))) = tmGLQMap V D z) :
    let ctx := Val.list [encGroup as,encGroup ns,.list ((tmRiPcsO (gens as) Y).map tmGlObjsVal),
      encIntMatrix V,linVecVal (fun i => D i i)]
    let input := Val.list [ctx,.list ((tmRiPcsO (gens as) X).map tmGlObjsVal),encPerm g]
    FunDet P b input (linFiniteIntVecVal (tmGLQMod D)
      (E (q (linObjectIndexedConfigEquiv as π hπ Y hker ⟨tmGlMs X ↼ g,hy⟩))))
      (linObjectSourceCoordinateCost hs hm hc input.wt) := by
  let refs := tmRiPcsO (gens as) Y
  let srcs := tmRiPcsO (gens as) X
  let d := as.length*refs.length
  let ctx := Val.list [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),encIntMatrix V,linVecVal (fun i => D i i)]
  let input := Val.list [ctx,.list (srcs.map tmGlObjsVal),encPerm g]
  let W := input.wt
  let OB := linObjectSourceCoordinateOffsetBudget hs hm hc W
  let RB := linObjectSourceCoordinateRowBudget hs hm hc W
  let FB := linObjectSourceCoordinateReduceBudget hs hm hc W
  let C := linObjectSourceCoordinateSource hs hm hc W
  let target := E (q (linObjectIndexedConfigEquiv as π hπ Y hker ⟨tmGlMs X ↼ g,hy⟩))
  let Rw := fun out : Val => ∃ w : Fin d → ℤ,out = linVecVal w ∧ tmGLQMap V D w = target ∧ out.wt ≤ OB
  have wc : ctx.wt ≤ W := (wt_le_wt_list (by simp [input,W])).le
  have wa : (encGroup as).wt ≤ W := (wt_le_wt_list (by simp [ctx])).le.trans wc
  have wn : (encGroup ns).wt ≤ W := (wt_le_wt_list (by simp [ctx])).le.trans wc
  have wp : (Val.list (refs.map tmGlObjsVal)).wt ≤ W := (wt_le_wt_list (by simp [ctx])).le.trans wc
  have wV : (encIntMatrix V).wt ≤ W := (wt_le_wt_list (by simp [ctx])).le.trans wc
  have wm : (linVecVal (fun i => D i i)).wt ≤ W := (wt_le_wt_list (by simp [ctx])).le.trans wc
  have ws : (Val.list (srcs.map tmGlObjsVal)).wt ≤ W := (wt_le_wt_list (by simp [input,W])).le
  have wg : (encPerm g).wt ≤ W := (wt_le_wt_list (by simp [input,W])).le
  have hdW : d ≤ W := by
    have hh := length_lt_wt_list ((List.finRange d).map fun i => encInt (D i i))
    simp only [List.length_map,List.length_finRange] at hh
    change d < (linVecVal (fun i => D i i)).wt at hh
    omega
  have wd : (Val.nat d).wt ≤ W+2 := by have hh := wt_nat_le d; omega
  have hoArg : (Val.list [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),.list (srcs.map tmGlObjsVal),encPerm g]).wt ≤
      100*(W+1)^2 := by
    have hh := wt_list4_le (encGroup as) (encGroup ns) (.list (refs.map tmGlObjsVal)) (.list (srcs.map tmGlObjsVal))
    have ht := wt_list_snoc_le [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),.list (srcs.map tmGlObjsVal)] (encPerm g)
    simp only [List.cons_append,List.nil_append] at ht
    have hp : W+1 ≤ (W+1)^2 := Nat.le_self_pow (by decide) _
    omega
  have ho : FunAll P (b+1) (.list [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),.list (srcs.map tmGlObjsVal),encPerm g])
      (fun out cost => Rw out ∧ cost ≤ OB) := by
    refine (linObjectSourceOffsets_spec h.offsets as ns π Y X hok hsol hNA H hAH hA hN hcomm hal hfY hfX g hg hy).wt_lt.mono
      fun out cost hout => ?_
    have hb : cost ≤ OB := hout.1.2.trans (linPolyEnvelope_bound
      (linObjectShiftOffsetsCost_poly hs hm hc) (Nat.zero_le _) hoArg (Nat.zero_le _))
    obtain ⟨w,he,hframe⟩ := linObjectFrame_offsets as π hπ Y hker q V D E hE _ hy hout.1.1
    exact ⟨⟨w,he,hframe,hout.2.le.trans hb⟩,hb⟩
  have hdRow : d ≤ linObjectSourceCoordinateRowArg hs hm hc W := by
    change d ≤ 100*(W+OB+1)^2
    have hp : W+OB+1 ≤ (W+OB+1)^2 := Nat.le_self_pow (by decide) _
    omega
  have hdReduce : d ≤ linObjectSourceCoordinateReduceArg hs hm hc W := by
    change d ≤ 100*(W+RB+1)^2
    have hp : W+RB+1 ≤ (W+RB+1)^2 := Nat.le_self_pow (by decide) _
    omega
  have hr (out : Val) (hout : Rw out) : FunDet P (b+185) (.list [.nat d,out,encIntMatrix V])
      (linObjectEvalRowImage V out) RB := by
    obtain ⟨w,rfl,hw,ww⟩ := hout
    have harg : (Val.list [.nat d,linVecVal w,encIntMatrix V]).wt ≤ linObjectSourceCoordinateRowArg hs hm hc W :=
      linObjectEvalArg3Middle _ _ _ W OB wd ww (by omega)
    have hh := linRowMul_spec h.dense.ints h.dense.row h.dense.column h.dense.dot w V
    rw [linObjectEvalRowImage_vec]
    exact hh.mono (linPolyEnvelope_bound linObjectEvalRowPoly
      hdRow
      harg (Nat.zero_le _))
  have hdiag : (fun i => ((tmGLQMod D i : ℕ) : ℤ)) = (fun i => D i i) := by
    funext i
    exact Int.toNat_of_nonneg (hpos i).le
  have hf (out : Val) (hout : Rw out) : FunDet P (b+213)
      (.list [linObjectEvalRowImage V out,linVecVal (fun i => D i i)])
      (linFiniteIntVecVal (tmGLQMod D) target) FB := by
    obtain ⟨w,rfl,hw,ww⟩ := hout
    have wr : (linVecVal (Matrix.vecMul w V)).wt ≤ RB := by
      simpa only [linObjectEvalRowImage_vec] using (hr (linVecVal w) ⟨w,rfl,hw,ww⟩).wt_lt.le
    have harg : (Val.list [linVecVal (Matrix.vecMul w V),linVecVal (fun i => D i i)]).wt ≤
        linObjectSourceCoordinateReduceArg hs hm hc W := linObjectEvalArg2 _ _ W RB wr (by omega)
    have hh := linFiniteReduce_spec h.reduce (tmGLQMod D) (fun i => by have hp := hpos i; dsimp only [tmGLQMod]; omega)
      (Matrix.vecMul w V)
    rw [hdiag] at hh
    have hb : linFiniteReduceCost (Val.list [linVecVal (Matrix.vecMul w V),linVecVal (fun i => D i i)]).wt d ≤ FB :=
      linPolyEnvelope_bound linFiniteReduceCost_poly
        hdReduce
        harg (Nat.zero_le _)
    have heq : (fun i => ((Matrix.vecMul w V) i : ZMod (tmGLQMod D i))) = target := hw
    simpa only [linObjectEvalRowImage_vec,heq] using hh.mono hb
  have hp : W+OB+RB+FB+1 ≤ (W+OB+RB+FB+1)^2 := Nat.le_self_pow (by decide) _
  have wC : W ≤ C := by change W ≤ 100*(W+OB+RB+FB+1)^2; omega
  have oC : OB ≤ C := by change OB ≤ 100*(W+OB+RB+FB+1)^2; omega
  have rC : RB ≤ C := by change RB ≤ 100*(W+OB+RB+FB+1)^2; omega
  have fC : FB ≤ C := by change FB ≤ 100*(W+OB+RB+FB+1)^2; omega
  have hC : 100 ≤ C := by change 100 ≤ 100*(W+OB+RB+FB+1)^2; omega
  exact linObjectSourceCoordinate_comp h.entry (encGroup as) (encGroup ns) (.list (refs.map tmGlObjsVal))
    (encIntMatrix V) ((List.finRange d).map fun i => encInt (D i i)) (.list (srcs.map tmGlObjsVal)) (encPerm g)
    (linFiniteIntVecVal (tmGLQMod D) target) Rw (linObjectEvalRowImage V) hC wC
    (ho.mono fun out cost hout => ⟨hout.1,hout.2.trans oC⟩)
    (fun out hout => by simpa only [List.length_map,List.length_finRange] using (hr out hout).mono rC)
    (fun out hout => (hf out hout).mono fC)

end GI.Impl
