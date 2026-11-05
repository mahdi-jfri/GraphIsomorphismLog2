module

public import Workspace.Impl.LinAffineCallerPrep

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang
set_option maxRecDepth 24000

noncomputable def linAffineCallerPrepCost (hmem : Membership) (hm : ConstructiveMembership) (W : ℕ) : ℕ :=
  1000000 * (W + linAffineCallerContextBudget W + linAffineCallerDiffBudget W +
    linAffineCallerReduceBudget hmem W + linAffineCallerTailBudget hmem W +
    linAffineCallerRestrictBudget hmem hm W + 1)

theorem linFinitePoint_snoc {d : ℕ} (m : Fin d → ℕ) (x : linFiniteVec m) :
    linFinitePointVal m x =
      .list (((List.finRange d).map fun i => encInt ((x i).val : ℤ)) ++ [encInt 1]) :=
  congrArg Val.list (linExtend_value encInt (fun i => ((x i).val : ℤ)) 1)

set_option maxHeartbeats 2000000 in
theorem linAffineCallerPrepare_spec (hmem : Membership) (hm : ConstructiveMembership) (hv : VectorStabilizer)
    {P : Program} {b jmem jm jv n d : ℕ} (hat : linAffineTransportAllAt P b jmem jm jv hmem hm hv)
    (gs : List (Equiv.Perm (Fin n))) (hgs : gs ≠ []) (m : Fin d → ℕ) (hmpos : ∀ i, 0 < m i)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m)
    (hc : ∀ g k, c (g * k) = ρ g (c k) + c g) (v w : linFiniteVec m) :
    let kept := keepList gs
    let hle : gens kept ≤ gens gs := (gens_keepList gs).le
    let a := tmGLAffIn gs m ρ c v w
    let out := linMixedLoopInputVal kept m (ρ.comp (Subgroup.inclusion hle))
      (linFiniteRecenter ρ c w ∘ Subgroup.inclusion hle) (v - w) 1
    FunDet P (b + 1010) a out (linAffineCallerPrepCost hmem hm a.wt) ∧
      out.wt ≤ linAffineCallerLoopArg hmem hm a.wt := by
  rw [linTmGLAffIn_eq]
  let kept := keepList gs
  let hle : gens kept ≤ gens gs := (gens_keepList gs).le
  let c' := linFiniteRecenter ρ c w
  let orders := linVecVal (fun i => (m i : ℤ))
  let oldraw := Val.list ((linActionGens gs).map (linPlainAffineVal m ρ c))
  let vv := linVecVal (fun i => ((v i).val : ℤ))
  let wv := linVecVal (fun i => ((w i).val : ℤ))
  let a := Val.list [encGroup gs, orders, oldraw, vv, wv]
  let W := a.wt
  let ctx := linActionContext gs m ρ c'
  let diff := linFiniteIntVecVal m (v - w)
  let reduced := encGroup kept
  let raw := Val.list (kept.map encPerm)
  let nextCtx := linActionContext kept m (ρ.comp (Subgroup.inclusion hle)) (c' ∘ Subgroup.inclusion hle)
  let point := linFinitePointVal m (v - w)
  let out := linMixedLoopInputVal kept m (ρ.comp (Subgroup.inclusion hle))
    (c' ∘ Subgroup.inclusion hle) (v - w) 1
  have hbounds := linAffineCaller_source_bounds gs m ρ c v w
  rw [linTmGLAffIn_eq] at hbounds
  obtain ⟨hn0, hd0, hlen0, wo0⟩ := hbounds
  have hn : n ≤ W := hn0
  have hd : d ≤ W := hd0
  have hlen : gs.length ≤ W := hlen0
  have wo : orders.wt < W := wo0
  have wg : (encGroup gs).wt < W := wt_le_wt_list (by simp [a, W])
  have wv0 : vv.wt < W := wt_le_wt_list (by simp [a, W])
  have ww : wv.wt < W := wt_le_wt_list (by simp [a, W])
  have hc0 := linAffineCallerContext_spec hat.context gs hgs m hmpos ρ c hc v w
  rw [linTmGLAffIn_eq] at hc0
  have wctx : ctx.wt ≤ linAffineCallerContextBudget W := hc0.wt_lt.le
  have hdiff := linAffineCallerDifference_spec hat.difference gs m hmpos ρ c v w
  rw [linTmGLAffIn_eq] at hdiff
  have wdiff : diff.wt ≤ linAffineCallerDiffBudget W := hdiff.wt_lt.le
  have hred := (reduce_spec hmem hat.reduce hat.member gs).mono (linAffineCallerReduce_bound hmem hn hlen)
  have wred : reduced.wt ≤ linAffineCallerReduceBudget hmem W := hred.wt_lt.le
  have wkfull : (Val.list ((1 :: kept).map encPerm)).wt < reduced.wt :=
    wt_le_wt_list (by simp [reduced, encGroup])
  have wraw : raw.wt ≤ (Val.list ((1 :: kept).map encPerm)).wt :=
    wt_list_sublist (List.sublist_cons_self _ _)
  have hklen : kept.length ≤ W ^ 2 := (length_keepList_le gs).trans (Nat.pow_le_pow_left hn 2)
  have htail := (GI.Lang.tail_spec hat.tail (encPerm (1 : Equiv.Perm (Fin n))) (kept.map encPerm)).mono (show
    loopModK * ((kept.map encPerm).length + 1) *
      (3 * (Val.list (encPerm (1 : Equiv.Perm (Fin n)) :: kept.map encPerm)).wt + 1) ≤
      linAffineCallerTailBudget hmem W by
    have hh : (Val.list (encPerm (1 : Equiv.Perm (Fin n)) :: kept.map encPerm)).wt ≤
        linAffineCallerReduceBudget hmem W := by simpa only [List.map_cons] using wkfull.le.trans wred
    unfold linAffineCallerTailBudget
    simp only [List.length_map]
    gcongr)
  have wrarg : (Val.list [ctx, raw]).wt ≤ linAffineCallerRestrictArg hmem W := by
    have hh := wt_list2_le ctx raw
    unfold linAffineCallerRestrictArg
    omega
  have hrebase := (linAffineRestrict_spec hm hat.restrict gs kept hle m hmpos ρ c'
    (linFiniteRecenter_cocycle ρ c hc w)).mono (linAffineRestrictCost_mono hm wrarg)
  have wnctx : nextCtx.wt ≤ linAffineCallerRestrictBudget hmem hm W := hrebase.wt_lt.le
  have woldfull : (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt := wt_le_wt_list (by simp [encGroup])
  have wid : (encPerm (1 : Equiv.Perm (Fin n))).wt < (Val.list ((1 :: gs).map encPerm)).wt :=
    wt_le_wt_list (by simp)
  have wpoint : point.wt ≤ linAffineCallerDiffBudget W + 44 := by
    have hh := wt_list_snoc_le ((List.finRange d).map fun i => encInt (((v - w) i).val : ℤ)) (encInt 1)
    have h1 : (encInt 1).wt = 21 := rfl
    dsimp only [point]
    rw [linFinitePoint_snoc]
    change (Val.list ((List.finRange d).map fun i => encInt (((v - w) i).val : ℤ))).wt ≤ _ at wdiff
    omega
  have wout : out.wt ≤ linAffineCallerLoopArg hmem hm W := by
    have hh := wt_list4_le nextCtx point (encPerm (1 : Equiv.Perm (Fin n))) orders
    change (Val.list [nextCtx, point, encPerm (1 : Equiv.Perm (Fin n)), orders]).wt ≤ _
    unfold linAffineCallerLoopArg
    omega
  have darg (rest : List Val) (j : ℕ) {value : Val}
      (hj : ([encGroup gs, orders, oldraw, vv, wv] : List Val)[j]? = some value) :=
    Det.arg' (P := P) (vs := [encGroup gs, orders, oldraw, vv, wv]) (rest := rest) (j := j) hj
  have dc := Det.call (Det.var' (P := P) (env := [a]) (i := 0) rfl) hc0
  have dd := Det.call (Det.mk3 (darg [ctx] 1 rfl) (darg [ctx] 3 rfl) (darg [ctx] 4 rfl)) hdiff
  have dr := Det.call (darg [ctx, diff] 0 rfl) hred
  have dt := Det.call (Det.get' (Det.var' (P := P) (env := [a, ctx, diff, reduced]) (i := 3) rfl) (Det.nat 1) rfl) htail
  have dre := Det.call (Det.mk2 (Det.var' (P := P) (env := [a, ctx, diff, reduced, raw]) (i := 1) rfl)
    (Det.var' (P := P) (env := [a, ctx, diff, reduced, raw]) (i := 4) rfl)) hrebase
  have done : Det P [a, ctx, diff, reduced, raw, nextCtx] linIntOneE (encInt 1) 100 :=
    (Det.mk2 (Det.nat 0) (Det.mk1 (Det.nat 1))).mono (by decide)
  have dp := Det.snoc (Det.var' (P := P) (env := [a, ctx, diff, reduced, raw, nextCtx]) (i := 2) rfl) done
  rw [← linFinitePoint_snoc m (v - w)] at dp
  have did := Det.get' (Det.get' (darg [ctx, diff, reduced, raw, nextCtx] 0 rfl) (Det.nat 1) rfl) (Det.nat 0) rfl
  have dout := Det.snoc (Det.mk3
    (Det.var' (P := P) (env := [a, ctx, diff, reduced, raw, nextCtx]) (i := 5) rfl) dp did)
    (darg [ctx, diff, reduced, raw, nextCtx] 1 rfl)
  refine ⟨?_, wout⟩
  apply FunDet.intro hat.prepare
  refine (Det.letE dc (Det.letE dd (Det.letE dr (Det.letE dt (Det.letE dre dout))))).mono ?_
  have wdarg := wt_list3_le orders vv wv
  have wrbarg := wt_list2_le ctx raw
  have wout3 := wt_list3_le nextCtx point (encPerm (1 : Equiv.Perm (Fin n)))
  have wout4 := wt_list_snoc_le [nextCtx, point, encPerm (1 : Equiv.Perm (Fin n))] orders
  change _ ≤ linAffineCallerPrepCost hmem hm W
  unfold linAffineCallerPrepCost
  dsimp only [W, a, ctx, diff, reduced, raw, nextCtx, point, out, orders, oldraw, vv, wv,
    linAffineCallerContextBudget, linAffineCallerDiffBudget, linAffineCallerReduceBudget,
    linAffineCallerTailBudget, linAffineCallerRestrictBudget, encGroup, encPerms, c', kept,
    linMixedLoopInputVal, linFiniteIntVecVal, linVecVal] at *
  simp only [List.map_cons, List.cons_append, List.nil_append] at *
  omega

end GI.Impl
