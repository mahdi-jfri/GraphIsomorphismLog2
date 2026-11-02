import Workspace.Impl.LinPrimePassOut

namespace GI.Impl
open GI.Cited GI.Lang
set_option maxRecDepth 24000

def linPrimePassTailF (tail item point restrict compose : ℕ) : Expr :=
  .letE (.call tail (.get (.get (.get (.var 2) (.nat 0)) (.nat 0)) (.nat 1)))
    (.letE (.call item (mk2 (arg 0) (.get (.var 2) (.nat 2))))
      (.letE (.call point (mk2 (.var 4) (arg 1)))
        (.letE (.call restrict (mk2 (arg 0) (.var 3)))
          (.letE (.call compose (mk2 (.get (.var 2) (.nat 2)) (arg 2)))
            (mk3 (.var 6) (.var 5) (.var 7))))))

def linPrimePassTailBudget (W : ℕ) : ℕ := loopModK * (W + 1) * (3 * W + 1)
noncomputable def linPrimePassSuccessCost (hm : ConstructiveMembership) (W : ℕ) : ℕ :=
  1000 * (W + linPrimePassTailBudget W + linPrimarySuccessCost hm W + 1)

set_option maxHeartbeats 1500000 in
theorem linPrimePass_success_spec (hm : ConstructiveMembership) (hv : VectorStabilizer)
    {P : Program} {b jm jv n d : ℕ} (hat : linPrimePassAt P b jm jv hm hv)
    (gs ks : List (Equiv.Perm (Fin n))) (hle : gens ks ≤ gens gs)
    (m : Fin d → ℕ) (hmpos : ∀ i, 0 < m i)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m)
    (hc : ∀ g k, c (g * k) = ρ g (c k) + c g)
    (g : gens gs) (x : linFiniteVec m) (acc : Equiv.Perm (Fin n)) (p : ℕ)
    (prep table ident projectedPoint : Val) :
    let a := linPrimePrepareInputVal gs m ρ c x acc p
    let phase := Val.list [.list [encGroup ks, table, ident], projectedPoint, encPerm g.val]
    Det P [a, prep, phase] (linPrimePassTailF (b + 525) (b + 528) (b + 595) (b + 642) (b + 720))
      (.list [linActionContext ks m (ρ.comp (Subgroup.inclusion hle)) (c ∘ Subgroup.inclusion hle),
        linFinitePointVal m (linFiniteEval ρ c g x), encPerm (g.val * acc)])
      (linPrimePassSuccessCost hm (a.wt + prep.wt + phase.wt)) := by
  let ctx := linActionContext gs m ρ c
  let point := linFinitePointVal m x
  let a := linPrimePrepareInputVal gs m ρ c x acc p
  let raw := Val.list (ks.map encPerm)
  let phase := Val.list [.list [encGroup ks, table, ident], projectedPoint, encPerm g.val]
  let W := a.wt + prep.wt + phase.wt
  let record := linFiniteAffineVal m ρ c g
  let nextPoint := linFinitePointVal m (linFiniteEval ρ c g x)
  let nextCtx := linActionContext ks m (ρ.comp (Subgroup.inclusion hle)) (c ∘ Subgroup.inclusion hle)
  let nextAcc := encPerm (g.val * acc)
  have wa : a.wt ≤ W := by omega
  have wz : prep.wt ≤ W := by omega
  have wphase : phase.wt ≤ W := by omega
  have wctx : ctx.wt < a.wt := wt_le_wt_list (by simp [a, ctx, linPrimePrepareInputVal])
  have wpt : point.wt < a.wt := wt_le_wt_list (by simp [a, point, linPrimePrepareInputVal])
  have wacc : (encPerm acc).wt < a.wt := wt_le_wt_list (by simp [a, linPrimePrepareInputVal])
  have wg : (encPerm g.val).wt < phase.wt := wt_le_wt_list (by simp [phase])
  have wkctx : (Val.list [encGroup ks, table, ident]).wt < phase.wt := wt_le_wt_list (by simp [phase])
  have wks : (encGroup ks).wt < (Val.list [encGroup ks, table, ident]).wt := wt_le_wt_list (by simp)
  have wlist : (Val.list ((1 :: ks).map encPerm)).wt < (encGroup ks).wt := wt_le_wt_list (by simp [encGroup])
  have wr : raw.wt ≤ (Val.list ((1 :: ks).map encPerm)).wt :=
    wt_list_sublist (List.sublist_cons_self _ _)
  have wl : ks.length ≤ W := by
    have hh := length_lt_wt_list ((1 :: ks).map encPerm)
    simp only [List.length_map, List.length_cons] at hh
    omega
  have wtailin : (Val.list (encPerm (1 : Equiv.Perm (Fin n)) :: ks.map encPerm)).wt ≤ W := by
    simpa only [List.map_cons] using wlist.le.trans (wks.le.trans (wkctx.le.trans wphase))
  have wksfull : (Val.list [.nat n, .list ((1 :: ks).map encPerm)]).wt ≤ W :=
    wks.le.trans (wkctx.le.trans wphase)
  have wrawfull : (Val.list (ks.map encPerm)).wt ≤ W :=
    wr.trans (wlist.le.trans (wks.le.trans (wkctx.le.trans wphase)))
  have htail := (GI.Lang.tail_spec hat.tail (encPerm (1 : Equiv.Perm (Fin n))) (ks.map encPerm)).mono (show
    loopModK * ((ks.map encPerm).length + 1) * (3 * (Val.list (encPerm (1 : Equiv.Perm (Fin n)) :: ks.map encPerm)).wt + 1) ≤
      linPrimePassTailBudget W by
    unfold linPrimePassTailBudget
    simp only [List.length_map]
    gcongr <;> omega)
  have wgs : (encGroup gs).wt < ctx.wt := wt_le_wt_list (by simp [ctx, linActionContext])
  have hn : n ≤ W := by
    have hh := S_le_wt_encGroup gs
    have hh' : n + 1 ≤ (gs.length + 2) * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have wiarg : (Val.list [ctx, encPerm g.val]).wt ≤ 100 * (W + 1) := by
    have hh := wt_list2_le ctx (encPerm g.val)
    omega
  have hi := (linActionItem_spec hm hat.item gs m hmpos ρ c hc g).mono (linActionItemCost_mono hm wiarg)
  change FunDet P (b + 528) (.list [ctx, encPerm g.val]) record (linPrimarySuccessItemBudget hm W) at hi
  have wrecord := hi.wt_lt.le
  have wparg : (Val.list [record, point]).wt ≤ linPrimarySuccessPointArg hm W := by
    have hh := wt_list2_le record point
    unfold linPrimarySuccessPointArg
    omega
  have hp : FunDet P (b + 595) (.list [record, point]) nextPoint (linPrimarySuccessPointBudget hm W) := by
    have hh := linFinitePointApply_spec_poly.choose_spec.choose_spec hat.point m hmpos
      (ρ g).toAddMonoidHom (c g) x (encIntMatrix (linFiniteActionMatrix m ρ c g⁻¹))
    refine hh.mono ?_
    change linPrimaryPointCoefficient * ((Val.list [record, point]).wt + 1) ^ linPrimaryPointDegree ≤
      linPrimaryPointCoefficient * (linPrimarySuccessPointArg hm W + 1) ^ linPrimaryPointDegree
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right wparg 1) _)
  have wpoint := hp.wt_lt.le
  have wrarg : (Val.list [ctx, raw]).wt ≤ 100 * (W + 1) := by
    have hh := wt_list2_le ctx raw
    omega
  have hr := (linAffineRestrict_spec hm hat.restrict gs ks hle m hmpos ρ c hc).mono
    (linAffineRestrictCost_mono hm wrarg)
  change FunDet P (b + 642) (.list [ctx, raw]) nextCtx (linPrimarySuccessRestrictBudget hm W) at hr
  have wnext := hr.wt_lt.le
  have hcomp := (compose_spec hat.compose g.val acc).mono (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 3))
  change FunDet P (b + 720) (.list [encPerm g.val, encPerm acc]) nextAcc (linPrimarySuccessComposeBudget W) at hcomp
  have wcomp := hcomp.wt_lt.le
  have darg (rest : List Val) (k : ℕ) {v : Val}
      (hk : ([ctx, point, encPerm acc, .nat p, linVecVal (fun i => (m i : ℤ))] : List Val)[k]? = some v) :=
    Det.arg' (P := P) (vs := [ctx, point, encPerm acc, .nat p, linVecVal (fun i => (m i : ℤ))])
      (rest := rest) (j := k) hk
  have dphase (rest : List Val) := Det.var' (P := P) (env := [a, prep, phase] ++ rest) (i := 2) rfl
  have dt := Det.call (Det.get' (Det.get' (Det.get' (dphase []) (Det.nat 0) rfl) (Det.nat 0) rfl)
    (Det.nat 1) rfl) htail
  have di := Det.call (Det.mk2 (darg [prep, phase, raw] 0 rfl)
    (Det.get' (dphase [raw]) (Det.nat 2) rfl)) hi
  have dp := Det.call (Det.mk2 (Det.var' (P := P) (env := [a, prep, phase, raw, record]) (i := 4) rfl)
    (darg [prep, phase, raw, record] 1 rfl)) hp
  have dr := Det.call (Det.mk2 (darg [prep, phase, raw, record, nextPoint] 0 rfl)
    (Det.var' (P := P) (env := [a, prep, phase, raw, record, nextPoint]) (i := 3) rfl)) hr
  have dc := Det.call (Det.mk2 (Det.get' (dphase [raw, record, nextPoint, nextCtx]) (Det.nat 2) rfl)
    (darg [prep, phase, raw, record, nextPoint, nextCtx] 2 rfl)) hcomp
  have dout := Det.mk3
    (Det.var' (P := P) (env := [a, prep, phase, raw, record, nextPoint, nextCtx, nextAcc]) (i := 6) rfl)
    (Det.var' (P := P) (env := [a, prep, phase, raw, record, nextPoint, nextCtx, nextAcc]) (i := 5) rfl)
    (Det.var' (P := P) (env := [a, prep, phase, raw, record, nextPoint, nextCtx, nextAcc]) (i := 7) rfl)
  refine (Det.letE dt (Det.letE di (Det.letE dp (Det.letE dr (Det.letE dc dout))))).mono ?_
  have wa1 := wt_list2_le ctx (encPerm g.val)
  have wa2 := wt_list2_le record point
  have wa3 := wt_list2_le ctx raw
  have wa4 := wt_list2_le (encPerm g.val) (encPerm acc)
  have wout := wt_list3_le nextCtx nextPoint nextAcc
  change _ ≤ linPrimePassSuccessCost hm W
  unfold linPrimePassSuccessCost linPrimarySuccessCost
  have wstate : (Val.list [ctx, point, encPerm acc, .nat p, linVecVal (fun i => (m i : ℤ))]).wt ≤ W := wa
  clear hi hp hr hcomp htail dt di dp dr dc dout darg dphase hat hc hmpos
  clear_value ctx point a raw phase W record nextPoint nextCtx nextAcc
  clear wiarg wparg wrarg
  generalize hI : linPrimarySuccessItemBudget hm W = I at wrecord ⊢
  generalize hP : linPrimarySuccessPointBudget hm W = B at wpoint ⊢
  generalize hR : linPrimarySuccessRestrictBudget hm W = R at wnext ⊢
  generalize hC : linPrimarySuccessComposeBudget W = C at wcomp ⊢
  generalize hT : linPrimePassTailBudget W = T at ⊢
  clear hI hP hR hC hT hm hv
  omega

theorem linPrimePassSuccessCost_poly (hm : ConstructiveMembership) :
    PBU (fun _ W _ => linPrimePassSuccessCost hm W) := by
  have ht : PBU (fun _ W _ => linPrimePassTailBudget W) := by
    unfold linPrimePassTailBudget
    norm_poly
  exact PBU.smul 1000 (PBU.addc (PBU.add (PBU.add PBU.W ht) (linPrimarySuccessCost_poly hm)) 1)

end GI.Impl
