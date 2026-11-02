import Workspace.Impl.LinPrimaryStep
import Workspace.Impl.LinPrimaryContext

/-! The successful branch of one primary step evaluates the chosen element
in the full affine action and rebases the complete generator dictionary. -/
namespace GI.Impl
open GI.Cited GI.Lang
set_option maxRecDepth 18000

theorem linAffineRestrictCost_mono (h : ConstructiveMembership) {W V : ℕ} (hw : W ≤ V) :
    linAffineRestrictCost h W ≤ linAffineRestrictCost h V := by
  have hr : linActionRestrictCost h W ≤ linActionRestrictCost h V :=
    linMapBudget_mono hw (linActionItemCost_mono h (by omega))
  have hg : linAffineRestrictGroupBudget W ≤ linAffineRestrictGroupBudget V := by
    unfold linAffineRestrictGroupBudget
    gcongr
  unfold linAffineRestrictCost
  omega

noncomputable def linPrimaryPointCoefficient : ℕ := linFinitePointApply_spec_poly.choose
noncomputable def linPrimaryPointDegree : ℕ := linFinitePointApply_spec_poly.choose_spec.choose

noncomputable def linPrimaryIterationVal {n d : ℕ} (gs : List (Equiv.Perm (Fin n))) (m : Fin d → ℕ)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m)
    (x : linFiniteVec m) (acc : Equiv.Perm (Fin n)) (p : ℕ) (ν : Fin d → ℕ) (level : ℕ) : Val :=
  .list [linActionContext gs m ρ c, linFinitePointVal m x, encPerm acc, .nat p, encFun ν, .nat level]

noncomputable def linPrimarySuccessItemBudget (h : ConstructiveMembership) (W : ℕ) : ℕ :=
  linActionItemCost h (100 * (W + 1))
noncomputable def linPrimarySuccessPointArg (h : ConstructiveMembership) (W : ℕ) : ℕ :=
  100 * (W + linPrimarySuccessItemBudget h W + 1)
noncomputable def linPrimarySuccessPointBudget (h : ConstructiveMembership) (W : ℕ) : ℕ :=
  linPrimaryPointCoefficient * (linPrimarySuccessPointArg h W + 1) ^ linPrimaryPointDegree
noncomputable def linPrimarySuccessRestrictBudget (h : ConstructiveMembership) (W : ℕ) : ℕ :=
  linAffineRestrictCost h (100 * (W + 1))
def linPrimarySuccessComposeBudget (W : ℕ) : ℕ := permK * (W + 1) ^ 3
noncomputable def linPrimarySuccessCost (h : ConstructiveMembership) (W : ℕ) : ℕ :=
  100000 * (W + linPrimarySuccessItemBudget h W + linPrimarySuccessPointBudget h W +
    linPrimarySuccessRestrictBudget h W + linPrimarySuccessComposeBudget W + 1)

set_option maxHeartbeats 1000000 in
theorem linPrimaryStep_success_spec (hm : ConstructiveMembership) (hv : VectorStabilizer)
    {P : Program} {b jm jv n d : ℕ} (hat : linPrimaryStepAt P b jm jv hm hv)
    (gs hs : List (Equiv.Perm (Fin n))) (hle : gens hs ≤ gens gs)
    (m : Fin d → ℕ) (hmpos : ∀ i, 0 < m i)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m)
    (hc : ∀ g k, c (g * k) = ρ g (c k) + c g)
    (g : gens gs) (x : linFiniteVec m) (acc : Equiv.Perm (Fin n))
    (p : ℕ) (ν : Fin d → ℕ) (level : ℕ) (zero : Val) :
    let a := linPrimaryIterationVal gs m ρ c x acc p ν level
    let ans := Val.list [encPerm g.val, .list (hs.map encPerm)]
    Det P [a, zero, ans] (linPrimaryStepTailF (b + 233) (b + 300) (b + 347) (b + 425))
      (.list [linActionContext hs m (ρ.comp (Subgroup.inclusion hle)) (c ∘ Subgroup.inclusion hle),
        linFinitePointVal m (ρ g x + c g), encPerm (g.val * acc)])
      (linPrimarySuccessCost hm (a.wt + zero.wt + ans.wt)) := by
  let ctx := linActionContext gs m ρ c
  let point := linFinitePointVal m x
  let a := linPrimaryIterationVal gs m ρ c x acc p ν level
  let raw := Val.list (hs.map encPerm)
  let ans := Val.list [encPerm g.val, raw]
  let W := a.wt + zero.wt + ans.wt
  let record := linFiniteAffineVal m ρ c g
  let nextPoint := linFinitePointVal m (ρ g x + c g)
  let nextCtx := linActionContext hs m (ρ.comp (Subgroup.inclusion hle)) (c ∘ Subgroup.inclusion hle)
  let nextAcc := encPerm (g.val * acc)
  have wa : a.wt ≤ W := by omega
  have wz : zero.wt ≤ W := by omega
  have wans : ans.wt ≤ W := by omega
  have wctx : ctx.wt < a.wt := wt_le_wt_list (by simp [a, ctx, linPrimaryIterationVal])
  have wpt : point.wt < a.wt := wt_le_wt_list (by simp [a, point, linPrimaryIterationVal])
  have wacc : (encPerm acc).wt < a.wt := wt_le_wt_list (by simp [a, linPrimaryIterationVal])
  have wg : (encPerm g.val).wt < ans.wt := wt_le_wt_list (by simp [ans])
  have wr : raw.wt < ans.wt := wt_le_wt_list (by simp [ans])
  have wgs : (encGroup gs).wt < ctx.wt := wt_le_wt_list (by simp [ctx, linActionContext])
  have hn : n ≤ W := by
    have hh := S_le_wt_encGroup gs
    have hm : n + 1 ≤ (gs.length + 2) * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
    exact (Nat.le_succ n).trans (hm.trans (hh.trans (wgs.le.trans (wctx.le.trans wa))))
  have wiarg : (Val.list [ctx, encPerm g.val]).wt ≤ 100 * (W + 1) := by
    have hh := wt_list2_le ctx (encPerm g.val)
    omega
  have hi := (linActionItem_spec hm hat.item gs m hmpos ρ c hc g).mono (linActionItemCost_mono hm wiarg)
  change FunDet P (b + 233) (.list [ctx, encPerm g.val]) record (linPrimarySuccessItemBudget hm W) at hi
  have wrecord := hi.wt_lt.le
  have wparg : (Val.list [record, point]).wt ≤ linPrimarySuccessPointArg hm W := by
    have hh := wt_list2_le record point
    unfold linPrimarySuccessPointArg
    omega
  have hp : FunDet P (b + 300) (.list [record, point]) nextPoint (linPrimarySuccessPointBudget hm W) := by
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
  have hr := (linAffineRestrict_spec hm hat.restrict gs hs hle m hmpos ρ c hc).mono
    (linAffineRestrictCost_mono hm wrarg)
  change FunDet P (b + 347) (.list [ctx, raw]) nextCtx (linPrimarySuccessRestrictBudget hm W) at hr
  have wnext := hr.wt_lt.le
  have hcomp := (compose_spec hat.compose g.val acc).mono (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 3))
  change FunDet P (b + 425) (.list [encPerm g.val, encPerm acc]) nextAcc (linPrimarySuccessComposeBudget W) at hcomp
  have wcomp := hcomp.wt_lt.le
  have darg (rest : List Val) (k : ℕ) {v : Val}
      (hk : ([ctx, point, encPerm acc, .nat p, encFun ν, .nat level] : List Val)[k]? = some v) :=
    Det.arg' (P := P) (vs := [ctx, point, encPerm acc, .nat p, encFun ν, .nat level])
      (rest := rest) (j := k) hk
  have dans (rest : List Val) := Det.var' (P := P) (env := [a, zero, ans] ++ rest) (i := 2) rfl
  have di := Det.call (Det.mk2 (darg [zero, ans] 0 rfl) (Det.get' (dans []) (Det.nat 0) rfl)) hi
  have dp := Det.call (Det.mk2 (Det.var' (P := P) (env := [a, zero, ans, record]) (i := 3) rfl)
    (darg [zero, ans, record] 1 rfl)) hp
  have dr := Det.call (Det.mk2 (darg [zero, ans, record, nextPoint] 0 rfl)
    (Det.get' (dans [record, nextPoint]) (Det.nat 1) rfl)) hr
  have dc := Det.call (Det.mk2 (Det.get' (dans [record, nextPoint, nextCtx]) (Det.nat 0) rfl)
    (darg [zero, ans, record, nextPoint, nextCtx] 2 rfl)) hcomp
  have dout := Det.mk3
    (Det.var' (P := P) (env := [a, zero, ans, record, nextPoint, nextCtx, nextAcc]) (i := 5) rfl)
    (Det.var' (P := P) (env := [a, zero, ans, record, nextPoint, nextCtx, nextAcc]) (i := 4) rfl)
    (Det.var' (P := P) (env := [a, zero, ans, record, nextPoint, nextCtx, nextAcc]) (i := 6) rfl)
  refine (Det.letE di (Det.letE dp (Det.letE dr (Det.letE dc dout)))).mono ?_
  have wa1 := wt_list2_le ctx (encPerm g.val)
  have wa2 := wt_list2_le record point
  have wa3 := wt_list2_le ctx raw
  have wa4 := wt_list2_le (encPerm g.val) (encPerm acc)
  have wout := wt_list3_le nextCtx nextPoint nextAcc
  change _ ≤ linPrimarySuccessCost hm W
  unfold linPrimarySuccessCost
  have wstate : (Val.list [ctx, point, encPerm acc, .nat p, encFun ν, .nat level]).wt ≤ W := wa
  clear hi hp hr hcomp di dp dr dc dout darg dans hat hc hmpos
  clear_value ctx point a raw ans W record nextPoint nextCtx nextAcc
  clear wiarg wparg wrarg
  generalize hI : linPrimarySuccessItemBudget hm W = I at wrecord ⊢
  generalize hP : linPrimarySuccessPointBudget hm W = B at wpoint ⊢
  generalize hR : linPrimarySuccessRestrictBudget hm W = R at wnext ⊢
  generalize hC : linPrimarySuccessComposeBudget W = C at wcomp ⊢
  clear hI hP hR hC hm hv
  omega

theorem linPrimarySuccessCost_poly (h : ConstructiveMembership) :
    PBU (fun _ W _ => linPrimarySuccessCost h W) := by
  have hi : PBU (fun _ W _ => linPrimarySuccessItemBudget h W) :=
    linPoly_subst (linActionItemCost_poly h) (PBU.const 0) (PBU.smul 100 (PBU.addc PBU.W 1)) (PBU.const 0)
  have ha : PBU (fun _ W _ => linPrimarySuccessPointArg h W) := PBU.smul 100 (PBU.addc (PBU.add PBU.W hi) 1)
  have hp : PBU (fun _ W _ => linPrimarySuccessPointBudget h W) := PBU.smul _ (PBU.pow (PBU.addc ha 1) _)
  have hr : PBU (fun _ W _ => linPrimarySuccessRestrictBudget h W) :=
    linPoly_subst (linAffineRestrictCost_poly h) (PBU.const 0) (PBU.smul 100 (PBU.addc PBU.W 1)) (PBU.const 0)
  have hc : PBU (fun _ W _ => linPrimarySuccessComposeBudget W) := by unfold linPrimarySuccessComposeBudget; norm_poly
  exact PBU.smul 100000 (PBU.addc (PBU.add (PBU.add (PBU.add (PBU.add PBU.W hi) hp) hr) hc) 1)

end GI.Impl
