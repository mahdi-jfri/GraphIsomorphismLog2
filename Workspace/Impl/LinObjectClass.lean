import Workspace.Impl.LinGroupCompare
import Workspace.Impl.LinObjectColor

/-! Decide the orbit-color class of two unrestricted coset-object encodings.
The old numeric colors are compared in binary; no loop uses their magnitude. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linObjectClassF (eq : ℕ) : Expr :=
  .ite (.arith .eq (.get (arg 0) (.nat 0)) (.get (arg 1) (.nat 0)))
    (.call eq (mk2 (.get (arg 0) (.nat 1)) (.get (arg 1) (.nat 1)))) (.nat 0)
def linObjectClassFuns (b j : ℕ) : List Expr :=
  [linObjectClassF (b + 1)] ++ linGroupEqFuns (b + 1) j

theorem linObjectClassFuns_length (b j : ℕ) : (linObjectClassFuns b j).length = 7 := rfl

noncomputable def linObjectClassCost (h : Membership) (W : ℕ) : ℕ :=
  1000 * (W + linGroupEqCost h (10 * (W + 1)) + 1)

theorem linGroupEqCost_mono (h : Membership) {W V : ℕ} (hW : W ≤ V) :
    linGroupEqCost h W ≤ linGroupEqCost h V := by
  simp only [linGroupEqCost, linGroupLeCost, linGroupMemberCost, Prim.boundSize]
  gcongr

open Classical in
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem linObjectClass_spec (hm : Membership) {P : Program} {b j n : ℕ}
    (hp : P.HasAt b (linObjectClassFuns b j)) (hj : P.prims[j]? = some (membershipPrim hm))
    (o o' : TmRiO n) :
    FunDet P b (.list [tmGlObjVal o, tmGlObjVal o']) (boolVal (decide (linObjectColorEq o o')))
      (linObjectClassCost hm (Val.list [tmGlObjVal o, tmGlObjVal o']).wt) := by
  let a := Val.list [tmGlObjVal o, tmGlObjVal o']
  let W := a.wt
  have w₀ : (tmGlObjVal o).wt < W := wt_le_wt_list (by simp [W, a])
  have w₁ : (tmGlObjVal o').wt < W := wt_le_wt_list (by simp [W, a])
  have wg₀ : (encGroup o.2.1).wt < W :=
    (wt_le_wt_list (by simp [tmGlObjVal] : encGroup o.2.1 ∈ [.nat o.1, encGroup o.2.1, encPerm o.2.2])).trans w₀
  have wg₁ : (encGroup o'.2.1).wt < W :=
    (wt_le_wt_list (by simp [tmGlObjVal] : encGroup o'.2.1 ∈ [.nat o'.1, encGroup o'.2.1, encPerm o'.2.2])).trans w₁
  have wc₀ : (Val.nat o.1).wt < W :=
    (wt_le_wt_list (by simp [tmGlObjVal] : Val.nat o.1 ∈ [.nat o.1, encGroup o.2.1, encPerm o.2.2])).trans w₀
  have wc₁ : (Val.nat o'.1).wt < W :=
    (wt_le_wt_list (by simp [tmGlObjVal] : Val.nat o'.1 ∈ [.nat o'.1, encGroup o'.2.1, encPerm o'.2.2])).trans w₁
  have wi := wt_list2_le (encGroup o.2.1) (encGroup o'.2.1)
  have win : (Val.list [encGroup o.2.1, encGroup o'.2.1]).wt ≤ 10 * (W + 1) := by omega
  have hgroup : P.HasAt (b + 1) (linGroupEqFuns (b + 1) j) := hp.block 1 rfl
  have hgs := (linGroupEq_spec hm hgroup hj o.2.1 o'.2.1).mono (linGroupEqCost_mono hm win)
  have de (i : ℕ) {v : Val} (hv : [tmGlObjVal o, tmGlObjVal o'][i]? = some v) :=
    Det.arg' (P := P) (vs := [tmGlObjVal o, tmGlObjVal o']) (rest := []) (j := i) hv
  have dc₀ := Det.get' (de 0 rfl) (Det.nat 0) rfl
  have dc₁ := Det.get' (de 1 rfl) (Det.nat 0) rfl
  have dgs := Det.call (Det.mk2 (Det.get' (de 0 rfl) (Det.nat 1) rfl)
    (Det.get' (de 1 rfl) (Det.nat 1) rfl)) hgs
  have he := (hp.block (gs := [linObjectClassF (b + 1)]) 0 rfl).single
  have wb := wt_boolVal_le (decide (gens o.2.1 = gens o'.2.1))
  apply FunAll.intro he
  by_cases hc : o.1 = o'.1
  · have dt := Det.arith' (op := .eq) dc₀ dc₁ (z := 1) (by simp [GI.Machine.BinOp.eval, hc])
    refine (Det.ite_pos dt (by decide) dgs).post fun cost hcost => ⟨?_, ?_⟩
    · simp [linObjectColorEq, hc]
    · change cost ≤ linObjectClassCost hm W
      unfold linObjectClassCost
      dsimp only [W, a] at *
      omega
  · have dt := Det.arith' (op := .eq) dc₀ dc₁ (z := 0) (by simp [GI.Machine.BinOp.eval, hc])
    refine (Det.ite_zero dt (Det.nat 0)).post fun cost hcost => ⟨?_, ?_⟩
    · simp [linObjectColorEq, hc, boolVal]
    · have wz : (Val.nat 0).wt = 2 := by decide
      change cost ≤ linObjectClassCost hm W
      unfold linObjectClassCost
      dsimp only [W, a] at *
      omega

theorem linObjectClassCost_poly (h : Membership) : PBU (fun _ W _ => linObjectClassCost h W) := by
  simp only [linObjectClassCost, linGroupEqCost, linGroupLeCost, linGroupMemberCost, Prim.boundSize]
  norm_poly

end GI.Impl
