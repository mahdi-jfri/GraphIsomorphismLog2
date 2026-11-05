module

public import Workspace.Impl.LinObjectClass
public import Workspace.Impl.TermRecProgPcs

@[expose] public section

/-! Compute the first position of an object's (color, subgroup) class. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linObjectFindF (find : ℕ) : Expr := .call find (mk2 (arg 1) (arg 0))
def linObjectFindFuns (b j : ℕ) : List Expr :=
  [linObjectFindF (b + 1)] ++ findFuns (b + 1) (b + 4) ++ linObjectClassFuns (b + 4) j

theorem linObjectFindFuns_length (b j : ℕ) : (linObjectFindFuns b j).length = 11 := rfl

noncomputable def linObjectFindCost (h : Membership) (W : ℕ) : ℕ :=
  100000 * (W + 1) * (linObjectClassCost h (10 * (W + 1)) + W + 1)

theorem linObjectClassCost_mono (h : Membership) {W V : ℕ} (hW : W ≤ V) :
    linObjectClassCost h W ≤ linObjectClassCost h V := by
  simp only [linObjectClassCost, linGroupEqCost, linGroupLeCost, linGroupMemberCost, Prim.boundSize]
  gcongr

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem linObjectFind_spec (hm : Membership) {P : Program} {b j n : ℕ}
    (hp : P.HasAt b (linObjectFindFuns b j)) (hj : P.prims[j]? = some (membershipPrim hm))
    (Z : List (TmRiO n)) (o : TmRiO n) :
    FunDet P b (.list [tmGlObjsVal Z, tmGlObjVal o]) (.nat (linObjectColor Z o))
      (linObjectFindCost hm (Val.list [tmGlObjsVal Z, tmGlObjVal o]).wt) := by
  classical
  let a := Val.list [tmGlObjsVal Z, tmGlObjVal o]
  let W := a.wt
  let xs := Z.map tmGlObjVal
  let q (v : Val) := decide (linObjectColorEq o (tmRiDec (n := n) v))
  let B := linObjectClassCost hm (10 * (W + 1))
  have wz : (tmGlObjsVal Z).wt < W := wt_le_wt_list (by simp [W, a])
  have wo : (tmGlObjVal o).wt < W := wt_le_wt_list (by simp [W, a])
  have wl : xs.length ≤ W := (length_lt_wt_list xs).le.trans wz.le
  have hc : P.HasAt (b + 4) (linObjectClassFuns (b + 4) j) := hp.block 4 rfl
  have hf : P.HasAt (b + 1) (findFuns (b + 1) (b + 4)) := hp.block 1 rfl
  have hpred : ∀ v ∈ xs, FunDet P (b + 4) (.list [tmGlObjVal o, v]) (boolVal (q v)) B := by
    intro v hv
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv
    have wx : (tmGlObjVal z).wt < W := (wt_le_wt_list (vs := xs) (List.mem_map.mpr ⟨z, hz, rfl⟩)).trans wz
    have wa := wt_list2_le (tmGlObjVal o) (tmGlObjVal z)
    have ww : (Val.list [tmGlObjVal o, tmGlObjVal z]).wt ≤ 10 * (W + 1) := by omega
    have hh := (linObjectClass_spec hm hc hj o z).mono (linObjectClassCost_mono hm ww)
    simpa only [q, tmRiDec_val] using hh
  have hs := find_spec hf hpred
  have hout : xs.findIdx q = linObjectColor Z o := by
    unfold linObjectColor
    simp only [xs, List.findIdx_map]
    congr 1
    funext x
    simp only [Function.comp_apply, q, tmRiDec_val]
  have dfind := Det.call (Det.mk2
    (Det.arg' (P := P) (vs := [tmGlObjsVal Z, tmGlObjVal o]) (rest := []) (j := 1) rfl)
    (Det.arg' (P := P) (vs := [tmGlObjsVal Z, tmGlObjVal o]) (rest := []) (j := 0) rfl)) hs
  apply FunAll.intro (hp.block (gs := [linObjectFindF (b + 1)]) 0 rfl).single
  refine dfind.post fun cost hcost => ⟨congrArg Val.nat hout, ?_⟩
  have wi := wt_list2_le (tmGlObjVal o) (tmGlObjsVal Z)
  have widx := wt_nat_le (xs.findIdx q)
  have hidx := xs.findIdx_le_length (p := q)
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hcost
  have h₁ := Nat.mul_le_mul_right B wl
  have h₂ : loopModK * (xs.length + 1) * ((Val.list [tmGlObjVal o, .list xs]).wt + 2 * xs.length + 3) ≤
      1000 * (W + 1) * (6 * W + 10) := by
    unfold loopModK
    apply Nat.mul_le_mul
    · exact Nat.mul_le_mul_left _ (by omega)
    · change (Val.list [tmGlObjVal o, tmGlObjsVal Z]).wt + 2 * xs.length + 3 ≤ _
      omega
  change cost ≤ linObjectFindCost hm W
  unfold linObjectFindCost
  dsimp only [W, a, xs, B, tmGlObjsVal] at *
  simp only [loopModK] at *
  nlinarith

theorem linObjectFindCost_mono (h : Membership) {W V : ℕ} (hW : W ≤ V) :
    linObjectFindCost h W ≤ linObjectFindCost h V := by
  simp only [linObjectFindCost, linObjectClassCost, linGroupEqCost, linGroupLeCost,
    linGroupMemberCost, Prim.boundSize]
  gcongr

theorem linObjectFindCost_poly (h : Membership) : PBU (fun _ W _ => linObjectFindCost h W) := by
  simp only [linObjectFindCost, linObjectClassCost, linGroupEqCost, linGroupLeCost,
    linGroupMemberCost, Prim.boundSize]
  norm_poly

end GI.Impl
