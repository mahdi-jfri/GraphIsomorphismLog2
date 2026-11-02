import Workspace.Impl.LinObjectLiftAnswer

namespace GI.Impl
open GI.Cited GI.Lang

def linObjectLiftSuccessE (slice word : ℕ) : Expr :=
  .letE (.call slice (mk3
    (.arith .mul (.length (.get (arg 1) (.nat 0))) (.length (.get (arg 1) (.nat 2))))
    (.length (.get (arg 1) (.nat 1))) (.get (.var 3) (.nat 1))))
    (.letE (.call word (mk2 (arg 0) (.var 4))) (mk2 (.nat 1) (.var 5)))

def linObjectLiftAfterE (slice word : ℕ) : Expr :=
  .ite (.isNat (.var 3)) (.nat 0) (linObjectLiftSuccessE slice word)

noncomputable def linObjectLiftFinishCost (hH : HermiteFullRank) (W : ℕ) : ℕ :=
  1000000 * ((W + 1) ^ 2 + W + linObjectLiftBuildBudget W + linObjectLiftNegBudget W +
    linObjectLiftSolveBudget hH W + linObjectLiftSliceBudget hH W + linObjectLiftWordBudget hH W + 1)

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 5000 in
theorem linObjectLift_after_spec (hH : HermiteFullRank) {P : Program} {b jh n p r : ℕ}
    (h : linObjectLiftAt P b jh) {Q : Type*} [CommGroup Q]
    (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (B : Fin p → Submodule ℤ (Additive Q)) (hf : Function.Surjective (linObjectLiftCoord as π))
    (L : Fin p → Matrix (Fin r) (Fin as.length) ℤ)
    (hL : ∀ i, LinearMap.ker ((B i).mkQ.comp (linObjectLiftCoord as π)) = linRelations (L i))
    (w : Fin (as.length * p) → ℤ) (mv neg ans : Val)
    (hans : linRowAnswer (linObjectQuotientMatrix L) (-w) ans)
    (hanswt : ans.wt ≤ linObjectLiftSolveBudget hH
      (Val.list [encGroup as, linObjectBlockInput L, linVecVal w]).wt)
    (hoff : r * p ≤ linObjectLiftBuildBudget
      (Val.list [encGroup as, linObjectBlockInput L, linVecVal w]).wt) :
    let a := Val.list [encGroup as, linObjectBlockInput L, linVecVal w]
    EvalAll P [a, mv, neg, ans] (linObjectLiftAfterE (b + 104) (b + 107)) (fun out cost =>
      linObjectLiftAnswer as π B w out ∧ cost ≤ linObjectLiftFinishCost hH a.wt) := by
  let a := Val.list [encGroup as, linObjectBlockInput L, linVecVal w]
  let W := a.wt
  let RB := linObjectLiftSolveBudget hH W
  let SB := linObjectLiftSliceBudget hH W
  let WB := linObjectLiftWordBudget hH W
  have wa : (encGroup as).wt < W := wt_le_wt_list (by simp [a, W])
  have wl : (linObjectBlockInput L).wt < W := wt_le_wt_list (by simp [a, W])
  obtain ⟨hr, ht, hp⟩ := linObjectBlockInput_dimensions L
  have hrt : r ≤ W := hr.trans wl.le
  have htt : as.length ≤ W := ht.trans wl.le
  have hpt : p ≤ W := hp.trans wl.le
  have wrs : (encFun (fun i : Fin r => i.val)).wt < (linObjectBlockInput L).wt := wt_le_wt_list (by
    simp [linObjectBlockInput])
  have wcs : (encFun (fun i : Fin as.length => i.val)).wt < (linObjectBlockInput L).wt :=
    wt_le_wt_list (by simp [linObjectBlockInput])
  have wps : (Val.list ((List.finRange p).map fun i => encIntMatrix (L i))).wt <
      (linObjectBlockInput L).wt := wt_le_wt_list (by simp [linObjectBlockInput])
  have wrsW : (encFun (fun i : Fin r => i.val)).wt ≤ W := wrs.le.trans wl.le
  have wcsW : (encFun (fun i : Fin as.length => i.val)).wt ≤ W := wcs.le.trans wl.le
  rcases hans with ⟨rfl, hno⟩ | ⟨z, rfl, hz⟩
  · have dt := Det.isNat (Det.var' (P := P) (env := [a, mv, neg, .nat 0]) (i := 3) rfl)
    have dd := Det.ite_pos dt (by decide : 1 ≠ 0) (Det.nat 0)
      (e := linObjectLiftSuccessE (b + 104) (b + 107))
    refine dd.post fun cost hc => ⟨linObjectLift_failure as π B hf L hL w hno, ?_⟩
    change cost ≤ linObjectLiftFinishCost hH W
    unfold linObjectLiftFinishCost
    have hw : (Val.nat 0).wt = 2 := rfl
    dsimp only [RB, W, a] at *
    omega
  · let common := fun j : Fin as.length => z (Fin.natAdd (r * p) j)
    let cv := linVecVal common
    let g := linGroupWord (fun i => as.get i) common
    have wz : (linVecVal z).wt < (Val.list [.nat 1, linVecVal z]).wt := wt_le_wt_list (by simp)
    have hsarg : (Val.list [.nat (r * p), .nat as.length, linVecVal z]).wt ≤
        linObjectLiftSliceArg hH W := by
      have hw := wt_list3_le (.nat (r * p)) (.nat as.length) (linVecVal z)
      have ho := wt_nat_le (r * p)
      have ht := wt_nat_le as.length
      unfold linObjectLiftSliceArg
      dsimp only [a, W] at *
      omega
    have hs : FunDet P (b + 104) (.list [.nat (r * p), .nat as.length, linVecVal z]) cv SB :=
      (linSlice_vec_spec h.slice z (offset := r * p) (c := as.length) (by omega)).mono
        (linSliceCost_mono hsarg)
    have wcv : cv.wt ≤ SB := hs.wt_lt.le
    have hwarg : (Val.list [encGroup as, cv]).wt ≤ linObjectLiftWordArg hH W := by
      have hw := wt_list2_le (encGroup as) cv
      unfold linObjectLiftWordArg
      dsimp only [SB] at *
      omega
    have hw := (linPermWord_spec h.word as common).mono (linPermWordCost_mono hwarg)
    have wg : (encPerm g).wt ≤ WB := hw.wt_lt.le
    have dl := Det.arg' (P := P) (vs := [encGroup as, linObjectBlockInput L, linVecVal w])
      (rest := [mv, neg, .list [.nat 1, linVecVal z]]) (j := 1) rfl
    have dr := Det.length (Det.get' dl (Det.nat 0) rfl)
    have dp := Det.length (Det.get' dl (Det.nat 2) rfl)
    have dc := Det.length (Det.get' dl (Det.nat 1) rfl)
    simp only [linObjectBlockInput, encFun, List.length_map, List.length_finRange] at dr dp dc
    have doff := Det.arith' (op := .mul) dr dp (z := r * p) rfl
    have dz := Det.get' (Det.var' (P := P)
      (env := [a, mv, neg, .list [.nat 1, linVecVal z]]) (i := 3) rfl) (Det.nat 1) rfl
    have ds := Det.call (Det.mk3 doff dc dz) hs
    have das := Det.arg' (P := P) (vs := [encGroup as, linObjectBlockInput L, linVecVal w])
      (rest := [mv, neg, .list [.nat 1, linVecVal z], cv]) (j := 0) rfl
    have dcv := Det.var' (P := P)
      (env := [a, mv, neg, .list [.nat 1, linVecVal z], cv]) (i := 4) rfl
    have dw := Det.call (Det.mk2 das dcv) hw
    have dout := Det.mk2 (Det.nat (P := P)
      (env := [a, mv, neg, .list [.nat 1, linVecVal z], cv, encPerm g]) 1)
      (Det.var' (P := P)
        (env := [a, mv, neg, .list [.nat 1, linVecVal z], cv, encPerm g]) (i := 5) rfl)
    have dt := Det.isNat (Det.var' (P := P)
      (env := [a, mv, neg, .list [.nat 1, linVecVal z]]) (i := 3) rfl)
    have result := Det.ite_zero dt (Det.letE ds (Det.letE dw dout)) (t := .nat 0)
    refine result.post fun cost hc => ⟨linObjectLift_row_answer as π B L hL w z hz, ?_⟩
    have hws := wt_list3_le (.nat (r * p)) (.nat as.length) (linVecVal z)
    have hww := wt_list2_le (encGroup as) cv
    have hwo := wt_list2_le (.nat 1) (encPerm g)
    have ho := wt_nat_le (r * p)
    have ht := wt_nat_le as.length
    have hnat : (Val.nat 1).wt = 3 := rfl
    change cost ≤ linObjectLiftFinishCost hH W
    unfold linObjectLiftFinishCost
    dsimp only [a, W, cv, g, common, RB, SB, WB, linObjectBlockInput, encFun,
      linObjectLiftWordBudget] at *
    omega

end GI.Impl
