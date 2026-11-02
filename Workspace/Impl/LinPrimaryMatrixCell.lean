import Workspace.Impl.LinPrimaryFieldMatrix
import Workspace.Impl.LinMapEncoded
import Workspace.Impl.AggStructDC

/-! One explicit field-layer matrix cell, with fixed inactive coordinates. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linPrimaryMatrixCellF : Expr :=
  let A := .get (arg 0) (.nat 0)
  let ν := .get (arg 0) (.nat 1)
  let level := .get (arg 0) (.nat 2)
  let i := .get (arg 0) (.nat 3)
  let k := arg 1
  .ite (.arith .lt level (.get ν i))
    (.ite (.arith .lt level (.get ν k)) (.get (.get A i) k) (.nat 0))
    (.arith .eq i k)

private theorem linPrimaryCellIte {P : Program} {env : List Val} {c t e : Expr}
    {x nc nt ne T : ℕ} {a b : Val}
    (hc : StDC P env c (.nat x) nc 0 T) (ht : StDC P env t a nt 0 T)
    (he : StDC P env e b ne 0 T) (ha : a.wt ≤ T) (hb : b.wt ≤ T) :
    StDC P env (.ite c t e) (if x = 0 then b else a) (nc + nt + ne + 1) 0 T := by
  refine (Det.ite' hc.det ht.det he.det).mono ?_
  have hh : max a.wt b.wt ≤ T := max_le ha hb
  simp only [Nat.add_zero, Nat.add_mul, Nat.one_mul]
  omega

private theorem linPrimaryMatrixCell_formula {p d : ℕ} (hp : p.Prime)
    (A : Matrix (Fin (d + 1)) (Fin (d + 1)) (ZMod p)) (ν : Fin d → ℕ)
    (level : ℕ) (i k : Fin d) :
    (if GI.Machine.BinOp.lt.eval level (ν i) = 0 then
      Val.nat (GI.Machine.BinOp.eq.eval i.val k.val) else
      if GI.Machine.BinOp.lt.eval level (ν k) = 0 then Val.nat 0 else
      Val.nat (A i.castSucc k.castSucc).val) =
      Val.nat (linActiveMatrix (fun i => level < ν i)
        (A.submatrix Fin.castSucc Fin.castSucc) i k).val := by
  by_cases hik : i = k
  · subst k
    by_cases hi : level < ν i <;>
      simp [GI.Machine.BinOp.eval, linActiveMatrix, hi, Matrix.submatrix_apply,
        ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hp.one_lt]
  · have hval : i.val ≠ k.val := fun h => hik (Fin.ext h)
    by_cases hi : level < ν i <;> by_cases hk : level < ν k <;>
      simp [GI.Machine.BinOp.eval, linActiveMatrix, hi, hk, hik, hval, Matrix.submatrix_apply,
        ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hp.one_lt]

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 5000 in
theorem linPrimaryMatrixCell_spec {P : Program} {f p d : ℕ}
    (hf : P.funs[f]? = some linPrimaryMatrixCellF) (hp : p.Prime)
    (A : Matrix (Fin (d + 1)) (Fin (d + 1)) (ZMod p)) (ν : Fin d → ℕ)
    (level : ℕ) (i k : Fin d) :
    FunDet P f (.list [.list [encModMatrix A, encFun ν, .nat level, .nat i], .nat k])
      (.nat (linActiveMatrix (fun i => level < ν i) (A.submatrix Fin.castSucc Fin.castSucc) i k).val)
      (100000 * ((Val.list [.list [encModMatrix A, encFun ν, .nat level, .nat i], .nat k]).wt + 1)) := by
  let ctx := Val.list [encModMatrix A, encFun ν, .nat level, .nat i]
  let a := Val.list [ctx, .nat k]
  let W := a.wt
  let T := 100 * (W + 1)
  have hT : W + 10 ≤ T := by dsimp [T]; omega
  have wctx : ctx.wt < W := wt_le_wt_list (by simp [W, a])
  have wk : (Val.nat k).wt < W := wt_le_wt_list (by simp [W, a])
  have wA : (encModMatrix A).wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have wν : (encFun ν).wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have wlevel : (Val.nat level).wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have wi : (Val.nat i).wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have wrow : (encVec (A i.castSucc)).wt < (encModMatrix A).wt := wt_le_wt_list (by simp [encModMatrix])
  have wcell : (Val.nat (A i.castSucc k.castSucc).val).wt < (encVec (A i.castSucc)).wt :=
    wt_le_wt_list (by simp [encVec])
  have wνi : (Val.nat (ν i)).wt < (encFun ν).wt := wt_le_wt_list (by simp [encFun])
  have wνk : (Val.nat (ν k)).wt < (encFun ν).wt := wt_le_wt_list (by simp [encFun])
  have w0 : (Val.nat 0).wt = 2 := rfl
  have w1 : (Val.nat 1).wt = 3 := rfl
  have wlt (x y : ℕ) : (Val.nat (GI.Machine.BinOp.lt.eval x y)).wt ≤ T := by
    simp only [GI.Machine.BinOp.eval]; split_ifs <;> simp only [w0, w1] <;> omega
  have weq (x y : ℕ) : (Val.nat (GI.Machine.BinOp.eq.eval x y)).wt ≤ T := by
    simp only [GI.Machine.BinOp.eval]; split_ifs <;> simp only [w0, w1] <;> omega
  have dc := StDC.arg (P := P) (vs := [ctx, .nat k]) (rest := []) (j := 0) rfl
    (show a.wt ≤ T by change W ≤ T; omega) (by omega) (show ctx.wt ≤ T by omega)
  have dk := StDC.arg (P := P) (vs := [ctx, .nat k]) (rest := []) (j := 1) rfl
    (show a.wt ≤ T by change W ≤ T; omega) (by omega) (show (Val.nat k).wt ≤ T by omega)
  have da := StDC.get dc (StDC.nat 0 (by omega)) rfl (show (encModMatrix A).wt ≤ T by omega)
  have dν := StDC.get dc (StDC.nat 1 (by omega)) rfl (show (encFun ν).wt ≤ T by omega)
  have dl := StDC.get dc (StDC.nat 2 (by omega)) rfl (show (Val.nat level).wt ≤ T by omega)
  have di := StDC.get dc (StDC.nat 3 (by omega)) rfl (show (Val.nat i).wt ≤ T by omega)
  have dνi := StDC.get dν di (v := .nat (ν i)) (by
    rw [List.getElem?_map, List.getElem?_eq_getElem (by simpa using i.isLt)]
    simp) (show (Val.nat (ν i)).wt ≤ T by omega)
  have dνk := StDC.get dν dk (v := .nat (ν k)) (by
    rw [List.getElem?_map, List.getElem?_eq_getElem (by simpa using k.isLt)]
    simp) (show (Val.nat (ν k)).wt ≤ T by omega)
  have dr := StDC.get da di (v := encVec (A i.castSucc)) (by
    rw [List.getElem?_map, List.getElem?_eq_getElem (by simpa only [List.length_finRange] using Nat.lt_succ_of_lt i.isLt)]
    simp <;> rfl) (show (encVec (A i.castSucc)).wt ≤ T by omega)
  have de := StDC.get dr dk (v := .nat (A i.castSucc k.castSucc).val) (by
    rw [List.getElem?_map, List.getElem?_eq_getElem (by simpa only [List.length_finRange] using Nat.lt_succ_of_lt k.isLt)]
    simp <;> rfl) (show (Val.nat (A i.castSucc k.castSucc).val).wt ≤ T by omega)
  have dli := StDC.arith (op := .lt) dl dνi rfl (wlt _ _)
  have dlk := StDC.arith (op := .lt) dl dνk rfl (wlt _ _)
  have dz := StDC.nat (P := P) (env := [a]) 0 (by omega : 0 + 2 ≤ T)
  have dunit := StDC.arith (op := .eq) di dk rfl (weq _ _)
  have dzwt : (Val.nat 0).wt ≤ T := by have : (Val.nat 0).wt = 2 := rfl; omega
  have dcwt : (Val.nat (A i.castSucc k.castSucc).val).wt ≤ T := by omega
  have dinner := linPrimaryCellIte dlk de dz dcwt dzwt
  have winner : (if GI.Machine.BinOp.lt.eval level (ν k) = 0 then Val.nat 0 else
      Val.nat (A i.castSucc k.castSucc).val).wt ≤ T := by split_ifs <;> assumption
  have db := linPrimaryCellIte dli dinner dunit winner (weq _ _)
  apply FunAll.intro hf
  refine db.det.post fun cost hc => ⟨linPrimaryMatrixCell_formula hp A ν level i k, ?_⟩
  change cost ≤ 100000 * (W + 1)
  norm_num only [Nat.reduceAdd, Nat.add_zero] at hc
  dsimp only [T] at hc
  omega

end GI.Impl
