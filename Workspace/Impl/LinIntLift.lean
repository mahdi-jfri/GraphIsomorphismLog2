import Workspace.Impl.LinIntPad
import Workspace.Impl.LinIntTri
import Workspace.Lang.Lib.LinIntRowMul

/-! Lifting a Hermite-block answer through the unimodular row multiplier. -/
namespace GI.Impl
open GI.Cited GI.Lang Matrix

structure linLiftIndices where
  pad : ℕ
  rep : ℕ
  append : ℕ
  row : ℕ
  column : ℕ
  dot : ℕ
  ints : ℕ

structure linLiftInstalled (P : Program) (I : linLiftIndices) : Prop where
  pad : P.funs[I.pad]? = some (linPadF I.rep I.append)
  rep : P.HasAt I.rep (replicateFuns I.rep)
  append : P.HasAt I.append (appendFuns I.append)
  row : P.HasAt I.row (linRowMulFuns I.row I.column I.dot)
  column : P.HasAt I.column (linColumnFuns I.column)
  dot : P.HasAt I.dot (linDotLoopFuns I.dot I.ints)
  ints : linIntSpec P I.ints

/-- Input [r,U,answer]. Failure propagates. Success is padded and multiplied by U. -/
def linHermiteLiftF (I : linLiftIndices) : Expr :=
  .ite (.isNat (arg 2)) (.nat 0)
    (.letE (.call I.pad (mk2 (arg 0) (.get (arg 2) (.nat 1))))
      (mk2 (.nat 1) (.call I.row (mk3 (arg 0) (.var 1) (arg 1)))))

def linHermiteLiftPadCost (W r : ℕ) : ℕ := linPadCost (10 * (W + 1)) r
def linHermiteLiftRowArg (W r : ℕ) : ℕ := 10 * (W + linHermiteLiftPadCost W r + r + 1)
def linHermiteLiftRowCost (W r : ℕ) : ℕ := linRowMulCost (linHermiteLiftRowArg W r) r r
def linHermiteLiftCost (W r : ℕ) : ℕ :=
  1000 * (W + r + linHermiteLiftPadCost W r + linHermiteLiftRowCost W r + 1)

set_option maxHeartbeats 1000000 in
theorem linHermiteLift_spec {P : Program} {f : ℕ} {I : linLiftIndices}
    (h : linLiftInstalled P I) (hf : P.funs[f]? = some (linHermiteLiftF I))
    {r c : ℕ} (hcr : c ≤ r) (U : Matrix (Fin r) (Fin r) ℤ)
    (s : Option (Fin c → ℤ)) :
    FunDet P f (.list [.nat r, encIntMatrix U, linTriVal s])
      (linTriVal (s.map fun y => linPad (r := r) y ᵥ* U))
      (linHermiteLiftCost (Val.list [.nat r, encIntMatrix U, linTriVal s]).wt r) := by
  cases s with
  | none =>
    have dt := Det.isNat (Det.arg' (P := P) (vs := [.nat r, encIntMatrix U, linTriVal (none : Option (Fin c → ℤ))])
      (rest := []) (j := 2) rfl)
    apply FunDet.intro hf
    refine (Det.ite_pos dt (by decide : 1 ≠ 0) (Det.nat 0)).mono ?_
    unfold linHermiteLiftCost
    have w0 : (Val.nat 0).wt = 2 := rfl
    omega
  | some y =>
    let a := Val.list [.nat r, encIntMatrix U, linTriVal (some y)]
    let W := a.wt
    let v := linPad (r := r) y
    have wy : (linVecVal y).wt < W := (wt_le_wt_list (by simp : linVecVal y ∈ [.nat 1, linVecVal y])).trans
      (wt_le_wt_list (by simp : linTriVal (some y) ∈ [.nat r, encIntMatrix U, linTriVal (some y)]))
    have wu : (encIntMatrix U).wt < W := wt_le_wt_list (by simp)
    have wr : (Val.nat r).wt < W := wt_le_wt_list (by simp)
    have ws : (linTriVal (some y)).wt < W := wt_le_wt_list (by simp)
    have wpa := wt_list2_le (.nat r) (linVecVal y)
    have wpad : (Val.list [.nat r, linVecVal y]).wt ≤ 10 * (W + 1) := by omega
    have hp := linPad_spec h.pad h.rep h.append hcr y
    have hp' := hp.mono (show linPadCost (Val.list [.nat r, linVecVal y]).wt r ≤ linHermiteLiftPadCost W r by
      unfold linPadCost linHermiteLiftPadCost
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4))
    have wv : (linVecVal v).wt ≤ linHermiteLiftPadCost W r := hp'.wt_lt.le
    have wra := wt_list3_le (.nat r) (linVecVal v) (encIntMatrix U)
    have wrow : (Val.list [.nat r, linVecVal v, encIntMatrix U]).wt ≤ linHermiteLiftRowArg W r := by
      unfold linHermiteLiftRowArg; omega
    have hm := (linRowMul_spec h.ints h.row h.column h.dot v U).mono (linRowMulCost_mono wrow r r)
    have wo : (linVecVal (v ᵥ* U)).wt ≤ linHermiteLiftRowCost W r := hm.wt_lt.le
    have wa := wt_list2_le (.nat 1) (linVecVal (v ᵥ* U))
    have darg (j : ℕ) (rest : List Val) {z : Val} (hz : [.nat r, encIntMatrix U, linTriVal (some y)][j]? = some z) :=
      Det.arg' (P := P) (vs := [.nat r, encIntMatrix U, linTriVal (some y)]) (rest := rest) (j := j) hz
    have dy := Det.get' (darg 2 [] rfl) (Det.nat 1) rfl
    have dp := Det.call (Det.mk2 (darg 0 [] rfl) dy) hp'
    have dm := Det.call (Det.mk3 (darg 0 [linVecVal v] rfl)
      (Det.var' (P := P) (env := [a, linVecVal v]) (i := 1) rfl) (darg 1 [linVecVal v] rfl)) hm
    have ds := Det.letE dp (Det.mk2 (Det.nat 1) dm)
    have dt := Det.isNat (darg 2 [] rfl)
    apply FunDet.intro hf
    refine (Det.ite_zero dt ds).mono ?_
    have w1 : (Val.nat 1).wt = 3 := rfl
    change _ ≤ linHermiteLiftCost W r
    unfold linHermiteLiftCost linHermiteLiftRowCost at *
    simp only [v, W, a, linTriVal, Option.map_some] at *
    omega

end GI.Impl

namespace GI.Impl
open GI.Lang

theorem linHermiteLiftCost_mono {W V : ℕ} (h : W ≤ V) (r : ℕ) :
    linHermiteLiftCost W r ≤ linHermiteLiftCost V r := by
  have hp : linHermiteLiftPadCost W r ≤ linHermiteLiftPadCost V r := by
    unfold linHermiteLiftPadCost linPadCost; gcongr
  have ha : linHermiteLiftRowArg W r ≤ linHermiteLiftRowArg V r := by
    unfold linHermiteLiftRowArg; omega
  have hr := linRowMulCost_mono ha r r
  unfold linHermiteLiftCost linHermiteLiftRowCost
  omega
end GI.Impl
