import Workspace.Impl.LinModReduce

/-! Extract a layer digit from a nonnegative signed coordinate. The divisor
is supplied once by the outer layer loop. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linPrimaryDigitF (decode : ℕ) : Expr :=
  .letE (.call decode (arg 2))
    (.arith .mod (.arith .div (.get (.var 1) (.nat 0)) (arg 1)) (arg 0))

def linPrimaryDigitFuns (b : ℕ) : List Expr :=
  [linPrimaryDigitF (b + 3)] ++ linIntFuns (b + 1)

theorem linPrimaryDigitFuns_length (b : ℕ) : (linPrimaryDigitFuns b).length = 19 := rfl

def linPrimaryDigitCost (W : ℕ) : ℕ := 10000 * (W + linIntCodecCost W + 1)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem linPrimaryDigit_spec {P : Program} {b p : ℕ}
    (h : P.HasAt b (linPrimaryDigitFuns b)) (hp : 0 < p) (q x : ℕ) :
    FunDet P b (.list [.nat p, .nat q, encInt (x : ℤ)])
      (.nat ((x / q : ℕ) : ZMod p).val)
      (linPrimaryDigitCost (Val.list [.nat p, .nat q, encInt (x : ℤ)]).wt) := by
  let a := Val.list [.nat p, .nat q, encInt (x : ℤ)]
  let W := a.wt
  have hi : P.HasAt (b + 1) (linIntFuns (b + 1)) := h.block 1 rfl
  have hd : P.funs[b + 3]? = some (linIntDecodeF (b + 1)) := hi 2 (by simp [linIntFuns])
  have hb : P.funs[b + 1]? = some (linBitsDecodeF (b + 1)) := hi 0 (by simp [linIntFuns])
  have hs := linIntDecode_spec hd hb (x : ℤ)
  have dz := Det.call (Det.arg' (P := P) (vs := [.nat p, .nat q, encInt (x : ℤ)]) (rest := []) (j := 2) rfl) hs
  have dparts := Det.var' (P := P) (env := [a, linIntParts (x : ℤ)]) (i := 1) rfl
  have dx := Det.get' dparts (Det.nat 0) (v := .nat x) (by simp [linIntParts])
  have dq := Det.arg' (P := P) (vs := [.nat p, .nat q, encInt (x : ℤ)]) (rest := [linIntParts (x : ℤ)]) (j := 1) rfl
  have dp := Det.arg' (P := P) (vs := [.nat p, .nat q, encInt (x : ℤ)]) (rest := [linIntParts (x : ℤ)]) (j := 0) rfl
  have dd := Det.arith (op := .div) dx dq
  have dm := Det.arith (op := .mod) dd dp
  have wx : (encInt (x : ℤ)).wt < W := wt_le_wt_list (by simp [a, W])
  have wp : (Val.nat p).wt < W := wt_le_wt_list (by simp [a, W])
  have wq : (Val.nat q).wt < W := wt_le_wt_list (by simp [a, W])
  have wparts := hs.wt_lt.le
  have wc := linIntCodecCost_mono wx.le
  have wn : (Val.nat x).wt < (linIntParts (x : ℤ)).wt := wt_le_wt_list (by simp [linIntParts])
  have wd := linArithWt .div x q
  have wm := linArithWt .mod (x / q) p
  apply FunAll.intro ((h.block (gs := [linPrimaryDigitF (b + 3)]) 0 rfl).single)
  refine (Det.letE dz dm).post fun cost hc => ⟨?_, ?_⟩
  · simp only [GI.Machine.BinOp.eval_mod, GI.Machine.BinOp.eval_div, ZMod.val_natCast]
  · change cost ≤ linPrimaryDigitCost W
    unfold linPrimaryDigitCost
    dsimp only [W, a] at *
    simp only [GI.Machine.BinOp.eval_mod, GI.Machine.BinOp.eval_div] at *
    omega

theorem linPrimaryDigitCost_mono {W V : ℕ} (h : W ≤ V) :
    linPrimaryDigitCost W ≤ linPrimaryDigitCost V := by
  unfold linPrimaryDigitCost linIntCodecCost
  gcongr

theorem linPrimaryDigitCost_poly : PBU (fun _ W _ => linPrimaryDigitCost W) := by
  unfold linPrimaryDigitCost linIntCodecCost
  norm_poly

end GI.Impl
