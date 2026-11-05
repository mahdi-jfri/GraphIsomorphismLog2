module

public import Workspace.Impl.LinIntSlp

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

/-- Input [generator-vectors,instructions,zero-vector]. The empty SLP is zero. -/
def linSlpValueF (table : ℕ) : Expr :=
  .letE (.call table (mk2 (arg 0) (arg 1)))
    (.ite (.length (.var 1))
      (.get (.var 1) (.arith .sub (.length (.var 1)) (.nat 1))) (arg 2))

def linSlpValueCost (W L t : ℕ) : ℕ :=
  1000 * (W + L + linSlpCost (10 * (W + 1)) L t + 1)

theorem linSlpCost_mono {W V : ℕ} (h : W ≤ V) (L t : ℕ) :
    linSlpCost W L t ≤ linSlpCost V L t := by
  have hs := linSlpStepCost_mono (show linSlpStepArg W L t ≤ linSlpStepArg V L t by
    unfold linSlpStepArg; omega) t
  unfold linSlpCost linSlpLoopStepCost
  gcongr

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
theorem linSlpValue_spec {P : Program} {f table step add scale ib t : ℕ}
    (hf : P.funs[f]? = some (linSlpValueF table))
    (hp : P.HasAt table (linSlpFuns table step))
    (hstep : P.funs[step]? = some (linSlpStepF add scale)) (hi : linIntSpec P ib)
    (ha : P.HasAt add (linVectorBinaryFuns add (ib + 11)))
    (hs : P.HasAt scale (linVectorScaleFuns scale ib))
    (gs : List (Multiplicative (Fin t → ℤ))) (hg : ∀ v ∈ gs, linExponentBound 1 v)
    (prog : List SlpInstr) (es : List (Multiplicative (Fin t → ℤ)))
    (he : linSlpEntries gs prog [] = some es) :
    FunDet P f (.list [linSlpTable gs, .list (prog.map encSlpInstr), linVecVal (0 : Fin t → ℤ)])
      (linVecVal (Multiplicative.toAdd (es.getLast?.getD 1)))
      (linSlpValueCost (Val.list [linSlpTable gs, .list (prog.map encSlpInstr), linVecVal (0 : Fin t → ℤ)]).wt prog.length t) := by
  let a := Val.list [linSlpTable gs, .list (prog.map encSlpInstr), linVecVal (0 : Fin t → ℤ)]
  let W := a.wt
  have wg : (linSlpTable gs).wt < W := wt_le_wt_list (by simp)
  have wp : (Val.list (prog.map encSlpInstr)).wt < W := wt_le_wt_list (by simp)
  have wz : (linVecVal (0 : Fin t → ℤ)).wt < W := wt_le_wt_list (by simp)
  have wi := wt_list2_le (linSlpTable gs) (.list (prog.map encSlpInstr))
  have win : (Val.list [linSlpTable gs, .list (prog.map encSlpInstr)]).wt ≤ 10 * (W + 1) := by omega
  have ht := (linSlp_spec hp hstep hi ha hs gs hg prog es he).mono (linSlpCost_mono win prog.length t)
  have wt := ht.wt_lt.le
  have hl := linSlpEntries_length gs prog [] es he
  simp only [List.length_nil, Nat.zero_add] at hl
  have darg (j : ℕ) (rest : List Val) {v : Val}
      (hv : [linSlpTable gs, .list (prog.map encSlpInstr), linVecVal (0 : Fin t → ℤ)][j]? = some v) :=
    Det.arg' (P := P) (vs := [linSlpTable gs, .list (prog.map encSlpInstr), linVecVal (0 : Fin t → ℤ)])
      (rest := rest) (j := j) hv
  have dc := Det.call (Det.mk2 (darg 0 [] rfl) (darg 1 [] rfl)) ht
  have dv := Det.var' (P := P) (env := [a, linSlpTable es]) (i := 1) rfl
  have dl := Det.length dv
  simp only [List.length_map] at dl
  cases es using List.reverseRecOn with
  | nil =>
    have db := Det.ite_zero (t := .get (.var 1) (.arith .sub (.length (.var 1)) (.nat 1))) dl (darg 2 [linSlpTable []] rfl)
    apply FunDet.intro hf
    refine (Det.letE dc db).mono ?_
    unfold linSlpValueCost
    simp only [W, a, linSlpTable, List.map_nil] at *
    omega
  | append_singleton es x =>
    have dlen := Det.length dv
    simp only [List.length_map, List.length_append, List.length_singleton] at dlen
    have didx := Det.arith (op := .sub) dlen (Det.nat 1)
    have heq : GI.Machine.BinOp.eval .sub (es.length + 1) 1 = es.length := by simp
    rw [heq] at didx
    have dout := Det.get' dv didx (show
      ((es ++ [x]).map fun v => linVecVal (Multiplicative.toAdd v))[es.length]? =
        some (linVecVal (Multiplicative.toAdd x)) by simp)
    have db := Det.ite_pos (e := arg 2) dlen (by omega : es.length + 1 ≠ 0) dout
    have wx : (linVecVal (Multiplicative.toAdd x)).wt < (linSlpTable (es ++ [x])).wt :=
      wt_le_wt_list (by simp [linSlpTable])
    have wn := wt_nat_le (es.length + 1)
    have wo := wt_nat_le es.length
    have hlast : (es ++ [x]).getLast?.getD (1 : Multiplicative (Fin t → ℤ)) = x := by simp
    rw [hlast]
    apply FunDet.intro hf
    refine (Det.letE dc db).mono ?_
    unfold linSlpValueCost
    simp only [W, a, linSlpTable, List.length_append, List.length_singleton] at *
    omega

end GI.Impl
