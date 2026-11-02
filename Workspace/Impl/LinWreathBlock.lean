import Workspace.Impl.LinWreathBlockFormula
import Workspace.Impl.AggStructDC

namespace GI.Impl
open GI.Cited GI.Lang Equiv

private theorem linWreathBlock_ite {P : Program} {env : List Val} {c t e : Expr}
    {x nc nt ne T : ℕ} {a b : Val}
    (hc : StDC P env c (.nat x) nc 0 T)
    (ht : StDC P env t a nt 0 T) (he : StDC P env e b ne 0 T)
    (ha : a.wt ≤ T) (hb : b.wt ≤ T) :
    StDC P env (.ite c t e) (if x = 0 then b else a) (nc + nt + ne + 1) 0 T := by
  refine (Det.ite' hc.det ht.det he.det).mono ?_
  have hh : max a.wt b.wt ≤ T := max_le ha hb
  simp only [Nat.add_zero, Nat.add_mul, Nat.one_mul]
  omega

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
theorem linWreathBlockCell_spec {P : Program} {f p d : ℕ}
    (hf : P.funs[f]? = some linWreathBlockCellF) (hp : p.Prime) (hd : 0 < d)
    (A : Matrix (Fin d) (Fin d) (ZMod p)) (mode : Fin 3) (i j : Fin (d + d)) :
    FunDet P f (.list [.list [encModMatrix A, .nat mode, .nat i], .nat j])
      (.nat (linWreathBlock hd A mode i j).val)
      (100000 * ((Val.list [.list [encModMatrix A, .nat mode, .nat i], .nat j]).wt + d + 1)) := by
  let x : Fin d := ⟨i.val % d, Nat.mod_lt _ hd⟩
  let y : Fin d := ⟨j.val % d, Nat.mod_lt _ hd⟩
  let c := Val.list [encModMatrix A, .nat mode, .nat i]
  let v := Val.list [c, .nat j]
  let W := v.wt
  let T := 100 * (W + d + 1)
  have wc : c.wt < W := wt_le_wt_list (by simp [W, v])
  have wa : (encModMatrix A).wt < c.wt := wt_le_wt_list (by simp [c])
  have wr : (encVec (A x)).wt < (encModMatrix A).wt :=
    wt_le_wt_list (by simp [encModMatrix])
  have we : (Val.nat (A x y).val).wt < (encVec (A x)).wt :=
    wt_le_wt_list (by simp [encVec])
  have hi := i.isLt
  have hj := j.isLt
  have hm := mode.isLt
  have hT : 10 + W + 3 * d ≤ T := by dsimp [T]; omega
  have wv : v.wt ≤ T := by change W ≤ T; omega
  have wctx : c.wt ≤ T := by omega
  have wmat : (encModMatrix A).wt ≤ T := by omega
  have wrow : (encVec (A x)).wt ≤ T := by omega
  have wcell : (Val.nat (A x y).val).wt ≤ T := by omega
  have wn (k : ℕ) (hk : k ≤ 2 * d + 2) : (Val.nat k).wt ≤ T :=
    (wt_nat_le k).trans (by omega)
  have wlt (a b : ℕ) : (Val.nat (GI.Machine.BinOp.lt.eval a b)).wt ≤ T := by
    dsimp [GI.Machine.BinOp.eval]; split_ifs <;> exact wn _ (by omega)
  have weq (a b : ℕ) : (Val.nat (GI.Machine.BinOp.eq.eval a b)).wt ≤ T := by
    dsimp [GI.Machine.BinOp.eval]; split_ifs <;> exact wn _ (by omega)
  have dc := StDC.arg (P := P) (vs := [c, .nat j]) (rest := []) (j := 0) rfl wv (by omega) wctx
  have dj := StDC.arg (P := P) (vs := [c, .nat j]) (rest := []) (j := 1) rfl wv (by omega)
    (wn j (by omega))
  have da := StDC.get dc (StDC.nat 0 (by omega)) rfl wmat
  have dm := StDC.get dc (StDC.nat 1 (by omega)) rfl (wn mode (by omega))
  have di := StDC.get dc (StDC.nat 2 (by omega)) rfl (wn i (by omega))
  have dn := StDC.length da (by simp [encModMatrix]; omega)
  simp only [List.length_map, List.length_finRange] at dn
  have dx := StDC.arith (op := .mod) di dn rfl (wn (i.val % d) (by have := Nat.mod_lt i.val hd; omega))
  have dy := StDC.arith (op := .mod) dj dn rfl (wn (j.val % d) (by have := Nat.mod_lt j.val hd; omega))
  simp only [GI.Machine.BinOp.eval_mod] at dx dy
  have dr := StDC.get da dx (v := encVec (A x))
    (by simp [encModMatrix, List.getElem?_eq_getElem, Nat.mod_lt _ hd, x]) wrow
  have de := StDC.get dr dy (v := .nat (A x y).val)
    (by simp [encVec, List.getElem?_eq_getElem, Nat.mod_lt _ hd, y]) wcell
  have dli := StDC.arith (op := .lt) di dn rfl (wlt i d)
  have dlj := StDC.arith (op := .lt) dj dn rfl (wlt j d)
  have ds := StDC.arith (op := .eq) dli dlj rfl (weq _ _)
  have dzm := StDC.arith (op := .eq) dm (StDC.nat 0 (by omega)) rfl (weq _ _)
  have dt := StDC.arith (op := .eq) dli dzm rfl (weq _ _)
  have du := StDC.arith (op := .eq) dx dy rfl (weq _ _)
  have dlm := StDC.arith (op := .lt) dm (StDC.nat 2 (by omega)) rfl (wlt mode 2)
  have duwt := weq (i.val % d) (j.val % d)
  have dit := linWreathBlock_ite dt de du wcell duwt
  have wit : (if GI.Machine.BinOp.eq.eval (GI.Machine.BinOp.lt.eval i.val d)
      (GI.Machine.BinOp.eq.eval mode.val 0) = 0 then
        Val.nat (GI.Machine.BinOp.eq.eval (i.val % d) (j.val % d)) else
        Val.nat (A x y).val).wt ≤ T := by split_ifs <;> assumption
  have dz := StDC.nat (P := P) (env := [v]) 0 (by omega : 0 + 2 ≤ T)
  have dfirst := linWreathBlock_ite ds dit dz wit (wn 0 (by omega))
  have dsecond := linWreathBlock_ite ds dz du (wn 0 (by omega)) duwt
  have wfirst : (if GI.Machine.BinOp.eq.eval (GI.Machine.BinOp.lt.eval i.val d)
      (GI.Machine.BinOp.lt.eval j.val d) = 0 then Val.nat 0 else
      (if GI.Machine.BinOp.eq.eval (GI.Machine.BinOp.lt.eval i.val d)
        (GI.Machine.BinOp.eq.eval mode.val 0) = 0 then
          Val.nat (GI.Machine.BinOp.eq.eval (i.val % d) (j.val % d)) else
          Val.nat (A x y).val)).wt ≤ T := by split_ifs <;> first | assumption | exact wn 0 (by omega)
  have wsecond : (if GI.Machine.BinOp.eq.eval (GI.Machine.BinOp.lt.eval i.val d)
      (GI.Machine.BinOp.lt.eval j.val d) = 0 then
        Val.nat (GI.Machine.BinOp.eq.eval (i.val % d) (j.val % d)) else Val.nat 0).wt ≤ T := by
    split_ifs <;> first | assumption | exact wn 0 (by omega)
  have hh := linWreathBlock_ite dlm dfirst dsecond wfirst wsecond
  apply FunAll.intro hf
  refine hh.det.post fun cost hc => ⟨?_, ?_⟩
  · exact linWreathBlock_formula hp hd A mode i j
  · change cost ≤ 100000 * (W + d + 1)
    norm_num only [Nat.reduceAdd] at hc
    dsimp only [T] at hc
    omega

end GI.Impl
