import Workspace.Impl.AggItemCfDV

namespace GI.Impl

open GI.Algorithm GI.Lang GI.Cited
open GI.Machine (BinOp)

def itCfDDomK : ℕ := 10 ^ 12

theorem itCfD_ctxV_wt {V : List ℕ} {q B : ℕ} (hV : (natList V).wt ≤ B)
    (_hl : V.length = q) (hq : q ≤ B) :
    (Val.list [natList V, .nat q]).wt ≤ 20 * (B + 1) ^ 2 := by
  have := wt_list2_le (natList V) (.nat q)
  have := wt_nat_le q
  have : B + 1 ≤ (B + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  omega

theorem itCfD_domV_spec {P : Program} {f cb : ℕ} (hf : P.funs[f]? = some (stDDomVF cb))
    (hcb : P.HasAt cb (countFuns cb)) {V : List ℕ} {q B : ℕ} (hV : (natList V).wt ≤ B)
    (hl : V.length = q) (hq : q ≤ B) {j : ℕ} (hj : (Val.nat j).wt ≤ B) :
    FunDet P f (.list [.list [natList V, .nat q], .nat j]) (boolVal (stDDomV V q j))
      (itCfDDomK * (B + 1) ^ 3) := by
  have hc := itCfD_ctxV_wt hV hl hq
  have hVc : (natList V).wt < (Val.list [natList V, .nat q]).wt := wt_le_wt_list (by simp)
  have hqc : (Val.nat q).wt < (Val.list [natList V, .nat q]).wt := wt_le_wt_list (by simp)
  have hX : B + 1 ≤ (B + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hX3 : (B + 1) ^ 2 ≤ (B + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hca : (Val.list [.nat j, natList V]).wt ≤ 4 * B + 10 := by
    have := wt_list2_le (.nat j) (natList V); omega
  have hcnt0 := itCfD_count_spec hcb V j hca
  have hcnt : FunDet P cb (.list [.nat j, natList V]) (.nat (V.count j))
      (10 ^ 10 * (B + 1) ^ 3) := hcnt0.mono (by
    have hh := Nat.mul_le_mul_left (10 ^ 6)
      (Nat.pow_le_pow_left (show 4 * B + 10 + 1 ≤ 11 * (B + 1) by omega) 3)
    have he : 10 ^ 6 * (11 * (B + 1)) ^ 3 = 1331000000 * (B + 1) ^ 3 := by ring
    calc _ ≤ _ := hh
         _ = _ := he
         _ ≤ _ := Nat.mul_le_mul_right _ (by norm_num))
  have hcle : V.count j ≤ B := (List.count_le_length).trans (by omega)
  set W := 100 * (B + 1) ^ 2 + 10 with hW
  have hjw := hj
  have hvs : (Val.list [.list [natList V, .nat q], .nat j]).wt ≤ W := by
    have := wt_list2_le (.list [natList V, .nat q]) (.nat j); omega
  have g0 : StDC P [.list [.list [natList V, .nat q], .nat j]] (arg 0)
      (.list [natList V, .nat q]) 3 0 W := StDC.arg rfl hvs (by omega) (by omega)
  have g1 : StDC P [.list [.list [natList V, .nat q], .nat j]] (arg 1) (.nat j) 3 0 W :=
    StDC.arg rfl hvs (by omega) (by omega)
  have gV := StDC.get (v := natList V) g0 (StDC.nat 0 (by omega)) rfl (by omega)
  have gq := StDC.get (v := .nat q) g0 (StDC.nat 1 (by omega)) rfl (by omega)
  have g2 := StDC.mk2 g1 gV (by have := wt_list2_le (.nat j) (natList V); omega) (by omega)
  have gc := StDC.call g2 hcnt (by have := wt_nat_le (V.count j); omega)
  have g3q := StDC.arith' (StDC.nat 3 (by omega)) gq (op := .mul)
    (show BinOp.eval .mul 3 q = 3 * q from rfl) (by omega)
  have g4c := StDC.arith' (StDC.nat 4 (by omega)) gc (op := .mul)
    (show BinOp.eval .mul 4 (V.count j) = 4 * V.count j from rfl) (by omega)
  have g4c1 := StDC.arith' g4c (StDC.nat 1 (by omega)) (op := .add)
    (show BinOp.eval .add (4 * V.count j) 1 = 4 * V.count j + 1 from rfl) (by omega)
  have gr := StDC.arith' g3q g4c1 (op := .lt) (st_lt_toNat _ _) (by
    have : (decide (3 * q ≤ 4 * V.count j)).toNat ≤ 1 := Bool.toNat_le _; omega)
  refine StDC.funDet hf gr ?_
  unfold itCfDDomK

  generalize (B + 1) ^ 3 = Y at *
  generalize (B + 1) ^ 2 = X at *
  omega

theorem itCfD_dom_spec {P : Program} {f dv cb : ℕ} (hf : P.funs[f]? = some (stDDomF dv))
    (hdv : P.funs[dv]? = some (stDDomVF cb))
    (hcb : P.HasAt cb (countFuns cb)) {V : List ℕ} {q B : ℕ} (hV : (natList V).wt ≤ B)
    (hl : V.length = q) (hq : q ≤ B) {z : ℕ} (hz : z < q) :
    FunDet P f (.list [.list [natList V, .nat q], .nat z]) (boolVal (stDDom V q z))
      (2 * itCfDDomK * (B + 1) ^ 3) := by
  have hc := itCfD_ctxV_wt hV hl hq
  have hVc : (natList V).wt < (Val.list [natList V, .nat q]).wt := wt_le_wt_list (by simp)
  have hqc : (Val.nat q).wt < (Val.list [natList V, .nat q]).wt := wt_le_wt_list (by simp)
  have hX : B + 1 ≤ (B + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hX3 : (B + 1) ^ 2 ≤ (B + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hzl : z < V.length := by omega
  have hjB : (Val.nat (V.getD z 0)).wt ≤ B := by
    rw [List.getD_eq_getElem _ _ hzl]
    exact (wt_le_wt_list (vs := V.map Val.nat)
      (List.mem_map.2 ⟨V[z], List.getElem_mem hzl, rfl⟩)).le.trans hV
  have hd := itCfD_domV_spec hdv hcb hV hl hq hjB
  set W := 100 * (B + 1) ^ 2 + 10 with hW
  have hzw := wt_nat_le z
  have hjw := hjB
  have hvs : (Val.list [.list [natList V, .nat q], .nat z]).wt ≤ W := by
    have := wt_list2_le (.list [natList V, .nat q]) (.nat z); omega
  have g0 : StDC P [.list [.list [natList V, .nat q], .nat z]] (arg 0)
      (.list [natList V, .nat q]) 3 0 W := StDC.arg rfl hvs (by omega) (by omega)
  have g1 : StDC P [.list [.list [natList V, .nat q], .nat z]] (arg 1) (.nat z) 3 0 W :=
    StDC.arg rfl hvs (by omega) (by omega)
  have gV := StDC.get (v := natList V) g0 (StDC.nat 0 (by omega)) rfl (by omega)
  have gj := StDC.get (v := .nat (V.getD z 0)) gV g1
    (by simp [List.getElem?_eq_getElem hzl]) (by omega)
  have g2 := StDC.mk2 g0 gj (by
    have := wt_list2_le (.list [natList V, .nat q]) (.nat (V.getD z 0)); omega) (by omega)
  have gc := StDC.call g2 hd (by have := wt_boolVal_le (stDDomV V q (V.getD z 0)); omega)
  refine StDC.funDet hf gc ?_
  unfold itCfDDomK
  generalize (B + 1) ^ 3 = Y at *
  generalize (B + 1) ^ 2 = X at *
  omega

end GI.Impl
