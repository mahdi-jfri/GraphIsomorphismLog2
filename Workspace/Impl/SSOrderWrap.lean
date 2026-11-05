module

public import Workspace.Impl.SSOrderProg

@[expose] public section

/-!
# The order of a group

`ssOrdF` builds the table for the base `[0, …, n-1]` and multiplies, over the levels, one plus
the number of filled slots (`ssOrdF_spec`). By `ss_card_gens` this product is `|⟨gs⟩|`. The
program is `ssWrapProgram ssOrdFuns`, with `ssOrdF` at `60`.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-- On `encGroup gs`: the product `∏ (ssCnt T k + 1)` for the table `T` of `ssBuild`. -/
def ssOrdF (range start prod : ℕ) : Expr :=
  .letE (.get (.var 0) (.nat 0))
    (.letE (.call range (.var 1))
      (.letE (.call start (mk2 (.var 0) (.var 2)))
        (.call prod (mk3 (mk2 (.var 1) (.get (.var 3) (.nat 0))) (.var 1) (.nat 1)))))

/-- The functions of the order wrapper, from `52` on. -/
def ssOrdFuns : List Expr :=
  iterFuns 52 55 ++ ([ssProdStepF 56] ++ (iterFuns 56 59 ++ ([ssCntStepF] ++ [ssOrdF 47 50 52])))

/-- The parts of the order wrapper. -/
structure SsOrdAt (P : Program) : Prop where
  wrap : SsWrapAt P
  prodIt : P.HasAt 52 (iterFuns 52 55)
  prodSt : P.funs[55]? = some (ssProdStepF 56)
  cntIt : P.HasAt 56 (iterFuns 56 59)
  cntSt : P.funs[59]? = some ssCntStepF
  fn : P.funs[60]? = some (ssOrdF 47 50 52)

theorem ssOrdAt_of : SsOrdAt (ssWrapProgram ssOrdFuns) := by
  have h := ssWrap_extra ssOrdFuns
  unfold ssOrdFuns at h
  have h1 := h.right
  rw [show 52 + (iterFuns 52 55).length = 55 from rfl] at h1
  have h2 := h1.right
  rw [show 55 + [ssProdStepF 56].length = 56 from rfl] at h2
  have h3 := h2.right
  rw [show 56 + (iterFuns 56 59).length = 59 from rfl] at h3
  have h4 := h3.right
  rw [show 59 + [ssCntStepF].length = 60 from rfl] at h4
  exact ⟨ssWrapAt_of _, h.left, h1.left.single, h2.left, h3.left.single, h4.single⟩

theorem ss_ord_cost {X r s : ℕ} (hr : r ≤ 1000 * (X + 1) * (3 * X + 1))
    (hs : s ≤ 10 ^ 6 * (X + 1) ^ 3) :
    r + 2 * (10 ^ 8 * (X + 1) ^ 4) + s + 300 * (30 * X + 50 + 1) ≤
      4 * (10 ^ 8 * (X + 1) ^ 4) := by
  have h1 : (X + 1) * (3 * X + 1) ≤ 3 * (X + 1) ^ 2 := by nlinarith
  have h2 : (X + 1) ^ 2 ≤ (X + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h2' : (X + 1) ^ 3 ≤ (X + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h3 : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  rw [Nat.mul_assoc] at hr
  generalize (X + 1) * (3 * X + 1) = A at *
  generalize (X + 1) ^ 2 = Q2 at *
  generalize (X + 1) ^ 3 = Q3 at *
  generalize (X + 1) ^ 4 = Q4 at *
  linarith

theorem ss_nX {Y : ℕ} (h : n + 2 ≤ Y) : n * n + 3 * n + 3 ≤ ssW Y := by
  obtain ⟨-, -, -, hY3, hZ⟩ := ss_Y_facts (n := n) (L := 0) (G := 0) (by omega : n + 0 + 0 + 2 ≤ Y)
  have hZW := ssZ_le_ssW Y
  have e : n * n ≤ Y * Y := Nat.mul_le_mul (by omega) (by omega)
  have e3 : Y * Y ≤ Y ^ 3 := by
    rw [show Y ^ 3 = Y * Y * Y by ring]; exact Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- **The order.** -/
theorem ssOrdF_spec {P : Program} (hP : SsOrdAt P) (gs : List (Perm (Fin n))) :
    FunAll P 60 (encGroup gs) (fun v c => v = .nat (Nat.card (gens gs)) ∧
      c ≤ 10 * ssPolyK * ((encGroup gs).wt + 1) ^ 32) := by
  have hw := hP.wrap
  set w := (encGroup gs).wt with hwdef
  have hY : n + (List.finRange n).length + gs.length + 2 ≤ 3 * (w + 1) := by
    rw [List.length_finRange]; have := ss_encGroup_wt gs; omega
  set Y := 3 * (w + 1) with hYdef
  obtain ⟨hBw, hgw, hnW, hMW, hLW⟩ := ss_start_wts hY
  rw [ssEncB_finRange] at hBw
  have hst := ssStartF_spec hw.start hw.core hY
  rw [ssEncB_finRange] at hst
  obtain ⟨hinv, hcl, hgen⟩ := ssBuild_spec (B := List.finRange n) (gs := gs)
  have hsm := ssInv_small hinv hY
  have hsw := ss_st_wt hinv hY
  have hcard := ss_card_gens (fun i => List.mem_finRange i) hinv.wf hcl hinv.entry_mem hgen
  rw [List.length_finRange] at hcard
  have hG : (Val.list [.nat n, .list ((1 :: gs).map encPerm)]).wt ≤ ssW Y :=
    (ss_encGroup_small hY).wt_le_ssW
  have hYW := (ss_le_core (Y := Y) (by omega)).1
  have hnX := ss_nX (n := n) (Y := Y) (by rw [List.length_finRange] at hY; omega)
  generalize ssBuild (List.finRange n) gs = st at hst hinv hsm hsw hcard
  obtain ⟨T, prog⟩ := st
  have hlen : T.length = n * n := by rw [hinv.len, List.length_finRange]
  have hTw : (ssEncTab T).wt ≤ ssW Y := hsm.tab.wt_le_ssW
  have hprod := ssProdLoop_spec hP.prodIt hP.prodSt hP.cntIt hP.cntSt hlen hTw hnX
  set X := ssW Y with hX
  have hpw : (Val.nat (∏ i ∈ Finset.range n, (ssCnt T i + 1))).wt ≤ X :=
    (ss_prod_wt T le_rfl).trans hnX
  set W := 30 * X + 50 with hW
  clear_value W
  set a := Val.list [.nat n, .list ((1 :: gs).map encPerm)] with ha
  have haW : a.wt ≤ W := by omega
  have hnw : (Val.nat n).wt ≤ W := (wt_nat_le _).trans (by omega)
  have dn : StDC P [a] (.get (.var 0) (.nat 0)) (.nat n) 3 0 W :=
    StDC.get (x := 0) (v := .nat n) (StDC.var' rfl haW) (StDC.nat 0 (by omega)) rfl hnw
  have hrange : FunDet P 47 (.nat n) (natList (List.range n))
      (1000 * (X + 1) * (3 * X + 1)) :=
    (range_spec hw.range n).mono fun w c ⟨hw', hc⟩ => ⟨hw', hc.trans (by
      rw [hw']; unfold loopModK
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega))
        (by have := wt_nat_le n; omega))⟩
  have dR : StDC P [a, .nat n] (.call 47 (.var 1)) (natList (List.range n)) (1 + 1)
      (0 + 1000 * (X + 1) * (3 * X + 1)) W :=
    StDC.call (StDC.var' rfl hnw) hrange (by omega)
  have dS : StDC P [a, .nat n, natList (List.range n)] (.call 50 (mk2 (.var 0) (.var 2)))
      (ssEncSt (T, prog)) (1 + 1 + 3 + 1) (0 + 0 + 2 * ssCoreCost Y) W :=
    StDC.call (StDC.mk2 (StDC.var' rfl haW) (StDC.var' rfl (by omega))
      ((st_wt_list2 hG hBw).trans (by omega)) (by omega)) hst (by omega)
  set env3 := [a, .nat n, natList (List.range n), ssEncSt (T, prog)] with henv3
  have dT : StDC P env3 (.get (.var 3) (.nat 0)) (ssEncTab T) 3 0 W :=
    StDC.get (x := 0) (v := ssEncTab T)
      (StDC.var' (v := .list [ssEncTab T, ssEncProg prog]) rfl (by
        show (ssEncSt (T, prog)).wt ≤ W; omega)) (StDC.nat 0 (by omega)) rfl (by omega)
  have dV1 : StDC P env3 (.var 1) (.nat n) 1 0 W := StDC.var' rfl hnw
  have hnX' : (Val.nat n).wt ≤ X := (wt_nat_le n).trans (by omega)
  have h1X : (Val.nat 1).wt ≤ X := (wt_nat_le 1).trans (by omega)
  have hcX := st_wt_list2 hnX' hTw
  have dc := StDC.mk2 dV1 dT (hcX.trans (by omega)) (by omega)
  have hA : (Val.list [.list [.nat n, ssEncTab T], .nat n, .nat 1]).wt ≤ W :=
    (st_wt_list3 hcX ((hnX').trans (by omega)) (h1X.trans (by omega))).trans (by omega)
  have dPr := StDC.call (StDC.mk3 dc dV1 (StDC.nat 1 (by omega)) hA (by omega)) hprod
    (hpw.trans (by omega))
  refine FunAll.mono (StDC.funDet (c := 4 * ssCoreCost Y) hP.fn (StDC.letE dn (StDC.letE dR (StDC.letE dS dPr
    (hpw.trans (by omega))) (hpw.trans (by omega))) (hpw.trans (by omega))) (ss_cost_fin2 (by norm_num) ?_)) fun v c ⟨hv, hc⟩ =>
    ⟨by rw [hv, hcard], ss_wrap_cost ?_⟩
  · have := ss_ord_cost (X := X) (r := 1000 * (X + 1) * (3 * X + 1))
      (s := 10 ^ 6 * (X + 1) ^ 3) le_rfl le_rfl
    unfold ssCoreCost
    rw [hW]
    simp only [Nat.zero_add, Nat.add_zero]
    rw [← Nat.add_assoc]
    exact this
  · show c ≤ 100 * ssCoreCost Y
    have h4 : 4 * ssCoreCost Y ≤ 100 * ssCoreCost Y := Nat.mul_le_mul_right _ (by norm_num)
    exact hc.trans h4

end GI.Impl
