module

public import Workspace.Impl.AggItemCfDMatrix

@[expose] public section

namespace GI.Impl

open GI.Algorithm GI.Lang GI.Cited
open GI.Machine (BinOp)

/-- On `[[V,q,a],b]`, the indicator that `b` lies in `a`'s color class. -/
def itCfDBlockCellF : Expr :=
  .arith .eq (.get (.get (arg 0) (.nat 0)) (arg 1))
    (.get (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 2)))

/-- On `[[[A,m],q,a],b]`, the pair-skeleton color. -/
def itCfDPairCellF (cf : ℕ) : Expr :=
  .call cf (mk4 (.get (.get (arg 0) (.nat 0)) (.nat 0))
    (.get (.get (arg 0) (.nat 0)) (.nat 1)) (.get (arg 0) (.nat 2)) (arg 1))

theorem itCfD_block_cell {P : Program} {f N : ℕ}
    (hf : P.funs[f]? = some itCfDBlockCellF) (V : List ℕ) (q : ℕ)
    (hlen : V.length = q) (a b : Fin q) (hV : (natList V).wt ≤ N) (hq : q ≤ N) :
    FunDet P f (.list [.list [natList V, .nat q, .nat a], .nat b])
      (.nat (if V.getD b 0 = V.getD a 0 then 1 else 0)) (10 ^ 12 * (N + 1) ^ 2) := by
  have ha : (a : ℕ) < V.length := by omega
  have hb : (b : ℕ) < V.length := by omega
  have hga : (V.map Val.nat)[(a : ℕ)]? = some (.nat (V.getD a 0)) := by
    rw [List.getElem?_map, List.getElem?_eq_getElem ha, List.getD_eq_getElem _ _ ha]; rfl
  have hgb : (V.map Val.nat)[(b : ℕ)]? = some (.nat (V.getD b 0)) := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hb, List.getD_eq_getElem _ _ hb]; rfl
  have wa : (Val.nat (V.getD a 0)).wt ≤ N :=
    (wt_le_wt_list (List.mem_of_getElem? hga)).le.trans hV
  have wb : (Val.nat (V.getD b 0)).wt ≤ N :=
    (wt_le_wt_list (List.mem_of_getElem? hgb)).le.trans hV
  have wna := wt_nat_le (a : ℕ)
  have wnb := wt_nat_le (b : ℕ)
  have wnq := wt_nat_le q
  have wc := wt_list3_le (natList V) (.nat q) (.nat a)
  have wi := wt_list2_le (.list [natList V, .nat q, .nat a]) (.nat b)
  have g0 := Det.arg' (P := P) (vs := [.list [natList V, .nat q, .nat a], .nat b])
    (rest := []) (j := 0) rfl
  have gv := Det.get' g0 (Det.nat 0) (v := natList V) rfl
  have ga := Det.get' g0 (Det.nat 2) (v := .nat a) rfl
  have gb := Det.arg' (P := P) (vs := [.list [natList V, .nat q, .nat a], .nat b])
    (rest := []) (j := 1) rfl
  have gr := Det.arith (Det.get' gv gb hgb) (Det.get' gv ga hga) (op := .eq)
  have he : BinOp.eval .eq (V.getD b 0) (V.getD a 0) =
      (if V.getD b 0 = V.getD a 0 then 1 else 0) := rfl
  rw [he] at gr
  have wr := wt_nat_le (if V.getD b 0 = V.getD a 0 then 1 else 0)
  have hr : (if V.getD b 0 = V.getD a 0 then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have hp : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  exact FunDet.intro hf (gr.mono (by omega))

theorem itCfD_pair_cell {P : Program} {f cf h N : ℕ}
    (hf : P.funs[f]? = some (itCfDPairCellF cf))
    (hcf : P.funs[cf]? = some (stDColF h)) (hh : P.HasAt h (stDHorFuns h))
    {dl tl : List ℕ} {q κ : ℕ} (hc : ItCfDCtx dl tl q κ) (m : ℕ) (a b : Fin q)
    (hN : (Val.list [stDA dl tl q κ, .nat m]).wt ≤ N) :
    FunDet P f (.list [.list [.list [stDA dl tl q κ, .nat m], .nat q, .nat a], .nat b])
      (.nat (stDCol dl tl q κ m a b)) (10 ^ 12 * (N + 1) ^ 2) := by
  set C : Val := .list [stDA dl tl q κ, .nat m]
  have wA : (stDA dl tl q κ).wt < C.wt := wt_le_wt_list (by simp [C])
  have wm : (Val.nat m).wt < C.wt := wt_le_wt_list (by simp [C])
  have hq : q < N := by have := hc.le_wt.2.2; change C.wt ≤ N at hN; omega
  have wna := wt_nat_le (a : ℕ)
  have wnb := wt_nat_le (b : ℕ)
  have wnq := wt_nat_le q
  have wc := wt_list3_le C (.nat q) (.nat a)
  have wi := wt_list2_le (.list [C, .nat q, .nat a]) (.nat b)
  have warg := wt_list4_le (stDA dl tl q κ) (.nat m) (.nat a) (.nat b)
  have wcol := itCfD_col_wt dl tl q κ m a b
  have wdl : (natList dl).wt < (stDA dl tl q κ).wt := wt_stDA_ge.2.2.1
  have harg : (stDCA dl tl q κ m a b).wt ≤ 8 * N + 16 := by
    unfold stDCA; change C.wt ≤ N at hN; omega
  have g0 := Det.arg' (P := P) (vs := [.list [C, .nat q, .nat a], .nat b])
    (rest := []) (j := 0) rfl
  have gC := Det.get' g0 (Det.nat 0) (v := C) rfl
  have gA := Det.get' gC (Det.nat 0) (v := stDA dl tl q κ) rfl
  have gm := Det.get' gC (Det.nat 1) (v := .nat m) rfl
  have ga := Det.get' g0 (Det.nat 2) (v := .nat a) rfl
  have gb := Det.arg' (P := P) (vs := [.list [C, .nat q, .nat a], .nat b])
    (rest := []) (j := 1) rfl
  have hcst := itCfD_col_spec hcf hh hc m a.isLt b.isLt
  have hcost : stDColK * ((stDCA dl tl q κ m a b).wt + 1) ^ 2 ≤
      578000000 * (N + 1) ^ 2 := by
    have hh := Nat.mul_le_mul_left stDColK
      (Nat.pow_le_pow_left (show (stDCA dl tl q κ m a b).wt + 1 ≤ 17 * (N + 1) by omega) 2)
    calc _ ≤ _ := hh
         _ = _ := by unfold stDColK; ring
  have hp : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  exact FunDet.intro hf ((Det.call (Det.mk4 gA gm ga gb) hcst).mono (by
    change C.wt ≤ N at hN
    omega))

/-- Read indicator rows, retaining the original vertex colors. -/
theorem itCfD_blocks_spec {P : Program} {f mb rb rw rm ce N : ℕ}
    (hf : P.funs[f]? = some (itCfRTableF mb rb))
    (hmb : P.HasAt mb (mapFuns mb rw)) (hrb : P.HasAt rb (rangeFuns rb))
    (hrw : P.funs[rw]? = some (itCfRRowF rm rb)) (hrm : P.HasAt rm (mapFuns rm ce))
    (hce : P.funs[ce]? = some itCfDBlockCellF)
    (V : List ℕ) (q : ℕ) (hlen : V.length = q) (hV : (natList V).wt ≤ N) (hq : q ≤ N) :
    FunDet P f (.list [natList V, .nat q]) (itCfDBlocks V q) (10 ^ 16 * (N + 1) ^ 4) := by
  have hm := itCfD_matrix_spec hf hmb hrb hrw hrm (natList V) q
    (fun a b : Fin q => if V.getD b 0 = V.getD a 0 then 1 else 0)
    (fun a b => itCfD_block_cell hce V q hlen a b hV hq) hV hq (by
      intro a b
      have hw := (natList V).two_le_size.trans (natList V).size_le_wt
      have hw4 : 4 ≤ (natList V).wt := by
        rw [natList, wt_list_eq]; omega
      have hpos : 0 < N := by omega
      have hlenw : q < (natList V).wt := by
        have := length_lt_wt_list (V.map Val.nat); simpa [natList, hlen] using this
      by_cases he : V.getD b 0 = V.getD a 0
      · simp only [if_pos he, wt_nat, GI.Machine.len_one]; omega
      · simp only [if_neg he, wt_nat, GI.Machine.len_zero]; omega)
  have he : Val.list ((List.finRange q).map fun a : Fin q => natList
      ((List.finRange q).map fun b : Fin q => if V.getD b 0 = V.getD a 0 then 1 else 0)) =
      itCfDBlocks V q := by
    simp only [itCfDBlocks, natList, ← List.map_coe_finRange_eq_range,
      List.map_map, Function.comp_def]
  rw [he] at hm
  have hqq : q * q ≤ 1 * (N + 1) ^ 2 := by
    simpa only [one_mul, pow_two] using
      (Nat.mul_le_mul (show q ≤ N + 1 by omega) (show q ≤ N + 1 by omega))
  have hprod := mul_pow_le (A := 1) (B := 10 ^ 12) (X := N + 1) (i := 2) (j := 2) hqq
    (show 10 ^ 12 * (N + 1) ^ 2 ≤ 10 ^ 12 * (N + 1) ^ 2 from le_rfl)
  change q * q * (10 ^ 12 * (N + 1) ^ 2) ≤ 10 ^ 12 * (N + 1) ^ 4 at hprod
  exact hm.mono (by omega)

/-- Read the pair-skeleton table, retaining every input color. -/
theorem itCfD_table_spec {P : Program} {f mb rb rw rm ce cf h N : ℕ}
    (hf : P.funs[f]? = some (itCfRTableF mb rb))
    (hmb : P.HasAt mb (mapFuns mb rw)) (hrb : P.HasAt rb (rangeFuns rb))
    (hrw : P.funs[rw]? = some (itCfRRowF rm rb)) (hrm : P.HasAt rm (mapFuns rm ce))
    (hce : P.funs[ce]? = some (itCfDPairCellF cf))
    (hcf : P.funs[cf]? = some (stDColF h)) (hh : P.HasAt h (stDHorFuns h))
    {dl tl : List ℕ} {q κ : ℕ} (hc : ItCfDCtx dl tl q κ) (m : ℕ)
    (hN : (Val.list [stDA dl tl q κ, .nat m]).wt ≤ N) :
    FunDet P f (.list [.list [stDA dl tl q κ, .nat m], .nat q])
      (itCfDTable dl tl q κ m) (10 ^ 16 * (N + 1) ^ 4) := by
  have wA : (stDA dl tl q κ).wt < (Val.list [stDA dl tl q κ, .nat m]).wt := wt_le_wt_list (by simp)
  have hq : q ≤ N := by have := hc.le_wt.2.2; omega
  have wdl : (natList dl).wt < (stDA dl tl q κ).wt := wt_stDA_ge.2.2.1
  have hm := itCfD_matrix_spec hf hmb hrb hrw hrm (.list [stDA dl tl q κ, .nat m]) q
    (fun a b : Fin q => stDCol dl tl q κ m a b)
    (fun a b => itCfD_pair_cell hce hcf hh hc m a b hN) hN hq (fun a b =>
      (itCfD_col_wt dl tl q κ m a b).trans (by omega))
  have he : Val.list ((List.finRange q).map fun a : Fin q => natList
      ((List.finRange q).map fun b : Fin q => stDCol dl tl q κ m a b)) =
      itCfDTable dl tl q κ m := by
    simp only [itCfDTable, natList, ← List.map_coe_finRange_eq_range,
      List.map_map, Function.comp_def]
  rw [he] at hm
  have hqq : q * q ≤ 1 * (N + 1) ^ 2 := by
    simpa only [one_mul, pow_two] using
      (Nat.mul_le_mul (show q ≤ N + 1 by omega) (show q ≤ N + 1 by omega))
  have hprod := mul_pow_le (A := 1) (B := 10 ^ 12) (X := N + 1) (i := 2) (j := 2) hqq
    (show 10 ^ 12 * (N + 1) ^ 2 ≤ 10 ^ 12 * (N + 1) ^ 2 from le_rfl)
  change q * q * (10 ^ 12 * (N + 1) ^ 2) ≤ 10 ^ 12 * (N + 1) ^ 4 at hprod
  exact hm.mono (by omega)

end GI.Impl
