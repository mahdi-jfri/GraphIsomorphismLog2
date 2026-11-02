import Workspace.Impl.AggItemCfRMath
import Workspace.Impl.AggStructDesV
import Workspace.Lang.Lib.OrbitT
import Workspace.Lang.Lib.Tabulate

set_option maxRecDepth 10000

namespace GI.Impl

open GI.Algorithm GI.Lang GI.Cited Equiv
open GI.Machine (BinOp)

/-- On `[[table,q,a],b]`, read the color at the binary tuple `(a,b)`. -/
def itCfRCellF : Expr :=
  .get (.get (arg 0) (.nat 0))
    (.arith .add (.get (arg 0) (.nat 2))
      (.arith .mul (.get (arg 0) (.nat 1)) (arg 1)))

/-- On `[[table,q],a]`, tabulate row `a`. -/
def itCfRRowF (mb rb : ℕ) : Expr :=
  .call mb (mk2 (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (arg 1))
    (.call rb (.get (arg 0) (.nat 1))))

/-- On `[table,q]`, tabulate the rows. -/
def itCfRTableF (mb rb : ℕ) : Expr :=
  .call mb (mk2 (.var 0) (.call rb (arg 1)))

/-- The weight of a table entry, without any bound on the numeric color. -/
theorem itCfRColor_wt {dl : List ℕ} {q a b : ℕ} (hlen : dl.length = q * q)
    (ha : a < q) (hb : b < q) :
    (Val.nat (itCfRColor dl q a b)).wt ≤ (natList dl).wt := by
  have hi : a + q * b < dl.length := by
    rw [hlen, Nat.add_comm a, Nat.mul_comm q b]
    exact st_pair_lt hb ha
  unfold itCfRColor
  rw [List.getD_eq_getElem _ _ hi]
  exact (wt_le_wt_list (vs := dl.map Val.nat)
    (List.mem_map.2 ⟨dl[a + q * b], List.getElem_mem hi, rfl⟩)).le

theorem itCfR_cell_spec {P : Program} {f : ℕ}
    (hf : P.funs[f]? = some itCfRCellF) (dl : List ℕ) (q a b : ℕ)
    (hlen : dl.length = q * q) (ha : a < q) (hb : b < q) :
    FunDet P f (.list [.list [natList dl, .nat q, .nat a], .nat b])
      (.nat (itCfRColor dl q a b)) (1000 * ((natList dl).wt + q + 10)) := by
  have hi : a + q * b < dl.length := by
    rw [hlen, Nat.add_comm a, Nat.mul_comm q b]
    exact st_pair_lt hb ha
  have hlenw : dl.length < (natList dl).wt := by
    have := length_lt_wt_list (dl.map Val.nat)
    simpa [natList] using this
  have hcolw := itCfRColor_wt hlen ha hb
  have hidxw := wt_nat_le (a + q * b)
  have hmulw := wt_nat_le (q * b)
  have hprod : q * b ≤ a + q * b := Nat.le_add_left _ _
  have hqw := wt_nat_le q
  have haw := wt_nat_le a
  have hbw := wt_nat_le b
  have hc := wt_list3_le (natList dl) (.nat q) (.nat a)
  have hiw := wt_list2_le (.list [natList dl, .nat q, .nat a]) (.nat b)
  have g0 := Det.arg' (P := P) (vs := [.list [natList dl, .nat q, .nat a], .nat b])
    (rest := []) (j := 0) rfl
  have g1 := Det.arg' (P := P) (vs := [.list [natList dl, .nat q, .nat a], .nat b])
    (rest := []) (j := 1) rfl
  have gdl := Det.get' g0 (Det.nat 0) (v := natList dl) rfl
  have gq := Det.get' g0 (Det.nat 1) (v := .nat q) rfl
  have ga := Det.get' g0 (Det.nat 2) (v := .nat a) rfl
  have gp := Det.arith' gq g1 (op := .mul) (z := q * b) rfl
  have gi := Det.arith' ga gp (op := .add) (z := a + q * b) rfl
  have he : (dl.map Val.nat)[a + q * b]? = some (.nat (itCfRColor dl q a b)) := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hi]
    simp only [itCfRColor, List.getD_eq_getElem _ _ hi, Option.map_some]
  exact FunDet.intro hf ((Det.get' gdl gi he).mono (by omega))

/-- A row of the binary table. -/
def itCfRRow (dl : List ℕ) (q a : ℕ) : Val :=
  natList ((List.range q).map fun b => itCfRColor dl q a b)

theorem itCfRRow_wt {dl : List ℕ} {q a : ℕ} (hlen : dl.length = q * q) (ha : a < q) :
    (itCfRRow dl q a).wt ≤ q * (2 * (natList dl).wt + 1) + 4 := by
  unfold itCfRRow natList
  have h := wt_list_le_of (((List.range q).map fun b => itCfRColor dl q a b).map Val.nat)
    (c := (natList dl).wt) (by
      intro v hv
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
      exact itCfRColor_wt hlen ha (List.mem_range.1 hb))
  simpa only [List.length_map, List.length_range] using h

/-- Tabulate a row with a bound in weights, allowing arbitrary color values. -/
theorem itCfR_row_spec {P : Program} {f mb rb ce : ℕ}
    (hf : P.funs[f]? = some (itCfRRowF mb rb))
    (hmb : P.HasAt mb (mapFuns mb ce)) (hrb : P.HasAt rb (rangeFuns rb))
    (hce : P.funs[ce]? = some itCfRCellF) (dl : List ℕ) (q a : ℕ)
    (hlen : dl.length = q * q) (ha : a < q) {N : ℕ}
    (hdw : (natList dl).wt ≤ N) (hqw : q ≤ N) :
    FunDet P f (.list [.list [natList dl, .nat q], .nat a]) (itCfRRow dl q a)
      (10 ^ 8 * (N + 1) ^ 3) := by
  set ctx : Val := .list [natList dl, .nat q, .nat a]
  set inp : Val := .list [.list [natList dl, .nat q], .nat a]
  have hwq := wt_nat_le q
  have hwa := wt_nat_le a
  have hwc := wt_list3_le (natList dl) (.nat q) (.nat a)
  have hwi := wt_list2_le (.list [natList dl, .nat q]) (.nat a)
  have hwdq := wt_list2_le (natList dl) (.nat q)
  have hcw : ctx.wt ≤ 10 * (N + 1) := by dsimp [ctx]; omega
  have hiw : inp.wt ≤ 20 * (N + 1) := by dsimp [inp]; omega
  have hrow := itCfRRow_wt hlen ha
  have hroww : (itCfRRow dl q a).wt ≤ 5 * (N + 1) ^ 2 := by
    have := Nat.mul_le_mul hqw (show 2 * (natList dl).wt + 1 ≤ 2 * N + 1 by omega)
    nlinarith
  have hrw : (encFun fun i : Fin q => (i : ℕ)).wt ≤ 4 * (N + 1) ^ 2 :=
    (wt_ids_le q).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have hargw : (Val.list [ctx, encFun fun i : Fin q => (i : ℕ)]).wt ≤ 40 * (N + 1) ^ 2 := by
    have := wt_list2_le ctx (encFun fun i : Fin q => (i : ℕ))
    have : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have htab := tabulate_spec hmb (c := ctx)
    (F := fun b : Fin q => Val.nat (itCfRColor dl q a b)) (B := 10000 * (N + 1))
    (fun b => (itCfR_cell_spec hce dl q a b hlen ha b.isLt).mono (by omega))
  have hid : (encFun fun i : Fin q => (i : ℕ)) = natList (List.range q) := by
    rw [encFun_eq_natList, List.map_coe_finRange_eq_range]
  have hout : (Val.list ((List.finRange q).map fun b : Fin q => Val.nat (itCfRColor dl q a b))) =
      itCfRRow dl q a := by
    unfold itCfRRow natList
    rw [← List.map_coe_finRange_eq_range]
    simp only [List.map_map, Function.comp_def]
  rw [hout] at htab
  have htab' : FunDet P mb (.list [ctx, encFun fun i : Fin q => (i : ℕ)])
      (itCfRRow dl q a) (10 ^ 6 * (N + 1) ^ 3) := htab.mono (by
    have h1 := Nat.mul_le_mul hqw (show 10000 * (N + 1) ≤ 10000 * (N + 1) from le_rfl)
    have h2 := Nat.mul_le_mul (Nat.mul_le_mul_left mapK (show q + 1 ≤ N + 1 by omega))
      (show (Val.list [ctx, encFun fun i : Fin q => (i : ℕ)]).wt +
        (itCfRRow dl q a).wt + 1 ≤ 56 * (N + 1) ^ 2 by
          have := Nat.one_le_pow 2 (N + 1) (by omega); omega)
    have he : mapK * (N + 1) * (56 * (N + 1) ^ 2) = 56000 * (N + 1) ^ 3 := by
      unfold mapK; ring
    have hp := Nat.pow_le_pow_right (show 0 < N + 1 by omega) (by norm_num : 2 ≤ (3 : ℕ))
    have he1 : N * (10000 * (N + 1)) ≤ 10000 * (N + 1) ^ 2 := by nlinarith
    calc
      _ ≤ 10000 * (N + 1) ^ 2 + 56000 * (N + 1) ^ 3 :=
        Nat.add_le_add (h1.trans he1) (h2.trans_eq he)
      _ ≤ 10000 * (N + 1) ^ 3 + 56000 * (N + 1) ^ 3 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hp) _
      _ = 66000 * (N + 1) ^ 3 := by ring
      _ ≤ 10 ^ 6 * (N + 1) ^ 3 := Nat.mul_le_mul_right _ (by norm_num))
  have hrg : FunDet P rb (.nat q) (encFun fun i : Fin q => (i : ℕ))
      (10000 * (q + 1) ^ 3) := hid.symm ▸ st_range_det hrb q
  set W := 100 * (N + 1) ^ 2
  have hn2 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hW5 : 5 ≤ W := by
    have := Nat.one_le_pow 2 (N + 1) (by omega); dsimp [W]; omega
  have g0 : StDC P [inp] (arg 0) (.list [natList dl, .nat q]) 3 0 W :=
    StDC.arg rfl (by dsimp [W]; omega) (by dsimp [W]; omega) (by omega)
  have gd := StDC.get g0 (StDC.nat 0 (by omega)) (v := natList dl) rfl (by dsimp [W]; omega)
  have gq := StDC.get g0 (StDC.nat 1 (by omega)) (v := .nat q) rfl (by dsimp [W]; omega)
  have ga : StDC P [inp] (arg 1) (.nat a) 3 0 W :=
    StDC.arg rfl (by dsimp [W]; omega) (by dsimp [W]; omega) (by omega)
  have gc := StDC.mk3 gd gq ga (by show ctx.wt ≤ W; dsimp [W]; omega) (by omega)
  have gr := StDC.call gq hrg (by dsimp [W]; omega)
  have gt := StDC.call (StDC.mk2 gc gr (by show (Val.list [ctx, encFun fun i : Fin q => (i : ℕ)]).wt ≤ W; dsimp [W]; omega) (by omega)) htab'
    (by dsimp [W]; omega)
  refine StDC.funDet hf gt ?_
  have hp := Nat.pow_le_pow_right (show 0 < N + 1 by omega) (by norm_num : 2 ≤ (3 : ℕ))
  have hq3 := Nat.pow_le_pow_left (show q + 1 ≤ N + 1 by omega) 3
  have h13 : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  dsimp [W]
  omega

/-- Reading all rows costs a polynomial in the weight of the supplied table. -/
theorem itCfR_table_spec {P : Program} {f mb rb rw rm ce : ℕ}
    (hf : P.funs[f]? = some (itCfRTableF mb rb))
    (hmb : P.HasAt mb (mapFuns mb rw)) (hrb : P.HasAt rb (rangeFuns rb))
    (hrw : P.funs[rw]? = some (itCfRRowF rm rb))
    (hrm : P.HasAt rm (mapFuns rm ce)) (hce : P.funs[ce]? = some itCfRCellF)
    (dl : List ℕ) (q : ℕ) (hlen : dl.length = q * q) {N : ℕ}
    (hdw : (natList dl).wt ≤ N) (hqw : q ≤ N) :
    FunDet P f (.list [natList dl, .nat q]) (itCfRTable dl q)
      (10 ^ 10 * (N + 1) ^ 4) := by
  set inp : Val := .list [natList dl, .nat q]
  have hwq := wt_nat_le q
  have hwi := wt_list2_le (natList dl) (.nat q)
  have hiw : inp.wt ≤ 10 * (N + 1) := by dsimp [inp]; omega
  have hn2 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hp23 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h13 : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hroww : ∀ a, a < q → (itCfRRow dl q a).wt ≤ 5 * (N + 1) ^ 2 := by
    intro a ha
    have h := itCfRRow_wt hlen ha
    have := Nat.mul_le_mul hqw (show 2 * (natList dl).wt + 1 ≤ 2 * N + 1 by omega)
    nlinarith
  have htable : itCfRTable dl q = .list ((List.range q).map (itCfRRow dl q)) := rfl
  have htablew : (itCfRTable dl q).wt ≤ 15 * (N + 1) ^ 3 := by
    rw [htable]
    have ht := wt_list_le_of ((List.range q).map (itCfRRow dl q)) (c := 5 * (N + 1) ^ 2)
      (by intro v hv; obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hv
          exact hroww a (List.mem_range.1 ha))
    simp only [List.length_map, List.length_range] at ht
    have hm := Nat.mul_le_mul (show q ≤ N + 1 by omega)
      (show 2 * (5 * (N + 1) ^ 2) + 1 ≤ 11 * (N + 1) ^ 2 by
        have := Nat.one_le_pow 2 (N + 1) (by omega); omega)
    have he : (N + 1) * (11 * (N + 1) ^ 2) = 11 * (N + 1) ^ 3 := by ring
    omega
  have hrangew : (encFun fun i : Fin q => (i : ℕ)).wt ≤ 4 * (N + 1) ^ 2 :=
    (wt_ids_le q).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have hargw : (Val.list [inp, encFun fun i : Fin q => (i : ℕ)]).wt ≤ 40 * (N + 1) ^ 2 := by
    have := wt_list2_le inp (encFun fun i : Fin q => (i : ℕ)); omega
  have htab := tabulate_spec hmb (c := inp) (F := fun a : Fin q => itCfRRow dl q a)
    (fun a => itCfR_row_spec hrw hrm hrb hce dl q a hlen a.isLt hdw hqw)
  have hout : Val.list ((List.finRange q).map fun a : Fin q => itCfRRow dl q a) =
      itCfRTable dl q := by
    rw [htable, ← List.map_coe_finRange_eq_range, List.map_map]
    rfl
  rw [hout] at htab
  have htab' : FunDet P mb (.list [inp, encFun fun i : Fin q => (i : ℕ)])
      (itCfRTable dl q) (10 ^ 9 * (N + 1) ^ 4) := htab.mono (by
    have hm1 := Nat.mul_le_mul (show q ≤ N + 1 by omega)
      (show 10 ^ 8 * (N + 1) ^ 3 ≤ 10 ^ 8 * (N + 1) ^ 3 from le_rfl)
    have hm2 := Nat.mul_le_mul (Nat.mul_le_mul_left mapK (show q + 1 ≤ N + 1 by omega))
      (show (Val.list [inp, encFun fun i : Fin q => (i : ℕ)]).wt +
        (itCfRTable dl q).wt + 1 ≤ 56 * (N + 1) ^ 3 by omega)
    have he1 : (N + 1) * (10 ^ 8 * (N + 1) ^ 3) = 10 ^ 8 * (N + 1) ^ 4 := by ring
    have he2 : mapK * (N + 1) * (56 * (N + 1) ^ 3) = 56000 * (N + 1) ^ 4 := by
      unfold mapK; ring
    clear * - hm1 hm2 he1 he2
    omega)
  have hid : (encFun fun i : Fin q => (i : ℕ)) = natList (List.range q) := by
    rw [encFun_eq_natList, List.map_coe_finRange_eq_range]
  have hrg : FunDet P rb (.nat q) (encFun fun i : Fin q => (i : ℕ))
      (10000 * (q + 1) ^ 3) := hid.symm ▸ st_range_det hrb q
  set W := 100 * (N + 1) ^ 3
  have hW5 : 5 ≤ W := by dsimp [W]; omega
  have g0 : StDC P [inp] (.var 0) inp 1 0 W := StDC.var' rfl (by dsimp [W]; omega)
  have gq : StDC P [inp] (arg 1) (.nat q) 3 0 W :=
    StDC.arg rfl (by dsimp [W]; omega) (by dsimp [W]; omega) (by omega)
  have gr := StDC.call gq hrg (by dsimp [W]; omega)
  have gt := StDC.call (StDC.mk2 g0 gr (by dsimp [W]; omega) (by omega)) htab'
    (by dsimp [W]; omega)
  refine StDC.funDet hf gt ?_
  have hp34 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hq3 := Nat.pow_le_pow_left (show q + 1 ≤ N + 1 by omega) 3
  dsimp [W]
  omega

end GI.Impl
