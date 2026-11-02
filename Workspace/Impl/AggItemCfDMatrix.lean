import Workspace.Impl.AggItemCfDHit
import Workspace.Impl.AggItemCfRTable

namespace GI.Impl

open GI.Algorithm GI.Lang GI.Cited

/-- The common row program can tabulate any weight-bounded cell function. -/
theorem itCfD_row_spec {P : Program} {f mb rb ce B N : ℕ}
    (hf : P.funs[f]? = some (itCfRRowF mb rb))
    (hmb : P.HasAt mb (mapFuns mb ce)) (hrb : P.HasAt rb (rangeFuns rb))
    (C : Val) (q a : ℕ) (ha : a < q) (F : Fin q → ℕ)
    (hcell : ∀ b : Fin q, FunDet P ce (.list [.list [C, .nat q, .nat a], .nat b]) (.nat (F b)) B)
    (hC : C.wt ≤ N) (hq : q ≤ N) (hF : ∀ b, (Val.nat (F b)).wt ≤ N) :
    FunDet P f (.list [.list [C, .nat q], .nat a])
      (natList ((List.finRange q).map F)) (q * B + 10 ^ 7 * (N + 1) ^ 3) := by
  set ctx : Val := .list [C, .nat q, .nat a]
  set inp : Val := .list [.list [C, .nat q], .nat a]
  set row := natList ((List.finRange q).map F)
  have hwq := wt_nat_le q
  have hwa := wt_nat_le a
  have hwc := wt_list3_le C (.nat q) (.nat a)
  have hwi := wt_list2_le (.list [C, .nat q]) (.nat a)
  have hwdq := wt_list2_le C (.nat q)
  have hcw : ctx.wt ≤ 10 * (N + 1) := by dsimp [ctx]; omega
  have hiw : inp.wt ≤ 20 * (N + 1) := by dsimp [inp]; omega
  have hn2 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have h12 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hroww : row.wt ≤ 5 * (N + 1) ^ 2 := by
    have h := wt_list_le_of (((List.finRange q).map F).map Val.nat) (c := N) (by
      intro v hv
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv
      obtain ⟨b, _, rfl⟩ := List.mem_map.1 hx
      exact hF b)
    simp only [List.length_map, List.length_finRange] at h
    have hm := Nat.mul_le_mul_right (2 * N + 1) hq
    change row.wt ≤ _ at h
    clear * - h hm
    nlinarith
  have hrw : (encFun fun i : Fin q => (i : ℕ)).wt ≤ 4 * (N + 1) ^ 2 :=
    (wt_ids_le q).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have hargw : (Val.list [ctx, encFun fun i : Fin q => (i : ℕ)]).wt ≤ 40 * (N + 1) ^ 2 := by
    have := wt_list2_le ctx (encFun fun i : Fin q => (i : ℕ)); omega
  have htab := tabulate_spec hmb (c := ctx) hcell
  have hout : Val.list ((List.finRange q).map fun b => Val.nat (F b)) = row := by
    simp only [row, natList, List.map_map, Function.comp_def]
  rw [hout] at htab
  have htab' : FunDet P mb (.list [ctx, encFun fun i : Fin q => (i : ℕ)]) row
      (q * B + 56000 * (N + 1) ^ 3) := htab.mono (by
    have hh := Nat.mul_le_mul (Nat.mul_le_mul_left mapK (show q + 1 ≤ N + 1 by omega))
      (show (Val.list [ctx, encFun fun i : Fin q => (i : ℕ)]).wt + row.wt + 1 ≤
        56 * (N + 1) ^ 2 by omega)
    have he : mapK * (N + 1) * (56 * (N + 1) ^ 2) = 56000 * (N + 1) ^ 3 := by
      unfold mapK; ring
    exact Nat.add_le_add_left (hh.trans_eq he) _)
  have hid : (encFun fun i : Fin q => (i : ℕ)) = natList (List.range q) := by
    rw [encFun_eq_natList, List.map_coe_finRange_eq_range]
  have hrg : FunDet P rb (.nat q) (encFun fun i : Fin q => (i : ℕ))
      (10000 * (q + 1) ^ 3) := hid.symm ▸ st_range_det hrb q
  set W := 100 * (N + 1) ^ 2
  have hW5 : 5 ≤ W := by dsimp [W]; omega
  have g0 : StDC P [inp] (arg 0) (.list [C, .nat q]) 3 0 W :=
    StDC.arg rfl (by dsimp [W]; omega) (by omega) (by dsimp [W]; omega)
  have gd := StDC.get g0 (StDC.nat 0 (by omega)) (v := C) rfl (by dsimp [W]; omega)
  have gq := StDC.get g0 (StDC.nat 1 (by omega)) (v := .nat q) rfl (by dsimp [W]; omega)
  have ga : StDC P [inp] (arg 1) (.nat a) 3 0 W :=
    StDC.arg rfl (by dsimp [W]; omega) (by omega) (by dsimp [W]; omega)
  have gc := StDC.mk3 gd gq ga (by show ctx.wt ≤ W; dsimp [W]; omega) (by omega)
  have gr := StDC.call gq hrg (by dsimp [W]; omega)
  have gt := StDC.call (StDC.mk2 gc gr (by
      show (Val.list [ctx, encFun fun i : Fin q => (i : ℕ)]).wt ≤ W; dsimp [W]; omega)
    (by omega)) htab' (by dsimp [W]; omega)
  refine StDC.funDet hf gt ?_
  have hp23 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hp13 : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hq3 := Nat.pow_le_pow_left (show q + 1 ≤ N + 1 by omega) 3
  dsimp [W]
  omega

/-- The matrix wrapper, with a common cell cost and weight bound. -/
theorem itCfD_matrix_spec {P : Program} {f mb rb rw rm ce B N : ℕ}
    (hf : P.funs[f]? = some (itCfRTableF mb rb))
    (hmb : P.HasAt mb (mapFuns mb rw)) (hrb : P.HasAt rb (rangeFuns rb))
    (hrw : P.funs[rw]? = some (itCfRRowF rm rb)) (hrm : P.HasAt rm (mapFuns rm ce))
    (C : Val) (q : ℕ) (F : Fin q → Fin q → ℕ)
    (hcell : ∀ a b : Fin q, FunDet P ce (.list [.list [C, .nat q, .nat a], .nat b])
      (.nat (F a b)) B)
    (hC : C.wt ≤ N) (hq : q ≤ N) (hF : ∀ a b, (Val.nat (F a b)).wt ≤ N) :
    FunDet P f (.list [C, .nat q])
      (.list ((List.finRange q).map fun a => natList ((List.finRange q).map (F a))))
      (q * q * B + 10 ^ 9 * (N + 1) ^ 4) := by
  set inp : Val := .list [C, .nat q]
  set rows := Val.list ((List.finRange q).map fun a => natList ((List.finRange q).map (F a)))
  have hwq := wt_nat_le q
  have hwi := wt_list2_le C (.nat q)
  have hiw : inp.wt ≤ 10 * (N + 1) := by dsimp [inp]; omega
  have hn2 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hp23 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h13 : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hroww : ∀ a, (natList ((List.finRange q).map (F a))).wt ≤ 5 * (N + 1) ^ 2 := by
    intro a
    have h := wt_list_le_of (((List.finRange q).map (F a)).map Val.nat) (c := N) (by
      intro v hv
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv
      obtain ⟨b, _, rfl⟩ := List.mem_map.1 hx
      exact hF a b)
    simp only [List.length_map, List.length_finRange] at h
    have hm := Nat.mul_le_mul_right (2 * N + 1) hq
    change (natList ((List.finRange q).map (F a))).wt ≤ _ at h
    clear * - h hm
    nlinarith
  have hrowsw : rows.wt ≤ 15 * (N + 1) ^ 3 := by
    have ht := wt_list_le_of ((List.finRange q).map fun a => natList ((List.finRange q).map (F a)))
      (c := 5 * (N + 1) ^ 2) (by
        intro v hv; obtain ⟨a, _, rfl⟩ := List.mem_map.1 hv; exact hroww a)
    simp only [List.length_map, List.length_finRange] at ht
    have hm := Nat.mul_le_mul (show q ≤ N + 1 by omega)
      (show 2 * (5 * (N + 1) ^ 2) + 1 ≤ 11 * (N + 1) ^ 2 by
        have := Nat.one_le_pow 2 (N + 1) (by omega); omega)
    have he : (N + 1) * (11 * (N + 1) ^ 2) = 11 * (N + 1) ^ 3 := by ring
    change rows.wt ≤ _ at ht
    omega
  have hrangew : (encFun fun i : Fin q => (i : ℕ)).wt ≤ 4 * (N + 1) ^ 2 :=
    (wt_ids_le q).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have hargw : (Val.list [inp, encFun fun i : Fin q => (i : ℕ)]).wt ≤ 40 * (N + 1) ^ 2 := by
    have := wt_list2_le inp (encFun fun i : Fin q => (i : ℕ)); omega
  have htab := tabulate_spec hmb (c := inp)
    (fun a : Fin q => itCfD_row_spec hrw hrm hrb C q a a.isLt (F a) (hcell a) hC hq (hF a))
  have htab' : FunDet P mb (.list [inp, encFun fun i : Fin q => (i : ℕ)]) rows
      (q * q * B + 10100000 * (N + 1) ^ 4) := htab.mono (by
    have hh := Nat.mul_le_mul (Nat.mul_le_mul_left mapK (show q + 1 ≤ N + 1 by omega))
      (show (Val.list [inp, encFun fun i : Fin q => (i : ℕ)]).wt + rows.wt + 1 ≤
        56 * (N + 1) ^ 3 by omega)
    have he : mapK * (N + 1) * (56 * (N + 1) ^ 3) = 56000 * (N + 1) ^ 4 := by
      unfold mapK; ring
    have hm := Nat.mul_le_mul_right (10 ^ 7 * (N + 1) ^ 3) (show q ≤ N + 1 by omega)
    have he' : (N + 1) * (10 ^ 7 * (N + 1) ^ 3) = 10 ^ 7 * (N + 1) ^ 4 := by ring
    rw [Nat.mul_add, ← Nat.mul_assoc]
    change q * q * B + q * (10 ^ 7 * (N + 1) ^ 3) +
      mapK * (q + 1) * ((Val.list [inp, encFun fun i : Fin q => (i : ℕ)]).wt + rows.wt + 1) ≤ _
    clear * - hh he hm he'
    omega)
  have hid : (encFun fun i : Fin q => (i : ℕ)) = natList (List.range q) := by
    rw [encFun_eq_natList, List.map_coe_finRange_eq_range]
  have hrg : FunDet P rb (.nat q) (encFun fun i : Fin q => (i : ℕ))
      (10000 * (q + 1) ^ 3) := hid.symm ▸ st_range_det hrb q
  set W := 100 * (N + 1) ^ 3
  have hW5 : 5 ≤ W := by dsimp [W]; omega
  have g0 : StDC P [inp] (.var 0) inp 1 0 W := StDC.var' rfl (by dsimp [W]; omega)
  have gq : StDC P [inp] (arg 1) (.nat q) 3 0 W :=
    StDC.arg rfl (by dsimp [W]; omega) (by omega) (by dsimp [W]; omega)
  have gr := StDC.call gq hrg (by dsimp [W]; omega)
  have gt := StDC.call (StDC.mk2 g0 gr (by dsimp [W]; omega) (by omega)) htab'
    (by dsimp [W]; omega)
  refine StDC.funDet hf gt ?_
  have hp34 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hq3 := Nat.pow_le_pow_left (show q + 1 ≤ N + 1 by omega) 3
  dsimp [W]
  omega

end GI.Impl
