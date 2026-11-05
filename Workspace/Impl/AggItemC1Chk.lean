module

public import Workspace.Impl.AggItemC1Sch

@[expose] public section

/-!
# Case 1 as a program: the two tests

* `it_chk_spec`: on the block sizes of two labelings, whether for every size `s` the two
  labelings have the same number of points in blocks of size `s`. Sizes are at most `q`, so the
  program checks the sizes `0, …, q` (`itp_cnt_all`).
* `it_fnd_spec`: on a labeling and the list `[0, …, q-1]`, the first point `a` with
  `lab a ≠ a`, if there is one.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens)

variable {q : ℕ}

/-! ### The counts -/

theorem itpCnt_eq_count (lab : Fin q → ℕ) (s : ℕ) :
    itpCnt lab s = (acpLabs (itpSz lab)).count s := by
  classical
  rw [itpCnt, ac_card_filter, acpLabs, List.count, List.countP_map,
    List.countP_eq_length_filter]
  congr 1

theorem itpCnt_big (lab : Fin q → ℕ) {s : ℕ} (hs : q < s) : itpCnt lab s = 0 := by
  rw [itpCnt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro y _ h
  have := itpSz_le lab y
  omega

/-- The counts agree for all sizes when they agree for the sizes `0, …, q`. -/
theorem itp_cnt_all (labX labY : Fin q → ℕ) :
    (∀ s, itpCnt labX s = itpCnt labY s) ↔ ∀ s, s ≤ q → itpCnt labX s = itpCnt labY s := by
  refine ⟨fun h s _ => h s, fun h s => ?_⟩
  by_cases hs : s ≤ q
  · exact h s hs
  · rw [itpCnt_big labX (by omega), itpCnt_big labY (by omega)]

/-- On `[[SX, SY], s]`: whether `s` occurs equally often in `SX` and `SY`. -/
def itCntT (cnt : ℕ) : Expr :=
  .arith .eq (.call cnt (mk2 (arg 1) (.get (arg 0) (.nat 0))))
    (.call cnt (mk2 (arg 1) (.get (arg 0) (.nat 1))))

/-- The test of `itCntT` on values. -/
def itCntQ (labX labY : Fin q → ℕ) : Val → Bool
  | .nat s => decide (itpCnt labX s = itpCnt labY s)
  | _ => false

theorem it_eq_toNat (a b : ℕ) : (decide (a = b)).toNat = GI.Machine.BinOp.eval .eq a b := by
  simp only [GI.Machine.BinOp.eval]
  by_cases h : a = b <;> simp [h]

set_option maxHeartbeats 1000000 in
theorem it_cntT_spec {P : Program} {f cnt : ℕ} (hf : P.funs[f]? = some (itCntT cnt))
    (hcnt : P.HasAt cnt (countFuns cnt)) (labX labY : Fin q → ℕ) {s : ℕ} (hs : s ≤ q) :
    FunDet P f (.list [.list [encFun (itpSz labX), encFun (itpSz labY)], .nat s])
      (boolVal (itCntQ labX labY (.nat s))) (3 * countK * (q + 1) ^ 3) := by
  have hq1 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqa : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hq3 : (q + 1) ^ 2 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  set W := 100 * (q + 1) ^ 2
  have hX := it_encFun_wt (itpSz labX) (itpSz_le labX)
  have hY := it_encFun_wt (itpSz labY) (itpSz_le labY)
  have hsw := wt_nat_le s
  have hc := wt_list2_le (encFun (itpSz labX)) (encFun (itpSz labY))
  have hin := wt_list2_le (.list [encFun (itpSz labX), encFun (itpSz labY)]) (.nat s)
  have h1 := wt_list2_le (.nat s) (encFun (itpSz labX))
  have h2 := wt_list2_le (.nat s) (encFun (itpSz labY))
  set vs : List Val := [.list [encFun (itpSz labX), encFun (itpSz labY)], .nat s]
  have g0 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 0) rfl (W := W) (by omega) (by omega)
    (by omega)
  have gs := StDC.arg (P := P) (rest := []) (vs := vs) (j := 1) rfl (W := W) (by omega) (by omega)
    (by omega)
  have gX := StDC.get g0 (StDC.nat 0 (by omega)) (v := encFun (itpSz labX)) rfl (by omega)
  have gY := StDC.get g0 (StDC.nat 1 (by omega)) (v := encFun (itpSz labY)) rfl (by omega)
  have cX : FunDet P cnt (.list [.nat s, encFun (itpSz labX)]) (.nat (itpCnt labX s))
      (countK * (q + 1) ^ 3) := by
    rw [itpCnt_eq_count, acp_encFun]
    exact count_spec hcnt (fun x hx => by obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx; exact itpSz_le labX y) hs (by rw [acp_labs_length])
  have cY : FunDet P cnt (.list [.nat s, encFun (itpSz labY)]) (.nat (itpCnt labY s))
      (countK * (q + 1) ^ 3) := by
    rw [itpCnt_eq_count, acp_encFun]
    exact count_spec hcnt (fun x hx => by obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx; exact itpSz_le labY y) hs (by rw [acp_labs_length])
  have hcX : (Val.nat (itpCnt labX s)).wt ≤ W := by
    have := wt_nat_le (itpCnt labX s)
    have : itpCnt labX s ≤ q := (Finset.card_le_univ _).trans (by simp)
    omega
  have hcY : (Val.nat (itpCnt labY s)).wt ≤ W := by
    have := wt_nat_le (itpCnt labY s)
    have : itpCnt labY s ≤ q := (Finset.card_le_univ _).trans (by simp)
    omega
  have dX := StDC.call (StDC.mk2 gs gX (by omega) (by omega)) cX hcX
  have dY := StDC.call (StDC.mk2 gs gY (by omega) (by omega)) cY hcY
  have dE := StDC.arith (op := .eq) dX dY rfl (by
    have := wt_nat_le (GI.Machine.BinOp.eval .eq (itpCnt labX s) (itpCnt labY s))
    simp only [GI.Machine.BinOp.eval] at this ⊢; split_ifs at this ⊢ <;> omega)
  rw [itCntQ, boolVal, it_eq_toNat]
  refine StDC.funDet hf dE ?_
  have : 100 * (W + 1) ≤ countK * (q + 1) ^ 3 := by simp only [countK]; omega
  have : 3 * countK * (q + 1) ^ 3 = 3 * (countK * (q + 1) ^ 3) := by ring
  omega

/-- On `[SX, SY]`: whether the counts of all sizes agree. -/
def itChkF (rng al : ℕ) : Expr :=
  .letE (.call rng (.arith .add (.length (.get (.var 0) (.nat 0))) (.nat 1)))
    (.call al (mk2 (.var 0) (.var 1)))

/-- The cost bound of `itChkF`. -/
def itChkC (q : ℕ) : ℕ := 10 ^ 7 * (q + 1) ^ 4

open Classical in
set_option maxHeartbeats 2000000 in
/-- **The test of the counts.** -/
theorem it_chk_spec {P : Program} {f rng al ct cnt : ℕ} (hf : P.funs[f]? = some (itChkF rng al))
    (hrng : P.HasAt rng (rangeFuns rng)) (hal : P.HasAt al (allFuns al ct))
    (hct : P.funs[ct]? = some (itCntT cnt)) (hcnt : P.HasAt cnt (countFuns cnt))
    (labX labY : Fin q → ℕ) :
    FunDet P f (.list [encFun (itpSz labX), encFun (itpSz labY)])
      (boolVal (decide (∀ s, itpCnt labX s = itpCnt labY s))) (itChkC q) := by
  classical
  have hq1 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqa : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hq3 : (q + 1) ^ 2 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hq4 : (q + 1) ^ 3 ≤ (q + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  set W := 100 * (q + 1) ^ 2
  have hX := it_encFun_wt (itpSz labX) (itpSz_le labX)
  have hY := it_encFun_wt (itpSz labY) (itpSz_le labY)
  have hc := wt_list2_le (encFun (itpSz labX)) (encFun (itpSz labY))
  have hR := it_range_wt (q := q + 1)
  have hR' : 5 * (q + 1 + 1) ^ 2 ≤ 20 * (q + 1) ^ 2 := by nlinarith
  have hin := wt_list2_le (.list [encFun (itpSz labX), encFun (itpSz labY)])
    (natList (List.range (q + 1)))
  -- the loop
  set xs := (List.range (q + 1)).map Val.nat
  have hA := all_spec hal (c := .list [encFun (itpSz labX), encFun (itpSz labY)]) (xs := xs)
    (q := itCntQ labX labY) (B := fun _ => 3 * countK * (q + 1) ^ 3) (fun v hv => by
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hv
      exact it_cntT_spec hct hcnt labX labY (Nat.lt_succ_iff.1 (List.mem_range.1 hs)))
  have hall : xs.all (itCntQ labX labY) = decide (∀ s, itpCnt labX s = itpCnt labY s) := by
    rw [Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_iff, itp_cnt_all]
    simp only [xs, List.mem_map, List.mem_range, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, itCntQ, decide_eq_true_eq]
    exact ⟨fun h s hs => h s (by omega), fun h s hs => h s (by omega)⟩
  have hxl : xs.length = q + 1 := by simp [xs]
  have hAd : FunDet P al (.list [.list [encFun (itpSz labX), encFun (itpSz labY)],
      natList (List.range (q + 1))]) (boolVal (decide (∀ s, itpCnt labX s = itpCnt labY s)))
      ((q + 1) * (3 * countK * (q + 1) ^ 3) + loopModK * (q + 2) * (W + q + 5)) := by
    refine hA.mono fun w c ⟨h1, h2⟩ => ⟨by rw [h1, hall], ?_⟩
    have hsum : (xs.map fun _ => 3 * countK * (q + 1) ^ 3).sum = (q + 1) * (3 * countK * (q + 1) ^ 3) := by
      simp [Function.comp_def, List.map_const', List.sum_replicate, xs]
    rw [hsum, hxl] at h2
    refine h2.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_) _)
    show (Val.list [.list [encFun (itpSz labX), encFun (itpSz labY)],
      natList (List.range (q + 1))]).wt + (q + 1) + 4 ≤ _
    omega
  -- the body
  have v0 : StDC P [.list [encFun (itpSz labX), encFun (itpSz labY)]] (.var 0)
      (.list [encFun (itpSz labX), encFun (itpSz labY)]) 1 0 W := StDC.var' rfl (by omega)
  have g0 := StDC.get v0 (StDC.nat 0 (by omega)) (v := encFun (itpSz labX)) rfl (by omega)
  have l0 := StDC.length (vs := (List.finRange q).map fun i => Val.nat (itpSz labX i)) g0
    (by simp; omega)
  simp only [List.length_map, List.length_finRange] at l0
  have a0 := StDC.arith (op := .add) l0 (StDC.nat 1 (by omega)) rfl (by
    simp only [GI.Machine.BinOp.eval]; have := wt_nat_le (q + 1); omega)
  have d1 := StDC.call a0 (st_range_det hrng (q + 1)) (by omega)
  have u0 : StDC P [.list [encFun (itpSz labX), encFun (itpSz labY)],
    natList (List.range (q + 1))] (.var 0) (.list [encFun (itpSz labX), encFun (itpSz labY)]) 1 0 W :=
    StDC.var' rfl (by omega)
  have u1 : StDC P [.list [encFun (itpSz labX), encFun (itpSz labY)],
    natList (List.range (q + 1))] (.var 1) (natList (List.range (q + 1))) 1 0 W := StDC.var' rfl (by omega)
  have hbw : (boolVal (decide (∀ s, itpCnt labX s = itpCnt labY s))).wt ≤ W := by
    unfold boolVal; have := wt_nat_le (decide (∀ s, itpCnt labX s = itpCnt labY s)).toNat
    have := Bool.toNat_le (decide (∀ s, itpCnt labX s = itpCnt labY s)); omega
  have d2 := StDC.call (StDC.mk2 u0 u1 (by omega) (by omega)) hAd hbw
  refine StDC.funDet hf (StDC.letE d1 d2 hbw) ?_
  have c1 : (q + 1) * (3 * countK * (q + 1) ^ 3) = 3 * 10 ^ 5 * (q + 1) ^ 4 := by
    simp only [countK]; ring
  have c2 : loopModK * (q + 2) * (W + q + 5) ≤ 10 ^ 6 * (q + 1) ^ 4 := by
    calc loopModK * (q + 2) * (W + q + 5) ≤ 1000 * (2 * (q + 1)) * (200 * (q + 1) ^ 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      _ = 4 * 10 ^ 5 * (q + 1) ^ 3 := by ring
      _ ≤ 10 ^ 6 * (q + 1) ^ 4 := by omega
  have c3 : 10000 * (q + 1 + 1) ^ 3 ≤ 8 * 10 ^ 4 * (q + 1) ^ 4 := by
    have : (q + 1 + 1) ^ 3 ≤ (2 * (q + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have e : (2 * (q + 1)) ^ 3 = 8 * (q + 1) ^ 3 := by ring
    omega
  have c4 : 100 * (W + 1) ≤ 2 * 10 ^ 4 * (q + 1) ^ 4 := by omega
  unfold itChkC
  omega

/-! ### The point that is not least in its orbit -/

/-- On `[L, x]`: whether `lab x ≠ x`. -/
def itFixT : Expr := .arith .sub (.nat 1) (.arith .eq (.get (arg 0) (arg 1)) (arg 1))

/-- The test of `itFixT` on values. -/
def itFixQ (lab : Fin q → ℕ) : Val → Bool
  | .nat x => if h : x < q then decide (lab ⟨x, h⟩ ≠ x) else false
  | _ => false

set_option maxHeartbeats 1000000 in
theorem it_fixT_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some itFixT) {lab : Fin q → ℕ}
    (hlt : ∀ x, lab x < q) (x : Fin q) :
    FunDet P f (.list [encFun lab, .nat x]) (boolVal (itFixQ lab (.nat x))) (1000 * (q + 1) ^ 2) := by
  have hq1 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqa : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  set W := 30 * (q + 1) ^ 2
  have hL := it_encFun_wt lab fun x => (hlt x).le
  have hx := wt_nat_le (x : ℕ)
  have hxq := x.isLt
  have hin := wt_list2_le (encFun lab) (.nat x)
  set vs : List Val := [encFun lab, .nat x]
  have g0 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 0) rfl (W := W) (by omega) (by omega)
    (by omega)
  have gX := StDC.arg (P := P) (rest := []) (vs := vs) (j := 1) rfl (W := W) (by omega) (by omega)
    (by omega)
  have lX := StDC.get (vs := (List.finRange q).map fun i => Val.nat (lab i)) g0 gX
    (encFun_getElem? lab x) (by have := wt_nat_le (lab x); have := hlt x; omega)
  have e1 := StDC.arith' (op := .eq) lX gX rfl
    (by simp only [GI.Machine.BinOp.eval]; split_ifs <;> omega)
  have e2 := StDC.arith' (op := .sub) (StDC.nat 1 (by omega)) e1 rfl
    (by simp only [GI.Machine.BinOp.eval]; split_ifs <;> omega)
  have hv : (itFixQ lab (.nat x)).toNat = GI.Machine.BinOp.eval .sub 1
      (GI.Machine.BinOp.eval .eq (lab x) x) := by
    simp only [itFixQ, x.isLt, dif_pos, GI.Machine.BinOp.eval]
    by_cases h : lab x = x <;> simp [h]
  rw [boolVal, hv]
  refine StDC.funDet hf e2 ?_
  omega

/-- **The first point that is not least in its orbit**, as `find` over `[0, …, q-1]`. -/
theorem it_fnd_spec {P : Program} {fd ft : ℕ} (hfd : P.HasAt fd (findFuns fd ft))
    (hft : P.funs[ft]? = some itFixT) {lab : Fin q → ℕ} (hlt : ∀ x, lab x < q)
    (hex : ∃ a : Fin q, lab a ≠ a) :
    ∃ a : Fin q, lab a ≠ a ∧ FunDet P fd (.list [encFun lab, natList (List.range q)]) (.nat a)
      (10 ^ 5 * (q + 1) ^ 3) := by
  have hq1 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqa : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  set xs := (List.range q).map Val.nat
  have hxl : xs.length = q := by simp [xs]
  have hlt' : xs.findIdx (itFixQ lab) < xs.length := by
    obtain ⟨a, ha⟩ := hex
    refine List.findIdx_lt_length_of_exists ⟨.nat a, List.mem_map.2 ⟨a, List.mem_range.2 a.isLt,
      rfl⟩, ?_⟩
    simp [itFixQ, a.isLt, ha]
  have hsat := List.findIdx_getElem (w := hlt')
  have hget : xs[xs.findIdx (itFixQ lab)] = .nat (xs.findIdx (itFixQ lab)) := by simp [xs]
  rw [hget] at hsat
  have hiq : xs.findIdx (itFixQ lab) < q := lt_of_lt_of_eq hlt' hxl
  refine ⟨⟨_, hiq⟩, ?_, ?_⟩
  · simpa [itFixQ, hiq] using hsat
  · have h := find_spec hfd (c := encFun lab) (xs := xs) (q := itFixQ lab)
      (B := fun _ => 1000 * (q + 1) ^ 2) (fun v hv => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv
        exact it_fixT_spec hft hlt ⟨x, List.mem_range.1 hx⟩)
    refine h.mono fun w c ⟨h1, h2⟩ => ⟨h1, ?_⟩
    have hsum : (xs.map fun _ => 1000 * (q + 1) ^ 2).sum = q * (1000 * (q + 1) ^ 2) := by
      simp [Function.comp_def, List.map_const', List.sum_replicate, xs]
    rw [hsum, hxl] at h2
    have hL := it_encFun_wt lab fun x => (hlt x).le
    have hR := it_range_wt (q := q)
    have hin := wt_list2_le (encFun lab) (natList (List.range q))
    have hw : (Val.list [encFun lab, .list xs]).wt ≤ 30 * (q + 1) ^ 2 := by
      show (Val.list [encFun lab, natList (List.range q)]).wt ≤ _; omega
    refine h2.trans ?_
    have c1 : q * (1000 * (q + 1) ^ 2) ≤ 1000 * (q + 1) ^ 3 := by
      calc q * (1000 * (q + 1) ^ 2) ≤ (q + 1) * (1000 * (q + 1) ^ 2) :=
            Nat.mul_le_mul_right _ (by omega)
        _ = 1000 * (q + 1) ^ 3 := by ring
    have c2 : loopModK * (q + 1) * ((Val.list [encFun lab, .list xs]).wt + 2 * q + 3) ≤
        5 * 10 ^ 4 * (q + 1) ^ 3 := by
      calc loopModK * (q + 1) * ((Val.list [encFun lab, .list xs]).wt + 2 * q + 3)
          ≤ 1000 * (q + 1) * (50 * (q + 1) ^ 2) := Nat.mul_le_mul_left _ (by omega)
        _ = 5 * 10 ^ 4 * (q + 1) ^ 3 := by ring
    omega

end GI.Impl
