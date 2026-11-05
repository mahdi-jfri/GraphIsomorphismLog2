module

public import Workspace.Impl.AggItemCiCfgI

@[expose] public section

/-!
# The configuration query: the transpositions outside the fiber, and two list helpers

* `itcq_csF_spec`: `itcqCsF rng cm` on `[itcqDV X, [0, …, q - 1]]` gives `itcqCs X` (the map of
  `itcqCsB` over `[0, …, d² - 1]`), in cost `itcqCsC q`.
* `itcq_app_det`: `append` as a deterministic function.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm Finset
open GI.Cited (Val encPerm gens encGroup encPerms)

variable {q : ℕ}

theorem itcq_csC_arith {V d n C : ℕ} (hd : d * d ≤ V ^ 2) (hn : n ≤ 100)
    (hC : C ≤ n * (40 * (V + 1) ^ 4 + 101) + (10000 * (d * d + 1) ^ 3 +
      (d * d * itcqCbC (2 * V ^ 2 + 16 * V + 42) + 1000 * (d * d + 1) *
        (40 * (V + 1) ^ 4 + 101)))) :
    C ≤ itcqCsC V := by
  unfold itcqCsC itcqCbC at *
  have hV2 : V ^ 2 ≤ (V + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hdd : d * d + 1 ≤ (V + 1) ^ 2 := by
    have : (V + 1) ^ 2 = V ^ 2 + 2 * V + 1 := by ring
    omega
  have hb : 2 * V ^ 2 + 16 * V + 42 + 2 ≤ 46 * (V + 1) ^ 2 := by nlinarith
  have k1 : (2 * V ^ 2 + 16 * V + 42 + 2) ^ 3 ≤ (46 * (V + 1) ^ 2) ^ 3 := Nat.pow_le_pow_left hb 3
  have e1 : (46 * (V + 1) ^ 2) ^ 3 = 97336 * (V + 1) ^ 6 := by ring
  rw [e1] at k1
  have k2 : d * d * (10 ^ 7 * (2 * V ^ 2 + 16 * V + 42 + 2) ^ 3) ≤
      (V + 1) ^ 2 * (10 ^ 7 * (97336 * (V + 1) ^ 6)) :=
    Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ k1)
  have e2 : (V + 1) ^ 2 * (10 ^ 7 * (97336 * (V + 1) ^ 6)) = 973360000000 * (V + 1) ^ 8 := by ring
  rw [e2] at k2
  have k3 : (d * d + 1) ^ 3 ≤ ((V + 1) ^ 2) ^ 3 := Nat.pow_le_pow_left hdd 3
  have e3 : ((V + 1) ^ 2) ^ 3 = (V + 1) ^ 6 := by ring
  rw [e3] at k3
  have k4 : 1000 * (d * d + 1) * (40 * (V + 1) ^ 4 + 101) ≤
      1000 * ((V + 1) ^ 2 * (141 * (V + 1) ^ 4)) := by
    rw [Nat.mul_assoc]
    refine Nat.mul_le_mul_left _ (Nat.mul_le_mul hdd ?_)
    have : 1 ≤ (V + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have e4 : (V + 1) ^ 2 * (141 * (V + 1) ^ 4) = 141 * (V + 1) ^ 6 := by ring
  rw [e4] at k4
  have k5 : n * (40 * (V + 1) ^ 4 + 101) ≤ 100 * (141 * (V + 1) ^ 4) := Nat.mul_le_mul hn (by
    have : 1 ≤ (V + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega)
  have p46 : (V + 1) ^ 4 ≤ (V + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p68 : (V + 1) ^ 6 ≤ (V + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  generalize d * d * (10 ^ 7 * (2 * V ^ 2 + 16 * V + 42 + 2) ^ 3) = A at *
  generalize (V + 1) ^ 4 = T4 at *
  generalize (V + 1) ^ 6 = T6 at *
  generalize (V + 1) ^ 8 = T8 at *
  norm_num at *
  omega

section Prog

variable {P : Program}

/-- **`append`** as a deterministic function. -/
theorem itcq_app_det {app : ℕ} (h : P.HasAt app (appendFuns app)) (xs ys : List Val) :
    FunDet P app (.list [.list xs, .list ys]) (.list (xs ++ ys)) (loopModK * (ys.length + 1) *
      ((Val.list [.list xs, .list ys]).wt + ys.length + (Val.list (xs ++ ys)).wt + 1)) :=
  (append_spec h xs ys).mono fun w c ⟨hw, hc⟩ => ⟨hw, by subst hw; exact hc⟩

set_option maxHeartbeats 2000000 in
/-- **The transpositions of the outer classes** as a program. -/
theorem itcq_csF_spec {f rng cm cb sm fs : ℕ} (hf : P.funs[f]? = some (itcqCsF rng cm))
    (hrng : P.HasAt rng (rangeFuns rng)) (hcm : P.HasAt cm (mapFuns cm cb))
    (hcb : P.funs[cb]? = some (itcqCsB sm)) (hsm : P.HasAt sm (mapFuns sm fs))
    (hfs : P.funs[fs]? = some itcqSwB) (X : PairCfg q) (x₀ : ℕ) {V : ℕ} (hq : q + 1 ≤ V)
    (hV : (Val.list [itcqDV X, natList (List.range q),
      .list [rcColVal X, .nat X.j, .nat x₀]]).wt ≤ V) :
    FunDet P f (.list [itcqDV X, natList (List.range q), .list [rcColVal X, .nat X.j, .nat x₀]])
      (.list ((itcqCs X).map encPerm)) (itcqCsC V) := by
  set cX : Val := .list [rcColVal X, .nat X.j, .nat x₀]
  have hd : (itciFo X).length ≤ q := by
    rw [itciFo_length]; exact Finset.card_le_univ _ |>.trans (by simp)
  set d := (itciFo X).length
  have hDVw : (itcqDV X).wt ≤ V := (st_wt_mem (by simp)).trans hV
  have hRw : (natList (List.range q)).wt ≤ V := (st_wt_mem (by simp)).trans hV
  have hXw : cX.wt ≤ V := (st_wt_mem (by simp)).trans hV
  have hdd : d * d ≤ V ^ 2 := by
    have := Nat.mul_le_mul hd hd
    have : q * q ≤ V ^ 2 := by nlinarith
    omega
  have hV4 : V ^ 2 ≤ (V + 1) ^ 4 := by nlinarith
  have hV1 : V + 1 ≤ (V + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
  have hRR : (natList (List.range (d * d))).wt ≤ 5 * (V + 1) ^ 4 := by
    have h := itcq_range_wt (d * d)
    have : (d * d + 1) ^ 2 ≤ ((V + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left (by nlinarith) 2
    have e : ((V + 1) ^ 2) ^ 2 = (V + 1) ^ 4 := by ring
    omega
  have hOw := it_perms_wt (q := q) (l := itcqCs X) (m := d * d)
    (by simp only [itcqCs, List.length_map, List.length_range]; exact le_rfl)
  have hOw' : (d * d) * (9 * (q + 1) ^ 2) ≤ 9 * (V + 1) ^ 4 := by
    have : (q + 1) ^ 2 ≤ (V + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h1 : (d * d) * (9 * (q + 1) ^ 2) ≤ (V + 1) ^ 2 * (9 * (V + 1) ^ 2) :=
      Nat.mul_le_mul (by nlinarith) (by omega)
    have e : (V + 1) ^ 2 * (9 * (V + 1) ^ 2) = 9 * (V + 1) ^ 4 := by ring
    omega
  obtain ⟨Wl, hWl⟩ : ∃ Wl, Wl = 40 * (V + 1) ^ 4 + 100 := ⟨_, rfl⟩
  have hs2 := (Val.list [itcqDV X, natList (List.range q), cX]).two_le_size
  have hs3 := (Val.list [itcqDV X, natList (List.range q), cX]).size_le_wt
  have v0 := StDC.var' (P := P) (env := [.list [itcqDV X, natList (List.range q), cX]])
    (i := 0) rfl (W := Wl) (by omega)
  have hDVe : itcqDV X = .list (((itciFo X).map Fin.val).map Val.nat) := rfl
  have g0 := StDC.get v0 (StDC.nat 0 (by omega)) (v := itcqDV X) rfl (by omega)
  have ln := StDC.length (vs := ((itciFo X).map Fin.val).map Val.nat) g0
    (by simp only [List.length_map]; omega)
  simp only [List.length_map] at ln
  set e1 : List Val := [.list [itcqDV X, natList (List.range q), cX], .nat d]
  have u0 := StDC.var' (P := P) (env := e1) (i := 0) rfl (W := Wl) (by omega)
  have u1 := StDC.var' (P := P) (env := e1) (i := 1) rfl (W := Wl)
    ((wt_nat_le _).trans (by omega))
  have ug0 := StDC.get u0 (StDC.nat 0 (by omega)) (v := itcqDV X) rfl (by omega)
  have ug1 := StDC.get u0 (StDC.nat 1 (by omega)) (v := natList (List.range q)) rfl (by omega)
  have ug2 := StDC.get u0 (StDC.nat 2 (by omega)) (v := cX) rfl (by omega)
  have hdw := wt_nat_le d
  have hc4 := st_wt_list4 (a := itcqDV X) (b := .nat d) (c := natList (List.range q)) (d := cX)
    (X := V + 1) (by omega) (by omega) (by omega) (by omega)
  have m4 := StDC.mk4 ug0 u1 ug1 ug2 (by omega) (by omega)
  have mu := StDC.arith u1 u1 (op := .mul) (z := d * d) rfl
    ((wt_nat_le _).trans (by omega))
  have cr := StDC.call mu (st_range_det hrng (d * d)) (by omega)
  have hmi := wt_list2_le (.list [itcqDV X, .nat d, natList (List.range q), cX])
    (natList (List.range (d * d)))
  have key := itcq_mapPosV_spec (P := P) hcm
    (c := .list [itcqDV X, .nat d, natList (List.range q), cX])
    (m := d * d) (g := fun t => encPerm (itcqCsE X (itciFo X) t))
    (Bd := itcqCbC (2 * V ^ 2 + 16 * V + 42)) (fun t => by
      have ht := t.isLt
      have htw := wt_nat_le (t : ℕ)
      have h2 := wt_list2_le (.list [itcqDV X, .nat d, natList (List.range q), cX]) (.nat (t : ℕ))
      have htd : (t : ℕ) ≤ V ^ 2 := by omega
      exact itcq_csB_spec (P := P) hcb hsm hfs X x₀ (j := t) t.isLt (by nlinarith)
        (show (Val.list [.list [itcqDV X, .nat d, natList (List.range q), cX], .nat (t : ℕ)]).wt ≤
          2 * V ^ 2 + 16 * V + 42 by nlinarith))
  have hval : ((List.finRange (d * d)).map
      fun t : Fin (d * d) => encPerm (itcqCsE X (itciFo X) t.1)) = (itcqCs X).map encPerm := by
    rw [itcqCs, List.map_map, ← List.map_coe_finRange_eq_range, List.map_map]; rfl
  have hmd : FunDet P cm (.list [.list [itcqDV X, .nat d, natList (List.range q), cX],
      natList (List.range (d * d))]) (.list ((itcqCs X).map encPerm))
      (d * d * itcqCbC (2 * V ^ 2 + 16 * V + 42) + 1000 * (d * d + 1) *
        (40 * (V + 1) ^ 4 + 101)) := by
    refine key.mono fun w c ⟨hw, hc⟩ => ⟨by rw [hw, hval], hc.trans ?_⟩
    rw [hw, hval]
    unfold mapK
    refine Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_) _
    omega
  have cm2 := StDC.call (StDC.mk2 m4 cr (by omega) (by omega)) hmd (by omega)
  have body := StDC.letE ln cm2 (by omega)
  refine StDC.funDet hf body ?_
  clear body cm2 key hmd m4 mu cr ln v0 g0 u0 u1 ug0 ug1 ug2
  refine itcq_csC_arith hdd (n := 100) le_rfl ?_
  rw [hWl] at *
  omega

end Prog

end GI.Impl
