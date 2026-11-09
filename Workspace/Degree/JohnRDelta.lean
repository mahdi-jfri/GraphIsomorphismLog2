module

public import Workspace.Degree.JohnRBall

@[expose] public section

/-!
# The step `δ` of `johnRProgram`

`johnR_delta_det` shows that the step `johnDeltaRE` gives the label `johnDeltaR`, within the cost
that `john_main_specG` asks for.
-/

namespace GI.Degree

open GI.Lang GI.Cited GI.Proved GI.Impl Equiv
open GI.Machine (BinOp)

/-- The environment of `johnMainG` at the step `δ`. -/
def johnEnv10 {n : ℕ} (gs : List (Perm (Fin n))) (m k : ℕ) (labL : List ℕ) : List Val :=
  [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n),
    natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm),
    natList labL, natList (List.range n), natList (johnRow n labL),
    natList (johnCnt (johnRow n labL))]

/-- **The step `δ`.** The hypotheses: the labels are `n * n` numbers at most `n * n`, `k ≤ n`,
`k (m - k) ≤ n * n`, and both searches find an entry. -/
theorem johnR_delta_det {n : ℕ} (gs : List (Perm (Fin n))) (m k : ℕ) (labL : List ℕ)
    (hLlen : labL.length = n * n) (hLle : ∀ v ∈ labL, v ≤ n * n) (hn : 0 < n) (hm : m ≤ n) (hkm' : k ≤ m)
    (hkm : k * (m - k) ≤ n * n)
    (hυ : (johnCnt (johnRow n labL)).findIdx (fun c => decide (c = k * (m - k))) < n)
    (hδ : (johnBall n labL (johnUps m k (johnRow n labL)) (k - 1)).findIdx
      (fun x => decide (x = 0)) < n) :
    Det johnRProgram (johnEnv10 gs m k labL) johnDeltaRE
      (Val.nat (johnDeltaR n labL (johnUps m k (johnRow n labL)) k))
      (johnA * ((Val.list [encGroup gs, .nat m, .nat k]).wt + 1) ^ 15) := by
  obtain ⟨hnW, hgW, hGW, hmW, hkW, hPW⟩ := john_in_wt gs m k
  set W := (Val.list [encGroup gs, .nat m, .nat k]).wt with hW
  set Y := W + 1 with hY
  have hY1 : 1 ≤ Y := by omega
  have hn1 : n + 1 ≤ Y := by omega
  have y615 : Y ^ 6 ≤ Y ^ 15 := Nat.pow_le_pow_right hY1 (by omega)
  have hWY : (Val.list [encGroup gs, .nat m, .nat k]).wt + 1 ≤ Y ^ 6 := by
    have : Y ≤ Y ^ 6 := by
      calc Y = Y ^ 1 := (pow_one Y).symm
        _ ≤ Y ^ 6 := Nat.pow_le_pow_right hY1 (by omega)
    omega
  have pn2 : (n + 1) ^ 2 ≤ Y ^ 2 := john_pow_mono hn1 2
  have pn6 : (n + 1) ^ 6 ≤ Y ^ 6 := john_pow_mono hn1 6
  have y26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := john_pow_le (by omega) (by omega)
  have y46 : (n + 1) ^ 4 ≤ (n + 1) ^ 6 := john_pow_le (by omega) (by omega)
  have y56 : (n + 1) ^ 5 ≤ (n + 1) ^ 6 := john_pow_le (by omega) (by omega)
  have y36 : (n + 1) ^ 3 ≤ (n + 1) ^ 6 := john_pow_le (by omega) (by omega)
  have hnn : n * n + 1 ≤ (n + 1) ^ 2 := by nlinarith
  have hnn6 : (n * n + 1) ^ 3 ≤ (n + 1) ^ 6 := by
    calc (n * n + 1) ^ 3 ≤ ((n + 1) ^ 2) ^ 3 := john_pow_mono hnn 3
      _ = (n + 1) ^ 6 := by ring
  have hnn' : n ≤ n * n := Nat.le_mul_self n
  have hn6 : n + 1 ≤ (n + 1) ^ 6 := by nlinarith
  have hn4 : n + 1 ≤ (n + 1) ^ 4 :=
    calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ (n + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  -- The lists and their weights.
  set row := johnRow n labL with hrow
  set cnt := johnCnt row with hcnt
  set υ := johnUps m k row with hυdef
  set R := johnBall n labL υ (k - 1) with hR
  have hrowlen : row.length = n := by simp [row, johnRow]
  have hrowle : ∀ v ∈ row, v ≤ n * n := by
    intro v hv
    simp only [row, johnRow, List.mem_map] at hv
    obtain ⟨y, -, rfl⟩ := hv
    rw [List.getD_eq_getElem?_getD]
    cases h : labL[y]? with
    | none => simp
    | some a => exact hLle a (List.mem_of_getElem? h)
  have hcntlen : cnt.length = n := by simp [cnt, johnCnt, hrowlen]
  have hcntle : ∀ v ∈ cnt, v ≤ n * n := by
    intro v hv
    simp only [cnt, johnCnt, List.mem_map] at hv
    obtain ⟨y, -, rfl⟩ := hv
    exact (List.count_le_length).trans (by omega)
  have hυr : _ < row.length := hrowlen ▸ hυ
  have hυle : υ ≤ n * n := by
    show row.getD _ 0 ≤ n * n
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hυr, Option.getD_some]
    exact hrowle _ (List.getElem_mem _)
  have h0L : 0 < labL.length := by rw [hLlen]; exact Nat.mul_pos hn hn
  have h0le : labL.getD 0 0 ≤ n * n := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h0L, Option.getD_some]
    exact hLle _ (List.getElem_mem _)
  have hLυ : JohnLabOK n labL υ := ⟨hLlen, hLle, hυle⟩
  have hL0 : JohnLabOK n labL (labL.getD 0 0) := ⟨hLlen, hLle, h0le⟩
  have hRok : BallOK n R := johnBall_ok (k - 1)
  have hδr : _ < row.length := hrowlen ▸ hδ
  have hδle : johnDeltaR n labL υ k ≤ n * n := by
    show row.getD _ 0 ≤ n * n
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hδr, Option.getD_some]
    exact hrowle _ (List.getElem_mem _)
  have wlab := john_wt_natList_sq hLlen hLle
  have wrow : (natList row).wt ≤ 5 * (n * n + 1) ^ 2 := wt_natList_le_sq hrowle (by omega)
  have wcnt : (natList cnt).wt ≤ 5 * (n * n + 1) ^ 2 := wt_natList_le_sq hcntle (by omega)
  have hnn4 : (n * n + 1) ^ 2 ≤ (n + 1) ^ 4 := by
    calc (n * n + 1) ^ 2 ≤ ((n + 1) ^ 2) ^ 2 := john_pow_mono hnn 2
      _ = (n + 1) ^ 4 := by ring
  have wRn := john_wt_Rn n
  have wD := john_wt_DV n labL υ
  have wR0 := johnBall_wt (n := n) (labL := labL) (υ := υ) 0
  have wR := hRok.wt
  have wυ := wt_nat_le υ
  have wδ := wt_nat_le (johnDeltaR n labL υ k)
  have wk := wt_nat_le k
  have w0 := wt_nat_le 0; have w1 := wt_nat_le 1; have w2 := wt_nat_le 2
  have wn := wt_nat_le n
  set E10 := johnEnv10 gs m k labL with hE10
  -- Step 1: the label `υ`.
  have s1 : Det johnRProgram E10 (.get (.var 8) (.call 62 (mk2 (.arith .mul (.get (.var 0) (.nat 2))
      (.arith .sub (.get (.var 0) (.nat 1)) (.get (.var 0) (.nat 2)))) (.var 9))))
      (Val.nat υ) (100000000 * Y ^ 6) := by
    have hk' := Det.get' (Det.var' (P := johnRProgram) (env := E10) (i := 0)
      (v := Val.list [encGroup gs, .nat m, .nat k]) rfl) (Det.nat 2)
      (show [encGroup gs, Val.nat m, Val.nat k][2]? = some (Val.nat k) from rfl)
    have hm' := Det.get' (Det.var' (P := johnRProgram) (env := E10) (i := 0)
      (v := Val.list [encGroup gs, .nat m, .nat k]) rfl) (Det.nat 1)
      (show [encGroup gs, Val.nat m, Val.nat k][1]? = some (Val.nat m) from rfl)
    have hsub := Det.arith' hm' hk' (show BinOp.eval .sub m k = m - k from rfl)
    have hmul := Det.arith' hk' hsub (show BinOp.eval .mul k (m - k) = k * (m - k) from rfl)
    have hf := Det.call (Det.mk2 hmul (Det.var' (P := johnRProgram) (env := E10) (i := 9)
      (v := natList cnt) rfl))
      (findEq_spec (john_at_findEq (P := johnRProgram)) (xs := cnt) (B := n * n) hcntle hkm
        (by omega))
    refine (Det.get' (Det.var' (P := johnRProgram) (env := E10) (i := 8)
      (v := Val.list (row.map Val.nat)) rfl) hf (john_get_row hυr)).mono ?_
    have e1 := wt_list2_le (Val.nat (k * (m - k))) (natList cnt)
    have wi := wt_nat_le (cnt.findIdx fun c => decide (c = k * (m - k)))
    have hi : cnt.findIdx (fun c => decide (c = k * (m - k))) ≤ n * n := by
      have := List.findIdx_le_length (p := fun c => decide (c = k * (m - k))) (xs := cnt)
      omega
    have ew : (Val.list (row.map Val.nat)).wt = (natList row).wt := rfl
    have hmk : m - k ≤ n := by omega
    have wkm := wt_nat_le (k * (m - k))
    have wmk := wt_nat_le (m - k)
    have eυ : (Val.nat (row.getD (cnt.findIdx fun c => decide (c = k * (m - k))) 0)).wt ≤
        n * n + 2 :=
      (wt_nat_le _).trans (by have : row.getD (cnt.findIdx fun c => decide (c = k * (m - k))) 0 ≤ n * n := hυle; omega)
    have p : findEqK * (n * n + 1) ^ 3 ≤ 100000 * (n + 1) ^ 6 := Nat.mul_le_mul_left _ hnn6
    omega
  set E11 := E10 ++ [Val.nat υ] with hE11
  set E12 := E11 ++ [johnDV n labL υ] with hE12
  set E13 := E12 ++ [natList (johnBall n labL υ 0)] with hE13
  set E14 := E13 ++ [natList R] with hE14
  -- Step 2: the matrix of `υ`.
  have s2 : Det johnRProgram E11 (.call 66 (mk2 (mk4 (.var 6) (.var 2) (.var 10) (.var 7)) (.var 7)))
      (johnDV n labL υ) (100000000 * Y ^ 6) := by
    have h4 := Det.mk4 (Det.var' (P := johnRProgram) (env := E11) (i := 6) (v := natList labL) rfl)
      (Det.var' (P := johnRProgram) (env := E11) (i := 2) (v := Val.nat n) rfl)
      (Det.var' (P := johnRProgram) (env := E11) (i := 10) (v := Val.nat υ) rfl)
      (Det.var' (P := johnRProgram) (env := E11) (i := 7) (v := natList (List.range n)) rfl)
    refine (Det.call (Det.mk2 h4 (Det.var' (P := johnRProgram) (env := E11) (i := 7)
      (v := natList (List.range n)) rfl)) (john_matD_spec (P := johnRProgram) hLυ)).mono ?_
    have e1 := wt_list4_le (natList labL) (Val.nat n) (Val.nat υ) (natList (List.range n))
    have e2 := wt_list2_le (Val.list [natList labL, Val.nat n, Val.nat υ, natList (List.range n)])
      (natList (List.range n))
    omega
  -- Step 3: the ball of radius `0`.
  have s3 : Det johnRProgram E12
      (.call 70 (mk2 (mk4 (.var 6) (.var 2) (.get (.var 6) (.nat 0)) (.nat 0)) (.var 7)))
      (natList (johnBall n labL υ 0)) (100000000 * Y ^ 6) := by
    have hg := Det.get' (Det.var' (P := johnRProgram) (env := E12) (i := 6)
      (v := Val.list (labL.map Val.nat)) rfl) (Det.nat 0) (john_get_row h0L)
    have h4 := Det.mk4 (Det.var' (P := johnRProgram) (env := E12) (i := 6) (v := natList labL) rfl)
      (Det.var' (P := johnRProgram) (env := E12) (i := 2) (v := Val.nat n) rfl) hg (Det.nat 0)
    refine (Det.call (Det.mk2 h4 (Det.var' (P := johnRProgram) (env := E12) (i := 7)
      (v := natList (List.range n)) rfl)) (john_rowD_spec (P := johnRProgram) hL0 hn)).mono ?_
    have e1 := wt_list4_le (natList labL) (Val.nat n) (Val.nat (labL.getD 0 0)) (Val.nat 0)
    have e2 := wt_list2_le (Val.list [natList labL, Val.nat n, Val.nat (labL.getD 0 0), Val.nat 0])
      (natList (List.range n))
    have w3 := wt_nat_le (labL.getD 0 0)
    have ew : (Val.list (labL.map Val.nat)).wt = (natList labL).wt := rfl
    have eb : (natList (johnDRow n labL (labL.getD 0 0) 0)).wt =
      (natList (johnBall n labL υ 0)).wt := rfl
    omega
  -- Step 4: the ball of radius `k - 1`.
  have s4 : Det johnRProgram E13
      (.call 106 (mk3 (mk2 (.var 11) (.var 7)) (.arith .sub (.get (.var 0) (.nat 2)) (.nat 1))
        (.var 12)))
      (natList R) (100000000 * Y ^ 6) := by
    have hk' := Det.get' (Det.var' (P := johnRProgram) (env := E13) (i := 0)
      (v := Val.list [encGroup gs, .nat m, .nat k]) rfl) (Det.nat 2)
      (show [encGroup gs, Val.nat m, Val.nat k][2]? = some (Val.nat k) from rfl)
    have hsub := Det.arith' hk' (Det.nat 1) (show BinOp.eval .sub k 1 = k - 1 from rfl)
    have h3 := Det.mk3 (Det.mk2 (Det.var' (P := johnRProgram) (env := E13) (i := 11)
      (v := johnDV n labL υ) rfl) (Det.var' (P := johnRProgram) (env := E13) (i := 7)
      (v := natList (List.range n)) rfl)) hsub
      (Det.var' (P := johnRProgram) (env := E13) (i := 12) (v := natList (johnBall n labL υ 0)) rfl)
    refine (Det.call h3 (johnR_iter_spec (n := n) (labL := labL) (υ := υ) (k - 1))).mono ?_
    have e1 := wt_list2_le (johnDV n labL υ) (natList (List.range n))
    have e2 := wt_list3_le (Val.list [johnDV n labL υ, natList (List.range n)]) (Val.nat (k - 1))
      (natList (johnBall n labL υ 0))
    have wk1 := wt_nat_le (k - 1)
    have p : 10000000 * (k - 1 + 1) * ((n + 1) ^ 4 + (k - 1)) ≤ 20000000 * (n + 1) ^ 6 := by
      calc 10000000 * (k - 1 + 1) * ((n + 1) ^ 4 + (k - 1))
          ≤ 10000000 * (n + 1) * ((n + 1) ^ 4 + (n + 1) ^ 4) := by
            exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
        _ = 20000000 * (n + 1) ^ 5 := by ring
        _ ≤ 20000000 * (n + 1) ^ 6 := Nat.mul_le_mul_left _ y56
    have eR : (natList (johnBall n labL υ (k - 1))).wt = (natList R).wt := rfl
    omega
  -- Step 5: the label of `0` and the first point outside the ball.
  have s5 : Det johnRProgram E14 (.get (.var 8) (.call 62 (mk2 (.nat 0) (.var 13))))
      (Val.nat (johnDeltaR n labL υ k)) (100000000 * Y ^ 6) := by
    have hf := Det.call (Det.mk2 (Det.nat 0) (Det.var' (P := johnRProgram) (env := E14) (i := 13)
      (v := natList R) rfl))
      (findEq_spec (john_at_findEq (P := johnRProgram)) (xs := R) (j := 0) (B := n)
        (fun v hv => (hRok.bits v hv).trans (by omega)) (Nat.zero_le _) hRok.len.le)
    refine (Det.get' (Det.var' (P := johnRProgram) (env := E14) (i := 8)
      (v := Val.list (row.map Val.nat)) rfl) hf (john_get_row hδr)).mono ?_
    have e1 := wt_list2_le (Val.nat 0) (natList R)
    have wi := wt_nat_le (R.findIdx fun x => decide (x = 0))
    have hi : R.findIdx (fun x => decide (x = 0)) ≤ n := by
      have := List.findIdx_le_length (p := fun x => decide (x = 0)) (xs := R)
      have := hRok.len
      omega
    have ew : (Val.list (row.map Val.nat)).wt = (natList row).wt := rfl
    have eδ : (Val.nat (row.getD (R.findIdx fun x => decide (x = 0)) 0)).wt ≤ n * n + 2 :=
      (wt_nat_le _).trans (by
        have : row.getD (R.findIdx fun x => decide (x = 0)) 0 ≤ n * n := hδle
        omega)
    have p : findEqK * (n + 1) ^ 3 ≤ 100000 * (n + 1) ^ 6 := Nat.mul_le_mul_left _ y36
    have ed : (Val.nat (row.getD (R.findIdx fun x => decide (x = 0)) 0)) =
      Val.nat (johnDeltaR n labL υ k) := rfl
    omega
  have t := Det.letE s1 (Det.letE s2 (Det.letE s3 (Det.letE s4 s5)))
  refine t.mono ?_
  have hD20 : (johnDV n labL υ).wt ≤ 20 * Y ^ 6 := by omega
  unfold johnA
  omega

end GI.Degree
