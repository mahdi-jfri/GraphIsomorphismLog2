import Workspace.Impl.JohnCnt

/-!
# The main function

`johnMain` on `[encGroup gs, m, k]` (`john_main_spec`). Its cost is at most
`johnK · (wt + 1) ^ 15`, where `wt` is the weight of the input. The main function binds the
values of `johnMain` one after the other. Each step costs at most `johnA · (wt + 1) ^ 15`
(`john_letE` adds them up).
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

/-- The bound of one step. -/
def johnA : ℕ := 100000000000

/-- The constant of the cost. -/
def johnK : ℕ := 3000000000000

theorem john_letE {P : Program} {env : List Val} {e body : Expr} {v w : Val} {a b c Q : ℕ}
    (ha : Det P env e v (a * Q)) (hb : Det P (env ++ [v]) body w (b * Q)) (hw : w.wt + 1 ≤ c * Q) :
    Det P env (.letE e body) w ((a + b + c) * Q) :=
  (Det.letE ha hb).mono (by rw [Nat.add_mul, Nat.add_mul]; omega)

theorem john_get_row {row : List ℕ} {i : ℕ} (h : i < row.length) :
    (row.map Val.nat)[i]? = some (.nat (row.getD i 0)) := by
  simp [List.getD_eq_getElem?_getD, h]

theorem john_wt_out {n : ℕ} {lam : List (List ℕ)} (ha : JohnAccOK n lam) :
    (Val.list ((johnOut n lam).map natList)).wt ≤ n * (2 * (5 * (n + 1) ^ 2) + 1) + 4 := by
  have hlen := ha.len
  have wO := john_wt_list_le (vs := (johnOut n lam).map natList) (B := 5 * (n + 1) ^ 2) (by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hv
    exact wt_natList_le_sq (fun v hv => by simp only [List.mem_filter, List.mem_range] at hv; omega)
      ((List.length_filter_le _ _).trans (by simpa using hlen)))
  simpa [johnOut] using wO

theorem john_range_det (L : ℕ) : FunDet johnProgram 1 (.nat L) (natList (List.range L))
    (1000 * (L + 1) * ((Val.nat L).wt + L + (natList (List.range L)).wt + 1)) :=
  (range_spec john_at_range L).mono fun w c h => ⟨h.1, by have := h.2; rw [h.1] at this; exact this⟩

theorem john_encFun_eq {n : ℕ} (lab : Fin (n * n) → ℕ) : encFun lab = natList (johnLabL lab) := by
  simp [encFun, natList, johnLabL, List.map_map, Function.comp_def]

/-- The input is heavier than `n` and than the number of generators. -/
theorem john_in_wt {n : ℕ} (gs : List (Perm (Fin n))) (m k : ℕ) :
    n + 1 ≤ (Val.list [encGroup gs, .nat m, .nat k]).wt ∧
      gs.length + 2 ≤ (Val.list [encGroup gs, .nat m, .nat k]).wt ∧
      (encGroup gs).wt < (Val.list [encGroup gs, .nat m, .nat k]).wt ∧
      (Val.nat m).wt < (Val.list [encGroup gs, .nat m, .nat k]).wt ∧
      (Val.nat k).wt < (Val.list [encGroup gs, .nat m, .nat k]).wt ∧
      (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt := by
  have h2 := length_lt_wt_list ((List.finRange n).map fun i => Val.nat ((1 : Perm (Fin n)) i))
  simp only [List.length_map, List.length_finRange] at h2
  have h1 : (encPerm (1 : Perm (Fin n))).wt < (Val.list ((1 :: gs).map encPerm)).wt :=
    wt_le_wt_list (by simp)
  have h3 : (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt :=
    wt_le_wt_list (vs := [.nat n, .list ((1 :: gs).map encPerm)]) (by simp)
  have h4 : (encGroup gs).wt < (Val.list [encGroup gs, .nat m, .nat k]).wt := wt_le_wt_list (by simp)
  have h5 := length_lt_wt_list ((1 :: gs).map encPerm)
  simp only [List.length_map, List.length_cons] at h5
  have hm : (Val.nat m).wt < (Val.list [encGroup gs, .nat m, .nat k]).wt := wt_le_wt_list (by simp)
  have hk : (Val.nat k).wt < (Val.list [encGroup gs, .nat m, .nat k]).wt := wt_le_wt_list (by simp)
  have e : (encPerm (1 : Perm (Fin n))).wt =
    (Val.list ((List.finRange n).map fun i => Val.nat ((1 : Perm (Fin n)) i))).wt := rfl
  refine ⟨by omega, by omega, h4, hm, hk, h3⟩

theorem john_pow_mono {a b : ℕ} (h : a ≤ b) (j : ℕ) : a ^ j ≤ b ^ j := Nat.pow_le_pow_left h j


/-- **The main function.** The hypotheses are facts about the labels of the orbitals; they hold
for the labels of the program by `john_main_hyp`. -/
theorem john_main_spec {n : ℕ} (gs : List (Perm (Fin n))) (m k : ℕ) (lab : Fin (n * n) → ℕ)
    (horb : FunDet johnProgram 12 (encPerms ((1 :: gs).map johnPairPerm)) (encFun lab)
      (orbitK * ((((1 :: gs).map johnPairPerm).length + 1) * (n * n + 1)) ^ 5))
    (hlab : ∀ x, lab x < n * n) (hm : m ≤ n) (hkm : k * (m - k) ≤ n * n)
    (hδ : (johnCnt (johnRow n (johnLabL lab))).findIdx
      (fun c => decide (c = (johnCnt (johnRow n (johnLabL lab))).foldl max 0)) < n)
    (hυ : (johnCnt (johnRow n (johnLabL lab))).findIdx (fun c => decide (c = k * (m - k))) < n)
    (hok : ∀ i ≤ n * n, JohnAccOK n (((List.range (n * n)).take i).foldl
      (johnStep n (johnLabL lab) (johnDelta (johnRow n (johnLabL lab)))
        (johnUps m k (johnRow n (johnLabL lab)))) [])) :
    FunDet johnProgram 0 (.list [encGroup gs, .nat m, .nat k])
      (.list ((johnOut n (johnLam n (johnLabL lab) (johnDelta (johnRow n (johnLabL lab)))
        (johnUps m k (johnRow n (johnLabL lab))))).map natList))
      (johnK * ((Val.list [encGroup gs, .nat m, .nat k]).wt + 1) ^ 15) := by
  obtain ⟨hnW, hgW, hGW, hmW, hkW, hPW⟩ := john_in_wt gs m k
  set W := (Val.list [encGroup gs, .nat m, .nat k]).wt with hW
  set Y := W + 1 with hY
  set Q := Y ^ 15 with hQ
  have hY1 : 1 ≤ Y := by omega
  have hn1 : n + 1 ≤ Y := by omega
  have pj : ∀ j ≤ 15, Y ^ j ≤ Q := fun j hj => Nat.pow_le_pow_right hY1 hj
  have q1 := pj 1 (by omega)
  have q2 := pj 2 (by omega)
  have q3 := pj 3 (by omega)
  have q4 := pj 4 (by omega)
  have q5 := pj 5 (by omega)
  have q6 := pj 6 (by omega)
  have q8 := pj 8 (by omega)
  have q12 := pj 12 (by omega)
  have y1 : Y ≤ Y ^ 1 := by rw [pow_one]
  have y12 : Y ≤ Y ^ 2 := by nlinarith
  have y23 : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right hY1 (by omega)
  have y34 : Y ^ 3 ≤ Y ^ 4 := Nat.pow_le_pow_right hY1 (by omega)
  have y45 : Y ^ 4 ≤ Y ^ 5 := Nat.pow_le_pow_right hY1 (by omega)
  have pn2 : (n + 1) ^ 2 ≤ Y ^ 2 := john_pow_mono hn1 2
  have pn3 : (n + 1) ^ 3 ≤ Y ^ 3 := john_pow_mono hn1 3
  have pn4 : (n + 1) ^ 4 ≤ Y ^ 4 := john_pow_mono hn1 4
  have pn6 : (n + 1) ^ 6 ≤ Y ^ 6 := john_pow_mono hn1 6
  have pn8 : (n + 1) ^ 8 ≤ Y ^ 8 := john_pow_mono hn1 8
  have hnn1 : n * n + 1 ≤ Y ^ 2 := by
    have : (n + 1) ^ 2 = n * n + 2 * n + 1 := by ring
    omega
  have hnn : n ≤ n * n := Nat.le_mul_self n
  -- The lists.
  set labL := johnLabL lab with hlabL
  set row := johnRow n labL with hrow
  set cnt := johnCnt row with hcnt
  set δ := johnDelta row with hδdef
  set υ := johnUps m k row with hυdef
  set lam := johnLam n labL δ υ with hlam
  have hLlen : labL.length = n * n := by simp [labL, johnLabL]
  have hLle : ∀ v ∈ labL, v ≤ n * n := by
    intro v hv
    simp only [labL, johnLabL, List.mem_map] at hv
    obtain ⟨x, -, rfl⟩ := hv
    exact (hlab x).le
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
  have hδr : _ < row.length := hrowlen ▸ hδ
  have hυr : _ < row.length := hrowlen ▸ hυ
  have hδle : δ ≤ n * n := by
    show row.getD _ 0 ≤ n * n
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hδr, Option.getD_some]
    exact hrowle _ (List.getElem_mem _)
  have hυle : υ ≤ n * n := by
    show row.getD _ 0 ≤ n * n
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hυr, Option.getD_some]
    exact hrowle _ (List.getElem_mem _)
  have hL : JohnLabOK n labL δ := ⟨hLlen, hLle, hδle⟩
  have hacc : JohnAccOK n lam := by
    have := hok (n * n) le_rfl
    rwa [List.take_of_length_le (by simp)] at this
  have hlamlen := hacc.len
  -- The weights.
  have wG : (Val.list [Val.nat n, .list ((1 :: gs).map encPerm)]).wt < W := hGW
  have wnn := wt_nat_le (n * n)
  have wn := wt_nat_le n
  have w0 := wt_nat_le 0
  have w1 := wt_nat_le 1
  have w2 := wt_nat_le 2
  have wR2 := john_wt_R2 (n := n)
  have wRn := john_wt_Rn n
  have wlab := john_wt_natList_sq hLlen hLle
  have wrow : (natList row).wt ≤ 5 * (n * n + 1) ^ 2 := wt_natList_le_sq hrowle (by omega)
  have wcnt : (natList cnt).wt ≤ 5 * (n * n + 1) ^ 2 := wt_natList_le_sq hcntle (by omega)
  have hnn4 : (n * n + 1) ^ 2 ≤ Y ^ 4 := by
    calc (n * n + 1) ^ 2 ≤ (Y ^ 2) ^ 2 := john_pow_mono hnn1 2
      _ = Y ^ 4 := by ring
  have wδ := wt_nat_le δ
  have wυ := wt_nat_le υ
  have wD := john_wt_DV n labL δ
  have wΛ := john_wt_acc hacc
  have wout := john_wt_out hacc
  have pout : n * (2 * (5 * (n + 1) ^ 2) + 1) ≤ 11 * Y ^ 3 := by
    have : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    calc _ ≤ (n + 1) * (11 * (n + 1) ^ 2) := Nat.mul_le_mul (by omega) (by omega)
      _ = 11 * (n + 1) ^ 3 := by ring
      _ ≤ 11 * Y ^ 3 := Nat.mul_le_mul_left _ pn3
  have wPG : (Val.list (((1 :: gs).map johnPairPerm).map encPerm)).wt ≤ 9 * Y ^ 5 + 4 := by
    have := john_wt_list_le (vs := ((1 :: gs).map johnPairPerm).map encPerm)
      (B := 4 * (n * n + 1) ^ 2) (by
        intro v hv; obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hv; exact wt_encPerm_le _)
    simp only [List.length_map, List.length_cons] at this
    have : (gs.length + 1) * (2 * (4 * (n * n + 1) ^ 2) + 1) ≤ 9 * Y ^ 5 := by
      calc _ ≤ Y * (9 * Y ^ 4) := Nat.mul_le_mul (by omega) (by omega)
        _ = 9 * Y ^ 5 := by ring
    omega
  -- Step 14: the output.
  have s14 : Det johnProgram [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm), natList labL, natList (List.range n), natList row, natList cnt, Val.nat δ, Val.nat υ, johnDV n labL δ, Val.list (lam.map natList)]
      (.call 98 (mk2 (mk2 (.var 13) (.call 1 (.length (.var 13)))) (.var 7)))
      (.list ((johnOut n lam).map natList)) (johnA * Q) := by
    have hΛ := (Det.var' (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm), natList labL, natList (List.range n), natList row, natList cnt, Val.nat δ, Val.nat υ, johnDV n labL δ, Val.list (lam.map natList)]) (i := 13) (v := Val.list (lam.map natList)) rfl)
    have hlen := Det.length hΛ
    rw [List.length_map] at hlen
    have hR := Det.call hlen (john_range_det lam.length)
    have hmk := Det.mk2 (Det.mk2 hΛ hR) (Det.var' (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm), natList labL, natList (List.range n), natList row, natList cnt, Val.nat δ, Val.nat υ, johnDV n labL δ, Val.list (lam.map natList)]) (i := 7) (v := natList (List.range n)) rfl)
    refine (Det.call hmk (john_mapOut_spec hacc)).mono ?_
    have e1 := wt_list2_le (Val.list (lam.map natList)) (natList (List.range lam.length))
    have e2 := wt_list2_le (Val.list [.list (lam.map natList), natList (List.range lam.length)])
      (natList (List.range n))
    have wRl : (natList (List.range lam.length)).wt ≤ 5 * (n + 1) ^ 2 :=
      wt_natList_le_sq (fun v hv => by simp only [List.mem_range] at hv; omega) (by simpa using hlamlen)
    have wl := wt_nat_le lam.length
    have p : 1000 * (lam.length + 1) * ((Val.nat lam.length).wt + lam.length +
        (natList (List.range lam.length)).wt + 1) ≤ 1000 * (10 * Y ^ 3) := by
      rw [Nat.mul_assoc]
      refine Nat.mul_le_mul_left _ ?_
      calc _ ≤ Y * (10 * Y ^ 2) := Nat.mul_le_mul (by omega) (by omega)
        _ = 10 * Y ^ 3 := by ring
    have p2 : 10000000 * (n + 1) ^ 4 ≤ 10000000 * Y ^ 4 := Nat.mul_le_mul_left _ pn4
    unfold johnA
    omega
  -- Step 13: the fold.
  have s13 : Det johnProgram [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm), natList labL, natList (List.range n), natList row, natList cnt, Val.nat δ, Val.nat υ, johnDV n labL δ]
      (.call 74 (mk3 (.snoc (mk4 (.var 12) (.var 6) (.var 2) (.var 11)) (.var 7)) (.var 4) .nil))
      (Val.list (lam.map natList)) (johnA * Q) := by
    have h4 := Det.mk4 (Det.var' (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm), natList labL, natList (List.range n), natList row, natList cnt, Val.nat δ, Val.nat υ, johnDV n labL δ]) (i := 12) (v := johnDV n labL δ) rfl) (Det.var' (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm), natList labL, natList (List.range n), natList row, natList cnt, Val.nat δ, Val.nat υ, johnDV n labL δ]) (i := 6) (v := natList labL) rfl) (Det.var' (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm), natList labL, natList (List.range n), natList row, natList cnt, Val.nat δ, Val.nat υ, johnDV n labL δ]) (i := 2) (v := Val.nat n) rfl) (Det.var' (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm), natList labL, natList (List.range n), natList row, natList cnt, Val.nat δ, Val.nat υ, johnDV n labL δ]) (i := 11) (v := Val.nat υ) rfl)
    have hs := Det.snoc h4 (Det.var' (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm), natList labL, natList (List.range n), natList row, natList cnt, Val.nat δ, Val.nat υ, johnDV n labL δ]) (i := 7) (v := natList (List.range n)) rfl)
    have hmk := Det.mk3 hs (Det.var' (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm), natList labL, natList (List.range n), natList row, natList cnt, Val.nat δ, Val.nat υ, johnDV n labL δ]) (i := 4) (v := natList (List.range (n * n))) rfl) (Det.nil (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm), natList labL, natList (List.range n), natList row, natList cnt, Val.nat δ, Val.nat υ, johnDV n labL δ]))
    refine (Det.call hmk (john_fold_spec hL hυle hok)).mono ?_
    have ec : (Val.list ([johnDV n labL δ, natList labL, Val.nat n, Val.nat υ] ++
        [natList (List.range n)])).wt = (johnCtxV n labL δ υ).wt := rfl
    have e1 := wt_list4_le (johnDV n labL δ) (natList labL) (Val.nat n) (Val.nat υ)
    have e2 := wt_list_snoc_le [johnDV n labL δ, natList labL, Val.nat n, Val.nat υ]
      (natList (List.range n))
    have e3 := wt_list3_le (johnCtxV n labL δ υ) (natList (List.range (n * n))) (Val.list [])
    have ed : (Val.list [Val.list ([johnDV n labL δ, natList labL, Val.nat n, Val.nat υ] ++
        [natList (List.range n)]), natList (List.range (n * n)), Val.list []]).wt =
        (Val.list [johnCtxV n labL δ υ, natList (List.range (n * n)), Val.list []]).wt := rfl
    have el : (Val.list ((johnLam n labL δ υ).map natList)).wt =
        (Val.list (lam.map natList)).wt := rfl
    have wnil : (Val.list []).wt ≤ 10 := by simp [Val.wt, GI.Machine.len_zero]
    have p2 : 100000000 * (n + 1) ^ 8 ≤ 100000000 * Y ^ 8 := Nat.mul_le_mul_left _ pn8
    unfold johnA
    omega
  have hnn6 : (n * n + 1) ^ 3 ≤ Y ^ 6 := by
    calc (n * n + 1) ^ 3 ≤ (Y ^ 2) ^ 3 := john_pow_mono hnn1 3
      _ = Y ^ 6 := by ring
  have hnn8 : (n * n + 1) ^ 4 ≤ Y ^ 8 := by
    calc (n * n + 1) ^ 4 ≤ (Y ^ 2) ^ 4 := john_pow_mono hnn1 4
      _ = Y ^ 8 := by ring
  have hwout : (Val.list ((johnOut n lam).map natList)).wt + 1 ≤ johnA * Q := by
    unfold johnA; omega
  -- Step 12: the matrix `D`.
  have s12 : Det johnProgram [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm), natList labL, natList (List.range n), natList row, natList cnt, Val.nat δ, Val.nat υ]
      (.call 66 (mk2 (mk4 (.var 6) (.var 2) (.var 10) (.var 7)) (.var 7)))
      (johnDV n labL δ) (johnA * Q) := by
    have hmk := Det.mk2 (Det.mk4 (Det.var' (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm), natList labL, natList (List.range n), natList row, natList cnt, Val.nat δ, Val.nat υ]) (i := 6) (v := natList labL) rfl) (Det.var' (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm), natList labL, natList (List.range n), natList row, natList cnt, Val.nat δ, Val.nat υ]) (i := 2) (v := Val.nat n) rfl) (Det.var' (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm), natList labL, natList (List.range n), natList row, natList cnt, Val.nat δ, Val.nat υ]) (i := 10) (v := Val.nat δ) rfl) (Det.var' (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm), natList labL, natList (List.range n), natList row, natList cnt, Val.nat δ, Val.nat υ]) (i := 7) (v := natList (List.range n)) rfl)) (Det.var' (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm), natList labL, natList (List.range n), natList row, natList cnt, Val.nat δ, Val.nat υ]) (i := 7) (v := natList (List.range n)) rfl)
    refine (Det.call hmk (john_matD_spec hL)).mono ?_
    have e1 := wt_list4_le (natList labL) (Val.nat n) (Val.nat δ) (natList (List.range n))
    have e2 := wt_list2_le (Val.list [natList labL, Val.nat n, Val.nat δ, natList (List.range n)])
      (natList (List.range n))
    have p : 1000000 * (n + 1) ^ 6 ≤ 1000000 * Y ^ 6 := Nat.mul_le_mul_left _ pn6
    unfold johnA
    omega
  -- Step 11: the label `υ`.
  have s11 : Det johnProgram [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm), natList labL, natList (List.range n), natList row, natList cnt, Val.nat δ]
      (.get (.var 8) (.call 62 (mk2 (.arith .mul (.get (.var 0) (.nat 2))
        (.arith .sub (.get (.var 0) (.nat 1)) (.get (.var 0) (.nat 2)))) (.var 9))))
      (Val.nat υ) (johnA * Q) := by
    have hk' := Det.get' (Det.var' (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm), natList labL, natList (List.range n), natList row, natList cnt, Val.nat δ]) (i := 0) (v := Val.list [encGroup gs, .nat m, .nat k]) rfl) (Det.nat 2)
      (show [encGroup gs, Val.nat m, Val.nat k][2]? = some (Val.nat k) from rfl)
    have hm' := Det.get' (Det.var' (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm), natList labL, natList (List.range n), natList row, natList cnt, Val.nat δ]) (i := 0) (v := Val.list [encGroup gs, .nat m, .nat k]) rfl) (Det.nat 1)
      (show [encGroup gs, Val.nat m, Val.nat k][1]? = some (Val.nat m) from rfl)
    have hsub := Det.arith' hm' hk' (show BinOp.eval .sub m k = m - k from rfl)
    have hmul := Det.arith' hk' hsub (show BinOp.eval .mul k (m - k) = k * (m - k) from rfl)
    have hf := Det.call (Det.mk2 hmul (Det.var' (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm), natList labL, natList (List.range n), natList row, natList cnt, Val.nat δ]) (i := 9) (v := natList cnt) rfl))
      (findEq_spec john_at_findEq (xs := cnt) (B := n * n) hcntle hkm (by omega))
    refine (Det.get' (Det.var' (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm), natList labL, natList (List.range n), natList row, natList cnt, Val.nat δ]) (i := 8) (v := Val.list (row.map Val.nat)) rfl) hf (john_get_row hυr)).mono ?_
    have e1 := wt_list2_le (Val.nat (k * (m - k))) (natList cnt)
    have wi := wt_nat_le (cnt.findIdx fun c => decide (c = k * (m - k)))
    have ew : (Val.list (row.map Val.nat)).wt = (natList row).wt := rfl
    have hmk : m - k ≤ n := by omega
    have wkm := wt_nat_le (k * (m - k))
    have eυ : (Val.nat (row.getD (cnt.findIdx fun c => decide (c = k * (m - k))) 0)).wt =
      (Val.nat υ).wt := rfl
    have p : findEqK * (n * n + 1) ^ 3 ≤ 100000 * Y ^ 6 := Nat.mul_le_mul_left _ hnn6
    unfold johnA
    omega
  -- Step 10: the label `δ`.
  have s10 : Det johnProgram [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm), natList labL, natList (List.range n), natList row, natList cnt]
      (.get (.var 8) (.call 62 (mk2 (.call 57 (.var 9)) (.var 9))))
      (Val.nat δ) (johnA * Q) := by
    have hmax := Det.call (Det.var' (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm), natList labL, natList (List.range n), natList row, natList cnt]) (i := 9) (v := natList cnt) rfl) (max_spec john_at_max (xs := cnt) (B := n * n) hcntle (by omega))
    have hf := Det.call (Det.mk2 hmax (Det.var' (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm), natList labL, natList (List.range n), natList row, natList cnt]) (i := 9) (v := natList cnt) rfl))
      (findEq_spec john_at_findEq (xs := cnt) (j := cnt.foldl max 0) (B := n * n) hcntle
        (foldl_max_le (Nat.zero_le _) hcntle) (by omega))
    refine (Det.get' (Det.var' (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm), natList labL, natList (List.range n), natList row, natList cnt]) (i := 8) (v := Val.list (row.map Val.nat)) rfl) hf (john_get_row hδr)).mono ?_
    have hmx : cnt.foldl max 0 ≤ n * n := foldl_max_le (Nat.zero_le _) hcntle
    have wmx := wt_nat_le (cnt.foldl max 0)
    have e1 := wt_list2_le (Val.nat (cnt.foldl max 0)) (natList cnt)
    have wi := wt_nat_le (cnt.findIdx fun c => decide (c = cnt.foldl max 0))
    have ew : (Val.list (row.map Val.nat)).wt = (natList row).wt := rfl
    have eδ : (Val.nat (row.getD (cnt.findIdx fun c => decide (c = cnt.foldl max 0)) 0)).wt =
      (Val.nat δ).wt := rfl
    have p1 : maxK * (n * n + 1) ^ 3 ≤ 100000 * Y ^ 6 := Nat.mul_le_mul_left _ hnn6
    have p2 : findEqK * (n * n + 1) ^ 3 ≤ 100000 * Y ^ 6 := Nat.mul_le_mul_left _ hnn6
    unfold johnA
    omega
  -- Step 9: the counts.
  have s9 : Det johnProgram [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm), natList labL, natList (List.range n), natList row] (.call 48 (mk2 (.var 8) (.var 8))) (natList cnt) (johnA * Q) := by
    refine (Det.call (Det.mk2 (Det.var' (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm), natList labL, natList (List.range n), natList row]) (i := 8) (v := natList row) rfl) (Det.var' (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm), natList labL, natList (List.range n), natList row]) (i := 8) (v := natList row) rfl))
      (john_mapCnt_spec (B := n * n) hrowle (by omega))).mono ?_
    have e1 := wt_list2_le (natList row) (natList row)
    have ec : (natList (johnCnt row)).wt = (natList cnt).wt := rfl
    have p1 : countK * (n * n + 1) ^ 4 ≤ 100000 * Y ^ 8 := Nat.mul_le_mul_left _ hnn8
    have p2 : 2000000 * (n * n + 1) ^ 3 ≤ 2000000 * Y ^ 6 := Nat.mul_le_mul_left _ hnn6
    unfold johnA
    omega
  -- Step 8: row `0`.
  have s8 : Det johnProgram [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm), natList labL, natList (List.range n)] (.call 44 (mk2 (.var 6) (.var 7))) (natList row) (johnA * Q) := by
    have hg := gather_spec john_at_gather (L := labL.map Val.nat) (is := List.range n)
      (fun i hi => by simp only [List.mem_range] at hi; simp only [List.length_map]; omega)
    have he : Val.list ((List.range n).map fun i => (labL.map Val.nat).getD i (.nat 0)) =
        natList row := by
      simp [natList, row, johnRow, Function.comp_def, List.getD_map]
    have hc := Det.call (Det.mk2 (Det.var' (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm), natList labL, natList (List.range n)]) (i := 6) (v := natList labL) rfl) (Det.var' (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm), natList labL, natList (List.range n)]) (i := 7) (v := natList (List.range n)) rfl)) hg
    rw [he] at hc
    refine hc.mono ?_
    have e1 := wt_list2_le (natList labL) (natList (List.range n))
    have ew : (Val.list [Val.list (labL.map Val.nat), natList (List.range n)]).wt =
      (Val.list [natList labL, natList (List.range n)]).wt := rfl
    have p : gatherK * ((Val.list [Val.list (labL.map Val.nat), natList (List.range n)]).wt + 1) ^ 3
        ≤ 100000 * (29791 * Y ^ 12) := by
      refine Nat.mul_le_mul_left _ ?_
      calc _ ≤ (31 * Y ^ 4) ^ 3 := john_pow_mono (by omega) 3
        _ = 29791 * Y ^ 12 := by ring
    unfold johnA
    omega
  -- Step 7: the points.
  have s7 : Det johnProgram [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm), natList labL] (.call 1 (.var 2)) (natList (List.range n)) (johnA * Q) := by
    refine (Det.call (Det.var' (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm), natList labL]) (i := 2) (v := Val.nat n) rfl) (john_range_det n)).mono ?_
    have p : 1000 * (n + 1) * ((Val.nat n).wt + n + (natList (List.range n)).wt + 1) ≤
        1000 * (10 * Y ^ 3) := by
      rw [Nat.mul_assoc]
      refine Nat.mul_le_mul_left _ ?_
      calc _ ≤ Y * (10 * Y ^ 2) := Nat.mul_le_mul (by omega) (by omega)
        _ = 10 * Y ^ 3 := by ring
    unfold johnA
    omega
  -- Step 6: the orbitals.
  have s6 : Det johnProgram [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm)] (.call 12 (mk2 (.var 3) (.var 5))) (natList labL) (johnA * Q) := by
    have hc := Det.call (Det.mk2 (Det.var' (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm)]) (i := 3) (v := Val.nat (n * n)) rfl) (Det.var' (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n)), Val.list (((1 :: gs).map johnPairPerm).map encPerm)]) (i := 5) (v := Val.list (((1 :: gs).map johnPairPerm).map encPerm)) rfl)) horb
    rw [john_encFun_eq] at hc
    refine hc.mono ?_
    have e1 := wt_list2_le (Val.nat (n * n)) (Val.list (((1 :: gs).map johnPairPerm).map encPerm))
    have el : ((1 :: gs).map johnPairPerm).length + 1 ≤ Y := by simp; omega
    have p : orbitK * ((((1 :: gs).map johnPairPerm).length + 1) * (n * n + 1)) ^ 5 ≤
        1000000 * Q := by
      refine Nat.mul_le_mul_left _ ?_
      calc _ ≤ (Y * Y ^ 2) ^ 5 := john_pow_mono (Nat.mul_le_mul el hnn1) 5
        _ = Q := by rw [hQ]; ring
    have ew : (natList (johnLabL lab)).wt = (natList labL).wt := rfl
    unfold johnA
    omega
  -- Step 5: the pair generators.
  have s5 : Det johnProgram [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n))]
      (.call 4 (mk2 (mk2 (.var 2) (.var 4)) (.get (.var 1) (.nat 1))))
      (Val.list (((1 :: gs).map johnPairPerm).map encPerm)) (johnA * Q) := by
    have hG := Det.get' (Det.var' (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n))]) (i := 1) (v := Val.list [Val.nat n, Val.list ((1 :: gs).map encPerm)]) rfl) (Det.nat 1)
      (show [Val.nat n, Val.list ((1 :: gs).map encPerm)][1]? =
        some (Val.list ((1 :: gs).map encPerm)) from rfl)
    have hc := Det.call (Det.mk2 (Det.mk2 (Det.var' (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n))]) (i := 2) (v := Val.nat n) rfl) (Det.var' (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n), natList (List.range (n * n))]) (i := 4) (v := natList (List.range (n * n))) rfl)) hG) (john_mapPg_spec (1 :: gs))
    rw [show ((1 :: gs).map fun g => encPerm (johnPairPerm g)) =
      ((1 :: gs).map johnPairPerm).map encPerm by simp [List.map_map, Function.comp_def]] at hc
    refine hc.mono ?_
    have e1 := wt_list2_le (Val.nat n) (natList (List.range (n * n)))
    have e2 := wt_list2_le (Val.list [Val.nat n, natList (List.range (n * n))])
      (Val.list ((1 :: gs).map encPerm))
    have eG : (encGroup gs).wt = (Val.list [Val.nat n, Val.list ((1 :: gs).map encPerm)]).wt := rfl
    have el : n + (1 :: gs).length + 1 ≤ 2 * Y := by simp; omega
    have p : 100000000 * (n + (1 :: gs).length + 1) ^ 8 ≤ 100000000 * (256 * Y ^ 8) := by
      refine Nat.mul_le_mul_left _ ?_
      calc _ ≤ (2 * Y) ^ 8 := john_pow_mono el 8
        _ = 256 * Y ^ 8 := by ring
    unfold johnA
    omega
  -- Step 4: the pair indices.
  have s4 : Det johnProgram [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n)] (.call 1 (.var 3)) (natList (List.range (n * n))) (johnA * Q) := by
    refine (Det.call (Det.var' (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n, Val.nat (n * n)]) (i := 3) (v := Val.nat (n * n)) rfl) (john_range_det (n * n))).mono ?_
    have p : 1000 * (n * n + 1) * ((Val.nat (n * n)).wt + n * n +
        (natList (List.range (n * n))).wt + 1) ≤ 1000 * (10 * Y ^ 6) := by
      rw [Nat.mul_assoc]
      refine Nat.mul_le_mul_left _ ?_
      calc _ ≤ Y ^ 2 * (10 * Y ^ 4) := Nat.mul_le_mul hnn1 (by omega)
        _ = 10 * Y ^ 6 := by ring
    unfold johnA
    omega
  -- Steps 1 to 3.
  have s3 : Det johnProgram [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n] (.arith .mul (.var 2) (.var 2)) (Val.nat (n * n)) (johnA * Q) :=
    (Det.arith' (Det.var' (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n]) (i := 2) (v := Val.nat n) rfl) (Det.var' (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k], encGroup gs, Val.nat n]) (i := 2) (v := Val.nat n) rfl) (show BinOp.eval .mul n n = n * n from rfl)).mono
      (by unfold johnA; omega)
  have s2 : Det johnProgram [Val.list [encGroup gs, .nat m, .nat k], encGroup gs] (.get (.var 1) (.nat 0)) (Val.nat n) (johnA * Q) := by
    refine (Det.get' (Det.var' (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k], encGroup gs]) (i := 1) (v := Val.list [Val.nat n, Val.list ((1 :: gs).map encPerm)]) rfl) (Det.nat 0)
      (show [Val.nat n, Val.list ((1 :: gs).map encPerm)][0]? = some (Val.nat n) from rfl)).mono ?_
    have eG : (encGroup gs).wt = (Val.list [Val.nat n, Val.list ((1 :: gs).map encPerm)]).wt := rfl
    unfold johnA
    omega
  have s1 : Det johnProgram [Val.list [encGroup gs, .nat m, .nat k]] (.get (.var 0) (.nat 0)) (encGroup gs) (johnA * Q) :=
    (Det.get' (Det.var' (P := johnProgram) (env := [Val.list [encGroup gs, .nat m, .nat k]]) (i := 0) (v := Val.list [encGroup gs, .nat m, .nat k]) rfl) (Det.nat 0)
      (show [encGroup gs, Val.nat m, Val.nat k][0]? = some (encGroup gs) from rfl)).mono
      (by unfold johnA; omega)
  -- The chain of `letE`.
  have t := john_letE s1 (john_letE s2 (john_letE s3 (john_letE s4 (john_letE s5 (john_letE s6
    (john_letE s7 (john_letE s8 (john_letE s9 (john_letE s10 (john_letE s11 (john_letE s12
    (john_letE s13 s14 hwout) hwout) hwout) hwout) hwout) hwout) hwout) hwout) hwout) hwout)
    hwout) hwout) hwout
  refine FunDet.intro (show johnProgram.funs[0]? = some johnMain from rfl) (t.mono ?_)
  unfold johnA johnK
  omega

end GI.Impl
