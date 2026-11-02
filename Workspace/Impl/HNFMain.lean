import Workspace.Impl.HNFTabs

/-!
# The Hermite program

On `[r, c, A]` the main function runs, in order:

1. Bareiss elimination, giving the rows `s` and `d = det A[s,:]`;
2. the numbers `K` and `m = |d| K` (`hnfNumsF`);
3. the complement of `s`;
4. `r + r`;
5. the table of the big matrix `[[A', I], [0, K I]]` mod `m`;
6. the modular Hermite form of the big matrix;
7. the table of the transform `U`;
8. the table of the Hermite form `H`;

and returns `[U, H]`. By `GI.Proved.hnfRect_spec` these are the outputs `hnfRectU`, `hnfRectH`.
All sizes are bounded with `W`, the weight of the input, and `L = 10 (W + 1)^2`.
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved
open GI.Machine (BinOp len len_le_iff)

variable {r c : ℕ}

/-! ### Facts about the input -/

theorem hnf_natAbs_lt_wt (z : ℤ) : z.natAbs < 2 ^ (encInt z).wt := by
  apply Nat.size_le.mp
  rw [← Nat.size_eq_bits_len] at *
  have h1 := length_lt_wt_list ((Nat.bits z.natAbs).map fun b => Val.nat (if b then 1 else 0))
  have h2 : (Val.list ((Nat.bits z.natAbs).map fun b => Val.nat (if b then 1 else 0))).wt <
      (encInt z).wt := wt_le_wt_list (by simp [encInt])
  simp only [List.length_map, ← Nat.size_eq_bits_len] at h1
  omega

theorem hnf_entry_lt_wt (A : Matrix (Fin r) (Fin c) ℤ) (i : Fin r) (j : Fin c) :
    (A i j).natAbs < 2 ^ (encIntMatrix A).wt := by
  refine lt_of_lt_of_le (hnf_natAbs_lt_wt (A i j)) (Nat.pow_le_pow_right (by decide) ?_)
  exact (lt_trans (linVecEntryWt (A i) j) (hnf_row_wt_lt A i)).le

theorem hnf_rows_lt_wt (A : Matrix (Fin r) (Fin c) ℤ) : r < (encIntMatrix A).wt := by
  have := length_lt_wt_list ((List.finRange r).map fun i => linVecVal (A i))
  simpa [encIntMatrix, linVecVal] using this

theorem hnf_rcB {W : ℕ} (hrW : r ≤ W) (hcr : c ≤ r) : r * (c * 2 ^ W) < 2 ^ (3 * W) := by
  have h1 : r < 2 ^ W := hnf_lt_two_pow_of_le hrW
  have h2 : c * 2 ^ W ≤ 2 ^ W * 2 ^ W :=
    Nat.mul_le_mul_right _ (hnf_lt_two_pow_of_le (hcr.trans hrW)).le
  have h3 : r * (c * 2 ^ W) < 2 ^ W * (2 ^ W * 2 ^ W) := by
    rcases Nat.eq_zero_or_pos (c * 2 ^ W) with h0 | h0
    · rw [h0, Nat.mul_zero]; positivity
    · exact Nat.mul_lt_mul_of_lt_of_le h1 h2 (by positivity)
  have e : 2 ^ W * (2 ^ W * 2 ^ W) = 2 ^ (3 * W) := by ring
  omega

theorem hnfAbsSum_ge {n : ℕ} (x : Fin n → ℤ) (j : Fin n) : (x j).natAbs ≤ hnfAbsSum x n := by
  rw [hnfAbsSum_full]
  exact List.le_sum_of_mem (List.mem_map.mpr ⟨j, List.mem_finRange _, rfl⟩)

theorem hnfAbsTot_ge (A : Matrix (Fin r) (Fin c) ℤ) (i : Fin r) (j : Fin c) :
    (A i j).natAbs ≤ hnfAbsTot A r := by
  refine (hnfAbsSum_ge (A i) j).trans ?_
  unfold hnfAbsTot
  rw [List.take_of_length_le (by simp)]
  exact List.le_sum_of_mem (List.mem_map.mpr ⟨i, List.mem_finRange _, rfl⟩)

/-- `|A i j| ≤ T`. -/
theorem hnf_abs_le_Tn (A : Matrix (Fin r) (Fin c) ℤ) (i : Fin r) (j : Fin c) :
    |A i j| ≤ (hnfTn A : ℤ) := by
  have h := hnfAbsTot_ge A i j
  have : ((A i j).natAbs : ℤ) ≤ (hnfTn A : ℤ) := by
    unfold hnfTn; exact_mod_cast (show (A i j).natAbs ≤ hnfAbsTot A r + 1 by omega)
  rwa [Int.natCast_natAbs] at this

theorem hnfComplVal_wt (s : List (Fin r)) : (hnfComplVal s).wt ≤ 5 * (r + 1) ^ 2 := by
  have hcl : (hnfCompl s).length ≤ r := by
    unfold hnfCompl; exact (List.length_filter_le _ _).trans (by simp)
  unfold hnfComplVal
  exact wt_natList_le_sq (fun x hx => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx; exact j.isLt.le) (by simpa using hcl)

/-! ### The program -/

/-- The main function. -/
def hnfMainE : Expr :=
  .letE (.call 18 (.var 0))
  (.letE (.call 150 (mk4 (arg 0) (arg 1) (arg 2) (.get (.var 1) (.nat 1))))
  (.letE (.call 54 (mk2 (.get (.var 1) (.nat 0)) (arg 0)))
  (.letE (.arith .add (arg 0) (arg 0))
  (.letE (.call 67 (mk3 (.snoc (.snoc (mk4 (arg 2) (.var 3) (.get (.var 2) (.nat 0))
      (.get (.var 2) (.nat 1))) (arg 0)) (arg 1)) (.var 4) (.var 4)))
  (.letE (.call 84 (mk3 (.get (.var 2) (.nat 1)) (.var 4) (.var 5)))
  (.letE (.call 116 (mk3 (mk3 (.var 6) (.get (.var 2) (.nat 0)) (arg 0)) (arg 0) (arg 0)))
  (.letE (.call 133 (mk3 (mk3 (.var 6) (.get (.var 2) (.nat 0)) (arg 0)) (arg 0) (arg 1)))
    (mk2 (.var 7) (.var 8)))))))))

/-- Where the pieces are. -/
structure hnfMainAt (P : Program) : Prop where
  ints : P.HasAt 0 (linIntFuns 0)
  bar : P.HasAt 18 (hnfBarFuns 18 0)
  abs : P.HasAt 42 (hnfMatAbsFuns 42 0)
  pow : P.HasAt 50 (hnfPowFuns 50)
  compl : P.HasAt 54 (hnfComplFuns 54)
  tb : P.HasAt 67 (hnfTabFuns 67 83)
  bcell : P.funs[83]? = some (hnfBigCellF 0)
  md : P.HasAt 84 (hnfModFuns 84 0)
  tu : P.HasAt 116 (hnfTabFuns 116 132)
  ucell : P.funs[132]? = some (hnfUCellF 0)
  th : P.HasAt 133 (hnfTabFuns 133 149)
  hcell : P.funs[149]? = some hnfHCellF
  nums : P.funs[150]? = some (hnfNumsF 42 50 0)
  main : P.funs[151]? = some hnfMainE

/-- The parameter `X` of the costs, from the input weight `W`. -/
def hnfXW (W : ℕ) : ℕ := 1000 * ((4 * W + 2) * (hnfL W + 1))

/-- The cost of the main function. -/
def hnfMainCost (W : ℕ) : ℕ :=
  200 * (hnfBarCost (hnfXW W) + hnfNumsCost (hnfXW W) + hnfComplCost (10 * (hnfXW W * hnfXW W)) +
    hnfTabCost (100 * (hnfXW W * hnfXW W)) (hnfBigCellCost (10 * (100 * (hnfXW W * hnfXW W)) + 18)) +
    hnfModCost (hnfXW W) +
    hnfTabCost (100 * (hnfXW W * hnfXW W))
      (hnfUCellCost (10 * (100 * (hnfXW W * hnfXW W)) + 18 + 100 * (hnfL W + 1))) +
    hnfTabCost (100 * (hnfXW W * hnfXW W)) (hnfHCellCost (10 * (100 * (hnfXW W * hnfXW W)) + 18)) +
    hnfXW W + 100)

theorem hnfXW_facts (W : ℕ) : 1000 * (W + 1) ≤ hnfXW W ∧ 1000 * (hnfL W + 1) ≤ hnfXW W ∧
    hnfL W ≤ hnfXW W ∧ 3 * W ≤ hnfXW W := by
  unfold hnfXW
  have h1 : 1 ≤ hnfL W + 1 := by omega
  have h2 : W + 1 ≤ (4 * W + 2) * (hnfL W + 1) := by nlinarith
  have h3 : hnfL W + 1 ≤ (4 * W + 2) * (hnfL W + 1) := by nlinarith
  omega

set_option maxHeartbeats 8000000 in
/-- **The Hermite program.** -/
theorem hnfMain_spec {P : Program} (h : hnfMainAt P) (I : FullRankInst) :
    FunDet P 151 (fullRankInput I)
      (.list [encIntMatrix (hnfRectU I.A (hnfTn I.A)), encIntMatrix (hnfRectH I.A I.c_le (hnfTn I.A))])
      (hnfMainCost (fullRankInput I).wt) := by
  obtain ⟨r, c, hc0, hcr, A, hA⟩ := I
  simp only
  set W := (fullRankInput ⟨r, c, hc0, hcr, A, hA⟩).wt with hW
  have eW : (Val.list [.nat r, .nat c, encIntMatrix A]).wt = W := rfl
  set L := hnfL W with hL
  set X := hnfXW W with hX
  obtain ⟨hX1, hX2, hX3, hX4⟩ := hnfXW_facts W
  rw [← hL, ← hX] at hX2 hX3
  rw [← hX] at hX1 hX4
  have hI := linInt_spec h.ints
  have hD := hnfDecAt_of h.ints
  have hE := hnfEncAt_of h.ints
  -- facts about the input
  have wA : (encIntMatrix A).wt < W := wt_le_wt_list (by simp)
  have wr : (Val.nat r).wt < W := wt_le_wt_list (by simp)
  have wc : (Val.nat c).wt < W := wt_le_wt_list (by simp)
  have hrW : r ≤ W := (hnf_rows_lt_wt A).le.trans wA.le
  have hAW : ∀ i j, (A i j).natAbs < 2 ^ W := fun i j =>
    lt_of_lt_of_le (hnf_entry_lt_wt A i j) (Nat.pow_le_pow_right (by decide) wA.le)
  have hr0 : 0 < r := lt_of_lt_of_le hc0 hcr
  set Tz : ℤ := (hnfTn A : ℤ) with hTz
  have hT1 : 1 ≤ Tz := by rw [hTz]; unfold hnfTn; omega
  have hT : ∀ i j, |A i j| ≤ Tz := hnf_abs_le_Tn A
  obtain ⟨-, -, -, hUK, hHd, hdT⟩ := hnfRect_spec A hA hc0 hcr hT1 hT
  set st := hnfBarIter A c with hst
  set s := st.s with hs
  set d := st.d with hd
  obtain ⟨hKL, hmL, hbar⟩ := hnf_sizes A hrW hcr hAW hdT
  rw [← hL] at hKL hmL hbar
  have hsq := hnfRect_sq A hA hc0 hcr hT1
  have hrows := (hnfBar_rows A hA ⟨0, hr0⟩ ⟨0, hc0⟩).1
  have hd0 : d ≠ 0 := hsq.d_ne
  set Kn := hnfKn A with hKn
  set mn := hnfMn A d with hmn
  have eK : hnfK r Tz = (Kn : ℤ) := (hnfKn_eq A).symm
  have em : |d| * (Kn : ℤ) = (mn : ℤ) := by
    rw [hmn, hnfMn]; push_cast; rfl
  rw [eK] at hsq hUK hHd
  rw [em] at hHd
  set A' := hnfAp A s with hA'
  set Hb := hnfModMat (mn : ℤ) (hnfBig A' (Kn : ℤ)) with hHb
  have eHb : hnfBigH A' d (Kn : ℤ) = Hb := by rw [hHb, hnfBigH, em]
  have hHb' := (hnfBigH_spec hsq).2.2
  rw [eHb, em] at hHb'
  have hXdef : X = 1000 * ((4 * W + 2) * (L + 1)) := rfl
  have hQ : (r + r + c + 1) * (L + 1) ≤ (4 * W + 2) * (L + 1) := Nat.mul_le_mul_right _ (by omega)
  have hXb : 1000 * ((r + c + 1) * (L + 1)) ≤ X := by
    rw [hXdef]; exact Nat.mul_le_mul_left _ (le_trans (Nat.mul_le_mul_right _ (by omega)) hQ)
  have hXm : 1000 * ((r + r + 1) * (L + 1)) ≤ X := by
    rw [hXdef]; exact Nat.mul_le_mul_left _ (le_trans (Nat.mul_le_mul_right _ (by omega)) hQ)
  have hXq : 1000 * ((r + r + (r + r) + 1) * (L + 1)) ≤ X := by
    rw [hXdef]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
  have hXX : 1000 * X ≤ X * X := Nat.mul_le_mul_right _ (by omega)
  have hXX' : X ≤ X * X := Nat.le_mul_self X
  have hdL : d.natAbs < 2 ^ L := by
    have : d.natAbs ≤ mn := by
      rw [hmn, hnfMn]; exact Nat.le_mul_of_pos_right _ (by unfold hnfKn; omega)
    omega
  have wd : (encInt d).wt ≤ 20 * (L + 1) := hnf_wt_int hdL
  have wK : (encInt (Kn : ℤ)).wt ≤ 20 * (L + 1) := hnf_wt_int (by simpa using hKL)
  have wm : (encInt (mn : ℤ)).wt ≤ 20 * (L + 1) := hnf_wt_int (by simpa using hmL)
  set inp := Val.list [.nat r, .nat c, encIntMatrix A] with hinp
  -- step 1: Bareiss elimination
  have sb := hnfBar_spec (hnfBarAt_of hI h.bar) A hA ⟨0, hr0⟩ ⟨0, hc0⟩ hT1 hT hbar hXb
  have d1 := Det.call (Det.var' (P := P) (env := [inp]) (i := 0) rfl) sb
  set v1 := hnfBarVal st with hv1
  have wv1 : v1.wt < hnfBarCost X := sb.wt_lt
  -- step 2: `K` and `m`
  have wn := wt_list_le [Val.nat r, .nat c, encIntMatrix A, encInt d]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at wn
  have sn := hnfNums_spec hD hE h.nums h.abs h.pow A d hr0 hd0 (B := 2 ^ W) (Y := X)
    (fun i j => (hAW i j).le)
    (lt_of_lt_of_le (hnf_rcB hrW hcr) (Nat.pow_le_pow_right (by decide) hX4)) (by omega)
    (lt_of_lt_of_le hmL (Nat.pow_le_pow_right (by decide) hX3))
  have dv1 : Det P [inp, v1] (.var 1) (.list [hnfSVal s, encInt d, encIntMatrix st.W]) _ :=
    Det.var' (i := 1) rfl
  have d2 := Det.call (Det.mk4
    (Det.arg' (P := P) (vs := [.nat r, .nat c, encIntMatrix A]) (rest := [v1]) (j := 0) rfl)
    (Det.arg' (P := P) (vs := [.nat r, .nat c, encIntMatrix A]) (rest := [v1]) (j := 1) rfl)
    (Det.arg' (P := P) (vs := [.nat r, .nat c, encIntMatrix A]) (rest := [v1]) (j := 2) rfl)
    (Det.get' dv1 (Det.nat 1) rfl)) sn
  set v2 := Val.list [encInt (Kn : ℤ), encInt (mn : ℤ)] with hv2
  have wv2 : v2.wt < hnfNumsCost X := sn.wt_lt
  -- step 3: the complement
  have hsl : s.length = c := hrows.len
  have wsv := hnf_sVal_wt s (le_of_eq hsl) (show 1000 * (r + c + 1) ≤ X by
    rw [hXdef]; exact Nat.mul_le_mul_left _ (le_trans (by omega) (Nat.le_mul_of_pos_right _ (by omega))))
  have sc := hnfComplP_spec h.compl s (by omega) (Y := 10 * (X * X)) (by omega) (by
    have := wt_list2_le (hnfSVal s) (.nat r); omega)
  have dv1' : Det P [inp, v1, v2] (.var 1) (.list [hnfSVal s, encInt d, encIntMatrix st.W]) _ :=
    Det.var' (i := 1) rfl
  have d3 := Det.call (Det.mk2 (Det.get' dv1' (Det.nat 0) rfl)
    (Det.arg' (P := P) (vs := [.nat r, .nat c, encIntMatrix A]) (rest := [v1, v2]) (j := 0) rfl)) sc
  set v3 := hnfComplVal s with hv3
  have wv3 : v3.wt < hnfComplCost (10 * (X * X)) := sc.wt_lt
  -- step 4: `r + r`
  have d4 : Det P [inp, v1, v2, v3] (.arith .add (arg 0) (arg 0)) (.nat (r + r)) _ :=
    Det.arith (Det.arg' (vs := [.nat r, .nat c, encIntMatrix A]) (rest := [v1, v2, v3]) (j := 0) rfl)
      (Det.arg' (vs := [.nat r, .nat c, encIntMatrix A]) (rest := [v1, v2, v3]) (j := 0) rfl)
  have wrr : (Val.nat (r + r)).wt ≤ X := by have := wt_nat_le (r + r); omega
  -- step 5: the big matrix mod `m`
  set Xt := 100 * (X * X) with hXt
  have hr1 : (r + 1) ^ 2 ≤ X * X := by
    rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  have wv3' := hnfComplVal_wt s
  have dv2 : Det P [inp, v1, v2, v3, .nat (r + r)] (.var 2)
      (.list [encInt (Kn : ℤ), encInt (mn : ℤ)]) _ := Det.var' (i := 2) rfl
  have dctx : Det P [inp, v1, v2, v3, .nat (r + r)]
      (.snoc (.snoc (mk4 (arg 2) (.var 3) (.get (.var 2) (.nat 0)) (.get (.var 2) (.nat 1))) (arg 0))
        (arg 1)) (.list (hnfBigCtx A s (Kn : ℤ) (mn : ℤ))) _ :=
    Det.snoc (Det.snoc (Det.mk4
      (Det.arg' (vs := [.nat r, .nat c, encIntMatrix A]) (rest := [v1, v2, v3, .nat (r + r)]) (j := 2) rfl)
      (Det.var' (i := 3) rfl) (Det.get' dv2 (Det.nat 0) rfl) (Det.get' dv2 (Det.nat 1) rfl))
      (Det.arg' (vs := [.nat r, .nat c, encIntMatrix A]) (rest := [v1, v2, v3, .nat (r + r)]) (j := 0) rfl))
      (Det.arg' (vs := [.nat r, .nat c, encIntMatrix A]) (rest := [v1, v2, v3, .nat (r + r)]) (j := 1) rfl)
  have wctx := wt_list_le (hnfBigCtx A s (Kn : ℤ) (mn : ℤ))
  simp only [hnfBigCtx, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at wctx
  have wctx3 := wt_list3_le (.list (hnfBigCtx A s (Kn : ℤ) (mn : ℤ))) (.nat (r + r)) (.nat (r + r))
  have hX5 : (Val.list [.list (hnfBigCtx A s (Kn : ℤ) (mn : ℤ)), .nat (r + r), .nat (r + r)]).wt ≤ Xt := by
    rw [hXt]; unfold hnfBigCtx at wctx3 ⊢; omega
  have st5 := hnfBigTab_spec hI (hnfTabAt_of h.tb) h.bcell A s hrows.nodup hsl hcr (Kn : ℤ) (mn : ℤ)
    (X := Xt) hX5 (by omega)
  have d5 := Det.call (Det.mk3 dctx (Det.var' (P := P) (env := [inp, v1, v2, v3, .nat (r + r)]) (i := 4) rfl)
    (Det.var' (P := P) (env := [inp, v1, v2, v3, .nat (r + r)]) (i := 4) rfl)) st5
  set v5 := encIntMatrix (fun i j => hnfBig A' (Kn : ℤ) i j % (mn : ℤ)) with hv5
  have wv5 : v5.wt < hnfTabCost Xt (hnfBigCellCost (10 * Xt + 18)) := st5.wt_lt
  -- step 6: the modular Hermite form
  have hm0 : (0 : ℤ) < (mn : ℤ) := by
    have : 0 < mn := by rw [hmn, hnfMn]; exact Nat.mul_pos (Int.natAbs_pos.mpr hd0) (by unfold hnfKn; omega)
    exact_mod_cast this
  have sm := hnfMod_spec (hnfModAt_of hI h.md) hm0 (by simpa using hmL) hXm (hnfBig A' (Kn : ℤ))
  set env5 := [inp, v1, v2, v3, .nat (r + r), v5] with henv5
  have dv2b : Det P env5 (.var 2) (.list [encInt (Kn : ℤ), encInt (mn : ℤ)]) _ := Det.var' (i := 2) rfl
  have d6 := Det.call (Det.mk3 (Det.get' dv2b (Det.nat 1) rfl) (Det.var' (P := P) (env := env5) (i := 4) rfl)
    (Det.var' (P := P) (env := env5) (i := 5) rfl)) sm
  set v6 := encIntMatrix Hb with hv6
  have wv6 : v6.wt < hnfModCost X := sm.wt_lt
  have hHbL : ∀ a b, (Hb a b).natAbs < 2 ^ L := fun a b => by
    have h1 := hHb' a b
    have : (Hb a b).natAbs ≤ mn := by omega
    omega
  have wHb : v6.wt ≤ X * X := hnf_mat_wt Hb hHbL hXq
  -- step 7: the transform
  set env6 := env5 ++ [v6] with henv6
  have dv2c : Det P env6 (.var 2) (.list [encInt (Kn : ℤ), encInt (mn : ℤ)]) _ := Det.var' (i := 2) rfl
  have dout6 : Det P env6 (mk3 (.var 6) (.get (.var 2) (.nat 0)) (arg 0))
      (.list (hnfOutCtx Hb (Kn : ℤ))) _ :=
    Det.mk3 (Det.var' (i := 6) rfl) (Det.get' dv2c (Det.nat 0) rfl)
      (Det.arg' (vs := [.nat r, .nat c, encIntMatrix A]) (rest := [v1, v2, v3, .nat (r + r), v5, v6])
        (j := 0) rfl)
  have wout := wt_list3_le (encIntMatrix Hb) (encInt (Kn : ℤ)) (.nat r)
  have e6 : (encIntMatrix Hb).wt = v6.wt := rfl
  have wout3 := wt_list3_le (.list (hnfOutCtx Hb (Kn : ℤ))) (.nat r) (.nat r)
  have wout3' := wt_list3_le (.list (hnfOutCtx Hb (Kn : ℤ))) (.nat r) (.nat c)
  have hX7 : (Val.list [.list (hnfOutCtx Hb (Kn : ℤ)), .nat r, .nat r]).wt ≤ Xt := by
    rw [hXt]; unfold hnfOutCtx at wout3 ⊢; omega
  have hX8 : (Val.list [.list (hnfOutCtx Hb (Kn : ℤ)), .nat r, .nat c]).wt ≤ Xt := by
    rw [hXt]; unfold hnfOutCtx at wout3' ⊢; omega
  have su := hnfUTab_spec hI (hnfTabAt_of h.tu) h.ucell Hb (Kn : ℤ) (L := L) (X := Xt) hHbL
    (by simpa using hKL) hX7 (by omega)
  have d7 := Det.call (Det.mk3 dout6
    (Det.arg' (vs := [.nat r, .nat c, encIntMatrix A]) (rest := [v1, v2, v3, .nat (r + r), v5, v6])
      (j := 0) rfl)
    (Det.arg' (vs := [.nat r, .nat c, encIntMatrix A]) (rest := [v1, v2, v3, .nat (r + r), v5, v6])
      (j := 0) rfl)) su
  set v7 := encIntMatrix (fun i j => hnfLift (Kn : ℤ) (Hb (Fin.castAdd r i) (Fin.natAdd r j))) with hv7
  have wv7 : v7.wt < hnfTabCost Xt (hnfUCellCost (10 * Xt + 18 + 100 * (L + 1))) := su.wt_lt
  -- step 8: the Hermite form
  set env7 := env6 ++ [v7] with henv7
  have dv2d : Det P env7 (.var 2) (.list [encInt (Kn : ℤ), encInt (mn : ℤ)]) _ := Det.var' (i := 2) rfl
  have dout7 : Det P env7 (mk3 (.var 6) (.get (.var 2) (.nat 0)) (arg 0))
      (.list (hnfOutCtx Hb (Kn : ℤ))) _ :=
    Det.mk3 (Det.var' (i := 6) rfl) (Det.get' dv2d (Det.nat 0) rfl)
      (Det.arg' (vs := [.nat r, .nat c, encIntMatrix A]) (rest := [v1, v2, v3, .nat (r + r), v5, v6, v7])
        (j := 0) rfl)
  have sh := hnfHTab_spec (hnfTabAt_of h.th) h.hcell hcr Hb (Kn : ℤ) (X := Xt) hX8 (by omega)
  have d8 := Det.call (Det.mk3 dout7
    (Det.arg' (vs := [.nat r, .nat c, encIntMatrix A]) (rest := [v1, v2, v3, .nat (r + r), v5, v6, v7])
      (j := 0) rfl)
    (Det.arg' (vs := [.nat r, .nat c, encIntMatrix A]) (rest := [v1, v2, v3, .nat (r + r), v5, v6, v7])
      (j := 1) rfl)) sh
  set v8 := encIntMatrix (fun i j => Hb (Fin.castAdd r i) (Fin.castAdd r (Fin.castLE hcr j))) with hv8
  have wv8 : v8.wt < hnfTabCost Xt (hnfHCellCost (10 * Xt + 18)) := sh.wt_lt
  -- the output
  set env8 := env7 ++ [v8] with henv8
  have d9 := Det.mk2 (Det.var' (P := P) (env := env8) (i := 7) rfl)
    (Det.var' (P := P) (env := env8) (i := 8) rfl)
  have dall := Det.letE d1 (Det.letE d2 (Det.letE d3 (Det.letE d4 (Det.letE d5 (Det.letE d6
    (Det.letE d7 (Det.letE d8 d9)))))))
  have eU : encIntMatrix (hnfRectU A Tz) = v7 := by
    rw [hv7, hnfRectU, eK]; unfold hnfUp GI.Proved.hnfX; rw [eHb]
  have eH : encIntMatrix (hnfRectH A hcr Tz) = v8 := by
    rw [hv8]; unfold hnfRectH; rw [eK]; unfold hnfHp; rw [eHb]
  rw [eU, eH]
  apply FunDet.intro h.main
  refine dall.mono ?_
  -- the weights in the cost
  have g1 : (Val.list [hnfSVal s, encInt d, encIntMatrix st.W]).wt = v1.wt := rfl
  have g2 := wt_list2_le v7 v8
  have g3 := wt_list2_le (encInt (Kn : ℤ)) (encInt (mn : ℤ))
  have g4 := wt_list2_le (hnfSVal s) (.nat r)
  have g5 : (Val.nat (BinOp.add.eval r r)).wt = (Val.nat (r + r)).wt := rfl
  have g6 := wt_list_le [encIntMatrix A, v3, encInt (Kn : ℤ), encInt (mn : ℤ)]
  have g7 := wt_list_le [encIntMatrix A, v3, encInt (Kn : ℤ), encInt (mn : ℤ), .nat r]
  have g8 := wt_list_le [encIntMatrix A, v3, encInt (Kn : ℤ), encInt (mn : ℤ), .nat r, .nat c]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at g6 g7 g8
  have g7' : (Val.list ([encIntMatrix A, v3, encInt (Kn : ℤ), encInt (mn : ℤ)] ++ [.nat r])).wt =
    (Val.list [encIntMatrix A, v3, encInt (Kn : ℤ), encInt (mn : ℤ), .nat r]).wt := rfl
  have g8' : (Val.list ([encIntMatrix A, v3, encInt (Kn : ℤ), encInt (mn : ℤ)] ++ [.nat r] ++
    [.nat c])).wt = (Val.list [encIntMatrix A, v3, encInt (Kn : ℤ), encInt (mn : ℤ), .nat r, .nat c]).wt :=
    rfl
  have g9 := wt_list3_le (encInt (mn : ℤ)) (.nat (r + r)) v5
  have g10 : (Val.list [encIntMatrix Hb, encInt (Kn : ℤ), .nat r]).wt ≤ Xt := by
    rw [hXt]; omega
  have t5 : 100 * (Xt + 1) ≤ hnfTabCost Xt (hnfBigCellCost (10 * Xt + 18)) := by
    unfold hnfTabCost; omega
  have t7 : 100 * (Xt + 1) ≤ hnfTabCost Xt (hnfUCellCost (10 * Xt + 18 + 100 * (L + 1))) := by
    unfold hnfTabCost; omega
  have t8 : 100 * (Xt + 1) ≤ hnfTabCost Xt (hnfHCellCost (10 * Xt + 18)) := by
    unfold hnfTabCost; omega
  have hXtX : X * X ≤ Xt := by rw [hXt]; omega
  have g11 : (Val.list [.nat r, .nat c, encIntMatrix A]).wt = inp.wt := rfl
  have g12 : (hnfComplVal s).wt = v3.wt := rfl
  have g13 : inp.wt = W := rfl
  unfold hnfMainCost
  rw [← hX, ← hL, ← hXt]
  clear * - wv1 wv2 wv3 wv5 wv6 wv7 wv8 g1 g2 g3 g4 g5 g6 g7 g8 g7' g8' g9 g10 g11 g12 g13 wn wd wK
    wm wsv wrr hX5 hX7 hX8 t5 t7 t8 hXtX hX1 hX2 hXX hXX' wv3' hr1 wA wr wc hrW e6 wHb
  omega

end GI.Impl
