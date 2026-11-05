module

public import Workspace.Impl.AggItemCfDPair
public import Workspace.Impl.AggStructDesSplit

@[expose] public section

namespace GI.Impl

open GI.Algorithm GI.Lang GI.Cited
open GI.Machine (BinOp)

theorem itCfD_split_spec {P : Program} {f fd fr ad rb cf h dv dv' cb rf df : ℕ}
    (hf : P.funs[f]? = some (stDSplitF fd fr ad rb cf))
    (hfd : P.HasAt fd (findFuns fd dv)) (hdv : P.funs[dv]? = some (stDDomF dv'))
    (hdv' : P.funs[dv']? = some (stDDomVF cb)) (hcb : P.HasAt cb (countFuns cb))
    (hfr : P.HasAt fr (findFuns fr rf)) (hrf : P.funs[rf]? = some stDRefF)
    (had : P.HasAt ad (anyFuns ad df)) (hdf : P.funs[df]? = some (stDDifF rf cf))
    (hrb : P.HasAt rb (rangeFuns rb)) (hcf : P.funs[cf]? = some (stDColF h))
    (hh : P.HasAt h (stDHorFuns h)) {dl tl : List ℕ} {q κ : ℕ} (hc : ItCfDCtx dl tl q κ) (m : ℕ)
    (hb : stDBal (stDV dl tl q κ m) q = false) {M : ℕ}
    (hM : (Val.list [.list [stDA dl tl q κ, .nat m], natList (stDV dl tl q κ m)]).wt ≤ M) :
    FunDet P f (.list [.list [stDA dl tl q κ, .nat m], natList (stDV dl tl q κ m)])
      (boolVal (stDSplit dl tl q κ m (stDV dl tl q κ m)
        ((stDV dl tl q κ m).getD (stDZ (stDV dl tl q κ m) q) 0)))
      (stDSplitK * (M + 1) ^ 8) := by
  -- facts about the values
  have hVl := stDV_length dl tl q κ m
  obtain ⟨V, hVd⟩ : ∃ V, stDV dl tl q κ m = V := ⟨_, rfl⟩
  rw [hVd] at hb hVl hM ⊢
  have hAw : (stDA dl tl q κ).wt < M := by
    have h1 : (Val.list [stDA dl tl q κ, .nat m]).wt <
        (Val.list [.list [stDA dl tl q κ, .nat m], natList V]).wt := wt_le_wt_list (by simp)
    have h2 : (stDA dl tl q κ).wt < (Val.list [stDA dl tl q κ, .nat m]).wt :=
      wt_le_wt_list (by simp)
    omega
  have hmw : (Val.nat m).wt < M := by
    have h1 : (Val.list [stDA dl tl q κ, .nat m]).wt <
        (Val.list [.list [stDA dl tl q κ, .nat m], natList V]).wt := wt_le_wt_list (by simp)
    have h2 : (Val.nat m).wt < (Val.list [stDA dl tl q κ, .nat m]).wt :=
      wt_le_wt_list (by simp)
    omega
  have hVw : (natList V).wt < M := by
    have : (natList V).wt < (Val.list [.list [stDA dl tl q κ, .nat m], natList V]).wt :=
      wt_le_wt_list (by simp)
    omega
  have hqM : q < M := by have := hc.le_wt.2.2; omega
  have hVB : (natList V).wt ≤ 2 * M := by omega
  have hwzero := wt_nat_le 0
  have hY1 : 1 ≤ M + 1 := by omega
  have hP := fun i j (h : i ≤ j) => Nat.pow_le_pow_right hY1 h
  have hqq : q * q ≤ (M + 1) ^ 2 := by
    have := Nat.mul_le_mul (show q ≤ M + 1 by omega) (show q ≤ M + 1 by omega); nlinarith
  -- the first large class
  have hany : (List.range q).any (stDDom V q) = true := by
    rw [stDBal] at hb; simpa using hb
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, stDZ V q = z₀ := ⟨_, rfl⟩
  have hz₀q : z₀ < q := by
    obtain ⟨z, hz, hzp⟩ := List.any_eq_true.1 hany
    have := List.findIdx_lt_length_of_exists (p := stDDom V q) (xs := List.range q) ⟨z, hz, hzp⟩
    rw [← hz₀]; unfold stDZ; simpa using this
  obtain ⟨j, hj⟩ : ∃ j, V.getD z₀ 0 = j := ⟨_, rfl⟩
  have hjV : V[z₀]? = some j := by
    rw [← hj, List.getD_eq_getElem _ _ (by omega)]; exact List.getElem?_eq_getElem (by omega)
  have hjM : (Val.nat j).wt ≤ 2 * M := by
    have hw := wt_le_wt_list (vs := V.map Val.nat)
      (List.mem_map.2 ⟨j, List.mem_of_getElem? hjV, rfl⟩)
    exact hw.le.trans hVB
  rw [hz₀, hj]
  -- the first pair
  obtain ⟨p₀, hp₀⟩ : ∃ p₀, (List.range (q * q)).findIdx (stDRef V q j) = p₀ := ⟨_, rfl⟩
  have hp₀le : p₀ ≤ q * q := by rw [← hp₀]; exact (List.findIdx_le_length).trans (by simp)
  -- weights
  have hX2 : M + 1 ≤ (M + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hX24 := hP 2 4 (by norm_num)
  have hrq : (natList (List.range q)).wt ≤ 5 * (M + 1) ^ 2 := by
    have := wt_natList_le_sq (xs := List.range q) (B := q) (fun x hx => (List.mem_range.1 hx).le)
      (by simp)
    have : (q + 1) ^ 2 ≤ (M + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hrqq : (natList (List.range (q * q))).wt ≤ 20 * (M + 1) ^ 4 := by
    have := wt_natList_le_sq (xs := List.range (q * q)) (B := q * q)
      (fun x hx => (List.mem_range.1 hx).le) (by simp)
    have h1 : (q * q + 1) ^ 2 ≤ (2 * (M + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : (2 * (M + 1) ^ 2) ^ 2 = 4 * (M + 1) ^ 4 := by ring
    omega
  have hcp : ∀ c, (Val.nat c).wt ≤ 2 * M → (stDCP dl tl q κ m V j c).wt ≤ 20 * M + 30 := by
    intro c hc'
    have h1 := wt_list_le [stDA dl tl q κ, .nat m, natList V, .nat j, .nat c]
    have := wt_nat_le j; have := wt_nat_le c
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at h1
    unfold stDCP; omega
  have hokc : ∀ c, (Val.nat c).wt ≤ 2 * M → ItCfDPOK dl tl q κ m V j c (20 * M + 30) := fun c hc' =>
    ⟨hc, hVl, hcp c hc'⟩
  have hcV : (Val.list [natList V, .nat q]).wt ≤ 20 * (2 * M + 1) ^ 2 :=
    itCfD_ctxV_wt hVB hVl (by omega)
  have hM2 : (2 * M + 1) ^ 2 ≤ 4 * (M + 1) ^ 2 := by nlinarith
  obtain ⟨W, hW⟩ : ∃ W, W = 1000 * (M + 1) ^ 4 + 1000 := ⟨_, rfl⟩
  have ha_eq : (Val.list [.list [Val.list [natList dl, natList tl, .nat q, .nat κ], .nat m],
      natList V]).wt = (Val.list [.list [stDA dl tl q κ, .nat m], natList V]).wt := rfl
  have e_cp : ∀ c, (Val.list ([Val.list [natList dl, natList tl, .nat q, .nat κ], .nat m,
      natList V, .nat j] ++ [.nat c])).wt = (stDCP dl tl q κ m V j c).wt := fun c => rfl
  have e_4 : (Val.list [Val.list [natList dl, natList tl, .nat q, .nat κ], .nat m, natList V,
      .nat j]).wt = (Val.list [stDA dl tl q κ, .nat m, natList V, .nat j]).wt := rfl
  have e_cpl : ∀ c, (Val.list [Val.list ([Val.list [natList dl, natList tl, .nat q, .nat κ],
      .nat m, natList V, .nat j] ++ [.nat c]), natList (List.range (q * q))]).wt =
      (Val.list [stDCP dl tl q κ m V j c, natList (List.range (q * q))]).wt := fun c => rfl
  -- the parts in each environment
  have hqqW : q * q + 2 ≤ W := by omega
  obtain ⟨gA1, gm1, gV1, gq1, gqq1⟩ := stDS_parts (P := P) (m := m) (Vv := natList V)
    (Avs := [natList dl, natList tl, .nat q, .nat κ]) rfl rfl [] (W := W) (by omega) (by omega)
    hqqW
  obtain ⟨gA2, gm2, gV2, gq2, gqq2⟩ := stDS_parts (P := P) (m := m) (Vv := natList V)
    (Avs := [natList dl, natList tl, .nat q, .nat κ]) rfl rfl [.nat z₀] (W := W) (by omega)
    (by omega) hqqW
  obtain ⟨gA3, gm3, gV3, gq3, gqq3⟩ := stDS_parts (P := P) (m := m) (Vv := natList V)
    (Avs := [natList dl, natList tl, .nat q, .nat κ]) rfl rfl [.nat z₀, .nat p₀] (W := W)
    (by omega) (by omega) hqqW
  -- the first large class
  have hdom := st_find_det hfd (c := .list [natList V, .nat q]) (n := q) (t := stDDom V q)
    (B := 2 * itCfDDomK * (2 * M + 1) ^ 3) (X := 200 * (M + 1) ^ 2)
    (fun i hi => itCfD_dom_spec hdv hdv' hcb hVB hVl (by omega) hi)
    (by have := wt_list2_le (.list [natList V, .nat q]) (natList (List.range q)); omega)
    (by omega)
  have hz₀' : (List.range q).findIdx (stDDom V q) = z₀ := hz₀
  rw [hz₀'] at hdom
  have gr1 := StDC.call gq1 (st_range_det hrb q) (by omega)
  have g1 := StDC.call (StDC.mk2 (StDC.mk2 gV1 gq1 (by omega) (by omega)) gr1
    (by have := wt_list2_le (.list [natList V, .nat q]) (natList (List.range q)); omega)
    (by omega)) hdom (by have := wt_nat_le z₀; omega)
  -- the first pair
  have gj2 := StDC.get (v := .nat j) gV2 (StDC.var' (i := 1) rfl (by have := wt_nat_le z₀; omega))
    (by simp [hjV]) (by have := wt_nat_le j; omega)
  have g42 := StDC.mk4 gA2 gm2 gV2 gj2 (by
    have := wt_list4_le (stDA dl tl q κ) (.nat m) (natList V) (.nat j); have := wt_nat_le j
    omega) (by omega)
  have gcp0 := StDC.snoc g42 (StDC.nat 0 (by omega)) (by
    have := hcp 0 (by omega); rw [e_cp]; omega)
  have hrr := st_range_det hrb (q * q)
  have hrrc : 10000 * (q * q + 1) ^ 3 ≤ 80000 * (M + 1) ^ 6 := by
    have h1 : (q * q + 1) ^ 3 ≤ (2 * (M + 1) ^ 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h2 : (2 * (M + 1) ^ 2) ^ 3 = 8 * (M + 1) ^ 6 := by ring
    omega
  have gr2 := StDC.call gqq2 hrr (by omega)
  have href := st_find_det hfr (c := stDCP dl tl q κ m V j 0) (n := q * q) (t := stDRef V q j)
    (B := stDRefK * (20 * M + 30 + 1) ^ 2) (X := 100 * (M + 1) ^ 4)
    (fun i hi => itCfD_ref_spec hrf (hokc 0 (by omega)) hi)
    (by have := wt_list2_le (stDCP dl tl q κ m V j 0) (natList (List.range (q * q)))
        have := hcp 0 (by omega); omega)
    (by omega)
  rw [hp₀] at href
  have g2 := StDC.call (StDC.mk2 gcp0 gr2 (by
    have := wt_list2_le (stDCP dl tl q κ m V j 0) (natList (List.range (q * q)))
    have := hcp 0 (by omega); rw [e_cpl]; omega) (by omega)) href
    (by have := wt_nat_le p₀; omega)
  -- the test of the second pair, when the first pair exists
  have gcond := StDC.arith' (StDC.var' (P := P) (env := [Val.list [.list [stDA dl tl q κ, .nat m],
    natList V], .nat z₀, .nat p₀]) (i := 2) rfl (by have := wt_nat_le p₀; omega)) gqq3
    (op := .lt) (z := BinOp.eval .lt p₀ (q * q)) rfl
    (by simp only [BinOp.eval]; split_ifs <;> omega)
  have hval : stDSplit dl tl q κ m V j =
      (decide (p₀ < q * q) && (List.range (q * q)).any fun p => stDRef V q j p &&
        !decide (stDCol dl tl q κ m (p / q) (p % q) =
          stDCol dl tl q κ m (p₀ / q) (p₀ % q))) := by
    unfold stDSplit; rw [hp₀]
  rw [hval]
  by_cases hlt : p₀ < q * q
  · have hu := st_div_lt hlt
    have hv := st_mod_lt hlt
    obtain ⟨c₀, hc₀⟩ : ∃ c₀, stDCol dl tl q κ m (p₀ / q) (p₀ % q) = c₀ := ⟨_, rfl⟩
    have hc₀M : (Val.nat c₀).wt ≤ 2 * M := by
      have hw := itCfD_col_wt dl tl q κ m (p₀ / q) (p₀ % q)
      rw [hc₀] at hw
      have hdl : (natList dl).wt < (stDA dl tl q κ).wt := wt_stDA_ge.2.2.1
      omega
    rw [hc₀]
    have gj3 := StDC.get (v := .nat j) gV3 (StDC.var' (i := 1) rfl
      (by have := wt_nat_le z₀; omega)) (by simp [hjV]) (by have := wt_nat_le j; omega)
    have g43 := StDC.mk4 gA3 gm3 gV3 gj3 (by
      have := wt_list4_le (stDA dl tl q κ) (.nat m) (natList V) (.nat j); have := wt_nat_le j
      omega) (by omega)
    have gp := StDC.var' (P := P) (env := [Val.list [.list [stDA dl tl q κ, .nat m],
      natList V], .nat z₀, .nat p₀]) (i := 2) rfl (W := W) (by have := wt_nat_le p₀; omega)
    have gu := StDC.arith' gp gq3 (op := .div) (show BinOp.eval .div p₀ q = p₀ / q from rfl)
      (by omega)
    have gv := StDC.arith' gp gq3 (op := .mod) (show BinOp.eval .mod p₀ q = p₀ % q from rfl)
      (by omega)
    have hca : (stDCA dl tl q κ m (p₀ / q) (p₀ % q)).wt ≤ 8 * M + 8 := by
      have := wt_list4_le (stDA dl tl q κ) (.nat m) (.nat (p₀ / q)) (.nat (p₀ % q))
      have := wt_nat_le (p₀ / q); have := wt_nat_le (p₀ % q)
      unfold stDCA; omega
    have hcol := itCfD_col_spec hcf hh hc m hu hv
    rw [hc₀] at hcol
    have gcol := StDC.call (StDC.mk4 gA3 gm3 gu gv (by
      have := wt_list4_le (stDA dl tl q κ) (.nat m) (.nat (p₀ / q)) (.nat (p₀ % q))
      have := wt_nat_le (p₀ / q); have := wt_nat_le (p₀ % q)
      have e : (Val.list [Val.list [natList dl, natList tl, .nat q, .nat κ], .nat m,
        .nat (p₀ / q), .nat (p₀ % q)]).wt = (Val.list [stDA dl tl q κ, .nat m, .nat (p₀ / q),
        .nat (p₀ % q)]).wt := rfl
      omega) (by omega)) hcol
      (by have := wt_nat_le c₀; omega)
    have gcp1 := StDC.snoc g43 gcol (by have := hcp c₀ hc₀M; rw [e_cp]; omega)
    have gr3 := StDC.call gqq3 hrr (by omega)
    have hdif := st_any_det had (c := stDCP dl tl q κ m V j c₀) (n := q * q)
      (t := fun p => stDRef V q j p && !decide (stDCol dl tl q κ m (p / q) (p % q) = c₀))
      (B := stDDifK * (20 * M + 30 + 1) ^ 2) (X := 100 * (M + 1) ^ 4)
      (fun i hi => itCfD_dif_spec hdf hrf hcf hh (hokc c₀ hc₀M) hi)
      (by have := wt_list2_le (stDCP dl tl q κ m V j c₀) (natList (List.range (q * q)))
          have := hcp c₀ hc₀M; omega)
      (by omega)
    have gad := StDC.call (StDC.mk2 gcp1 gr3 (by
      have := wt_list2_le (stDCP dl tl q κ m V j c₀) (natList (List.range (q * q)))
      have := hcp c₀ hc₀M; rw [e_cpl]; omega) (by omega)) hdif
      (by have := wt_boolVal_le ((List.range (q * q)).any fun p => stDRef V q j p &&
        !decide (stDCol dl tl q κ m (p / q) (p % q) = c₀)); omega)
    rw [decide_eq_true hlt, Bool.true_and]
    have gite := StDC.ite (ne := 0) (Ee := 0) (e := .nat 0) gcond (fun _ => gad)
      (fun hx => absurd hx (by simp [BinOp.eval, hlt]))
      (by have := wt_boolVal_le ((List.range (q * q)).any fun p => stDRef V q j p &&
        !decide (stDCol dl tl q κ m (p / q) (p % q) = c₀)); omega)
    have gall := StDC.letE g1 (StDC.letE g2 gite (by
      have := wt_boolVal_le ((List.range (q * q)).any fun p => stDRef V q j p &&
        !decide (stDCol dl tl q κ m (p / q) (p % q) = c₀)); omega)) (by
      have := wt_boolVal_le ((List.range (q * q)).any fun p => stDRef V q j p &&
        !decide (stDCol dl tl q κ m (p / q) (p % q) = c₀)); omega)
    refine StDC.funDet hf gall ?_
    have hqY : q ≤ M + 1 := by omega
    have hqqY : q * q ≤ (M + 1) ^ 2 := hqq
    have t1 : q * (2 * itCfDDomK * (2 * M + 1) ^ 3) ≤ 16 * itCfDDomK * (M + 1) ^ 4 := by
      have := Nat.pow_le_pow_left (show 2 * M + 1 ≤ 2 * (M + 1) by omega) 3
      calc q * (2 * itCfDDomK * (2 * M + 1) ^ 3) ≤ (M + 1) * (2 * itCfDDomK * (2 * (M + 1)) ^ 3) :=
            Nat.mul_le_mul hqY (Nat.mul_le_mul_left _ this)
        _ = 16 * itCfDDomK * (M + 1) ^ 4 := by ring
    have t2 : loopModK * (200 * (M + 1) ^ 2 + 1) * (3 * (200 * (M + 1) ^ 2) + 3) ≤
        loopModK * 201 * 603 * (M + 1) ^ 4 := by
      have h1 : 1 ≤ (M + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      calc _ ≤ loopModK * (201 * (M + 1) ^ 2) * (603 * (M + 1) ^ 2) :=
            st_mul3 le_rfl (by omega) (by omega)
        _ = _ := by ring
    have t3 : ∀ K, q * q * (K * (20 * M + 30 + 1) ^ 2) ≤ 961 * K * (M + 1) ^ 4 := by
      intro K
      have := Nat.pow_le_pow_left (show 20 * M + 30 + 1 ≤ 31 * (M + 1) by omega) 2
      calc q * q * (K * (20 * M + 30 + 1) ^ 2) ≤ (M + 1) ^ 2 * (K * (31 * (M + 1)) ^ 2) :=
            Nat.mul_le_mul hqqY (Nat.mul_le_mul_left _ this)
        _ = 961 * K * (M + 1) ^ 4 := by ring
    have t4 : loopModK * (100 * (M + 1) ^ 4 + 1) * (3 * (100 * (M + 1) ^ 4) + 3) ≤
        loopModK * 101 * 303 * (M + 1) ^ 8 := by
      have h1 : 1 ≤ (M + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
      calc _ ≤ loopModK * (101 * (M + 1) ^ 4) * (303 * (M + 1) ^ 4) :=
            st_mul3 le_rfl (by omega) (by omega)
        _ = _ := by ring
    have t5 : stDColK * ((stDCA dl tl q κ m (p₀ / q) (p₀ % q)).wt + 1) ^ 2 ≤
        81 * stDColK * (M + 1) ^ 2 := by
      have := Nat.pow_le_pow_left (show (stDCA dl tl q κ m (p₀ / q) (p₀ % q)).wt + 1 ≤
        9 * (M + 1) by omega) 2
      calc _ ≤ stDColK * (9 * (M + 1)) ^ 2 := Nat.mul_le_mul_left _ this
        _ = _ := by ring
    have t6 : 10000 * (q + 1) ^ 3 ≤ 80000 * (M + 1) ^ 3 := by
      have := Nat.pow_le_pow_left (show q + 1 ≤ 2 * (M + 1) by omega) 3
      calc _ ≤ 10000 * (2 * (M + 1)) ^ 3 := Nat.mul_le_mul_left _ this
        _ = _ := by ring
    have hp2 := hP 2 8 (by norm_num)
    have hp3 := hP 3 8 (by norm_num)
    have hp4 := hP 4 8 (by norm_num)
    have hp6 := hP 6 8 (by norm_num)
    have t7 : W + 1 ≤ 2001 * (M + 1) ^ 4 := by
      have : 1 ≤ (M + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
      omega
    have t3a := t3 stDRefK
    have t3b := t3 stDDifK
    clear gall gite gad hdif gcp1 gcol hcol gr3 g43 gj3 gp gu gv g1 g2 gr1 gr2 gcp0 g42 gj2
      href hdom gcond gA1 gm1 gV1 gq1 gqq1 gA2 gm2 gV2 gq2 gqq2 gA3 gm3 gV3 gq3 gqq3
    generalize (stDCA dl tl q κ m (p₀ / q) (p₀ % q)).wt = cw at t5 ⊢
    generalize (M + 1) ^ 8 = Y8 at *
    generalize (M + 1) ^ 6 = Y6 at *
    generalize (M + 1) ^ 4 = Y4 at *
    generalize (M + 1) ^ 3 = Y3 at *
    generalize (M + 1) ^ 2 = Y2 at *
    generalize (q * q + 1) ^ 3 = Q3 at *
    generalize (q + 1) ^ 3 = q3 at *
    simp only [stDSplitK, itCfDDomK, loopModK, stDRefK, stDDifK, stDColK] at t1 t2 t3a t3b t4 t5 ⊢
    norm_num at t1 t2 t3a t3b t4 t5 ⊢
    linarith
  · have hp₀e : p₀ = q * q := by omega
    rw [decide_eq_false hlt, Bool.false_and]
    have gite := StDC.ite (nt := 0) (Et := 0) (W := W)
      (t := .call ad (mk2 (.snoc (mk4 stDSA stDSm stDSV (.get stDSV (.var 1)))
            (.call cf (mk4 stDSA stDSm (.arith .div (.var 2) stDSq) (.arith .mod (.var 2) stDSq))))
          (.call rb stDSqq))) (v := boolVal false) gcond
      (fun hx => absurd hx (by simp [BinOp.eval, hlt]))
      (fun _ => StDC.nat 0 (by omega)) (by have := wt_boolVal_le false; omega)
    have gall := StDC.letE g1 (StDC.letE g2 gite (by have := wt_boolVal_le false; omega))
      (by have := wt_boolVal_le false; omega)
    refine StDC.funDet hf gall ?_
    have hqY : q ≤ M + 1 := by omega
    have hqqY : q * q ≤ (M + 1) ^ 2 := hqq
    have t1 : q * (2 * itCfDDomK * (2 * M + 1) ^ 3) ≤ 16 * itCfDDomK * (M + 1) ^ 4 := by
      have := Nat.pow_le_pow_left (show 2 * M + 1 ≤ 2 * (M + 1) by omega) 3
      calc q * (2 * itCfDDomK * (2 * M + 1) ^ 3) ≤ (M + 1) * (2 * itCfDDomK * (2 * (M + 1)) ^ 3) :=
            Nat.mul_le_mul hqY (Nat.mul_le_mul_left _ this)
        _ = 16 * itCfDDomK * (M + 1) ^ 4 := by ring
    have t2 : loopModK * (200 * (M + 1) ^ 2 + 1) * (3 * (200 * (M + 1) ^ 2) + 3) ≤
        loopModK * 201 * 603 * (M + 1) ^ 4 := by
      have h1 : 1 ≤ (M + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      calc _ ≤ loopModK * (201 * (M + 1) ^ 2) * (603 * (M + 1) ^ 2) :=
            st_mul3 le_rfl (by omega) (by omega)
        _ = _ := by ring
    have t3 : q * q * (stDRefK * (20 * M + 30 + 1) ^ 2) ≤ 961 * stDRefK * (M + 1) ^ 4 := by
      have := Nat.pow_le_pow_left (show 20 * M + 30 + 1 ≤ 31 * (M + 1) by omega) 2
      calc q * q * (stDRefK * (20 * M + 30 + 1) ^ 2) ≤
            (M + 1) ^ 2 * (stDRefK * (31 * (M + 1)) ^ 2) :=
            Nat.mul_le_mul hqqY (Nat.mul_le_mul_left _ this)
        _ = 961 * stDRefK * (M + 1) ^ 4 := by ring
    have t4 : loopModK * (100 * (M + 1) ^ 4 + 1) * (3 * (100 * (M + 1) ^ 4) + 3) ≤
        loopModK * 101 * 303 * (M + 1) ^ 8 := by
      have h1 : 1 ≤ (M + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
      calc _ ≤ loopModK * (101 * (M + 1) ^ 4) * (303 * (M + 1) ^ 4) :=
            st_mul3 le_rfl (by omega) (by omega)
        _ = _ := by ring
    have t6 : 10000 * (q + 1) ^ 3 ≤ 80000 * (M + 1) ^ 3 := by
      have := Nat.pow_le_pow_left (show q + 1 ≤ 2 * (M + 1) by omega) 3
      calc _ ≤ 10000 * (2 * (M + 1)) ^ 3 := Nat.mul_le_mul_left _ this
        _ = _ := by ring
    have hp3 := hP 3 8 (by norm_num)
    have hp4 := hP 4 8 (by norm_num)
    have hp6 := hP 6 8 (by norm_num)
    have t7 : W + 1 ≤ 2001 * (M + 1) ^ 4 := by
      have : 1 ≤ (M + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
      omega
    clear gall gite g1 g2 gr1 gr2 gcp0 g42 gj2 href hdom gcond gA1 gm1 gV1 gq1 gqq1 gA2 gm2 gV2
      gq2 gqq2 gA3 gm3 gV3 gq3 gqq3
    simp only [stDSplitK, itCfDDomK, loopModK, stDRefK] at t1 t2 t3 t4 ⊢
    norm_num at t1 t2 t3 t4 ⊢
    linarith

end GI.Impl
