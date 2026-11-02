import Workspace.Impl.AggItemCfDDom
import Workspace.Impl.AggStructDesPair

namespace GI.Impl

open GI.Algorithm GI.Lang GI.Cited
open GI.Machine (BinOp)

structure ItCfDPOK (dl tl : List ℕ) (q κ m : ℕ) (V : List ℕ) (j c₀ M : ℕ) : Prop where
  ctx : ItCfDCtx dl tl q κ
  len : V.length = q
  wt : (stDCP dl tl q κ m V j c₀).wt ≤ M

theorem ItCfDPOK.facts {dl tl : List ℕ} {q κ m : ℕ} {V : List ℕ} {j c₀ M : ℕ}
    (h : ItCfDPOK dl tl q κ m V j c₀ M) :
    (stDA dl tl q κ).wt < M ∧ (Val.nat m).wt < M ∧ (natList V).wt < M ∧ (Val.nat j).wt < M ∧
      (Val.nat c₀).wt < M ∧ q < M ∧ (Val.nat q).wt < M := by
  have h1 : (stDA dl tl q κ).wt < (stDCP dl tl q κ m V j c₀).wt := wt_le_wt_list (by simp [stDCP])
  have h2 : (Val.nat m).wt < (stDCP dl tl q κ m V j c₀).wt := wt_le_wt_list (by simp [stDCP])
  have h3 : (natList V).wt < (stDCP dl tl q κ m V j c₀).wt := wt_le_wt_list (by simp [stDCP])
  have h4 : (Val.nat j).wt < (stDCP dl tl q κ m V j c₀).wt := wt_le_wt_list (by simp [stDCP])
  have h5 : (Val.nat c₀).wt < (stDCP dl tl q κ m V j c₀).wt := wt_le_wt_list (by simp [stDCP])
  have h6 := h.ctx.le_wt.2.2
  have h7 : (Val.nat q).wt < (stDA dl tl q κ).wt := wt_stDA_ge.2.2.2.2.1
  have := h.wt
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem itCfD_ref_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some stDRefF) {dl tl : List ℕ}
    {q κ m : ℕ} {V : List ℕ} {j c₀ M : ℕ} (h : ItCfDPOK dl tl q κ m V j c₀ M) {p : ℕ}
    (hp : p < q * q) :
    FunDet P f (.list [stDCP dl tl q κ m V j c₀, .nat p]) (boolVal (stDRef V q j p))
      (stDRefK * (M + 1) ^ 2) := by
  obtain ⟨hA, hm, hV, hj, hc0, hq, hqw⟩ := h.facts
  have hM := h.wt
  have hu := st_div_lt hp
  have hv := st_mod_lt hp
  have hl := h.len
  have hX : M + 1 ≤ (M + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hpq : p < (M + 1) ^ 2 := by
    have : q * q ≤ (M + 1) * (M + 1) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  obtain ⟨W, hW⟩ : ∃ W, W = 4 * (M + 1) ^ 2 + 20 := ⟨_, rfl⟩
  have hpw := wt_nat_le p
  have hvs : (Val.list [stDCP dl tl q κ m V j c₀, .nat p]).wt ≤ W := by
    have := wt_list2_le (stDCP dl tl q κ m V j c₀) (.nat p); omega
  have g0 : StDC P [Val.list [stDCP dl tl q κ m V j c₀, .nat p]] (arg 0) (stDCP dl tl q κ m V j c₀) 3 0 W :=
    StDC.arg rfl hvs (by omega) (by omega)
  have g1 : StDC P [Val.list [stDCP dl tl q κ m V j c₀, .nat p]] (arg 1) (.nat p) 3 0 W := StDC.arg rfl hvs (by omega) (by omega)
  have gA := StDC.get (v := stDA dl tl q κ) g0 (StDC.nat 0 (by omega)) rfl (by omega)
  have gq : StDC P [Val.list [stDCP dl tl q κ m V j c₀, .nat p]] stDPq (.nat q) 7 0 W :=
    StDC.get (v := .nat q) gA (StDC.nat 2 (by omega)) rfl (by omega)
  have gu : StDC P [Val.list [stDCP dl tl q κ m V j c₀, .nat p]] stDPu (.nat (p / q)) 11 0 W :=
    StDC.arith' g1 gq (op := .div) rfl (by omega)
  have gv : StDC P [Val.list [stDCP dl tl q κ m V j c₀, .nat p]] stDPv (.nat (p % q)) 11 0 W :=
    StDC.arith' g1 gq (op := .mod) rfl (by omega)
  have gV := StDC.get (v := natList V) g0 (StDC.nat 2 (by omega)) rfl (by omega)
  have gj := StDC.get (v := .nat j) g0 (StDC.nat 3 (by omega)) rfl (by omega)
  have hVu : V[p / q]? = some (V.getD (p / q) 0) := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem?_eq_getElem (by omega)
  have hVv : V[p % q]? = some (V.getD (p % q) 0) := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem?_eq_getElem (by omega)
  have hwu : (Val.nat (V.getD (p / q) 0)).wt ≤ W := by
    have : (Val.nat (V.getD (p / q) 0)).wt < (natList V).wt :=
      wt_le_wt_list (List.mem_map.2 ⟨_, List.mem_of_getElem? hVu, rfl⟩)
    omega
  have hwv : (Val.nat (V.getD (p % q) 0)).wt ≤ W := by
    have : (Val.nat (V.getD (p % q) 0)).wt < (natList V).wt :=
      wt_le_wt_list (List.mem_map.2 ⟨_, List.mem_of_getElem? hVv, rfl⟩)
    omega
  have gVu := StDC.get (v := .nat (V.getD (p / q) 0)) gV gu (by rw [List.getElem?_map, hVu]; rfl) hwu
  have gVv := StDC.get (v := .nat (V.getD (p % q) 0)) gV gv (by rw [List.getElem?_map, hVv]; rfl) hwv
  have gc1 := StDC.arith' gu gv (op := .eq) (st_eq_toNat _ _)
    (by have := Bool.toNat_le (decide (p / q = p % q)); omega)
  have gc2 := StDC.arith' gVu gj (op := .eq) (st_eq_toNat _ _)
    (by have := Bool.toNat_le (decide (V.getD (p / q) 0 = j)); omega)
  have gc3 := StDC.arith' gVv gj (op := .eq) (st_eq_toNat _ _)
    (by have := Bool.toNat_le (decide (V.getD (p % q) 0 = j)); omega)
  have gin := StDC.ite (v := boolVal (decide (V.getD (p / q) 0 = j ∧ V.getD (p % q) 0 = j)))
    (t := .arith .eq (.get (.get (arg 0) (.nat 2)) stDPv) (.get (arg 0) (.nat 3)))
    (e := .nat 0) (nt := 23) (ne := 1) (Et := 0) (Ee := 0) gc2
    (fun hx => by
      have hx' := of_decide_eq_true (st_toNat_ne hx)
      have : decide (V.getD (p / q) 0 = j ∧ V.getD (p % q) 0 = j) =
          decide (V.getD (p % q) 0 = j) :=
        decide_eq_decide.2 ⟨fun h => h.2, fun h => ⟨hx', h⟩⟩
      rw [this]; exact gc3)
    (fun hx => by
      have hx' := of_decide_eq_false (st_toNat_eq hx)
      have : decide (V.getD (p / q) 0 = j ∧ V.getD (p % q) 0 = j) = false :=
        decide_eq_false (fun h => hx' h.1)
      rw [this]; exact StDC.nat 0 (by omega))
    (by have := wt_boolVal_le (decide (V.getD (p / q) 0 = j ∧ V.getD (p % q) 0 = j)); omega)
  have gout := StDC.ite (v := boolVal (stDRef V q j p))
    (t := .nat 0) (ne := 48) (nt := 1) (Et := 0) (Ee := 0) gc1
    (fun hx => by
      have hx' := of_decide_eq_true (st_toNat_ne hx)
      have : stDRef V q j p = false := by simp [stDRef, hx']
      rw [this]; exact StDC.nat 0 (by omega))
    (fun hx => by
      have hx' := of_decide_eq_false (st_toNat_eq hx)
      have : stDRef V q j p = decide (V.getD (p / q) 0 = j ∧ V.getD (p % q) 0 = j) := by
        simp [stDRef, hx']
      rw [this]; exact gin)
    (by have := wt_boolVal_le (stDRef V q j p); omega)
  refine StDC.funDet hf gout ?_
  unfold stDRefK
  subst hW
  generalize (M + 1) ^ 2 = X at *
  omega

theorem itCfD_dif_spec {P : Program} {f rf cf h : ℕ} (hf : P.funs[f]? = some (stDDifF rf cf))
    (hrf : P.funs[rf]? = some stDRefF) (hcf : P.funs[cf]? = some (stDColF h))
    (hh : P.HasAt h (stDHorFuns h)) {dl tl : List ℕ}
    {q κ m : ℕ} {V : List ℕ} {j c₀ M : ℕ} (hok : ItCfDPOK dl tl q κ m V j c₀ M) {p : ℕ}
    (hp : p < q * q) :
    FunDet P f (.list [stDCP dl tl q κ m V j c₀, .nat p])
      (boolVal (stDRef V q j p && !decide (stDCol dl tl q κ m (p / q) (p % q) = c₀)))
      (stDDifK * (M + 1) ^ 2) := by
  obtain ⟨hA, hm, hV, hj, hc0, hq, hqw⟩ := hok.facts
  have hM := hok.wt
  have hu := st_div_lt hp
  have hv := st_mod_lt hp
  have hX : M + 1 ≤ (M + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hpq : p < (M + 1) ^ 2 := by
    have : q * q ≤ (M + 1) * (M + 1) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  obtain ⟨W, hW⟩ : ∃ W, W = 20 * (M + 1) ^ 2 + 20 := ⟨_, rfl⟩
  have hpw := wt_nat_le p
  have hvs : (Val.list [stDCP dl tl q κ m V j c₀, .nat p]).wt ≤ W := by
    have := wt_list2_le (stDCP dl tl q κ m V j c₀) (.nat p); omega
  have g0 : StDC P [Val.list [stDCP dl tl q κ m V j c₀, .nat p]] (arg 0)
      (stDCP dl tl q κ m V j c₀) 3 0 W := StDC.arg rfl hvs (by omega) (by omega)
  have g1 : StDC P [Val.list [stDCP dl tl q κ m V j c₀, .nat p]] (arg 1) (.nat p) 3 0 W :=
    StDC.arg rfl hvs (by omega) (by omega)
  have gA := StDC.get (v := stDA dl tl q κ) g0 (StDC.nat 0 (by omega)) rfl (by omega)
  have gm := StDC.get (v := .nat m) g0 (StDC.nat 1 (by omega)) rfl (by omega)
  have gc0 := StDC.get (v := .nat c₀) g0 (StDC.nat 4 (by omega)) rfl (by omega)
  have gq : StDC P [Val.list [stDCP dl tl q κ m V j c₀, .nat p]] stDPq (.nat q) 7 0 W :=
    StDC.get (v := .nat q) gA (StDC.nat 2 (by omega)) rfl (by omega)
  have gu : StDC P [Val.list [stDCP dl tl q κ m V j c₀, .nat p]] stDPu (.nat (p / q)) 11 0 W :=
    StDC.arith' g1 gq (op := .div) rfl (by omega)
  have gv : StDC P [Val.list [stDCP dl tl q κ m V j c₀, .nat p]] stDPv (.nat (p % q)) 11 0 W :=
    StDC.arith' g1 gq (op := .mod) rfl (by omega)
  have hca : (stDCA dl tl q κ m (p / q) (p % q)).wt ≤ 8 * M + 8 := by
    have := wt_list4_le (stDA dl tl q κ) (.nat m) (.nat (p / q)) (.nat (p % q))
    have := wt_nat_le (p / q); have := wt_nat_le (p % q)
    unfold stDCA; omega
  have g4 := StDC.mk4 gA gm gu gv (by
    have := wt_list4_le (stDA dl tl q κ) (.nat m) (.nat (p / q)) (.nat (p % q))
    have := wt_nat_le (p / q); have := wt_nat_le (p % q); omega) (by omega)
  obtain ⟨x, hx⟩ : ∃ x, stDCol dl tl q κ m (p / q) (p % q) = x := ⟨_, rfl⟩
  have hcol := itCfD_col_spec hcf hh hok.ctx m hu hv
  rw [hx] at hcol
  have hxw : (Val.nat x).wt ≤ 2 * M + 2 := by
    have hw := itCfD_col_wt dl tl q κ m (p / q) (p % q)
    rw [hx] at hw
    have hdl : (natList dl).wt < (stDA dl tl q κ).wt := wt_stDA_ge.2.2.1
    omega
  have gcol := StDC.call g4 hcol (by omega)
  have geq := StDC.arith' gcol gc0 (op := .eq) (st_eq_toNat _ _)
    (by have := Bool.toNat_le (decide (x = c₀)); omega)
  have gsub := StDC.arith' (StDC.nat 1 (by omega)) geq (op := .sub)
    (show BinOp.eval .sub 1 (decide (x = c₀)).toNat = (!decide (x = c₀)).toNat by
      cases decide (x = c₀) <;> rfl)
    (by have := Bool.toNat_le (!decide (x = c₀)); omega)
  have gref := StDC.call (StDC.var' (P := P) (env := [Val.list [stDCP dl tl q κ m V j c₀, .nat p]])
    (i := 0) rfl (by omega)) (itCfD_ref_spec hrf hok hp) (by have := wt_boolVal_le (stDRef V q j p); omega)
  have gout := StDC.ite (v := boolVal (stDRef V q j p && !decide (x = c₀))) gref
    (fun hx' => by
      rw [st_toNat_ne hx', Bool.true_and]; exact gsub)
    (fun hx' => by
      rw [st_toNat_eq hx', Bool.false_and]; exact StDC.nat 0 (by omega))
    (by have := wt_boolVal_le (stDRef V q j p && !decide (x = c₀)); omega)
  rw [hx]
  refine StDC.funDet hf gout ?_
  have h3 : ((stDCA dl tl q κ m (p / q) (p % q)).wt + 1) ^ 2 ≤ 81 * (M + 1) ^ 2 := by
    have := Nat.pow_le_pow_left (show (stDCA dl tl q κ m (p / q) (p % q)).wt + 1 ≤ 9 * (M + 1)
      by omega) 2
    nlinarith
  generalize ((stDCA dl tl q κ m (p / q) (p % q)).wt + 1) ^ 2 = Y at *
  subst hW
  generalize (M + 1) ^ 2 = X at *
  have h6 : stDColK * Y ≤ stDColK * (81 * X) := Nat.mul_le_mul_left _ h3
  unfold stDDifK
  unfold stDColK stDRefK at *
  omega

end GI.Impl
