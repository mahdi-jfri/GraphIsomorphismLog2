module

public import Workspace.Impl.AggItemCiCfgU

@[expose] public section

/-!
# The configuration query: the color list and the domain as programs

* `itcqClF fmp fa` on `[zX, zY, R]` (with `zZ = [rcColVal Z, itcqFV Z, n]` and
  `R = [0, …, n² - 1]`) returns the list `itcqCL X Y hc` of all pair colors of `X` then `Y`
  (`itcq_clF_spec`, by `itcq_pcs_spec` twice and `append`).
* `itcq_cds_spec'` is `itcq_cds_spec` with the fiber size given as `n`; `itcq_memX`,
  `itcq_memY` are its hypothesis `hmem` for `X` and `Y`.
* `itcqOneF` (the constant `1`), mapped over `R`, gives the domain `encFun 1`
  (`itcq_dom_spec`).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm Finset
open GI.Cited (Val encPerm gens encGroup encPerms)

variable {q : ℕ}

/-- The input of the pair color programs of `Z` with `n` fiber points. -/
def itcqZ (Z : PairCfg q) (n : ℕ) : Val := .list [rcColVal Z, itcqFV Z, .nat n]

/-- On `[zX, zY, R]`: the list of all pair colors of `X` then `Y`. -/
def itcqClF (fmp fa : ℕ) : Expr :=
  .call fa (mk2 (.call fmp (mk2 (arg 0) (arg 2))) (.call fmp (mk2 (arg 1) (arg 2))))

/-- The constant `1`. -/
def itcqOneF : Expr := .nat 1

/-- The cost bound of `itcqClF`. -/
def itcqClC (W : ℕ) : ℕ := 3 * itcqMC (10 * (W + 2) ^ 2)

theorem itcq_memX (X Y : PairCfg q) (hc : X.fiber.card = Y.fiber.card)
    (t : Fin (X.fiber.card * X.fiber.card)) :
    itcqPC X rfl ((itciPE X.fiber.card).symm t) ∈ itcqCL X Y hc :=
  List.mem_append_left _ (List.mem_map.2 ⟨t, List.mem_finRange t, rfl⟩)

theorem itcq_memY (X Y : PairCfg q) (hc : X.fiber.card = Y.fiber.card)
    (t : Fin (X.fiber.card * X.fiber.card)) :
    itcqPC Y hc.symm ((itciPE X.fiber.card).symm t) ∈ itcqCL X Y hc :=
  List.mem_append_right _ (List.mem_map.2 ⟨t, List.mem_finRange t, rfl⟩)

/-- A pair color list weighs at most `2 n² W + n² + 4` for a color table of weight `W`. -/
theorem itcq_pcsV_wt (Z : PairCfg q) {n : ℕ} (h : Z.fiber.card = n) :
    (natList (itcqPcsV Z n h)).wt ≤ 2 * (n * n * (rcColVal Z).wt) + n * n + 4 := by
  have := itcq_natList_wt (l := itcqPcsV Z n h) (B := (rcColVal Z).wt) (by
    intro x hx
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx
    exact itcq_pcw Z _ _)
  simpa [itcqPcsV] using this

theorem itcq_clC_arith {W m A B o C K : ℕ} (hK : K ≤ 30) (hm : m ≤ W) (hA : A ≤ 10 * (W + 2) ^ 2)
    (hB : B ≤ 10 * (W + 2) ^ 2) (ho : o ≤ 10 * (W + 2) ^ 2)
    (hC : C ≤ K * (10 * (W + 2) ^ 2 + 1) + (itcqMC (10 * (W + 2) ^ 2) +
      itcqMC (10 * (W + 2) ^ 2) + loopModK * (B + 1) * (A + B + o + 1))) :
    C ≤ itcqClC W := by
  unfold itcqClC
  unfold loopModK at hC
  set V := 10 * (W + 2) ^ 2 with hV
  have hBV : B + 1 ≤ V + 2 := by omega
  have h1 : 1000 * (B + 1) * (A + B + o + 1) ≤ 1000 * ((V + 2) * (V + 2) ^ 2) := by
    rw [Nat.mul_assoc]
    refine Nat.mul_le_mul_left _ (Nat.mul_le_mul hBV ?_)
    have : 3 * V + 1 ≤ (V + 2) ^ 2 := by nlinarith
    omega
  have h2 : K * (V + 1) ≤ 30 * (V + 2) ^ 3 := by
    have : V + 1 ≤ (V + 2) ^ 3 := by nlinarith
    exact Nat.mul_le_mul hK this
  have e : (V + 2) * (V + 2) ^ 2 = (V + 2) ^ 3 := by ring
  unfold itcqMC at hC ⊢
  omega

section Prog

variable {P : Program}

/-- `itcq_cds_spec` with the fiber size `n`. -/
theorem itcq_cds_spec' {fpc fb fe fcd mb : ℕ} (hfp : P.funs[fpc]? = some itcqPcF)
    (hfb : P.HasAt fb (findFuns fb fe)) (hfe : P.funs[fe]? = some eqTestF)
    (hcd : P.funs[fcd]? = some (itcqCdF fpc fb)) (hm : P.HasAt mb (mapFuns mb fcd))
    (Z : PairCfg q) {n : ℕ} (h : Z.fiber.card = n) (CL : List ℕ)
    (hmem : ∀ t, itcqPC Z h ((itciPE n).symm t) ∈ CL) {W : ℕ}
    (hW : (Val.list [.list [itcqZ Z n, natList CL], natList (List.range (n * n))]).wt ≤ W) :
    FunAll P mb (.list [.list [itcqZ Z n, natList CL], natList (List.range (n * n))])
      (fun w cost =>
        w = encFun (fun t : Fin (n * n) => itcqCode CL (itcqPC Z h ((itciPE n).symm t))) ∧
          cost ≤ itcqCdsC W) := by
  subst h
  exact itcq_cds_spec hfp hfb hfe hcd hm Z rfl CL hmem hW

/-- **The list of all pair colors** of `X` then `Y`. -/
theorem itcq_clF_spec {f fmp fa fpc : ℕ} (hf : P.funs[f]? = some (itcqClF fmp fa))
    (hm : P.HasAt fmp (mapFuns fmp fpc)) (hpc : P.funs[fpc]? = some itcqPcF)
    (ha : P.HasAt fa (appendFuns fa)) (X Y : PairCfg q) (hc : X.fiber.card = Y.fiber.card)
    {W : ℕ} (hW : (Val.list [itcqZ X X.fiber.card, itcqZ Y X.fiber.card,
      natList (List.range (X.fiber.card * X.fiber.card))]).wt ≤ W) :
    FunDet P f (.list [itcqZ X X.fiber.card, itcqZ Y X.fiber.card,
      natList (List.range (X.fiber.card * X.fiber.card))]) (natList (itcqCL X Y hc))
      (itcqClC W) := by
  set n := X.fiber.card with hn
  set R := natList (List.range (n * n)) with hR
  set vs : List Val := [itcqZ X n, itcqZ Y n, R] with hvs
  have hzX : (itcqZ X n).wt < W := lt_of_lt_of_le (wt_le_wt_list (by simp [hvs])) hW
  have hzY : (itcqZ Y n).wt < W := lt_of_lt_of_le (wt_le_wt_list (by simp [hvs])) hW
  have hRw : R.wt < W := lt_of_lt_of_le (wt_le_wt_list (by simp [hvs])) hW
  have hm2 : n * n < W := by
    have := length_lt_wt_list ((List.range (n * n)).map Val.nat)
    simp only [List.length_map, List.length_range] at this
    have : (Val.list ((List.range (n * n)).map Val.nat)).wt = R.wt := rfl
    omega
  have hcX : (rcColVal X).wt < W :=
    lt_of_lt_of_le (wt_le_wt_list (by simp)) hzX.le
  have hcY : (rcColVal Y).wt < W :=
    lt_of_lt_of_le (wt_le_wt_list (by simp)) hzY.le
  have hW2 : W + 1 ≤ (W + 2) ^ 2 := by nlinarith
  have hpX := itcq_pcsV_wt X (n := n) rfl
  have hpY := itcq_pcsV_wt Y hc.symm
  have hnW : n * n * (rcColVal X).wt ≤ W * W := Nat.mul_le_mul hm2.le hcX.le
  have hnW' : n * n * (rcColVal Y).wt ≤ W * W := Nat.mul_le_mul hm2.le hcY.le
  have hWW : W * W ≤ (W + 2) ^ 2 := by nlinarith
  have hsq : (W + 2) ^ 2 = W * W + 4 * W + 4 := by ring
  have A0 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 0) (W := (10 * (W + 2) ^ 2)) rfl (by omega)
    (by omega) (by omega)
  have A1 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 1) (W := (10 * (W + 2) ^ 2)) rfl (by omega)
    (by omega) (by omega)
  have A2 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 2) (W := (10 * (W + 2) ^ 2)) rfl (by omega)
    (by omega) (by omega)
  have hiX := wt_list2_le (itcqZ X n) R
  have hiY := wt_list2_le (itcqZ Y n) R
  have mX := StDC.mk2 A0 A2 (by omega) (by omega)
  have mY := StDC.mk2 A1 A2 (by omega) (by omega)
  have fX : FunDet P fmp (.list [itcqZ X n, R]) (natList (itcqPcsV X n rfl)) (itcqMC (10 * (W + 2) ^ 2)) :=
    (itcq_pcs_spec hm hpc X (n := n) rfl (W := (10 * (W + 2) ^ 2)) (by show (Val.list [itcqZ X n, R]).wt ≤ (10 * (W + 2) ^ 2); omega)).mono
      fun w c ⟨hw, hc⟩ => ⟨hw, hc⟩
  have fY : FunDet P fmp (.list [itcqZ Y n, R]) (natList (itcqPcsV Y n hc.symm)) (itcqMC (10 * (W + 2) ^ 2)) :=
    (itcq_pcs_spec hm hpc Y (n := n) hc.symm (W := (10 * (W + 2) ^ 2)) (by show (Val.list [itcqZ Y n, R]).wt ≤ (10 * (W + 2) ^ 2); omega)).mono
      fun w c ⟨hw, hc⟩ => ⟨hw, hc⟩
  have cX := StDC.call mX fX (by omega)
  have cY := StDC.call mY fY (by omega)
  have hCL : natList (itcqCL X Y hc) =
      .list ((itcqPcsV X n rfl).map Val.nat ++ (itcqPcsV Y n hc.symm).map Val.nat) := by
    rw [itcqCL_eq, natList, List.map_append]
  have hCLw : (natList (itcqCL X Y hc)).wt ≤ 2 * (2 * (W * W)) + 2 * W + 4 := by
    have := itcq_natList_wt (l := itcqCL X Y hc) (B := W) (by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx; exact (itcq_pcw X _ _).trans hcX.le
      · obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx; exact (itcq_pcw Y _ _).trans hcY.le)
    have hl : (itcqCL X Y hc).length = 2 * (n * n) := itcqCL_length X Y hc
    rw [hl] at this
    have h2 : 2 * (n * n) * W ≤ 2 * (W * W) := by
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hm2.le)
    omega
  have hap2 := wt_list2_le (natList (itcqPcsV X n rfl)) (natList (itcqPcsV Y n hc.symm))
  have mm := StDC.mk2 cX cY (by omega) (by omega)
  have fA : FunDet P fa (.list [natList (itcqPcsV X n rfl), natList (itcqPcsV Y n hc.symm)])
      (natList (itcqCL X Y hc))
      (loopModK * ((itcqPcsV Y n hc.symm).map Val.nat).length.succ *
        ((Val.list [natList (itcqPcsV X n rfl), natList (itcqPcsV Y n hc.symm)]).wt +
          ((itcqPcsV Y n hc.symm).map Val.nat).length + (natList (itcqCL X Y hc)).wt + 1)) :=
    (append_spec ha _ _).mono fun w c ⟨hw, hc'⟩ => ⟨by rw [hw, hCL], by rw [hw, ← hCL] at hc'; exact hc'⟩
  have cA := StDC.call mm fA (by omega)
  refine StDC.funDet hf cA ?_
  have hlen : ((itcqPcsV Y n hc.symm).map Val.nat).length = n * n := by simp [itcqPcsV]
  rw [hlen] at ⊢
  refine itcq_clC_arith (K := 30) (m := n * n) le_rfl hm2.le
    (A := (Val.list [natList (itcqPcsV X n rfl), natList (itcqPcsV Y n hc.symm)]).wt)
    (B := n * n) (o := (natList (itcqCL X Y hc)).wt) (by omega) (by omega) (by omega) ?_
  simp only [Nat.succ_eq_add_one] at ⊢
  omega

/-- **The domain** `encFun 1` of the pair structure, by `map` of the constant `1`. -/
theorem itcq_dom_spec {mb f1 : ℕ} (hm : P.HasAt mb (mapFuns mb f1))
    (h1 : P.funs[f1]? = some itcqOneF) (m : ℕ) :
    FunAll P mb (.list [.list [], natList (List.range m)]) (fun w cost =>
      w = encFun (fun _ : Fin m => 1) ∧
        cost ≤ m * 4 + mapK * (m + 1) *
          ((Val.list [.list [], natList (List.range m)]).wt + w.wt + 1)) := by
  refine itcq_mapPos_spec hm (g := fun _ => 1) (Bd := 4) fun t => ?_
  exact StDC.funDet (W := 3) h1 (StDC.nat 1 le_rfl) le_rfl

end Prog

end GI.Impl
