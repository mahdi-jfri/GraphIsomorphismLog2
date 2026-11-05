module

public import Workspace.Impl.AggItemCiCfgV

@[expose] public section

/-!
# The configuration query: the canonical value of the pair structure as a program

`itcqArgF` on `[zX, zY]` (with `zZ = itcqZ Z n`, `n = |C_X| = |C_Y|`) returns the canonical value
`itcqArg X Y hc` of the pair structure (`itcq_argF_spec`, cost `itcqArgC W`): it computes
`m = n²`, `R = [0, …, m - 1]`, the color list (`itcqClF`), the two color code lists
(`itcq_cds_spec'`), the group (`itcqGrpF`) and the domain (`itcq_dom_spec`), and lists the ten
entries with `itcqMkL` (a chain of `snoc`).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm Finset
open GI.Cited (Val encPerm gens encGroup encPerms)

variable {q : ℕ}

/-- The list of the values of `es`, by a chain of `snoc` from the empty list. -/
def itcqMkL (es : List Expr) : Expr := es.foldl .snoc .nil

section Prog

variable {P : Program}

theorem itcq_mkL_aux {env : List Val} {W : ℕ} :
    ∀ {es : List Expr} {vs : List Val}, List.Forall₂ (fun e v => StDC P env e v 1 0 W) es vs →
      ∀ {a : Expr} {us : List Val} {na : ℕ}, StDC P env a (.list us) na 0 W →
        (Val.list (us ++ vs)).wt ≤ W →
        StDC P env (es.foldl .snoc a) (.list (us ++ vs)) (na + 2 * es.length) 0 W
  | _, _, .nil, a, us, na, ha, _ => by simpa using ha
  | _, _, .cons (a := e) (b := v) (l₁ := es) (l₂ := vs) he hr, a, us, na, ha, hw => by
    have hpre : (Val.list (us ++ [v])).wt ≤ W :=
      (wt_list_mono ⟨vs, by simp⟩).trans hw
    have hs := StDC.snoc ha he hpre
    have := itcq_mkL_aux hr hs (by simpa using hw)
    simp only [List.foldl_cons, List.length_cons, List.append_assoc, List.singleton_append] at this ⊢
    exact this.mono (by omega) (by omega)

/-- **A list of simple entries.** -/
theorem itcq_mkL_spec {env : List Val} {W : ℕ} {es : List Expr} {vs : List Val}
    (h : List.Forall₂ (fun e v => StDC P env e v 1 0 W) es vs) (hw : (Val.list vs).wt ≤ W)
    (hW : 4 ≤ W) : StDC P env (itcqMkL es) (.list vs) (2 * es.length + 1) 0 W := by
  have := itcq_mkL_aux h (StDC.nil (P := P) (env := env) hW) (by simpa using hw)
  simp only [List.nil_append] at this
  exact this.mono (by omega) le_rfl

end Prog

/-- On `[zX, zY]`: the canonical value of the pair structure. -/
def itcqArgF (fr fcl fcd fg fd : ℕ) : Expr :=
  .letE (.arith .mul (.get (arg 0) (.nat 2)) (.get (arg 0) (.nat 2)))
  (.letE (.call fr (.var 1))
  (.letE (.call fcl (mk3 (arg 0) (arg 1) (.var 2)))
  (.letE (.call fcd (mk2 (mk2 (arg 0) (.var 3)) (.var 2)))
  (.letE (.call fcd (mk2 (mk2 (arg 1) (.var 3)) (.var 2)))
  (.letE (.call fg (.get (arg 0) (.nat 2)))
  (.letE (.call fd (mk2 .nil (.var 2)))
    (itcqMkL [.var 1, .var 6, .var 7, .var 4, .var 5, .nil, .nil, .nat 0, .nat 2, .var 1])))))))

/-- The weight bound inside `itcqArgF`. -/
def itcqAV (W : ℕ) : ℕ := 10 ^ 4 * (W + 2) ^ 8

/-- The cost bound of `itcqArgF`. -/
def itcqArgC (W : ℕ) : ℕ := 10 ^ 9 * (itcqAV W + 3) ^ 6

theorem itcq_argC_arith {V m K a r d o C : ℕ} (hK : K ≤ 200) (hm : m + 2 ≤ V)
    (ha : a ≤ V) (hr : r ≤ V) (hd : d ≤ V) (ho : o ≤ V)
    (hC : C ≤ K * (V + 1) + (loopModK * (m + 1) * (a + m + r + 1) + itcqClC V +
      itcqCdsC V + itcqCdsC V + itcqGrpC m + (m * 4 + mapK * (m + 1) * (d + o + 1)))) :
    C ≤ 10 ^ 9 * (V + 3) ^ 6 := by
  unfold loopModK mapK at hC
  unfold itcqClC itcqMC itcqCdsC itcqGrpC at hC
  have t1 : V + 3 ≤ (V + 3) ^ 2 := by nlinarith
  have t2 : (V + 3) ^ 2 ≤ (V + 3) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have t3 : (V + 3) ^ 3 ≤ (V + 3) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have t4 : (V + 3) ^ 4 ≤ (V + 3) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have t5 : (V + 3) ^ 5 ≤ (V + 3) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : 1000 * (m + 1) * (a + m + r + 1) ≤ 1000 * ((V + 3) * (4 * (V + 3))) := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
  have e1 : (V + 3) * (4 * (V + 3)) = 4 * (V + 3) ^ 2 := by ring
  have h2 : (10 * (V + 2) ^ 2 + 2) ^ 3 ≤ (11 * (V + 3) ^ 2) ^ 3 := by
    refine Nat.pow_le_pow_left ?_ 3
    have : (V + 2) ^ 2 ≤ (V + 3) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have e2 : (11 * (V + 3) ^ 2) ^ 3 = 1331 * (V + 3) ^ 6 := by ring
  have h3 : (m + 2) ^ 5 ≤ (V + 3) ^ 5 := Nat.pow_le_pow_left (by omega) 5
  have h4 : 1000 * (m + 1) * (d + o + 1) ≤ 1000 * ((V + 3) * (3 * (V + 3))) := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
  have e4 : (V + 3) * (3 * (V + 3)) = 3 * (V + 3) ^ 2 := by ring
  have h5 : K * (V + 1) ≤ 200 * (V + 3) := Nat.mul_le_mul hK (by omega)
  have h6 : m * 4 ≤ 4 * (V + 3) := by omega
  omega

/-- The weight of the canonical value of the pair structure. -/
theorem itcq_arg_wt (X Y : PairCfg q) (hc : X.fiber.card = Y.fiber.card) {W : ℕ}
    (hW : (Val.list [itcqZ X X.fiber.card, itcqZ Y X.fiber.card]).wt ≤ W) :
    (itcqArg X Y hc).wt ≤ itcqAV W := by
  obtain ⟨S, hS⟩ : ∃ S, S = (W + 2) ^ 2 := ⟨_, rfl⟩
  have hS1 : W + 2 ≤ S := by rw [hS]; nlinarith
  have hWW : W * W + 1 ≤ S := by rw [hS]; nlinarith
  have hS2 : S ≤ S * S := Nat.le_mul_self S
  have hS3 : S * S ≤ S * S * (S * S) := Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) (by omega))
  have hV : itcqAV W = 10 ^ 4 * (S * S * (S * S)) := by rw [itcqAV, hS]; ring
  -- the input
  set vs : List Val := [itcqZ X X.fiber.card, itcqZ Y X.fiber.card] with hvs
  have hzX : (itcqZ X X.fiber.card).wt < W := lt_of_lt_of_le (wt_le_wt_list (by simp [hvs])) hW
  have hzY : (itcqZ Y X.fiber.card).wt < W := lt_of_lt_of_le (wt_le_wt_list (by simp [hvs])) hW
  have hcX : (rcColVal X).wt < W := lt_of_lt_of_le (wt_le_wt_list (by simp [itcqZ])) hzX.le
  have hcY : (rcColVal Y).wt < W := lt_of_lt_of_le (wt_le_wt_list (by simp [itcqZ])) hzY.le
  have hFX : (itcqFV X).wt < W := lt_of_lt_of_le (wt_le_wt_list (by simp [itcqZ])) hzX.le
  have hn : X.fiber.card < W := by
    have := length_lt_wt_list (((itciFl X.fiber).map Fin.val).map Val.nat)
    simp only [List.length_map, itciFl_length] at this
    exact this.trans hFX
  have hm : X.fiber.card * X.fiber.card + 1 ≤ S := by
    have := Nat.mul_le_mul hn.le hn.le; omega
  have hS4 : 4 ≤ S * S := Nat.mul_le_mul (show 2 ≤ S by omega) (show 2 ≤ S by omega)
  -- the values and their weights
  have hRw : (natList (List.range (X.fiber.card * X.fiber.card))).wt ≤ 5 * (S * S) := by
    have h1 := itcq_range_wt (X.fiber.card * X.fiber.card)
    have h2 : (X.fiber.card * X.fiber.card + 1) ^ 2 ≤ S * S := by
      rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
    omega
  have hCLw : (natList (itcqCL X Y hc)).wt ≤ 10 * (S * S) := by
    have := itcq_natList_wt (l := itcqCL X Y hc) (B := W) (by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx; exact (itcq_pcw X _ _).trans hcX.le
      · obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx; exact (itcq_pcw Y _ _).trans hcY.le)
    have hl : (itcqCL X Y hc).length = 2 * (X.fiber.card * X.fiber.card) := itcqCL_length X Y hc
    rw [hl] at this
    have h2 : 2 * (X.fiber.card * X.fiber.card) * W ≤ 2 * (S * S) := by
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
    omega
  have hcode : ∀ (Z : PairCfg q) (h : Z.fiber.card = X.fiber.card),
      (∀ t, itcqPC Z h ((itciPE X.fiber.card).symm t) ∈ itcqCL X Y hc) →
      (encFun (fun t : Fin (X.fiber.card * X.fiber.card) =>
        itcqCode (itcqCL X Y hc) (itcqPC Z h ((itciPE X.fiber.card).symm t)))).wt ≤
          10 * (S * S) := by
    intro Z h hmem
    have := wt_encFun_le (fun t : Fin (X.fiber.card * X.fiber.card) =>
      itcqCode (itcqCL X Y hc) (itcqPC Z h ((itciPE X.fiber.card).symm t)))
      (B := 2 * (X.fiber.card * X.fiber.card)) (fun t => by
        have := itcqCode_lt (hmem t); rw [itcqCL_length] at this; exact this.le)
    have h2 : X.fiber.card * X.fiber.card * (2 * (2 * (X.fiber.card * X.fiber.card)) + 5) ≤
        S * (4 * S + 5) := Nat.mul_le_mul (by omega) (by omega)
    have h3 : S * (4 * S + 5) = 4 * (S * S) + 5 * S := by ring
    omega
  have hXV : (itcqXV X Y hc).wt ≤ 10 * (S * S) := hcode X rfl (itcq_memX X Y hc)
  have hYV : (itcqYV X Y hc).wt ≤ 10 * (S * S) := hcode Y hc.symm (itcq_memY X Y hc)
  have hGw : (encGroup (itcqGs X.fiber.card)).wt ≤ 160 * (S * S * (S * S)) := by
    have h1 : (encGroup (itcqGs X.fiber.card)).wt ≤
        40 * (((itcqGs X.fiber.card).length + 2) * (X.fiber.card * X.fiber.card + 1)) ^ 2 :=
      wt_encGroup_le _
    have hl : (itcqGs X.fiber.card).length ≤ X.fiber.card * X.fiber.card := by
      rw [itcqGs, List.length_map]; exact itcq_sw_length _
    have h2 : ((itcqGs X.fiber.card).length + 2) * (X.fiber.card * X.fiber.card + 1) ≤
        (2 * S) * S := Nat.mul_le_mul (by omega) (by omega)
    have h3 := Nat.pow_le_pow_left h2 2
    have h4 : ((2 * S) * S) ^ 2 = 4 * (S * S * (S * S)) := by ring
    omega
  have hDw : (encFun (fun _ : Fin (X.fiber.card * X.fiber.card) => 1)).wt ≤ 7 * S + 4 := by
    have := wt_encFun_le (fun _ : Fin (X.fiber.card * X.fiber.card) => 1) (B := 1) (fun _ => le_rfl)
    omega
  have hmw := wt_nat_le (X.fiber.card * X.fiber.card)
  have hnw := wt_nat_le X.fiber.card
  have hAw : (itcqArg X Y hc).wt ≤ 400 * (S * S * (S * S)) := by
    have := wt_list_le [Val.nat (X.fiber.card * X.fiber.card), encGroup (itcqGs X.fiber.card),
      encFun fun _ : Fin (X.fiber.card * X.fiber.card) => 1, itcqXV X Y hc, itcqYV X Y hc,
      .list [], .list [], boolVal false, .nat 2, .nat (X.fiber.card * X.fiber.card)]
    have hb := wt_boolVal_le false
    have h2 := wt_nat_le 2
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil, wt_list_nil] at this
    unfold itcqArg
    omega
  omega

section Prog

variable {P : Program}

set_option maxHeartbeats 1000000 in
/-- **The canonical value of the pair structure** as a program, in cost `itcqArgC W` for `W` at
least the input weight. -/
theorem itcq_argF_spec {f fr fcl fcd fg fd fmp fa fpc fb fe fcdi fgm fgg fgm' fsw f1 : ℕ}
    (hf : P.funs[f]? = some (itcqArgF fr fcl fcd fg fd))
    (hr : P.HasAt fr (rangeFuns fr))
    (hcl : P.funs[fcl]? = some (itcqClF fmp fa)) (hmp : P.HasAt fmp (mapFuns fmp fpc))
    (hpc : P.funs[fpc]? = some itcqPcF) (ha : P.HasAt fa (appendFuns fa))
    (hfb : P.HasAt fb (findFuns fb fe)) (hfe : P.funs[fe]? = some eqTestF)
    (hcdi : P.funs[fcdi]? = some (itcqCdF fpc fb)) (hcd : P.HasAt fcd (mapFuns fcd fcdi))
    (hg : P.funs[fg]? = some (itcqGrpF fr fgm fa)) (hgm : P.HasAt fgm (mapFuns fgm fgg))
    (hgg : P.funs[fgg]? = some (itcqGenF fgm')) (hgm' : P.HasAt fgm' (mapFuns fgm' fsw))
    (hsw : P.funs[fsw]? = some itcqSwF)
    (hd : P.HasAt fd (mapFuns fd f1)) (h1 : P.funs[f1]? = some itcqOneF)
    (X Y : PairCfg q) (hc : X.fiber.card = Y.fiber.card) {W : ℕ}
    (hW : (Val.list [itcqZ X X.fiber.card, itcqZ Y X.fiber.card]).wt ≤ W) :
    FunDet P f (.list [itcqZ X X.fiber.card, itcqZ Y X.fiber.card]) (itcqArg X Y hc)
      (itcqArgC W) := by
  obtain ⟨S, hS⟩ : ∃ S, S = (W + 2) ^ 2 := ⟨_, rfl⟩
  have hS1 : W + 2 ≤ S := by rw [hS]; nlinarith
  have hWW : W * W + 1 ≤ S := by rw [hS]; nlinarith
  have hS2 : S ≤ S * S := Nat.le_mul_self S
  have hS3 : S * S ≤ S * S * (S * S) := Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) (by omega))
  have hV : itcqAV W = 10 ^ 4 * (S * S * (S * S)) := by rw [itcqAV, hS]; ring
  -- the input
  set vs : List Val := [itcqZ X X.fiber.card, itcqZ Y X.fiber.card] with hvs
  have hzX : (itcqZ X X.fiber.card).wt < W := lt_of_lt_of_le (wt_le_wt_list (by simp [hvs])) hW
  have hzY : (itcqZ Y X.fiber.card).wt < W := lt_of_lt_of_le (wt_le_wt_list (by simp [hvs])) hW
  have hcX : (rcColVal X).wt < W := lt_of_lt_of_le (wt_le_wt_list (by simp [itcqZ])) hzX.le
  have hcY : (rcColVal Y).wt < W := lt_of_lt_of_le (wt_le_wt_list (by simp [itcqZ])) hzY.le
  have hFX : (itcqFV X).wt < W := lt_of_lt_of_le (wt_le_wt_list (by simp [itcqZ])) hzX.le
  have hn : X.fiber.card < W := by
    have := length_lt_wt_list (((itciFl X.fiber).map Fin.val).map Val.nat)
    simp only [List.length_map, itciFl_length] at this
    exact this.trans hFX
  have hm : X.fiber.card * X.fiber.card + 1 ≤ S := by
    have := Nat.mul_le_mul hn.le hn.le; omega
  have hS4 : 4 ≤ S * S := Nat.mul_le_mul (show 2 ≤ S by omega) (show 2 ≤ S by omega)
  -- the values and their weights
  have hRw : (natList (List.range (X.fiber.card * X.fiber.card))).wt ≤ 5 * (S * S) := by
    have h1 := itcq_range_wt (X.fiber.card * X.fiber.card)
    have h2 : (X.fiber.card * X.fiber.card + 1) ^ 2 ≤ S * S := by
      rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
    omega
  have hCLw : (natList (itcqCL X Y hc)).wt ≤ 10 * (S * S) := by
    have := itcq_natList_wt (l := itcqCL X Y hc) (B := W) (by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx; exact (itcq_pcw X _ _).trans hcX.le
      · obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx; exact (itcq_pcw Y _ _).trans hcY.le)
    have hl : (itcqCL X Y hc).length = 2 * (X.fiber.card * X.fiber.card) := itcqCL_length X Y hc
    rw [hl] at this
    have h2 : 2 * (X.fiber.card * X.fiber.card) * W ≤ 2 * (S * S) := by
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
    omega
  have hcode : ∀ (Z : PairCfg q) (h : Z.fiber.card = X.fiber.card),
      (∀ t, itcqPC Z h ((itciPE X.fiber.card).symm t) ∈ itcqCL X Y hc) →
      (encFun (fun t : Fin (X.fiber.card * X.fiber.card) =>
        itcqCode (itcqCL X Y hc) (itcqPC Z h ((itciPE X.fiber.card).symm t)))).wt ≤
          10 * (S * S) := by
    intro Z h hmem
    have := wt_encFun_le (fun t : Fin (X.fiber.card * X.fiber.card) =>
      itcqCode (itcqCL X Y hc) (itcqPC Z h ((itciPE X.fiber.card).symm t)))
      (B := 2 * (X.fiber.card * X.fiber.card)) (fun t => by
        have := itcqCode_lt (hmem t); rw [itcqCL_length] at this; exact this.le)
    have h2 : X.fiber.card * X.fiber.card * (2 * (2 * (X.fiber.card * X.fiber.card)) + 5) ≤
        S * (4 * S + 5) := Nat.mul_le_mul (by omega) (by omega)
    have h3 : S * (4 * S + 5) = 4 * (S * S) + 5 * S := by ring
    omega
  have hXV : (itcqXV X Y hc).wt ≤ 10 * (S * S) := hcode X rfl (itcq_memX X Y hc)
  have hYV : (itcqYV X Y hc).wt ≤ 10 * (S * S) := hcode Y hc.symm (itcq_memY X Y hc)
  have hGw : (encGroup (itcqGs X.fiber.card)).wt ≤ 160 * (S * S * (S * S)) := by
    have h1 : (encGroup (itcqGs X.fiber.card)).wt ≤
        40 * (((itcqGs X.fiber.card).length + 2) * (X.fiber.card * X.fiber.card + 1)) ^ 2 :=
      wt_encGroup_le _
    have hl : (itcqGs X.fiber.card).length ≤ X.fiber.card * X.fiber.card := by
      rw [itcqGs, List.length_map]; exact itcq_sw_length _
    have h2 : ((itcqGs X.fiber.card).length + 2) * (X.fiber.card * X.fiber.card + 1) ≤
        (2 * S) * S := Nat.mul_le_mul (by omega) (by omega)
    have h3 := Nat.pow_le_pow_left h2 2
    have h4 : ((2 * S) * S) ^ 2 = 4 * (S * S * (S * S)) := by ring
    omega
  have hDw : (encFun (fun _ : Fin (X.fiber.card * X.fiber.card) => 1)).wt ≤ 7 * S + 4 := by
    have := wt_encFun_le (fun _ : Fin (X.fiber.card * X.fiber.card) => 1) (B := 1) (fun _ => le_rfl)
    omega
  have hmw := wt_nat_le (X.fiber.card * X.fiber.card)
  have hnw := wt_nat_le X.fiber.card
  have hAw : (itcqArg X Y hc).wt ≤ 400 * (S * S * (S * S)) := by
    have := wt_list_le [Val.nat (X.fiber.card * X.fiber.card), encGroup (itcqGs X.fiber.card),
      encFun fun _ : Fin (X.fiber.card * X.fiber.card) => 1, itcqXV X Y hc, itcqYV X Y hc,
      .list [], .list [], boolVal false, .nat 2, .nat (X.fiber.card * X.fiber.card)]
    have hb := wt_boolVal_le false
    have h2 := wt_nat_le 2
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil, wt_list_nil] at this
    unfold itcqArg
    omega
  set V := itcqAV W with hVd
  have hSV : S * S * (S * S) ≤ V := by omega
  have hSS : S * S ≤ S * S * (S * S) := hS3
  -- names of the values
  set m := X.fiber.card * X.fiber.card with hmd
  set R := natList (List.range m) with hR
  set CLv := natList (itcqCL X Y hc) with hCLv
  set G := encGroup (itcqGs X.fiber.card) with hG
  set D := encFun (fun _ : Fin m => 1) with hD
  set XV := itcqXV X Y hc with hXVd
  set YV := itcqYV X Y hc with hYVd
  have hvw : (Val.list vs).wt ≤ V := by omega
  have hmw' : (Val.nat m).wt ≤ m + 2 := wt_nat_le m
  have hDV : D.wt ≤ V := le_trans hDw (by omega)
  have hRV : R.wt ≤ V := le_trans hRw (by omega)
  have hmV : m + 2 ≤ V := by omega
  have hnil : (Val.list []).wt = 4 := wt_list_nil
  -- the list of the ten entries
  have hA : itcqArg X Y hc = .list [(Val.nat m), G, D, XV, YV, .list [], .list [], .nat 0, .nat 2, (Val.nat m)] :=
    rfl
  have fin := itcq_mkL_spec (P := P) (env := [.list vs, (Val.nat m), R, CLv, XV, YV, G, D]) (W := V)
    (es := [.var 1, .var 6, .var 7, .var 4, .var 5, .nil, .nil, .nat 0, .nat 2, .var 1])
    (vs := [(Val.nat m), G, D, XV, YV, .list [], .list [], .nat 0, .nat 2, (Val.nat m)])
    (.cons (StDC.var' rfl (by omega)) (.cons (StDC.var' rfl (by omega))
      (.cons (StDC.var' rfl (by omega)) (.cons (StDC.var' rfl (by omega))
      (.cons (StDC.var' rfl (by omega)) (.cons (StDC.nil (by omega)) (.cons (StDC.nil (by omega))
      (.cons (StDC.nat 0 (by omega)) (.cons (StDC.nat 2 (by omega))
      (.cons (StDC.var' rfl (by omega)) .nil))))))))))
    (by rw [← hA]; omega) (by omega)
  rw [← hA] at fin
  simp only [List.length_cons, List.length_nil] at fin
  -- the domain
  have hd2 := wt_list2_le (.list []) R
  have d0 := StDC.mk2 (StDC.nil (P := P) (env := [.list vs, (Val.nat m), R, CLv, XV, YV, G]) (W := V) (by omega))
    (StDC.var' (P := P) (env := [.list vs, (Val.nat m), R, CLv, XV, YV, G]) (i := 2) rfl (by omega))
    (by simp only [wt_list_nil] at hd2; omega) (by omega)
  have hdom : FunDet P fd (.list [.list [], R]) D
      (m * 4 + mapK * (m + 1) * ((Val.list [.list [], R]).wt + D.wt + 1)) :=
    (itcq_dom_spec hd h1 m).mono fun w c ⟨hw, hc'⟩ => ⟨hw, by subst hw; exact hc'⟩
  have L7 := StDC.letE (StDC.call d0 hdom (by omega)) fin (by omega)
  -- the group
  have gn := StDC.get (StDC.arg (P := P) (rest := [(Val.nat m), R, CLv, XV, YV]) (vs := vs) (j := 0)
      (v := itcqZ X X.fiber.card) (W := V) rfl (by omega) (by omega) (by omega)) (StDC.nat 2 (by omega))
    (v := .nat X.fiber.card) rfl (by omega)
  have hgF : FunDet P fg (.nat X.fiber.card) G (itcqGrpC m) :=
    itcq_grpF_spec hg hr hgm ha hgg hgm' hsw X.fiber.card
  have L6 := StDC.letE (StDC.call gn hgF (by omega)) L7 (by omega)
  -- the color codes of `Y`
  have hcy1 := wt_list2_le (itcqZ Y X.fiber.card) CLv
  have hcy2 := wt_list2_le (.list [itcqZ Y X.fiber.card, CLv]) R
  have cy := StDC.mk2 (StDC.mk2 (StDC.arg (P := P) (rest := [(Val.nat m), R, CLv, XV]) (vs := vs) (j := 1)
      (W := V) rfl (by omega) (by omega) (by omega))
      (StDC.var' (P := P) (env := [.list vs, (Val.nat m), R, CLv, XV]) (i := 3) rfl (by omega)) (by omega)
      (by omega))
    (StDC.var' (P := P) (env := [.list vs, (Val.nat m), R, CLv, XV]) (i := 2) rfl (by omega)) (by omega) (by omega)
  have hYc : FunDet P fcd (.list [.list [itcqZ Y X.fiber.card, CLv], R]) YV (itcqCdsC V) :=
    (itcq_cds_spec' hpc hfb hfe hcdi hcd Y hc.symm (itcqCL X Y hc) (itcq_memY X Y hc)
      (W := V) (by show (Val.list [.list [itcqZ Y X.fiber.card, CLv], R]).wt ≤ V; omega)).mono fun w c ⟨hw, hc'⟩ => ⟨hw, hc'⟩
  have L5 := StDC.letE (StDC.call cy hYc (by omega)) L6 (by omega)
  -- the color codes of `X`
  have hcx1 := wt_list2_le (itcqZ X X.fiber.card) CLv
  have hcx2 := wt_list2_le (.list [itcqZ X X.fiber.card, CLv]) R
  have cx := StDC.mk2 (StDC.mk2 (StDC.arg (P := P) (rest := [(Val.nat m), R, CLv]) (vs := vs) (j := 0)
      (W := V) rfl (by omega) (by omega) (by omega))
      (StDC.var' (P := P) (env := [.list vs, (Val.nat m), R, CLv]) (i := 3) rfl (by omega)) (by omega)
      (by omega))
    (StDC.var' (P := P) (env := [.list vs, (Val.nat m), R, CLv]) (i := 2) rfl (by omega)) (by omega) (by omega)
  have hXc : FunDet P fcd (.list [.list [itcqZ X X.fiber.card, CLv], R]) XV (itcqCdsC V) :=
    (itcq_cds_spec' hpc hfb hfe hcdi hcd X rfl (itcqCL X Y hc) (itcq_memX X Y hc)
      (W := V) (by show (Val.list [.list [itcqZ X X.fiber.card, CLv], R]).wt ≤ V; omega)).mono fun w c ⟨hw, hc'⟩ => ⟨hw, hc'⟩
  have L4 := StDC.letE (StDC.call cx hXc (by omega)) L5 (by omega)
  -- the color list
  have hc3 := wt_list3_le (itcqZ X X.fiber.card) (itcqZ Y X.fiber.card) R
  have c3 := StDC.mk3 (StDC.arg (P := P) (rest := [(Val.nat m), R]) (vs := vs) (j := 0) (W := V) rfl
      (by omega) (by omega) (by omega))
    (StDC.arg (P := P) (rest := [(Val.nat m), R]) (vs := vs) (j := 1) (W := V) rfl (by omega) (by omega)
      (by omega))
    (StDC.var' (P := P) (env := [.list vs, (Val.nat m), R]) (i := 2) rfl (by omega)) (by omega) (by omega)
  have hclF : FunDet P fcl (.list [itcqZ X X.fiber.card, itcqZ Y X.fiber.card, R]) CLv
      (itcqClC V) := itcq_clF_spec hcl hmp hpc ha X Y hc (W := V)
        (by show (Val.list [itcqZ X X.fiber.card, itcqZ Y X.fiber.card, R]).wt ≤ V; omega)
  have L3 := StDC.letE (StDC.call c3 hclF (by omega)) L4 (by omega)
  -- the range
  have hrd : FunDet P fr (Val.nat m) R (loopModK * (m + 1) * ((Val.nat m).wt + m + R.wt + 1)) :=
    (range_spec hr m).mono fun w c ⟨hw, hc'⟩ => ⟨hw, by subst hw; exact hc'⟩
  have L2 := StDC.letE (StDC.call (StDC.var' (P := P) (env := [.list vs, (Val.nat m)]) (i := 1) rfl (by omega))
    hrd (by omega)) L3 (by omega)
  -- `m = n²`
  have g0 := StDC.get (StDC.arg (P := P) (rest := []) (vs := vs) (j := 0)
      (v := itcqZ X X.fiber.card) (W := V) rfl
      (by omega) (by omega) (by omega)) (StDC.nat 2 (by omega)) (v := .nat X.fiber.card) rfl
    (by omega)
  have mu := StDC.arith (op := .mul) g0 g0 (z := m) rfl (by omega)
  have L1 := StDC.letE mu L2 (by omega)
  refine StDC.funDet hf L1 ?_
  show _ ≤ 10 ^ 9 * (V + 3) ^ 6
  refine itcq_argC_arith (K := 200) (m := m) le_rfl (by omega) (a := (Val.nat m).wt) (by omega)
    (r := R.wt) (by omega) (d := (Val.list [.list [], R]).wt) (by omega) (o := D.wt) (by omega) ?_
  omega

end Prog

end GI.Impl
