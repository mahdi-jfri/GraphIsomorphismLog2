module

public import Workspace.Impl.AggItemCiPartP

@[expose] public section

/-!
# The colored-partition item as a program: the item

`itciF` on `[encFun fX, encFun fY]` returns the program's overcosets `itciOs fX fY (itciOt fX) E₀`
as values `[encPerm σ, ⟨ms⟩]` (`itci_f_spec`):
1. the aligning permutation `al` (`itciAF`) and the check that it maps `fX` to `fY` (`all` with
   `itciChkT`);
2. the generators `itciGF`: the found point `a` (if any), the transposition at `a` and the
   Schreier list;
3. the parity of `al` (Case 1's `itParF`), and the even representative: `al` if it is even,
   `al · t` if it is odd and `a` exists.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens)

variable {q : ℕ}

/-- The values of a list of overcosets. -/
def itciOV (os : List (LcOver q)) : Val := .list (os.map fun o => lcOv (o.1 : Perm (Fin q)) o.2.2)

/-- The branch after a successful check. -/
def itciBr (cmp : ℕ) : Expr :=
  .ite (.get (.var 4) (.nat 0))
    (.ite (.var 5)
      (.snoc .nil (mk2 (.call cmp (mk2 (.var 2) (.get (.var 4) (.nat 1)))) (.get (.var 4) (.nat 2))))
      (.snoc .nil (mk2 (.var 2) (.get (.var 4) (.nat 2)))))
    (.ite (.var 5) .nil (.snoc .nil (mk2 (.var 2) .nil)))

/-- On `[FX, FY]`: the overcosets of the item. -/
def itciF (rng fa all fg par cmp : ℕ) : Expr :=
  .letE (.call rng (.length (.get (.var 0) (.nat 0))))
  (.letE (.call fa (.var 0))
  (.letE (.call all (mk2 (mk3 (.get (.var 0) (.nat 0)) (.get (.var 0) (.nat 1)) (.var 2)) (.var 1)))
  (.letE (.call fg (mk2 (.get (.var 0) (.nat 0)) (.var 1)))
  (.letE (.call par (.var 2))
  (.ite (.var 3) (itciBr cmp) .nil)))))

theorem itci_par_ne {σ : Perm (Fin q)} : itpNInv σ % 2 ≠ 0 ↔ sign σ ≠ 1 := it_parity_ne

theorem itciOV_wt {os : List (LcOver q)} (hl : os.length ≤ 1)
    (hms : ∀ o ∈ os, o.2.2.length ≤ 2 * q) : (itciOV os).wt ≤ 200 * (q + 1) ^ 3 := by
  have hq1 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqb : (q + 1) ^ 2 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : 2 * q * (9 * (q + 1) ^ 2) ≤ 18 * (q + 1) ^ 3 := by
    calc 2 * q * (9 * (q + 1) ^ 2) ≤ 2 * (q + 1) * (9 * (q + 1) ^ 2) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 18 * (q + 1) ^ 3 := by ring
  have h := wt_list_le_of (os.map fun o => lcOv (o.1 : Perm (Fin q)) o.2.2)
    (c := 60 * (q + 1) ^ 3) (fun v hv => by
      obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hv
      have h1 := wt_encPerm_le (o.1 : Perm (Fin q))
      have h2 := it_perms_wt (l := o.2.2) (m := 2 * q) (hms o ho)
      have := wt_list2_le (encPerm (o.1 : Perm (Fin q))) (.list (o.2.2.map encPerm))
      unfold lcOv; omega)
  rw [List.length_map] at h
  have : os.length * (2 * (60 * (q + 1) ^ 3) + 1) ≤ 121 * (q + 1) ^ 3 := by
    calc os.length * (2 * (60 * (q + 1) ^ 3) + 1) ≤ 1 * (2 * (60 * (q + 1) ^ 3) + 1) :=
          Nat.mul_le_mul_right _ hl
      _ ≤ 121 * (q + 1) ^ 3 := by omega
  unfold itciOV; omega

theorem itciOs_props (fX fY : Fin q → ℕ) (E₀ : Subgroup (alternatingGroup (Fin q))) :
    (itciOs fX fY (itciOt fX) E₀).length ≤ 1 ∧
      ∀ o ∈ itciOs fX fY (itciOt fX) E₀, o.2.2.length ≤ 2 * q := by
  classical
  refine ⟨?_, fun o ho => ?_⟩
  · cases h : itciOt fX <;> simp only [itciOs, h] <;> split_ifs <;> simp
  · rw [(itciOs_snd ho).2]
    cases itciOt fX with
    | none => simp [itciMs]
    | some a => exact itciMs_length fX a

set_option maxHeartbeats 8000000 in
/-- **The branch after the check**, on an environment whose entries `2, 4, 5` are the aligning
permutation, the generators and the parity. -/
theorem itci_br_spec {P : Program} {cmp : ℕ} (hcmp : P.HasAt cmp (composeFuns cmp))
    {env : List Val} {W : ℕ} (fX fY : Fin q → ℕ) (E₀ : Subgroup (alternatingGroup (Fin q)))
    (h2 : env[2]? = some (encPerm (itciAl fX fY))) (h4 : env[4]? = some (itciGV fX))
    (h5 : env[5]? = some (.nat (itpNInv (itciAl fX fY) % 2)))
    (hc : ∀ a, fY (itciAl fX fY a) = fX a) (hW : 200 * (q + 1) ^ 3 + 100 ≤ W) :
    StDC P env (itciBr cmp) (itciOV (itciOs fX fY (itciOt fX) E₀)) 40 (permK * (q + 1) ^ 3) W := by
  classical
  have hq1 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqb : (q + 1) ^ 2 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hW4 : 4 ≤ W := by omega
  have hOV := itciOV_wt (itciOs_props fX fY E₀).1 (itciOs_props fX fY E₀).2
  have hal := wt_encPerm_le (itciAl fX fY)
  have hpw : (Val.nat (itpNInv (itciAl fX fY) % 2)).wt ≤ W := by
    have := wt_nat_le (itpNInv (itciAl fX fY) % 2)
    have := Nat.mod_lt (itpNInv (itciAl fX fY)) (show 2 > 0 by omega); omega
  have v2 : StDC P env (.var 2) (encPerm (itciAl fX fY)) 1 0 W := StDC.var' h2 (by omega)
  have v5 : StDC P env (.var 5) (.nat (itpNInv (itciAl fX fY) % 2)) 1 0 W := StDC.var' h5 hpw
  cases hot : itciOt fX with
  | some a =>
    set ms := itciMs fX (some a)
    have hms := it_perms_wt (l := ms) (m := 2 * q) (itciMs_length fX a)
    have h3 : 2 * q * (9 * (q + 1) ^ 2) ≤ 18 * (q + 1) ^ 3 := by
      calc 2 * q * (9 * (q + 1) ^ 2) ≤ 2 * (q + 1) * (9 * (q + 1) ^ 2) :=
            Nat.mul_le_mul_right _ (by omega)
        _ = 18 * (q + 1) ^ 3 := by ring
    have htw := wt_encPerm_le (itciTr fX a)
    have hG : itciGV fX = .list [.nat 1, encPerm (itciTr fX a), .list (ms.map encPerm)] := by
      unfold itciGV; rw [hot]
    have hGw := wt_list3_le (.nat 1) (encPerm (itciTr fX a)) (.list (ms.map encPerm))
    have h1w := wt_nat_le 1
    rw [hG] at h4
    have v4 : StDC P env (.var 4) (.list [.nat 1, encPerm (itciTr fX a), .list (ms.map encPerm)])
      1 0 W := StDC.var' h4 (by omega)
    have g0 := StDC.get v4 (StDC.nat 0 (by omega)) (v := .nat 1) rfl (by omega)
    have g1 := StDC.get v4 (StDC.nat 1 (by omega)) (v := encPerm (itciTr fX a)) rfl (by omega)
    have g2 := StDC.get v4 (StDC.nat 2 (by omega)) (v := .list (ms.map encPerm)) rfl (by omega)
    have hpair := wt_list2_le (encPerm (itciAl fX fY)) (encPerm (itciTr fX a))
    have hlc := wt_list2_le (encPerm (itciAl fX fY)) (.list (ms.map encPerm))
    have hat := wt_encPerm_le (itciAl fX fY * itciTr fX a)
    have hlc' := wt_list2_le (encPerm (itciAl fX fY * itciTr fX a)) (.list (ms.map encPerm))
    have hs1 : ∀ v : Val, v.wt ≤ 60 * (q + 1) ^ 3 → (Val.list ([] ++ [v])).wt ≤ W := by
      intro v hv
      have := wt_list_le_of [v] (c := 60 * (q + 1) ^ 3) (fun x hx => by
        rw [List.mem_singleton] at hx; subst hx; exact hv)
      simp only [List.nil_append, List.length_singleton] at this ⊢; omega
    have hodd := StDC.snoc (StDC.nil (env := env) hW4)
      (StDC.mk2 (StDC.call (StDC.mk2 v2 g1 (by omega) hW4)
        (compose_spec hcmp (itciAl fX fY) (itciTr fX a)) (by omega)) g2 (by omega) hW4)
      (hs1 _ (by omega))
    have hev := StDC.snoc (StDC.nil (env := env) hW4) (StDC.mk2 v2 g2 (by omega) hW4)
      (hs1 _ (by omega))
    simp only [List.nil_append] at hodd hev
    have hin := StDC.ite (v := itciOV (itciOs fX fY (itciOt fX) E₀)) v5
      (fun hp => by
        have hs := itci_par_ne.1 hp
        have ha := (itciOt_spec fX).2 a hot
        have hs' : sign (itciAl fX fY * itciTr fX a) = 1 := by
          rw [Perm.sign_mul, (itp_sign_cases _).resolve_left hs, itciTr, Perm.sign_swap ha]
          decide
        have e : itciOV (itciOs fX fY (itciOt fX) E₀) =
            .list [.list [encPerm (itciAl fX fY * itciTr fX a), .list (ms.map encPerm)]] := by
          simp only [itciOV, itciOs, if_pos hc, hot, dif_neg hs, dif_pos hs', List.map_cons,
            List.map_nil, lcOv, ms]
        rw [e]; exact hodd)
      (fun hp => by
        have hs : sign (itciAl fX fY) = 1 := by
          by_contra h; exact itci_par_ne.2 h hp
        have e : itciOV (itciOs fX fY (itciOt fX) E₀) =
            .list [.list [encPerm (itciAl fX fY), .list (ms.map encPerm)]] := by
          simp only [itciOV, itciOs, if_pos hc, hot, dif_pos hs, List.map_cons, List.map_nil,
            lcOv, ms]
        rw [e]; exact hev)
      (by omega)
    rw [← hot]
    unfold itciBr
    refine (StDC.ite (ne := 0) (Ee := 0) g0 (fun _ => hin) (fun h => absurd h one_ne_zero)
      (by omega)).mono ?_ ?_
    · norm_num
    · simp only [permK]; omega
  | none =>
    have hG : itciGV fX = .list [.nat 0] := by unfold itciGV; rw [hot]
    rw [hG] at h4
    have hGw := wt_list_le_of [Val.nat 0] (c := 2) (fun v hv => by
      rw [List.mem_singleton] at hv; subst hv; exact wt_nat_le 0)
    simp only [List.length_singleton] at hGw
    have v4 : StDC P env (.var 4) (.list [.nat 0]) 1 0 W := StDC.var' h4 (by omega)
    have g0 := StDC.get v4 (StDC.nat 0 (by omega)) (v := .nat 0) rfl (by have := wt_nat_le 0; omega)
    have hn := wt_list2_le (encPerm (itciAl fX fY)) (.list [])
    have hnil := wt_list_nil
    have hs1 : (Val.list ([] ++ [Val.list [encPerm (itciAl fX fY), .list []]])).wt ≤ W := by
      have := wt_list_le_of [Val.list [encPerm (itciAl fX fY), .list []]] (c := 45 * (q + 1) ^ 3)
        (fun x hx => by rw [List.mem_singleton] at hx; subst hx; omega)
      simp only [List.nil_append, List.length_singleton] at this ⊢; omega
    have hev := StDC.snoc (StDC.nil (env := env) hW4) (StDC.mk2 v2 (StDC.nil hW4) (by omega) hW4)
      hs1
    simp only [List.nil_append] at hev
    have hin := StDC.ite (v := itciOV (itciOs fX fY (itciOt fX) E₀)) v5
      (fun hp => by
        have hs := itci_par_ne.1 hp
        have e : itciOV (itciOs fX fY (itciOt fX) E₀) = .list [] := by
          simp only [itciOV, itciOs, if_pos hc, hot, dif_neg hs, List.map_nil]
        rw [e]; exact StDC.nil hW4)
      (fun hp => by
        have hs : sign (itciAl fX fY) = 1 := by
          by_contra h; exact itci_par_ne.2 h hp
        have e : itciOV (itciOs fX fY (itciOt fX) E₀) =
            .list [.list [encPerm (itciAl fX fY), .list []]] := by
          simp only [itciOV, itciOs, if_pos hc, hot, dif_pos hs, List.map_cons, List.map_nil,
            lcOv]
        rw [e]; exact hev)
      (by omega)
    rw [← hot]
    unfold itciBr
    refine (StDC.ite (nt := 0) (Et := 0) g0 (fun h => absurd rfl h) (fun _ => hin)
      (by omega)).mono ?_ ?_
    · norm_num
    · omega

/-- The cost bound of `itciF`. -/
def itciFC (M : ℕ) : ℕ := 10 ^ 12 * (M + 2) ^ 6

set_option maxHeartbeats 8000000 in
/-- **The colored-partition item as a program**, from the programs of its parts. -/
theorem itci_f_spec {P : Program} {f rng fa all chk fg par cmp : ℕ}
    (hf : P.funs[f]? = some (itciF rng fa all fg par cmp)) (hrng : P.HasAt rng (rangeFuns rng))
    (hall : P.HasAt all (allFuns all chk)) (hchk : P.funs[chk]? = some itciChkT)
    (hcmp : P.HasAt cmp (composeFuns cmp))
    (hpar : ∀ σ : Perm (Fin q), FunDet P par (encPerm σ) (.nat (itpNInv σ % 2)) (itParC q))
    (fX fY : Fin q → ℕ) {M : ℕ} (hMX : (encFun fX).wt ≤ M) (hMY : (encFun fY).wt ≤ M)
    (hfa : FunDet P fa (.list [encFun fX, encFun fY]) (encPerm (itciAl fX fY)) (itciAC M))
    (hfg : FunDet P fg (.list [encFun fX, natList (List.range q)]) (itciGV fX) (itciGC M))
    (E₀ : Subgroup (alternatingGroup (Fin q))) :
    FunDet P f (.list [encFun fX, encFun fY]) (itciOV (itciOs fX fY (itciOt fX) E₀))
      (itciFC M) := by
  classical
  have hqM := (itci_q_le_wt fX).trans hMX
  have hR := it_range_wt (q := q)
  have hq1 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqa : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hqb : (q + 1) ^ 2 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hq2 : (q + 1) ^ 2 ≤ (M + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hq3 : (q + 1) ^ 3 ≤ (M + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hq4 : (q + 1) ^ 4 ≤ (M + 2) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have hM2 : M + 2 ≤ (M + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hM23 : (M + 2) ^ 2 ≤ (M + 2) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hM34 : (M + 2) ^ 3 ≤ (M + 2) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hM46 : (M + 2) ^ 4 ≤ (M + 2) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  set W := 300 * (M + 2) ^ 3 with hW
  have hin := wt_list2_le (encFun fX) (encFun fY)
  have hal := wt_encPerm_le (itciAl fX fY)
  have hOV := itciOV_wt (itciOs_props fX fY E₀).1 (itciOs_props fX fY E₀).2
  have hGw : (itciGV fX).wt ≤ 200 * (q + 1) ^ 3 := by
    unfold itciGV
    split
    · rename_i a _
      have := wt_list3_le (.nat 1) (encPerm (itciTr fX a)) (.list ((itciMs fX (some a)).map encPerm))
      have h1 := wt_encPerm_le (itciTr fX a)
      have h2 := it_perms_wt (l := itciMs fX (some a)) (m := 2 * q) (itciMs_length fX a)
      have h3 : 2 * q * (9 * (q + 1) ^ 2) ≤ 18 * (q + 1) ^ 3 := by
        calc 2 * q * (9 * (q + 1) ^ 2) ≤ 2 * (q + 1) * (9 * (q + 1) ^ 2) :=
              Nat.mul_le_mul_right _ (by omega)
          _ = 18 * (q + 1) ^ 3 := by ring
      have := wt_nat_le 1
      omega
    · have := wt_list_le_of [Val.nat 0] (c := 2) (fun v hv => by
        rw [List.mem_singleton] at hv; subst hv; exact wt_nat_le 0)
      simp at this; omega
  have hW4 : 4 ≤ W := by omega
  -- the range and the alignment
  have w0 : StDC P [Val.list [encFun fX, encFun fY]] (.var 0) (.list [encFun fX, encFun fY])
    1 0 W := StDC.var' rfl (by omega)
  have gX0 := StDC.get w0 (StDC.nat 0 (by omega)) (v := encFun fX) rfl (by omega)
  have l1 := StDC.length (vs := (List.finRange q).map fun i => Val.nat (fX i)) gX0
    (by simp; omega)
  simp only [List.length_map, List.length_finRange] at l1
  have d1 := StDC.call l1 (st_range_det hrng q) (by omega)
  have d2 := StDC.call (StDC.var' (W := W) (env := [Val.list [encFun fX, encFun fY],
    natList (List.range q)]) (i := 0) rfl (by omega)) hfa (by omega)
  -- the check
  set E2 : List Val := [Val.list [encFun fX, encFun fY], natList (List.range q),
    encPerm (itciAl fX fY)]
  have y0 : StDC P E2 (.var 0) (.list [encFun fX, encFun fY]) 1 0 W := StDC.var' rfl (by omega)
  have y1 : StDC P E2 (.var 1) (natList (List.range q)) 1 0 W := StDC.var' rfl (by omega)
  have y2 : StDC P E2 (.var 2) (encPerm (itciAl fX fY)) 1 0 W := StDC.var' rfl (by omega)
  have yX := StDC.get y0 (StDC.nat 0 (by omega)) (v := encFun fX) rfl (by omega)
  have yY := StDC.get y0 (StDC.nat 1 (by omega)) (v := encFun fY) rfl (by omega)
  have hc3 := wt_list3_le (encFun fX) (encFun fY) (encPerm (itciAl fX fY))
  have hc2 := wt_list2_le (.list [encFun fX, encFun fY, encPerm (itciAl fX fY)])
    (natList (List.range q))
  set xs := (List.range q).map Val.nat
  have hxl : xs.length = q := by simp [xs]
  have hA := all_spec hall (c := .list [encFun fX, encFun fY, encPerm (itciAl fX fY)]) (xs := xs)
    (q := itciChQ fX fY (itciAl fX fY)) (B := fun _ => itciKC ((q + 1) ^ 2 + M)) (fun v hv => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hv
      exact itci_chkT_spec hchk fX fY (itciAl fX fY) hMX hMY ⟨a, List.mem_range.1 ha⟩)
  set CK := decide (∀ a, fY (itciAl fX fY a) = fX a) with hCK
  have hAd : FunDet P all (.list [.list [encFun fX, encFun fY, encPerm (itciAl fX fY)],
      natList (List.range q)]) (boolVal CK)
      (q * itciKC ((q + 1) ^ 2 + M) + loopModK * (q + 1) * (W + q + 4)) := by
    refine hA.mono fun w c ⟨h1, h2⟩ => ⟨by rw [h1, itci_all_chk], ?_⟩
    have hsum : (xs.map fun _ => itciKC ((q + 1) ^ 2 + M)).sum = q * itciKC ((q + 1) ^ 2 + M) := by
      simp [Function.comp_def, List.map_const', List.sum_replicate, xs]
    rw [hsum, hxl] at h2
    refine h2.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_) _)
    have : (Val.list [.list [encFun fX, encFun fY, encPerm (itciAl fX fY)], .list xs]).wt ≤ W := by
      show (Val.list [.list [encFun fX, encFun fY, encPerm (itciAl fX fY)],
        natList (List.range q)]).wt ≤ W
      omega
    omega
  have hbw := wt_boolVal_le CK
  have d3 := StDC.call (StDC.mk2 (StDC.mk3 yX yY y2 (by omega) hW4) y1 (by omega) hW4) hAd
    (by omega)
  -- the generators and the parity
  set E3 : List Val := E2 ++ [boolVal CK]
  have z0 : StDC P E3 (.var 0) (.list [encFun fX, encFun fY]) 1 0 W := StDC.var' rfl (by omega)
  have z1 : StDC P E3 (.var 1) (natList (List.range q)) 1 0 W := StDC.var' rfl (by omega)
  have zX := StDC.get z0 (StDC.nat 0 (by omega)) (v := encFun fX) rfl (by omega)
  have hxr := wt_list2_le (encFun fX) (natList (List.range q))
  have d4 := StDC.call (StDC.mk2 zX z1 (by omega) hW4) hfg (by omega)
  set E4 : List Val := E3 ++ [itciGV fX]
  have hpw : (Val.nat (itpNInv (itciAl fX fY) % 2)).wt ≤ W := by
    have := wt_nat_le (itpNInv (itciAl fX fY) % 2)
    have := Nat.mod_lt (itpNInv (itciAl fX fY)) (show 2 > 0 by omega); omega
  have d5 := StDC.call (StDC.var' (W := W) (env := E4) (i := 2) rfl (by omega))
    (hpar (itciAl fX fY)) hpw
  set E5 : List Val := E4 ++ [.nat (itpNInv (itciAl fX fY) % 2)]
  -- the branches
  have hite := StDC.ite (v := itciOV (itciOs fX fY (itciOt fX) E₀)) (x := CK.toNat)
    (StDC.var' (W := W) (env := E5) (i := 3) rfl (by unfold boolVal at hbw; omega))
    (fun hx => by
      have hc : ∀ a, fY (itciAl fX fY a) = fX a := by
        by_contra h
        have : CK = false := by rw [hCK]; exact decide_eq_false h
        rw [this] at hx; exact hx rfl
      exact itci_br_spec hcmp fX fY E₀ (env := E5) rfl rfl rfl hc (by omega))
    (fun hx => by
      have hc : ¬ ∀ a, fY (itciAl fX fY a) = fX a := by
        intro h
        have : CK = true := by rw [hCK]; exact decide_eq_true h
        rw [this] at hx; exact absurd hx (by decide)
      have e : itciOV (itciOs fX fY (itciOt fX) E₀) = .list [] := by
        simp only [itciOV, itciOs, if_neg hc, List.map_nil]
      rw [e]; exact StDC.nil hW4)
    (by omega)
  have dall := StDC.letE d1 (StDC.letE d2 (StDC.letE d3 (StDC.letE d4 (StDC.letE d5 hite
    (by omega)) (by omega)) (by omega)) (by omega)) (by omega)
  refine StDC.funDet hf dall ?_
  unfold itciFC itciAC itciGC itParC itciKC
  simp only [permK]
  have c1 : q * (10 ^ 4 * ((q + 1) ^ 2 + M + 2)) ≤ 2 * 10 ^ 4 * (M + 2) ^ 3 := by
    calc q * (10 ^ 4 * ((q + 1) ^ 2 + M + 2)) ≤ (M + 2) * (10 ^ 4 * (2 * (M + 2) ^ 2)) :=
          Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (by omega))
      _ = 2 * 10 ^ 4 * (M + 2) ^ 3 := by ring
  have c2 : loopModK * (q + 1) * (W + q + 4) ≤ 4 * 10 ^ 5 * (M + 2) ^ 4 := by
    calc loopModK * (q + 1) * (W + q + 4) ≤ 1000 * (M + 2) * (400 * (M + 2) ^ 3) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      _ = 4 * 10 ^ 5 * (M + 2) ^ 4 := by ring
  omega

end GI.Impl
