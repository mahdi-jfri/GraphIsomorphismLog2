module

public import Workspace.Impl.AggItemCiCfgB

@[expose] public section

/-!
# The configuration query: the spec of the overcoset program

`itcq_ouF_spec`: `itcqOuF` on `[σ₀, S, w]` returns `itciRes (itciOV (itcqOs X σ₀ S)) w` in cost
`itcqOuC M`, for `M` at least `q + 1` and the input weight.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm Finset
open GI.Cited (Val encPerm gens encGroup encPerms)

variable {q : ℕ}

theorem itcq_ouC_arith {M q s B W C : ℕ} (hs : s < M) (hq : q + 1 ≤ M) (hB : B ≤ 2 * M + 14)
    (hW : W = 1000 * (M + 1) ^ 3)
    (hC : C ≤ 171 * (W + 1) + (s * (itParC q + 200 * (q + 1) ^ 2) +
      loopModK * (s + 1) * (B + 2 * s + 3)) + itParC q + itcqSchC M + permK * (q + 1) ^ 3) :
    C ≤ itcqOuC M := by
  unfold itcqOuC
  unfold itParC itcqSchC permK loopModK at hC
  subst hW
  obtain ⟨T, hT⟩ : ∃ T, T = M + 1 := ⟨_, rfl⟩
  have hq2 : (q + 1) ^ 2 ≤ T ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hq3 : (q + 1) ^ 3 ≤ T ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hq4 : (q + 1) ^ 4 ≤ T ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have hM6 : M ^ 6 ≤ T ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have h1 : s * (10 ^ 7 * (q + 1) ^ 4 + 200 * (q + 1) ^ 2) ≤ T * (10 ^ 7 * T ^ 4 + 200 * T ^ 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e1 : T * (10 ^ 7 * T ^ 4 + 200 * T ^ 2) = 10 ^ 7 * T ^ 5 + 200 * T ^ 3 := by ring
  have h2 : 1000 * (s + 1) * (B + 2 * s + 3) ≤ 1000 * T * (17 * T) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e2 : 1000 * T * (17 * T) = 17000 * T ^ 2 := by ring
  rw [← hT] at hC ⊢
  have t1 : T ^ 2 ≤ T ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have t2 : T ^ 3 ≤ T ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have t3 : T ^ 4 ≤ T ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have t4 : T ^ 5 ≤ T ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have t0 : 1 ≤ T ^ 2 := Nat.one_le_pow _ _ (by omega)
  generalize T ^ 2 = A2 at *
  generalize T ^ 3 = A3 at *
  generalize T ^ 4 = A4 at *
  generalize T ^ 5 = A5 at *
  generalize T ^ 6 = A6 at *
  generalize (q + 1) ^ 2 = Q2 at *
  generalize (q + 1) ^ 3 = Q3 at *
  generalize (q + 1) ^ 4 = Q4 at *
  generalize M ^ 6 = M6 at *
  omega

section Prog

variable {P : Program}

set_option maxHeartbeats 2000000 in
/-- **The overcoset program.** -/
theorem itcq_ouF_spec {f fnd fo par cmp sch rng mp sb : ℕ}
    (hf : P.funs[f]? = some (itcqOuF fnd par cmp sch))
    (hfnd : P.HasAt fnd (findFuns fnd fo)) (hfo : P.funs[fo]? = some (itcqOdT par))
    (hpar : ∀ σ : Perm (Fin q), FunDet P par (encPerm σ) (.nat (itpNInv σ % 2)) (itParC q))
    (hcmp : P.HasAt cmp (composeFuns cmp))
    (hsch : P.funs[sch]? = some (itSchF rng mp)) (hrng : P.HasAt rng (rangeFuns rng))
    (hmp : P.HasAt mp (mapFuns mp sb)) (hsb : P.funs[sb]? = some (itSchB par cmp))
    (X : PairCfg q) (σ₀ : Perm (Fin q)) (S : List (Perm (Fin q))) (w : Val) {M : ℕ}
    (hq : q + 1 ≤ M) (hM : (Val.list [encPerm σ₀, .list (S.map encPerm), w]).wt ≤ M) :
    FunDet P f (.list [encPerm σ₀, .list (S.map encPerm), w])
      (itciRes (itciOV (itcqOs X σ₀ S)) w) (itcqOuC M) := by
  have hσw : (encPerm σ₀).wt < (Val.list [encPerm σ₀, .list (S.map encPerm), w]).wt :=
    wt_le_wt_list (List.mem_cons_self ..)
  have hSw : (Val.list (S.map encPerm)).wt < (Val.list [encPerm σ₀, .list (S.map encPerm), w]).wt :=
    wt_le_wt_list (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hww : w.wt < (Val.list [encPerm σ₀, .list (S.map encPerm), w]).wt :=
    wt_le_wt_list (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hSl : S.length < M := by
    have := length_lt_wt_list (S.map encPerm); rw [List.length_map] at this; omega
  have hq2 : (q + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hq 2
  have hM2 : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) _
  have hM3 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hMT : M ^ 3 ≤ (M + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hMT2 : M ^ 2 ≤ (M + 1) ^ 3 := le_trans hM3 hMT
  obtain ⟨W, hW⟩ : ∃ W, W = 1000 * (M + 1) ^ 3 := ⟨_, rfl⟩
  have hMW : M ≤ W := by
    have : M ≤ (M + 1) ^ 3 := le_trans hM2 hMT2
    omega
  have hσ := wt_encPerm_le σ₀
  -- the result weighs at most `W`
  have hEG : (itcqEG S).length ≤ 2 * M := by
    unfold itcqEG
    split
    · simp only [List.length_map, List.length_range]; omega
    · omega
  have hout : (itciRes (itciOV (itcqOs X σ₀ S)) w).wt ≤ W := by
    have hEm : (itcqEG S).length * (9 * (q + 1) ^ 2) ≤ 2 * M * (9 * M ^ 2) :=
      Nat.mul_le_mul hEG (by omega)
    have e3 : 2 * M * (9 * M ^ 2) = 18 * M ^ 3 := by ring
    have h1 : ∀ σ : Perm (Fin q), (itciRes (.list [lcOv σ (itcqEG S)]) w).wt ≤ W := fun σ => by
      have := itcq_res1_wt σ (itcqEG S) w
      omega
    have h0 : (itciRes (.list []) w).wt ≤ W := by
      have h6 := wt_list2_le (.nat 0) (.list [.list [], .list [], w])
      have h7 := wt_list3_le (.list []) (.list []) w
      have := wt_nat_le 0
      simp only [wt_list_nil] at h7
      unfold itciRes; omega
    by_cases hp : sign σ₀ = 1
    · rw [itcqOs_even hp]; exact h1 σ₀
    · cases ht : itcqOdd S with
      | some t => rw [itcqOs_odd_some hp ht]; exact h1 _
      | none => rw [itcqOs_odd_none hp ht]; exact h0
  -- the first odd entry
  obtain ⟨i, hi⟩ : ∃ i, S.findIdx (fun s => decide (sign s ≠ 1)) = i := ⟨_, rfl⟩
  have hil : i ≤ S.length := by rw [← hi]; exact List.findIdx_le_length
  have hfin := wt_list2_le (.list []) (.list (S.map encPerm))
  simp only [wt_list_nil] at hfin
  have hfd : FunDet P fnd (.list [.list [], .list (S.map encPerm)]) (.nat i)
      (S.length * (itParC q + 200 * (q + 1) ^ 2) + loopModK * (S.length + 1) *
        ((Val.list [.list [], .list (S.map encPerm)]).wt + 2 * S.length + 3)) := by
    refine (find_spec hfnd (c := .list []) (xs := S.map encPerm) (q := itcqOq q)
      (B := fun _ => itParC q + 200 * (q + 1) ^ 2) (fun x hx => by
        obtain ⟨s, -, rfl⟩ := List.mem_map.1 hx
        exact itcq_odT_spec hfo hpar s)).mono fun v c ⟨hv, hc⟩ => ⟨?_, ?_⟩
    · rw [hv, itcq_findIdx_map, hi]
    · simp only [List.map_const', List.sum_replicate, List.length_map, smul_eq_mul] at hc
      exact hc
  set v := Val.list [encPerm σ₀, .list (S.map encPerm), w] with hvdef
  have hA : ∀ (rest : List Val) (j : ℕ) (u : Val), [encPerm σ₀, .list (S.map encPerm), w][j]? =
      some u → u.wt ≤ W → j + 2 ≤ W → StDC P (v :: rest) (arg j) u 3 0 W :=
    fun rest j u h hu hj => StDC.arg h (by show v.wt ≤ W; omega) hj hu
  have h4 : 4 ≤ W := by have := wt_list_eq [encPerm σ₀, .list (S.map encPerm), w]; omega
  have d1 := StDC.call (StDC.mk2 (StDC.nil (env := [v]) (P := P) h4) (hA [] 1 _ rfl (by omega)
    (by omega)) (by omega) h4) hfd (by have := wt_nat_le i; omega)
  have hpr := wt_nat_le (itpNInv σ₀ % 2)
  have hpr2 : itpNInv σ₀ % 2 < 2 := Nat.mod_lt _ (by omega)
  have d2 := StDC.call (hA [.nat i] 0 _ rfl (by omega) (by omega)) (hpar σ₀) (by omega)
  -- the environment after the two lets
  have V1 := StDC.var' (P := P) (env := [v, .nat i, .nat (itpNInv σ₀ % 2)]) (i := 1) rfl
    (W := W) (by have := wt_nat_le i; omega)
  have V2 := StDC.var' (P := P) (env := [v, .nat i, .nat (itpNInv σ₀ % 2)]) (i := 2) rfl
    (W := W) (by omega)
  have L := StDC.length (hA [.nat i, .nat (itpNInv σ₀ % 2)] 1 _ rfl (by omega) (by omega))
    (by simp only [List.length_map]; omega)
  simp only [List.length_map] at L
  have C := StDC.arith V1 L (op := .lt) (z := if i < S.length then 1 else 0) rfl
    (itcq_01_wt (by omega) _)
  have body : StDC P [v] (itcqOuF fnd par cmp sch) (itciRes (itciOV (itcqOs X σ₀ S)) w) 171
      ((S.length * (itParC q + 200 * (q + 1) ^ 2) + loopModK * (S.length + 1) *
        ((Val.list [.list [], .list (S.map encPerm)]).wt + 2 * S.length + 3)) + itParC q +
        (itcqSchC M + permK * (q + 1) ^ 3)) W := by
    unfold itcqOuF
    refine (StDC.letE d1 (StDC.letE d2 (StDC.ite (nt := 92)
      (Et := itcqSchC M + permK * (q + 1) ^ 3) (ne := 58) (Ee := 0) C (fun hx => ?_)
      (fun hx => ?_) hout) hout) hout).mono (by omega) (by omega)
    · -- an odd entry exists
      have hlt : i < S.length := by
        by_contra h; simp [h] at hx
      have hid := (itcq_find_idx S).1 (by rw [hi]; exact hlt)
      simp only [hi] at hid
      have hti := wt_encPerm_le (S[i]'hlt)
      have G := StDC.get (hA [.nat i, .nat (itpNInv σ₀ % 2)] 1 _ rfl (by omega) (by omega)) V1
        (v := encPerm (S[i]'hlt)) (by simp [hlt]) (by omega)
      have hEw := it_perms_wt (q := q) (l := (List.range (2 * S.length)).map (itSchE (S[i]'hlt) S))
        (m := 2 * M) (by simp only [List.length_map, List.length_range]; omega)
      have hEm : 2 * M * (9 * (q + 1) ^ 2) ≤ 2 * M * (9 * M ^ 2) :=
        Nat.mul_le_mul_left _ (by omega)
      have e3 : 2 * M * (9 * M ^ 2) = 18 * M ^ 3 := by ring
      have hGS := wt_list2_le (encPerm (S[i]'hlt)) (.list (S.map encPerm))
      have SC := StDC.call (StDC.mk2 G (hA [.nat i, .nat (itpNInv σ₀ % 2)] 1 _ rfl (by omega)
        (by omega)) (by omega) h4)
        (itcq_sch_spec hsch hrng hmp hsb hpar hcmp (S[i]'hlt) hq (by omega)) (by omega)
      refine (StDC.letE SC (nb := 79) (Eb := permK * (q + 1) ^ 3) ?_ hout).mono
        (by omega) (by omega)
      -- the environment with the Schreier list
      have V2' := StDC.var' (P := P) (env := [v] ++ [.nat i] ++ [.nat (itpNInv σ₀ % 2)] ++
        [.list (((List.range (2 * S.length)).map (itSchE (S[i]'hlt) S)).map encPerm)]) (i := 2) rfl
        (W := W) (by omega)
      have V3 := StDC.var' (P := P) (env := [v] ++ [.nat i] ++ [.nat (itpNInv σ₀ % 2)] ++
        [.list (((List.range (2 * S.length)).map (itSchE (S[i]'hlt) S)).map encPerm)]) (i := 3) rfl
        (W := W) (by omega)
      have hEG' := itcqEG_some hid
      by_cases hp : sign σ₀ = 1
      · have hpz : itpNInv σ₀ % 2 = 0 := by rw [itcq_par_val]; simp [hp]
        refine (StDC.ite (nt := 43) (Et := permK * (q + 1) ^ 3) (ne := 34) (Ee := 0) V2'
          (fun h => absurd hpz h) (fun _ => ?_) hout).mono (by omega) (by omega)
        rw [itcqOs_even hp, hEG']
        rw [itcqOs_even hp, hEG'] at hout
        exact (itcq_res1_st (hA _ 0 _ rfl (by omega) (by omega)) V3 (by show v.wt ≤ W; omega) hout).mono
          (by omega) (by omega)
      · have hpo : itpNInv σ₀ % 2 = 1 := by rw [itcq_par_val]; simp [hp]
        refine (StDC.ite (nt := 43) (Et := permK * (q + 1) ^ 3) (ne := 34) (Ee := 0) V2'
          (fun _ => ?_) (fun h => absurd h (by omega)) hout).mono (by omega) (by omega)
        rw [itcqOs_odd_some hp hid, hEG']
        rw [itcqOs_odd_some hp hid, hEG'] at hout
        have hst := wt_encPerm_le (σ₀ * S[i]'hlt)
        have G' := StDC.get (hA _ 1 _ rfl (by omega) (by omega))
          (StDC.var' (P := P) (env := [v] ++ [.nat i] ++ [.nat (itpNInv σ₀ % 2)] ++
          [.list (((List.range (2 * S.length)).map (itSchE (S[i]'hlt) S)).map encPerm)])
          (i := 1) rfl (W := W) (v := .nat i) (by have := wt_nat_le i; omega))
          (v := encPerm (S[i]'hlt)) (by simp [hlt]) (by omega)
        have hσt := wt_list2_le (encPerm σ₀) (encPerm (S[i]'hlt))
        have CM := StDC.call (StDC.mk2 (hA _ 0 _ rfl (by omega) (by omega)) G' (by omega) h4)
          (compose_spec hcmp σ₀ (S[i]'hlt)) (by omega)
        exact (itcq_res1_st CM V3 (by show v.wt ≤ W; omega) hout).mono (by omega) (by omega)
    · -- no odd entry
      have hge : ¬ i < S.length := by
        intro h; simp [h] at hx
      have hid := (itcq_find_idx S).2 (by rw [hi]; exact hge)
      by_cases hp : sign σ₀ = 1
      · have hpz : itpNInv σ₀ % 2 = 0 := by rw [itcq_par_val]; simp [hp]
        refine StDC.ite (nt := 20) (Et := 0) (ne := 36) (Ee := 0) V2
          (fun h => absurd hpz h) (fun _ => ?_) hout
        rw [itcqOs_even hp, itcqEG_none hid]
        rw [itcqOs_even hp, itcqEG_none hid] at hout
        exact (itcq_res1_st (hA _ 0 _ rfl (by omega) (by omega)) (hA _ 1 _ rfl (by omega)
          (by omega)) (by show v.wt ≤ W; omega) hout).mono (by omega) (by omega)
      · have hpo : itpNInv σ₀ % 2 = 1 := by rw [itcq_par_val]; simp [hp]
        refine StDC.ite (nt := 20) (Et := 0) (ne := 36) (Ee := 0) V2
          (fun _ => ?_) (fun h => absurd h (by omega)) hout
        rw [itcqOs_odd_none hp hid]
        rw [itcqOs_odd_none hp hid] at hout
        exact itcq_res0_st (by show v.wt ≤ W; omega) hout

  refine StDC.funDet hf body ?_
  clear body d1 d2 V1 V2 L C hA hfd
  have hfin' : (Val.list [.list [], .list (S.map encPerm)]).wt ≤ 2 * M + 14 := by omega
  refine itcq_ouC_arith (B := (Val.list [.list [], .list (S.map encPerm)]).wt) hSl hq hfin' hW ?_
  omega

end Prog

end GI.Impl
