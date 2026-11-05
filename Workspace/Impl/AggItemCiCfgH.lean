module

public import Workspace.Impl.AggItemCiCfgY

@[expose] public section

/-!
# The configuration query: the Schreier list for long generator lists

Case 1's Schreier program `itSchF` (entry `j` of the list: `itSchE t S j`, built by `itSchB` from
`s = S[j / 2]`, its parity and `t`) is used here unchanged. Its spec `it_sch_spec` assumes
`|S| ≤ (q + 1)²`. In the configuration query `S` holds the lifted generators of the answer and
the transpositions outside the fiber, so it can be longer. `itcq_schB_spec` and `itcq_sch_spec`
are the same specs for `|S| ≤ M²` with `q + 1 ≤ M`, at cost `itcqSchC M = 10⁹ M⁶`.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens)

variable {q : ℕ}

set_option maxHeartbeats 4000000 in
/-- **One Schreier entry** for `|S| ≤ M²`. -/
theorem itcq_schB_spec {P : Program} {f par cmp : ℕ} (hf : P.funs[f]? = some (itSchB par cmp))
    (hpar : ∀ σ : Perm (Fin q), FunDet P par (encPerm σ) (.nat (itpNInv σ % 2)) (itParC q))
    (hcmp : P.HasAt cmp (composeFuns cmp)) (t : Perm (Fin q)) {S : List (Perm (Fin q))}
    {M : ℕ} (hM : q + 1 ≤ M) (hS : S.length ≤ M ^ 2) {j : ℕ} (hj : j < 2 * S.length) :
    FunDet P f (.list [.list [encPerm t, .list (S.map encPerm)], .nat j]) (encPerm (itSchE t S j))
      (2 * 10 ^ 7 * M ^ 4) := by
  have hq2 : (q + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hM 2
  have hq3' : (q + 1) ^ 3 ≤ M ^ 3 := Nat.pow_le_pow_left hM 3
  have hq4' : (q + 1) ^ 4 ≤ M ^ 4 := Nat.pow_le_pow_left hM 4
  have hq1 : 1 ≤ M ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqa : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) _
  have hq3 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hq4 : M ^ 3 ≤ M ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hj2 : j / 2 < S.length := by omega
  set W := 100 * M ^ 4
  set s := S[j / 2]
  have hSw0 : (Val.list (S.map encPerm)).wt ≤ M ^ 2 * (9 * (q + 1) ^ 2) + 4 := it_perms_wt hS
  have hSw1 : M ^ 2 * (9 * (q + 1) ^ 2) ≤ M ^ 2 * (9 * M ^ 2) :=
    Nat.mul_le_mul_left _ (by omega)
  have e4 : M ^ 2 * (9 * M ^ 2) = 9 * M ^ 4 := by ring
  have hT := wt_encPerm_le t
  have hs := wt_encPerm_le s
  have hst := wt_encPerm_le (s * t)
  have hts := wt_encPerm_le (t * s)
  have htst := wt_encPerm_le (t * s * t)
  have hE := wt_encPerm_le (itSchE t S j)
  have hjw := wt_nat_le j
  have hjq : j + 2 ≤ 3 * M ^ 2 := by omega
  have hc := wt_list2_le (encPerm t) (.list (S.map encPerm))
  have hin := wt_list2_le (.list [encPerm t, .list (S.map encPerm)]) (.nat j)
  set vs : List Val := [.list [encPerm t, .list (S.map encPerm)], .nat j]
  have g0 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 0) rfl (W := W) (by omega) (by omega)
    (by omega)
  have gJ := StDC.arg (P := P) (rest := []) (vs := vs) (j := 1) rfl (W := W) (by omega) (by omega)
    (by omega)
  have gT := StDC.get g0 (StDC.nat 0 (by omega)) (v := encPerm t) rfl (by omega)
  have gS := StDC.get g0 (StDC.nat 1 (by omega)) (v := .list (S.map encPerm)) rfl (by omega)
  have gD := StDC.arith' (op := .div) gJ (StDC.nat 2 (by omega)) rfl (by
    simp only [GI.Machine.BinOp.eval]; have := wt_nat_le (j / 2); omega)
  have gM := StDC.arith' (op := .mod) gJ (StDC.nat 2 (by omega)) rfl (by
    simp only [GI.Machine.BinOp.eval]; have := wt_nat_le (j % 2); omega)
  have gs := StDC.get gS gD (v := encPerm s) (by simp [s, hj2]) (by omega)
  have cP := StDC.call gs (hpar s) (by have := wt_nat_le (itpNInv s % 2); omega)
  have hpc : permK * (q + 1) ^ 3 ≤ 10 ^ 5 * M ^ 4 := by simp only [permK]; omega
  have h2 : ∀ a b : Val, a.wt ≤ 4 * M ^ 2 → b.wt ≤ 4 * M ^ 2 →
      (Val.list [a, b]).wt ≤ W := fun a b ha hb => by
    have := wt_list2_le a b; omega
  have outer := StDC.ite (v := encPerm (itSchE t S j)) cP
    (fun hp => by
      have hp' : sign s ≠ 1 := it_parity_ne.1 hp
      exact StDC.ite gM
        (fun hm => by
          have hv : itSchE t S j = t * s := by
            rw [itSchE, dif_pos hj2, if_neg hp']; simp only [GI.Machine.BinOp.eval] at hm
            rw [if_neg (by simpa using hm)]
          rw [hv]
          exact StDC.call (StDC.mk2 gT gs (h2 _ _ (by omega) (by omega)) (by omega))
            (compose_spec hcmp t s) (by omega))
        (fun hm => by
          have hv : itSchE t S j = s * t := by
            rw [itSchE, dif_pos hj2, if_neg hp']; simp only [GI.Machine.BinOp.eval] at hm
            rw [if_pos hm]
          rw [hv]
          exact StDC.call (StDC.mk2 gs gT (h2 _ _ (by omega) (by omega)) (by omega))
            (compose_spec hcmp s t) (by omega)) (by omega))
    (fun hp => by
      have hp' : sign s = 1 := by
        by_contra h; exact it_parity_ne.2 h hp
      exact StDC.ite gM
        (fun hm => by
          have hv : itSchE t S j = t * s * t := by
            rw [itSchE, dif_pos hj2, if_pos hp']; simp only [GI.Machine.BinOp.eval] at hm
            rw [if_neg (by simpa using hm)]
          rw [hv]
          have c1 := StDC.call (StDC.mk2 gT gs (h2 _ _ (by omega) (by omega)) (by omega))
            (compose_spec hcmp t s) (by omega)
          exact StDC.call (StDC.mk2 c1 gT (h2 _ _ (by omega) (by omega)) (by omega))
            (compose_spec hcmp (t * s) t) (by omega))
        (fun hm => by
          have hv : itSchE t S j = s := by
            rw [itSchE, dif_pos hj2, if_pos hp']; simp only [GI.Machine.BinOp.eval] at hm
            rw [if_pos hm]
          rw [hv]; exact gs) (by omega)) (by omega)
  refine StDC.funDet hf outer ?_
  have : 100 * (W + 1) ≤ 2 * 10 ^ 4 * M ^ 4 := by omega
  have hpq : itParC q ≤ 10 ^ 7 * M ^ 4 := by unfold itParC; omega
  omega

/-- The cost bound of the Schreier list for `|S| ≤ M²`. -/
def itcqSchC (M : ℕ) : ℕ := 10 ^ 9 * M ^ 6

set_option maxHeartbeats 4000000 in
/-- **The Schreier list as a program**, for `|S| ≤ M²` and `q + 1 ≤ M`. -/
theorem itcq_sch_spec {P : Program} {f rng mp sb par cmp : ℕ}
    (hf : P.funs[f]? = some (itSchF rng mp))
    (hrng : P.HasAt rng (rangeFuns rng)) (hmp : P.HasAt mp (mapFuns mp sb))
    (hsb : P.funs[sb]? = some (itSchB par cmp))
    (hpar : ∀ σ : Perm (Fin q), FunDet P par (encPerm σ) (.nat (itpNInv σ % 2)) (itParC q))
    (hcmp : P.HasAt cmp (composeFuns cmp)) (t : Perm (Fin q)) {S : List (Perm (Fin q))}
    {M : ℕ} (hM : q + 1 ≤ M) (hS : S.length ≤ M ^ 2) :
    FunDet P f (.list [encPerm t, .list (S.map encPerm)])
      (.list (((List.range (2 * S.length)).map (itSchE t S)).map encPerm)) (itcqSchC M) := by
  have hq2 : (q + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hM 2
  have hq1 : 1 ≤ M ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqa : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) _
  have hq3 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hq4 : M ^ 3 ≤ M ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hq5 : M ^ 4 ≤ M ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have hq6 : M ^ 5 ≤ M ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  set m := S.length with hm
  have hm2 : 2 * m + 1 ≤ 3 * M ^ 2 := by omega
  set W := 200 * M ^ 4
  have hSw0 : (Val.list (S.map encPerm)).wt ≤ M ^ 2 * (9 * (q + 1) ^ 2) + 4 := it_perms_wt hS
  have hSw1 : M ^ 2 * (9 * (q + 1) ^ 2) ≤ M ^ 2 * (9 * M ^ 2) :=
    Nat.mul_le_mul_left _ (by omega)
  have e4 : M ^ 2 * (9 * M ^ 2) = 9 * M ^ 4 := by ring
  have hT := wt_encPerm_le t
  have hc := wt_list2_le (encPerm t) (.list (S.map encPerm))
  set O := ((List.range (2 * m)).map (itSchE t S)).map encPerm
  have hOw0 : (Val.list O).wt ≤ 3 * M ^ 2 * (9 * (q + 1) ^ 2) + 4 :=
    it_perms_wt (by simp only [List.length_map, List.length_range]; omega)
  have hOw1 : 3 * M ^ 2 * (9 * (q + 1) ^ 2) ≤ 3 * M ^ 2 * (9 * M ^ 2) :=
    Nat.mul_le_mul_left _ (by omega)
  have e5 : 3 * M ^ 2 * (9 * M ^ 2) = 27 * M ^ 4 := by ring
  have hR := it_range_wt (q := 2 * m)
  have hR2 : 5 * (2 * m + 1) ^ 2 ≤ 45 * M ^ 4 := by
    have : (2 * m + 1) ^ 2 ≤ (3 * M ^ 2) ^ 2 := Nat.pow_le_pow_left hm2 2
    have e : (3 * M ^ 2) ^ 2 = 9 * M ^ 4 := by ring
    omega
  have hM' : FunDet P mp (.list [.list [encPerm t, .list (S.map encPerm)],
      natList (List.range (2 * m))]) (.list O)
      ((2 * m) * (2 * 10 ^ 7 * M ^ 4) + mapK * (2 * m + 1) * (300 * M ^ 4)) := by
    have h := map_det hmp (c := .list [encPerm t, .list (S.map encPerm)])
      (xs := (List.range (2 * m)).map Val.nat) (F := itSchV t S) (B := 2 * 10 ^ 7 * M ^ 4)
      (fun v hv => by
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hv
        exact itcq_schB_spec hsb hpar hcmp t hM hS (List.mem_range.1 hj))
    have e : ((List.range (2 * m)).map Val.nat).map (itSchV t S) = O := by
      simp only [O, List.map_map]; rfl
    rw [e] at h
    refine h.mono ?_
    have h2 := wt_list2_le (.list [encPerm t, .list (S.map encPerm)]) (natList (List.range (2 * m)))
    simp only [List.length_map, List.length_range]
    refine Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_) _
    show (Val.list [.list [encPerm t, .list (S.map encPerm)], natList (List.range (2 * m))]).wt +
      (Val.list O).wt + 1 ≤ _
    omega
  have v0 : StDC P [.list [encPerm t, .list (S.map encPerm)]] (.var 0)
      (.list [encPerm t, .list (S.map encPerm)]) 1 0 W := StDC.var' rfl (by omega)
  have g1 := StDC.get v0 (StDC.nat 1 (by omega)) (v := .list (S.map encPerm)) rfl (by omega)
  have l1 := StDC.length g1 (by simp only [List.length_map]; have := wt_nat_le m; omega)
  simp only [List.length_map, ← hm] at l1
  have a1 := StDC.arith (op := .mul) (StDC.nat 2 (by omega)) l1 rfl (by
    simp only [GI.Machine.BinOp.eval]; have := wt_nat_le (2 * m); omega)
  have d1 := StDC.call a1 (st_range_det hrng (2 * m)) (by omega)
  set E1 : List Val := [.list [encPerm t, .list (S.map encPerm)], natList (List.range (2 * m))]
  have u0 : StDC P E1 (.var 0) (.list [encPerm t, .list (S.map encPerm)]) 1 0 W :=
    StDC.var' rfl (by omega)
  have u1 : StDC P E1 (.var 1) (natList (List.range (2 * m))) 1 0 W := StDC.var' rfl (by omega)
  have h2 := wt_list2_le (.list [encPerm t, .list (S.map encPerm)]) (natList (List.range (2 * m)))
  have d2 := StDC.call (StDC.mk2 u0 u1 (by omega) (by omega)) hM' (by omega)
  refine StDC.funDet hf (StDC.letE d1 d2 (by omega)) ?_
  have c1 : 2 * m * (2 * 10 ^ 7 * M ^ 4) ≤ 6 * 10 ^ 7 * M ^ 6 := by
    calc 2 * m * (2 * 10 ^ 7 * M ^ 4) ≤ 3 * M ^ 2 * (2 * 10 ^ 7 * M ^ 4) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 6 * 10 ^ 7 * M ^ 6 := by ring
  have c2 : mapK * (2 * m + 1) * (300 * M ^ 4) ≤ 9 * 10 ^ 5 * M ^ 6 := by
    calc mapK * (2 * m + 1) * (300 * M ^ 4) ≤ 1000 * (3 * M ^ 2) * (300 * M ^ 4) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hm2)
      _ = 9 * 10 ^ 5 * M ^ 6 := by ring
  have c3 : 10000 * (2 * m + 1) ^ 3 ≤ 27 * 10 ^ 4 * M ^ 6 := by
    have : (2 * m + 1) ^ 3 ≤ (3 * M ^ 2) ^ 3 := Nat.pow_le_pow_left hm2 3
    have e : (3 * M ^ 2) ^ 3 = 27 * M ^ 6 := by ring
    omega
  have c4 : 100 * (W + 1) ≤ 10 ^ 5 * M ^ 6 := by omega
  unfold itcqSchC
  omega

end GI.Impl
