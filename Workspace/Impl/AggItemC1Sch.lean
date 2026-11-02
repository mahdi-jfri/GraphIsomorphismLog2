import Workspace.Impl.AggItemC1G
import Workspace.Impl.AggItemC1Par

/-!
# Case 1 as a program: the Schreier generators of the even part

Given a list `S` of permutations and an odd involution `t`, the list `itpSch t S` generates the
even part of the group of `S` (`itp_schreier`). The program `itSchF` computes a list with the same
members: entry `j < 2 |S|` is built from `s = S[j / 2]` and the parity of `s`, and is `s` or
`t s t` for even `s`, and `s t` or `t s` for odd `s`, as `j` is even or odd (`it_sch_spec`).
The parity and composition are calls, given by their specs.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens)

variable {q : ℕ}

/-- Entry `j` of the program's Schreier list. -/
def itSchE (t : Perm (Fin q)) (S : List (Perm (Fin q))) (j : ℕ) : Perm (Fin q) :=
  if h : j / 2 < S.length then
    if sign S[j / 2] = 1 then (if j % 2 = 0 then S[j / 2] else t * S[j / 2] * t)
    else (if j % 2 = 0 then S[j / 2] * t else t * S[j / 2])
  else 1

theorem itSchE_mem (t : Perm (Fin q)) (S : List (Perm (Fin q))) (g : Perm (Fin q)) :
    g ∈ (List.range (2 * S.length)).map (itSchE t S) ↔ g ∈ itpSch t S := by
  rw [itp_mem_sch, List.mem_map]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hj' : j / 2 < S.length := by have := List.mem_range.1 hj; omega
    refine ⟨S[j / 2], List.getElem_mem hj', ?_⟩
    rw [itSchE, dif_pos hj']
    by_cases hs : sign S[j / 2] = 1
    · left; refine ⟨hs, ?_⟩; rw [if_pos hs]; split_ifs <;> simp
    · right; refine ⟨hs, ?_⟩; rw [if_neg hs]; split_ifs <;> simp
  · rintro ⟨s, hs, h⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
    have e0 : (2 * i) / 2 = i := by omega
    have e1 : (2 * i + 1) / 2 = i := by omega
    have m0 : 2 * i ∈ List.range (2 * S.length) := List.mem_range.2 (by omega)
    have m1 : 2 * i + 1 ∈ List.range (2 * S.length) := List.mem_range.2 (by omega)
    have v0 : itSchE t S (2 * i) = if sign S[i] = 1 then S[i] else S[i] * t := by
      rw [itSchE, dif_pos (by omega)]; simp only [e0]; split_ifs <;> simp_all
    have v1 : itSchE t S (2 * i + 1) = if sign S[i] = 1 then t * S[i] * t else t * S[i] := by
      rw [itSchE, dif_pos (by omega)]; simp only [e1]; split_ifs <;> first | rfl | omega
    rcases h with ⟨h1, rfl | rfl⟩ | ⟨h1, rfl | rfl⟩
    · exact ⟨_, m0, by rw [v0, if_pos h1]⟩
    · exact ⟨_, m1, by rw [v1, if_pos h1]⟩
    · exact ⟨_, m0, by rw [v0, if_neg h1]⟩
    · exact ⟨_, m1, by rw [v1, if_neg h1]⟩

/-- **The program's Schreier list generates the even part.** -/
theorem itSchE_gens (t : Perm (Fin q)) (S : List (Perm (Fin q))) :
    gens ((List.range (2 * S.length)).map (itSchE t S)) = gens (itpSch t S) := by
  unfold gens
  congr 1
  ext g
  exact itSchE_mem t S g

/-! ### The body -/

/-- On `[[T, S], j]`: entry `j` of the Schreier list. -/
def itSchB (par cmp : ℕ) : Expr :=
  let T := Expr.get (arg 0) (.nat 0)
  let S := Expr.get (arg 0) (.nat 1)
  let s := Expr.get S (.arith .div (arg 1) (.nat 2))
  .ite (.call par s)
    (.ite (.arith .mod (arg 1) (.nat 2)) (.call cmp (mk2 T s)) (.call cmp (mk2 s T)))
    (.ite (.arith .mod (arg 1) (.nat 2)) (.call cmp (mk2 (.call cmp (mk2 T s)) T)) s)

theorem it_parity_ne {σ : Perm (Fin q)} : itpNInv σ % 2 ≠ 0 ↔ sign σ ≠ 1 := by
  rw [ne_eq, ne_eq, itp_sign_one_iff, Nat.even_iff]

set_option maxHeartbeats 4000000 in
theorem it_schB_spec {P : Program} {f par cmp : ℕ} (hf : P.funs[f]? = some (itSchB par cmp))
    (hpar : ∀ σ : Perm (Fin q), FunDet P par (encPerm σ) (.nat (itpNInv σ % 2)) (itParC q))
    (hcmp : P.HasAt cmp (composeFuns cmp)) (t : Perm (Fin q)) {S : List (Perm (Fin q))}
    (hS : S.length ≤ (q + 1) ^ 2) {j : ℕ} (hj : j < 2 * S.length) :
    FunDet P f (.list [.list [encPerm t, .list (S.map encPerm)], .nat j]) (encPerm (itSchE t S j))
      (2 * 10 ^ 7 * (q + 1) ^ 4) := by
  have hq1 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqa : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hq3 : (q + 1) ^ 2 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hq4 : (q + 1) ^ 3 ≤ (q + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hj2 : j / 2 < S.length := by omega
  set W := 100 * (q + 1) ^ 4
  set s := S[j / 2]
  have hSw : (Val.list (S.map encPerm)).wt ≤ (q + 1) ^ 2 * (9 * (q + 1) ^ 2) + 4 := it_perms_wt hS
  have e4 : (q + 1) ^ 2 * (9 * (q + 1) ^ 2) = 9 * (q + 1) ^ 4 := by ring
  have hT := wt_encPerm_le t
  have hs := wt_encPerm_le s
  have hst := wt_encPerm_le (s * t)
  have hts := wt_encPerm_le (t * s)
  have htst := wt_encPerm_le (t * s * t)
  have hE := wt_encPerm_le (itSchE t S j)
  have hjw := wt_nat_le j
  have hjq : j + 2 ≤ 3 * (q + 1) ^ 2 := by omega
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
  have hpc : permK * (q + 1) ^ 3 ≤ 10 ^ 5 * (q + 1) ^ 4 := by simp only [permK]; omega
  have h2 : ∀ a b : Val, a.wt ≤ 4 * (q + 1) ^ 2 → b.wt ≤ 4 * (q + 1) ^ 2 →
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
          exact StDC.call (StDC.mk2 gT gs (h2 _ _ hT hs) (by omega)) (compose_spec hcmp t s)
            (by omega))
        (fun hm => by
          have hv : itSchE t S j = s * t := by
            rw [itSchE, dif_pos hj2, if_neg hp']; simp only [GI.Machine.BinOp.eval] at hm
            rw [if_pos hm]
          rw [hv]
          exact StDC.call (StDC.mk2 gs gT (h2 _ _ hs hT) (by omega)) (compose_spec hcmp s t)
            (by omega)) (by omega))
    (fun hp => by
      have hp' : sign s = 1 := by
        by_contra h; exact it_parity_ne.2 h hp
      exact StDC.ite gM
        (fun hm => by
          have hv : itSchE t S j = t * s * t := by
            rw [itSchE, dif_pos hj2, if_pos hp']; simp only [GI.Machine.BinOp.eval] at hm
            rw [if_neg (by simpa using hm)]
          rw [hv]
          have c1 := StDC.call (StDC.mk2 gT gs (h2 _ _ hT hs) (by omega)) (compose_spec hcmp t s)
            (by omega)
          exact StDC.call (StDC.mk2 c1 gT (h2 _ _ hts hT) (by omega))
            (compose_spec hcmp (t * s) t) (by omega))
        (fun hm => by
          have hv : itSchE t S j = s := by
            rw [itSchE, dif_pos hj2, if_pos hp']; simp only [GI.Machine.BinOp.eval] at hm
            rw [if_pos hm]
          rw [hv]; exact gs) (by omega)) (by omega)
  refine StDC.funDet hf outer ?_
  have : 100 * (W + 1) ≤ 2 * 10 ^ 4 * (q + 1) ^ 4 := by omega
  unfold itParC at *
  omega

/-! ### The whole list -/

/-- On `[T, S]`: the Schreier list. -/
def itSchF (rng mp : ℕ) : Expr :=
  .letE (.call rng (.arith .mul (.nat 2) (.length (.get (.var 0) (.nat 1)))))
    (.call mp (mk2 (.var 0) (.var 1)))

/-- The cost bound of `itSchF`. -/
def itSchC (q : ℕ) : ℕ := 10 ^ 9 * (q + 1) ^ 6

/-- The Schreier entries as values. -/
def itSchV (t : Perm (Fin q)) (S : List (Perm (Fin q))) : Val → Val
  | .nat j => encPerm (itSchE t S j)
  | _ => .nat 0

set_option maxHeartbeats 4000000 in
/-- **The Schreier list as a program.** -/
theorem it_sch_spec {P : Program} {f rng mp sb par cmp : ℕ} (hf : P.funs[f]? = some (itSchF rng mp))
    (hrng : P.HasAt rng (rangeFuns rng)) (hmp : P.HasAt mp (mapFuns mp sb))
    (hsb : P.funs[sb]? = some (itSchB par cmp))
    (hpar : ∀ σ : Perm (Fin q), FunDet P par (encPerm σ) (.nat (itpNInv σ % 2)) (itParC q))
    (hcmp : P.HasAt cmp (composeFuns cmp)) (t : Perm (Fin q)) {S : List (Perm (Fin q))}
    (hS : S.length ≤ (q + 1) ^ 2) :
    FunDet P f (.list [encPerm t, .list (S.map encPerm)])
      (.list (((List.range (2 * S.length)).map (itSchE t S)).map encPerm)) (itSchC q) := by
  have hq1 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqa : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hq3 : (q + 1) ^ 2 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hq4 : (q + 1) ^ 3 ≤ (q + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hq5 : (q + 1) ^ 4 ≤ (q + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have hq6 : (q + 1) ^ 5 ≤ (q + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  set m := S.length with hm
  have hm2 : 2 * m + 1 ≤ 3 * (q + 1) ^ 2 := by omega
  set W := 200 * (q + 1) ^ 4
  have hSw : (Val.list (S.map encPerm)).wt ≤ (q + 1) ^ 2 * (9 * (q + 1) ^ 2) + 4 := it_perms_wt hS
  have e4 : (q + 1) ^ 2 * (9 * (q + 1) ^ 2) = 9 * (q + 1) ^ 4 := by ring
  have hT := wt_encPerm_le t
  have hc := wt_list2_le (encPerm t) (.list (S.map encPerm))
  set O := ((List.range (2 * m)).map (itSchE t S)).map encPerm
  have hOw : (Val.list O).wt ≤ 3 * (q + 1) ^ 2 * (9 * (q + 1) ^ 2) + 4 :=
    it_perms_wt (by simp only [List.length_map, List.length_range]; omega)
  have e5 : 3 * (q + 1) ^ 2 * (9 * (q + 1) ^ 2) = 27 * (q + 1) ^ 4 := by ring
  have hR := it_range_wt (q := 2 * m)
  have hR2 : 5 * (2 * m + 1) ^ 2 ≤ 45 * (q + 1) ^ 4 := by
    have : (2 * m + 1) ^ 2 ≤ (3 * (q + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left hm2 2
    have e : (3 * (q + 1) ^ 2) ^ 2 = 9 * (q + 1) ^ 4 := by ring
    omega
  have hM : FunDet P mp (.list [.list [encPerm t, .list (S.map encPerm)],
      natList (List.range (2 * m))]) (.list O)
      ((2 * m) * (2 * 10 ^ 7 * (q + 1) ^ 4) + mapK * (2 * m + 1) * (300 * (q + 1) ^ 4)) := by
    have h := map_det hmp (c := .list [encPerm t, .list (S.map encPerm)])
      (xs := (List.range (2 * m)).map Val.nat) (F := itSchV t S) (B := 2 * 10 ^ 7 * (q + 1) ^ 4)
      (fun v hv => by
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hv
        exact it_schB_spec hsb hpar hcmp t hS (List.mem_range.1 hj))
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
  have d2 := StDC.call (StDC.mk2 u0 u1 (by omega) (by omega)) hM (by omega)
  refine StDC.funDet hf (StDC.letE d1 d2 (by omega)) ?_
  have c1 : 2 * m * (2 * 10 ^ 7 * (q + 1) ^ 4) ≤ 6 * 10 ^ 7 * (q + 1) ^ 6 := by
    calc 2 * m * (2 * 10 ^ 7 * (q + 1) ^ 4) ≤ 3 * (q + 1) ^ 2 * (2 * 10 ^ 7 * (q + 1) ^ 4) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 6 * 10 ^ 7 * (q + 1) ^ 6 := by ring
  have c2 : mapK * (2 * m + 1) * (300 * (q + 1) ^ 4) ≤ 9 * 10 ^ 5 * (q + 1) ^ 6 := by
    calc mapK * (2 * m + 1) * (300 * (q + 1) ^ 4) ≤ 1000 * (3 * (q + 1) ^ 2) * (300 * (q + 1) ^ 4) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hm2)
      _ = 9 * 10 ^ 5 * (q + 1) ^ 6 := by ring
  have c3 : 10000 * (2 * m + 1) ^ 3 ≤ 27 * 10 ^ 4 * (q + 1) ^ 6 := by
    have : (2 * m + 1) ^ 3 ≤ (3 * (q + 1) ^ 2) ^ 3 := Nat.pow_le_pow_left hm2 3
    have e : (3 * (q + 1) ^ 2) ^ 3 = 27 * (q + 1) ^ 6 := by ring
    omega
  have c4 : 100 * (W + 1) ≤ 10 ^ 5 * (q + 1) ^ 6 := by omega
  unfold itSchC
  omega

end GI.Impl
