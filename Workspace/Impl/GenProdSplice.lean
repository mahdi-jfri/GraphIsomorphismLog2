module

public import Workspace.Impl.GenProdNum

@[expose] public section

/-!
# The product refinement: splicing the hierarchy

The exposed hierarchy is `pre ++ top :: post`, with `top` at index `t = |pre|`. The product
refinement replaces `top` by the `r` coordinate intervals. `splice_spec` does this on values: on
`[L, t, M]` with `t < |L|` it returns `take t L ++ M ++ drop (t + 1) L`, by a loop over the
entries of `L` that appends `M` at step `t`.
-/

namespace GI.Impl

open GI.Lang
open GI.Cited (Val)

/-- The value after `i` steps of the splice loop. -/
def spliceAt (L M : List Val) (t i : ℕ) : List Val :=
  if i ≤ t then L.take i else L.take t ++ M ++ (L.drop (t + 1)).take (i - t - 1)

/-- The splice loop at base `b` (three functions), with the list append at `bapp`. On
`[L, t, M]`. -/
def spliceFuns (b bapp : ℕ) : List Expr :=
  loopFuns b (.length (.get (.var 0) (.nat 0))) .nil
    (.ite (.arith .eq (arg 1) (.get (arg 0) (.nat 1)))
      (.call bapp (mk2 (arg 2) (.get (arg 0) (.nat 2))))
      (.snoc (arg 2) (.get (.get (arg 0) (.nat 0)) (arg 1))))

theorem spliceAt_succ (L M : List Val) {t i : ℕ} (hi : i < L.length) :
    spliceAt L M t (i + 1) =
      if i = t then spliceAt L M t i ++ M else spliceAt L M t i ++ [L[i]] := by
  rcases lt_trichotomy i t with h | rfl | h
  · simp only [spliceAt, if_pos (show i + 1 ≤ t by omega), if_pos (show i ≤ t by omega),
      if_neg (show i ≠ t by omega)]
    rw [List.take_add_one, List.getElem?_eq_getElem hi]
    rfl
  · simp [spliceAt]
  · simp only [spliceAt, if_neg (show ¬ i + 1 ≤ t by omega), if_neg (show ¬ i ≤ t by omega),
      if_neg (show i ≠ t by omega)]
    rw [show i + 1 - t - 1 = (i - t - 1) + 1 by omega, List.take_add_one, List.append_assoc]
    rw [List.getElem?_drop, show t + 1 + (i - t - 1) = i by omega, List.getElem?_eq_getElem hi]
    simp

theorem spliceAt_length (L M : List Val) {t : ℕ} (ht : t < L.length) :
    spliceAt L M t L.length = L.take t ++ M ++ L.drop (t + 1) := by
  unfold spliceAt
  rw [if_neg (by omega), List.take_of_length_le (l := L.drop (t + 1)) (by simp; omega)]

theorem sum_wt_spliceAt_le (L M : List Val) (t i : ℕ) :
    ((spliceAt L M t i).map Val.wt).sum ≤ (L.map Val.wt).sum + (M.map Val.wt).sum := by
  have h1 : ((L.take t).map Val.wt).sum + ((L.drop t).map Val.wt).sum = (L.map Val.wt).sum := by
    rw [← List.sum_append, ← List.map_append, List.take_append_drop]
  have h2 : ((L.drop (t + 1)).map Val.wt).sum ≤ ((L.drop t).map Val.wt).sum := by
    rw [← List.drop_drop]
    exact ((List.drop_sublist _ _).map _).sum_le_sum (fun _ _ => Nat.zero_le _)
  unfold spliceAt
  split_ifs
  · have := ((List.take_sublist i L).map Val.wt).sum_le_sum (fun _ _ => Nat.zero_le _)
    omega
  · simp only [List.map_append, List.sum_append]
    have h3 := ((List.take_sublist (i - t - 1) (L.drop (t + 1))).map Val.wt).sum_le_sum
      (fun _ _ => Nat.zero_le _)
    have h4 := ((List.take_sublist t L).map Val.wt).sum_le_sum (fun _ _ => Nat.zero_le _)
    omega

theorem length_spliceAt_le (L M : List Val) (t i : ℕ) :
    (spliceAt L M t i).length ≤ L.length + M.length := by
  unfold spliceAt
  split_ifs <;> (simp; try omega)

theorem wt_spliceAt_le (L M : List Val) (t i : ℕ) :
    (Val.list (spliceAt L M t i)).wt ≤ 3 * ((Val.list L).wt + (Val.list M).wt) + 4 := by
  have h1 := wt_list_le (spliceAt L M t i)
  have h2 := sum_wt_spliceAt_le L M t i
  have h3 := length_spliceAt_le L M t i
  have h4 := sum_wt_lt_wt_list L
  have h5 := sum_wt_lt_wt_list M
  have h6 := length_lt_wt_list L
  have h7 := length_lt_wt_list M
  omega

/-- The constant of the splice. -/
def spliceK : ℕ := 10 ^ 6

set_option maxHeartbeats 2000000 in
/-- **The splice.** -/
theorem splice_spec {P : Program} {b bapp : ℕ} (hb : P.HasAt b (spliceFuns b bapp))
    (happ : P.HasAt bapp (appendFuns bapp)) (L M : List Val) {t : ℕ} (ht : t < L.length) :
    FunDet P b (.list [.list L, .nat t, .list M]) (.list (L.take t ++ M ++ L.drop (t + 1)))
      (spliceK * ((Val.list [.list L, .nat t, .list M]).wt + 1) ^ 3) := by
  obtain ⟨A, hA⟩ : ∃ A, A = (Val.list [.list L, .nat t, .list M]).wt := ⟨_, rfl⟩
  rw [← hA]
  have wL : (Val.list L).wt < A := hA ▸ wt_le_wt_list (by simp)
  have wM : (Val.list M).wt < A := hA ▸ wt_le_wt_list (by simp)
  have wt' : (Val.nat t).wt < A := hA ▸ wt_le_wt_list (by simp)
  have hLl := length_lt_wt_list L
  have hMl := length_lt_wt_list M
  obtain ⟨Mw, hMw⟩ : ∃ Mw, Mw = 6 * A + 4 := ⟨_, rfl⟩
  have hacc : ∀ i, (Val.list (spliceAt L M t i)).wt ≤ Mw := fun i => by
    have := wt_spliceAt_le L M t i; omega
  have hk : Det P [Val.list [.list L, .nat t, .list M]] (.length (.get (.var 0) (.nat 0)))
      (.nat L.length) _ :=
    Det.length (Det.get' (Det.var' (P := P) (env := [Val.list [.list L, .nat t, .list M]])
      (i := 0) rfl) (Det.nat 0) (v := .list L) rfl)
  obtain ⟨D, hD⟩ : ∃ D, D = 1000 * (A + 1) * (30 * A + 30) + 300 * A + 300 := ⟨_, rfl⟩
  refine (loopBdd_spec hb hk (Det.nil (P := P) (env := [Val.list [.list L, .nat t, .list M]]))
    ?_ (M := Mw) (Inv := fun i acc => acc = .list (spliceAt L M t i)) (D := fun _ => D)
    (by simp [spliceAt]) ?_ ?_).mono ?_
  · rw [← hA]; omega
  · rintro i acc - rfl; exact hacc i
  · rintro i acc hi rfl
    set vs := [Val.list L, Val.nat t, Val.list M] with hvs
    set a3 := [Val.list vs, Val.nat i, Val.list (spliceAt L M t i)] with ha3
    have dA := Det.arg' (P := P) (vs := a3) (rest := []) (j := 0) rfl
    have dI := Det.arg' (P := P) (vs := a3) (rest := []) (j := 1) rfl
    have dC := Det.arg' (P := P) (vs := a3) (rest := []) (j := 2) rfl
    have dT := Det.get' dA (Det.nat 1) (v := .nat t) rfl
    have dc := Det.arith' (op := .eq) dI dT (z := if i = t then 1 else 0) (by
      simp only [GI.Machine.BinOp.eval])
    have w3 := wt_list3_le (Val.list vs) (.nat i) (.list (spliceAt L M t i))
    have wA3 : (Val.list vs).wt = A := hA.symm
    have wq : (Val.list a3).wt = (Val.list [Val.list vs, Val.nat i, Val.list (spliceAt L M t i)]).wt :=
      rfl
    have := wt_nat_le i
    have := wt_nat_le t
    have h1 := hacc i
    have h2 := hacc (i + 1)
    rw [spliceAt_succ L M hi] at h2
    by_cases hit : i = t
    · rw [if_pos hit] at h2
      have dM := Det.get' dA (Det.nat 2) (v := .list M) rfl
      have dapp := Det.call (Det.mk2 dC dM) ((append_spec happ (spliceAt L M t i) M).mono
        fun w c h => by obtain ⟨rfl, h2⟩ := h; exact ⟨rfl, h2⟩)
      have d := Det.ite_pos (e := .snoc (arg 2) (.get (.get (arg 0) (.nat 0)) (arg 1))) dc
        (by simp [hit]) dapp
      refine d.post fun c hc => ⟨by beta_reduce; rw [spliceAt_succ L M hi, if_pos hit], ?_⟩
      beta_reduce
      have w2 := wt_list2_le (Val.list (spliceAt L M t i)) (Val.list M)
      have m1 : loopModK * (M.length + 1) * ((Val.list [Val.list (spliceAt L M t i),
          Val.list M]).wt + M.length + (Val.list (spliceAt L M t i ++ M)).wt + 1) ≤
          1000 * (A + 1) * (30 * A + 30) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      have hif : (if i = t then 1 else 0) ≤ 1 := by split_ifs <;> omega
      have := wt_nat_le (if i = t then 1 else 0)
      omega
    · rw [if_neg hit] at h2
      have dL := Det.get' dA (Det.nat 0) (v := .list L) rfl
      have dE := Det.get' dL dI (v := L[i]) (by simp [List.getElem?_eq_getElem hi])
      have ds := Det.snoc dC dE
      have hc0 : (if i = t then 1 else 0) = 0 := by simp [hit]
      rw [hc0] at dc
      have d := Det.ite_zero (t := .call bapp (mk2 (arg 2) (.get (arg 0) (.nat 2)))) dc ds
      refine d.post fun c hc => ⟨by beta_reduce; rw [spliceAt_succ L M hi, if_neg hit], ?_⟩
      beta_reduce
      have wE : L[i].wt < (Val.list L).wt := wt_getElem_lt L i hi
      have := wt_nat_le 0
      omega
  · rintro w cost ⟨rfl, hcost⟩
    refine ⟨by rw [spliceAt_length L M ht], ?_⟩
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hcost
    have hA1 : 1 ≤ A := by omega
    have hDle : D ≤ 31000 * ((A + 1) * (A + 1)) := by
      have h1 : 1000 * (A + 1) * (30 * A + 30) ≤ 1000 * (A + 1) * (30 * (A + 1)) :=
        Nat.mul_le_mul_left _ (by omega)
      have e : 1000 * (A + 1) * (30 * (A + 1)) = 30000 * ((A + 1) * (A + 1)) := by ring
      have h2 : A + 1 ≤ (A + 1) * (A + 1) := Nat.le_mul_self _
      omega
    have m1 : L.length * D ≤ (A + 1) * (31000 * ((A + 1) * (A + 1))) :=
      Nat.mul_le_mul (by omega) hDle
    have e1 : (A + 1) * (31000 * ((A + 1) * (A + 1))) = 31000 * (A + 1) ^ 3 := by ring
    have m3 : loopModK * (L.length + 1) * ((Val.list [.list L, .nat t, .list M]).wt + L.length +
        Mw + 1) ≤ 1000 * (A + 1) * (10 * (A + 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have e2 : 1000 * (A + 1) * (10 * (A + 1)) = 10000 * (A + 1) ^ 2 := by ring
    have p23 : (A + 1) ^ 2 ≤ (A + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    simp only [spliceK]
    omega

end GI.Impl
