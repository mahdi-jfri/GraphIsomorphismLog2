import Workspace.Impl.TermJProgLocBit

/-!
# The local transporter of a class (program, part 2: the matching)

For a 0/1 matrix `M` stored as its list of rows (`tmJLRowsV M`), the matched column of row `a`
is read as in `tmJMatchO`: the rank of `a` (the number of earlier rows equal to row `a`), then
that entry of the list of columns of row `a`.

* `tmJLRkF`: on `[[rows, a], a']`, whether `a' < a` and row `a'` equals row `a`;
* `tmJLColF`: on `[row, j]`, the entry `j` of the row;
* `tmJLPiF`: on `[[rows, ids], a]`, the matched column of row `a` (`tmJL_pi_spec`).

Costs are stated in `Q = q + 1`.
-/

namespace GI.Impl

open GI.Lang GI.Assembly Equiv
open GI.Cited (Val encPerm encPerms encGroup gens)

variable {q : ℕ}

/-! ### Rows and points as values -/

/-- A test on the points of `Fin q`, read on values. -/
def tmJLLift (p : Fin q → Bool) : Val → Bool
  | .nat n => if hn : n < q then p ⟨n, hn⟩ else false
  | .list _ => false

/-- The points `0, …, q - 1` as a value. -/
abbrev tmJLIds (q : ℕ) : Val := encFun fun i : Fin q => (i : ℕ)

theorem tmJLIds_eq (q : ℕ) : tmJLIds q = .list ((List.finRange q).map fun i : Fin q => Val.nat (i : ℕ)) := rfl

theorem tmJL_filter_pts (p : Fin q → Bool) :
    ((List.finRange q).map fun i : Fin q => Val.nat (i : ℕ)).filter (tmJLLift p) =
      ((List.finRange q).filter p).map fun i : Fin q => Val.nat (i : ℕ) := by
  rw [List.filter_map]
  congr 2
  funext i
  simp [tmJLLift, i.2]

/-- Row `a` of a 0/1 matrix, as numbers. -/
def tmJLRowN (M : Fin q → Fin q → Bool) (a : Fin q) : List ℕ :=
  (List.finRange q).map fun j => (M a j).toNat

/-- Row `a` of a 0/1 matrix, as a value. -/
def tmJLRowV (M : Fin q → Fin q → Bool) (a : Fin q) : Val := natList (tmJLRowN M a)

/-- The rows of a 0/1 matrix, as a value. -/
def tmJLRowsV (M : Fin q → Fin q → Bool) : Val := .list ((List.finRange q).map (tmJLRowV M))

theorem tmJLRowV_eq (M : Fin q → Fin q → Bool) (a : Fin q) :
    tmJLRowV M a = .list ((List.finRange q).map fun j => boolVal (M a j)) := by
  simp [tmJLRowV, tmJLRowN, natList, List.map_map, Function.comp_def]

theorem tmJLRowN_inj (M : Fin q → Fin q → Bool) (a a' : Fin q) :
    tmJLRowN M a' = tmJLRowN M a ↔ M a' = M a := by
  constructor
  · intro h
    funext j
    have := (List.map_inj_left.1 h) j (List.mem_finRange j)
    cases h1 : M a' j <;> cases h2 : M a j <;> simp_all
  · intro h; simp only [tmJLRowN, h]

theorem tmJL_wt_row (M : Fin q → Fin q → Bool) (a : Fin q) : (tmJLRowV M a).wt ≤ 7 * (q + 1) := by
  have h := wt_natList_le (xs := tmJLRowN M a) (B := 1) (by
    intro x hx
    simp only [tmJLRowN, List.mem_map] at hx
    obtain ⟨j, -, rfl⟩ := hx
    exact Bool.toNat_le _)
  simp only [tmJLRowN, List.length_map, List.length_finRange] at h
  unfold tmJLRowV tmJLRowN
  omega

theorem tmJL_wt_rows (M : Fin q → Fin q → Bool) : (tmJLRowsV M).wt ≤ 20 * (q + 1) ^ 2 := by
  have h := tmJL_wt_list_le (l := (List.finRange q).map (tmJLRowV M)) (B := 7 * (q + 1)) (by
    intro v hv
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hv
    exact tmJL_wt_row M a)
  simp only [List.length_map, List.length_finRange] at h
  unfold tmJLRowsV
  nlinarith

/-! ### The rank test -/

/-- On `[[rows, a], a']`: `1` if `a' < a` and rows `a'`, `a` are equal, else `0`. -/
def tmJLRkF (en : ℕ) : Expr :=
  .ite (.arith .lt (arg 1) (.get (arg 0) (.nat 1)))
    (.call en (mk2 (.get (.get (arg 0) (.nat 0)) (arg 1))
      (.get (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)))))
    (.nat 0)

/-- The cost bound of the rank test, in `Q = q + 1`. -/
def tmJLRkC (Q : ℕ) : ℕ := 10 ^ 6 * Q ^ 2

theorem tmJL_rk_spec {P : Program} {f en : ℕ} (hf : P.funs[f]? = some (tmJLRkF en))
    (hen : P.HasAt en (eqNatsFuns en)) (M : Fin q → Fin q → Bool) (a a' : Fin q) :
    FunDet P f (.list [.list [tmJLRowsV M, .nat a], .nat a'])
      (boolVal (decide (a' < a) && decide (M a' = M a))) (tmJLRkC (q + 1)) := by
  set av := Val.list [.list [tmJLRowsV M, .nat a], .nat a'] with hav
  have d0 := Det.arg' (P := P) (vs := [.list [tmJLRowsV M, .nat a], .nat a']) (rest := [])
    (j := 0) (v := .list [tmJLRowsV M, .nat a]) rfl
  have d1 := Det.arg' (P := P) (vs := [.list [tmJLRowsV M, .nat a], .nat a']) (rest := [])
    (j := 1) (v := .nat a') rfl
  have dA := Det.get' d0 (Det.nat 1) (vs := [tmJLRowsV M, .nat a]) (v := .nat a) rfl
  have dR := Det.get' d0 (Det.nat 0) (vs := [tmJLRowsV M, .nat a]) (v := tmJLRowsV M) rfl
  have dlt := Det.arith' (op := .lt) d1 dA (z := if (a' : ℕ) < a then 1 else 0) rfl
  have hr1 : ((List.finRange q).map (tmJLRowV M))[(a' : ℕ)]? = some (tmJLRowV M a') := by
    simp [a'.2]
  have hr2 : ((List.finRange q).map (tmJLRowV M))[(a : ℕ)]? = some (tmJLRowV M a) := by
    simp [a.2]
  have dr1 := Det.get' dR d1 hr1
  have dr2 := Det.get' dR dA hr2
  have deq := Det.call (Det.mk2 dr1 dr2) (eqNats_spec hen (tmJLRowN M a') (tmJLRowN M a))
  have dite := Det.ite' dlt deq (Det.nat 0)
  have hv : (if (if (a' : ℕ) < a then 1 else 0) = 0 then Val.nat 0 else
      boolVal (decide (tmJLRowN M a' = tmJLRowN M a))) =
      boolVal (decide (a' < a) && decide (M a' = M a)) := by
    by_cases hlt : (a' : ℕ) < a
    · have hlt' : a' < a := hlt
      simp only [hlt, if_true, one_ne_zero, if_false, hlt', decide_true, Bool.true_and]
      congr 2
      exact propext (tmJLRowN_inj M a a')
    · have hlt' : ¬ a' < a := hlt
      simp [hlt, hlt']
  rw [hv] at dite
  refine FunDet.intro hf (dite.mono ?_)
  -- the cost
  have wR := tmJL_wt_rows M
  have w1 := tmJL_wt_row M a
  have w2 := tmJL_wt_row M a'
  have wa := wt_nat_le a
  have wa' := wt_nat_le a'
  have ha := a.2
  have ha' := a'.2
  have wc := wt_list2_le (tmJLRowsV M) (.nat a)
  have wav := wt_list2_le (.list [tmJLRowsV M, .nat a]) (.nat a')
  have w12 := wt_list2_le (tmJLRowV M a') (tmJLRowV M a)
  have wb := wt_boolVal_le (decide (a' < a) && decide (M a' = M a))
  have wb2 := wt_boolVal_le (decide (tmJLRowN M a' = tmJLRowN M a))
  have wlt := wt_nat_le (if (a' : ℕ) < a then 1 else 0)
  have hlt1 : (if (a' : ℕ) < a then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have w0 := wt_nat_le 0
  have hl : (tmJLRowN M a').length = q := by simp [tmJLRowN]
  have e1 : (Val.list [natList (tmJLRowN M a'), natList (tmJLRowN M a)]).wt =
      (Val.list [tmJLRowV M a', tmJLRowV M a]).wt := rfl
  rw [hl, e1]
  have hlp : loopModK * (q + 1) * ((Val.list [tmJLRowV M a', tmJLRowV M a]).wt + q + 4) ≤
      1000 * (q + 1) * (100 * (q + 1)) := Nat.mul_le_mul_left _ (by omega)
  have hlp2 : 1000 * (q + 1) * (100 * (q + 1)) = 10 ^ 5 * (q + 1) ^ 2 := by ring
  have hq1 : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have e2 : (tmJLRowV M a').wt = (natList (tmJLRowN M a')).wt := rfl
  unfold tmJLRkC
  omega

/-! ### The column test -/

/-- On `[row, j]`: entry `j` of the row. -/
def tmJLColF : Expr := .get (arg 0) (arg 1)

theorem tmJL_col_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some tmJLColF)
    (M : Fin q → Fin q → Bool) (a j : Fin q) :
    FunDet P f (.list [tmJLRowV M a, .nat j]) (boolVal (M a j)) (100 * (q + 1)) := by
  have d0 := Det.arg' (P := P) (vs := [tmJLRowV M a, .nat j]) (rest := []) (j := 0)
    (v := .list ((List.finRange q).map fun j => boolVal (M a j))) (by simp [tmJLRowV_eq])
  have d1 := Det.arg' (P := P) (vs := [tmJLRowV M a, .nat j]) (rest := []) (j := 1)
    (v := .nat j) rfl
  have hv : ((List.finRange q).map fun j => boolVal (M a j))[(j : ℕ)]? = some (boolVal (M a j)) := by
    simp [j.2]
  refine FunDet.intro hf ((Det.get' d0 d1 hv).mono ?_)
  have w1 := tmJL_wt_row M a
  have wj := wt_nat_le j
  have hj := j.2
  have wav := wt_list2_le (tmJLRowV M a) (.nat j)
  have wb := wt_boolVal_le (M a j)
  omega

/-! ### The matched column -/

/-- On `[[rows, ids], a]`: the column of row `a` whose index among the columns is the rank. -/
def tmJLPiF (fR fC : ℕ) : Expr :=
  .get (.call fC (mk2 (.get (.get (arg 0) (.nat 0)) (arg 1)) (.get (arg 0) (.nat 1))))
    (.length (.call fR (mk2 (mk2 (.get (arg 0) (.nat 0)) (arg 1)) (.get (arg 0) (.nat 1)))))

/-- The cost bound of the matched column, in `Q = q + 1`. -/
def tmJLPiC (Q : ℕ) : ℕ := 10 ^ 8 * Q ^ 3

theorem tmJL_pi_spec {P : Program} {f fR fC rk co en : ℕ} (hf : P.funs[f]? = some (tmJLPiF fR fC))
    (hfR : P.HasAt fR (filterFuns fR rk)) (hfC : P.HasAt fC (filterFuns fC co))
    (hrk : P.funs[rk]? = some (tmJLRkF en)) (hco : P.funs[co]? = some tmJLColF)
    (hen : P.HasAt en (eqNatsFuns en)) (M : Fin q → Fin q → Bool) (a j : Fin q)
    (hj : tmJMatchO M a = some j) :
    FunDet P f (.list [.list [tmJLRowsV M, tmJLIds q], .nat a]) (.nat j) (tmJLPiC (q + 1)) := by
  set xs := (List.finRange q).map fun i : Fin q => Val.nat (i : ℕ) with hxs
  have hids : tmJLIds q = .list xs := rfl
  set pR : Fin q → Bool := fun a' => decide (a' < a) && decide (M a' = M a) with hpR
  -- the two filters
  have hFR : FunDet P fR (.list [.list [tmJLRowsV M, .nat a], .list xs])
      (.list ((List.finRange q).filter pR |>.map fun i : Fin q => Val.nat (i : ℕ)))
      ((xs.map fun _ => tmJLRkC (q + 1)).sum + loopModK * (xs.length + 1) *
        ((Val.list [.list [tmJLRowsV M, .nat a], .list xs]).wt + xs.length +
          (Val.list ((List.finRange q).filter pR |>.map fun i : Fin q => Val.nat (i : ℕ))).wt + 1)) := by
    have := filter_spec hfR (c := .list [tmJLRowsV M, .nat a]) (xs := xs) (q := tmJLLift pR)
      (B := fun _ => tmJLRkC (q + 1)) (by
        intro x hx
        obtain ⟨a', -, rfl⟩ := List.mem_map.1 hx
        have e : tmJLLift pR (.nat a') = pR a' := by simp [tmJLLift, a'.2]
        rw [e]
        exact tmJL_rk_spec hrk hen M a a')
    rw [tmJL_filter_pts] at this
    exact this.mono fun w c hw => by obtain ⟨rfl, h2⟩ := hw; exact ⟨rfl, h2⟩
  have hFC : FunDet P fC (.list [tmJLRowV M a, .list xs])
      (.list ((List.finRange q).filter (M a) |>.map fun i : Fin q => Val.nat (i : ℕ)))
      ((xs.map fun _ => 100 * (q + 1)).sum + loopModK * (xs.length + 1) *
        ((Val.list [tmJLRowV M a, .list xs]).wt + xs.length +
          (Val.list ((List.finRange q).filter (M a) |>.map fun i : Fin q => Val.nat (i : ℕ))).wt + 1)) := by
    have := filter_spec hfC (c := tmJLRowV M a) (xs := xs) (q := tmJLLift (M a))
      (B := fun _ => 100 * (q + 1)) (by
        intro x hx
        obtain ⟨j', -, rfl⟩ := List.mem_map.1 hx
        have e : tmJLLift (M a) (.nat j') = M a j' := by simp [tmJLLift, j'.2]
        rw [e]
        exact tmJL_col_spec hco M a j')
    rw [tmJL_filter_pts] at this
    exact this.mono fun w c hw => by obtain ⟨rfl, h2⟩ := hw; exact ⟨rfl, h2⟩
  -- the reads
  have d0 := Det.arg' (P := P) (vs := [.list [tmJLRowsV M, tmJLIds q], .nat a]) (rest := [])
    (j := 0) (v := .list [tmJLRowsV M, .list xs]) rfl
  have d1 := Det.arg' (P := P) (vs := [.list [tmJLRowsV M, tmJLIds q], .nat a]) (rest := [])
    (j := 1) (v := .nat a) rfl
  have dR := Det.get' d0 (Det.nat 0) (vs := [tmJLRowsV M, .list xs]) (v := tmJLRowsV M) rfl
  have dI := Det.get' d0 (Det.nat 1) (vs := [tmJLRowsV M, .list xs]) (v := .list xs) rfl
  have hra : ((List.finRange q).map (tmJLRowV M))[(a : ℕ)]? = some (tmJLRowV M a) := by
    simp [a.2]
  have drow := Det.get' dR d1 hra
  have cC := Det.call (Det.mk2 drow dI) hFC
  have cR := Det.call (Det.mk2 (Det.mk2 dR d1) dI) hFR
  have cL := Det.length cR
  have hlen : ((List.finRange q).filter pR |>.map fun i : Fin q => Val.nat (i : ℕ)).length = tmJRank M a := by
    simp [tmJRank, hpR]
  rw [hlen] at cL
  have hent : ((List.finRange q).filter (M a) |>.map fun i : Fin q => Val.nat (i : ℕ))[tmJRank M a]? =
      some (.nat j) := by
    have : (tmJCols M a)[tmJRank M a]? = some j := hj
    simp only [tmJCols] at this
    simp [List.getElem?_map, this]
  refine FunDet.intro hf ((Det.get' cC cL hent).mono ?_)
  -- the cost
  have hxl : xs.length = q := by simp [hxs]
  have hs1 : (xs.map fun _ => tmJLRkC (q + 1)).sum = q * tmJLRkC (q + 1) := by
    simp [List.map_const', hxl]
  have hs2 : (xs.map fun _ => 100 * (q + 1)).sum = q * (100 * (q + 1)) := by
    simp [List.map_const', hxl]
  rw [hs1, hs2, hxl]
  set Q := q + 1 with hQ
  have wR := tmJL_wt_rows M
  have w1 := tmJL_wt_row M a
  have hQq : (q + 1) ^ 2 = Q ^ 2 := by rw [hQ]
  have wI : (Val.list xs).wt ≤ 4 * Q ^ 2 := by rw [← hids]; exact wt_ids_le q
  have wa := wt_nat_le a
  have ha := a.2
  have hrk : tmJRank M a ≤ q := by
    unfold tmJRank; exact (List.length_filter_le _ _).trans (by simp)
  have wrk := wt_nat_le (tmJRank M a)
  have wj := wt_nat_le j
  have hjq := j.2
  have wF1 : (Val.list ((List.finRange q).filter pR |>.map fun i : Fin q => Val.nat (i : ℕ))).wt ≤ 4 * Q ^ 2 := by
    have := tmJL_wt_list_le (l := (List.finRange q).filter pR |>.map fun i : Fin q => Val.nat (i : ℕ))
      (B := Q + 2) (by
        intro v hv
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hv
        show (Val.nat (i : ℕ)).wt ≤ Q + 2
        have := wt_nat_le i; have := i.2; omega)
    have hl : ((List.finRange q).filter pR |>.map fun i : Fin q => Val.nat (i : ℕ)).length ≤ q := by
      simp only [List.length_map]; exact (List.length_filter_le _ _).trans (by simp)
    have : ((List.finRange q).filter pR |>.map fun i : Fin q => Val.nat (i : ℕ)).length * (2 * (Q + 2) + 1) ≤
        q * (2 * (Q + 2) + 1) := Nat.mul_le_mul_right _ hl
    nlinarith
  have wF2 : (Val.list ((List.finRange q).filter (M a) |>.map fun i : Fin q => Val.nat (i : ℕ))).wt ≤
      4 * Q ^ 2 := by
    have := tmJL_wt_list_le (l := (List.finRange q).filter (M a) |>.map fun i : Fin q => Val.nat (i : ℕ))
      (B := Q + 2) (by
        intro v hv
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hv
        show (Val.nat (i : ℕ)).wt ≤ Q + 2
        have := wt_nat_le i; have := i.2; omega)
    have hl : ((List.finRange q).filter (M a) |>.map fun i : Fin q => Val.nat (i : ℕ)).length ≤ q := by
      simp only [List.length_map]; exact (List.length_filter_le _ _).trans (by simp)
    have : ((List.finRange q).filter (M a) |>.map fun i : Fin q => Val.nat (i : ℕ)).length *
        (2 * (Q + 2) + 1) ≤ q * (2 * (Q + 2) + 1) := Nat.mul_le_mul_right _ hl
    nlinarith
  have wc1 := wt_list2_le (tmJLRowsV M) (.list xs)
  have wc2 := wt_list2_le (tmJLRowsV M) (.nat a)
  have wc3 := wt_list2_le (.list [tmJLRowsV M, .nat a]) (.list xs)
  have wc4 := wt_list2_le (tmJLRowV M a) (.list xs)
  have wav := wt_list2_le (.list [tmJLRowsV M, .list xs]) (.nat a)
  have hQ1 : Q ≤ Q ^ 2 := Nat.le_self_pow (by norm_num) _
  have hQ2 : Q ^ 2 ≤ Q ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have l1 : loopModK * Q * ((Val.list [.list [tmJLRowsV M, .nat a], .list xs]).wt + q +
      (Val.list ((List.finRange q).filter pR |>.map fun i : Fin q => Val.nat (i : ℕ))).wt + 1) ≤
      1000 * Q * (200 * Q ^ 2) := Nat.mul_le_mul_left _ (by omega)
  have l2 : loopModK * Q * ((Val.list [tmJLRowV M a, .list xs]).wt + q +
      (Val.list ((List.finRange q).filter (M a) |>.map fun i : Fin q => Val.nat (i : ℕ))).wt + 1) ≤
      1000 * Q * (200 * Q ^ 2) := Nat.mul_le_mul_left _ (by omega)
  have l3 : 1000 * Q * (200 * Q ^ 2) = 200000 * Q ^ 3 := by ring
  have l4 : q * tmJLRkC Q ≤ 10 ^ 6 * Q ^ 3 := by
    unfold tmJLRkC
    calc q * (10 ^ 6 * Q ^ 2) ≤ Q * (10 ^ 6 * Q ^ 2) := Nat.mul_le_mul_right _ (by omega)
      _ = 10 ^ 6 * Q ^ 3 := by ring
  have l5 : q * (100 * Q) ≤ 100 * Q ^ 2 := by
    calc q * (100 * Q) ≤ Q * (100 * Q) := Nat.mul_le_mul_right _ (by omega)
      _ = 100 * Q ^ 2 := by ring
  have e1 : (Val.list [tmJLRowsV M, tmJLIds q]).wt = (Val.list [tmJLRowsV M, .list xs]).wt := rfl
  have e2 : (Val.list [.list [tmJLRowsV M, tmJLIds q], .nat a]).wt =
      (Val.list [.list [tmJLRowsV M, .list xs], .nat a]).wt := rfl
  unfold tmJLPiC
  omega

end GI.Impl
