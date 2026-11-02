import Workspace.Proved.HNFSylvester
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.List.GetD

/-!
# Bareiss elimination with row pivoting

We want `c` rows of an `r × c` integer matrix `A` of full column rank that form a nonsingular
block, together with the determinant of that block, using only numbers of polynomial size.

Bareiss elimination does this. After `k` steps it has chosen rows `s` (`k` of them) and holds a
matrix `W` whose entry `W i j` is the minor of `A` on rows `s ++ [i]` and columns
`0, …, k-1, j` (`hnfBord`), and a number `d`, the minor on rows `s` and columns `0, …, k-1`
(`hnfLead`). Step `k` picks the first row `p` with `W p k ≠ 0` and replaces `W i j` by
`(W p k * W i j - W i k * W p j) / d`. Sylvester's identity (`hnfSylvesterZ`) shows that the
division is exact and that the result is again a minor. So every number is a minor of `A`,
hence at most `c! M^c` for entries at most `M` (`hnfMin_abs_le`). Full column rank gives a pivot
at every step (`hnfPivot_exists`).

The result used later is `hnfBarIter_spec`.
-/

namespace GI.Proved

open Matrix

variable {r c : ℕ}

/-! ### Minors on chosen rows and the first columns -/

/-- Rows `s[0], …, s[n-1]`, with `i` past the end of `s`. -/
def hnfRowSel (s : List (Fin r)) (i : Fin r) (n : ℕ) : Fin n → Fin r := fun a => s.getD a i

/-- Columns `0, …, k-1`, then `j`. -/
def hnfColSel (k : ℕ) (j : Fin c) (n : ℕ) : Fin n → Fin c :=
  fun b => if h : (b : ℕ) < k ∧ (b : ℕ) < c then ⟨b, h.2⟩ else j

/-- The `n × n` minor of `A` on the rows `hnfRowSel s i n` and columns `hnfColSel k j n`. -/
def hnfMin (A : Matrix (Fin r) (Fin c) ℤ) (n : ℕ) (s : List (Fin r)) (i : Fin r) (k : ℕ)
    (j : Fin c) : ℤ :=
  (A.submatrix (hnfRowSel s i n) (hnfColSel k j n)).det

/-- The bordered minor: rows `s ++ [i]`, columns `0, …, k-1, j`, where `k` is the length of
`s`. -/
abbrev hnfBord (A : Matrix (Fin r) (Fin c) ℤ) (s : List (Fin r)) (i : Fin r) (j : Fin c) : ℤ :=
  hnfMin A (s.length + 1) s i s.length j

/-- The leading minor: rows `s`, columns `0, …, k-1`. It does not depend on `i, j`. -/
abbrev hnfLead (A : Matrix (Fin r) (Fin c) ℤ) (s : List (Fin r)) (i : Fin r) (j : Fin c) : ℤ :=
  hnfMin A s.length s i s.length j

/-- Every minor is at most `n! M^n` when the entries are at most `M`. -/
theorem hnfMin_abs_le (A : Matrix (Fin r) (Fin c) ℤ) {M : ℤ} (hM : ∀ i j, |A i j| ≤ M)
    (n : ℕ) (s : List (Fin r)) (i : Fin r) (k : ℕ) (j : Fin c) :
    |hnfMin A n s i k j| ≤ n.factorial * M ^ n := by
  have h := Matrix.det_le (A := A.submatrix (hnfRowSel s i n) (hnfColSel k j n))
    (abv := AbsoluteValue.abs) (x := M) (fun a b => hM _ _)
  simpa [Fintype.card_fin, nsmul_eq_mul] using h

/-- The leading minor of `s ++ [p]` is the bordered minor of `s` at `p` and column `k`. -/
theorem hnfLead_append (A : Matrix (Fin r) (Fin c) ℤ) (s : List (Fin r)) (p x : Fin r)
    (y : Fin c) (hk : s.length < c) :
    hnfLead A (s ++ [p]) x y = hnfBord A s p ⟨s.length, hk⟩ := by
  have e : (s ++ [p]).length = s.length + 1 := by simp
  unfold hnfLead hnfBord
  rw [e]
  unfold hnfMin
  congr 2
  · funext a
    simp only [hnfRowSel]
    by_cases ha : (a : ℕ) < s.length
    · rw [List.getD_append _ _ _ _ ha, List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ ha]
    · have ha' : (a : ℕ) = s.length := by omega
      rw [List.getD_append_right s [p] x a (by omega), List.getD_eq_default s p (by omega)]
      simp [ha']
  · funext b
    simp only [hnfColSel]
    by_cases hb : (b : ℕ) < s.length
    · simp [hb, show (b : ℕ) < c by omega, show (b : ℕ) < s.length + 1 by omega]
    · have hb' : (b : ℕ) = s.length := by omega
      simp [hb', hk]

/-! ### Sylvester's identity for bordered minors -/

/-- The rows and columns of a two-row border, indexed by `Fin k ⊕ Fin 2`. -/
private def hnfR2 (s : List (Fin r)) (p i : Fin r) : Fin s.length ⊕ Fin 2 → Fin r :=
  Sum.elim (fun a => s.getD a p) ![p, i]

private def hnfC2 (k : ℕ) (hk : k < c) (j : Fin c) : Fin k ⊕ Fin 2 → Fin c :=
  Sum.elim (fun b => ⟨b, by omega⟩) ![⟨k, hk⟩, j]

theorem hnfR2_eq (s : List (Fin r)) (p i : Fin r) :
    hnfRowSel (s ++ [p]) i (s.length + 1 + 1) ∘ (finSumFinEquiv (m := s.length) (n := 2)) =
      hnfR2 s p i := by
  funext x
  rcases x with a | a
  · simp only [Function.comp_apply, finSumFinEquiv_apply_left, hnfRowSel, hnfR2, Sum.elim_inl,
      Fin.val_castAdd]
    rw [List.getD_append _ _ _ _ a.isLt, List.getD_eq_getElem _ _ a.isLt,
      List.getD_eq_getElem _ _ a.isLt]
  · fin_cases a
    · simp [hnfRowSel, hnfR2]
    · simp only [Function.comp_apply, finSumFinEquiv_apply_right, hnfRowSel, hnfR2, Sum.elim_inr]
      rw [List.getD_eq_default _ _ (by simp)]
      simp

theorem hnfC2_eq (k : ℕ) (hk : k < c) (j : Fin c) :
    hnfColSel (k + 1) j (k + 1 + 1) ∘ (finSumFinEquiv (m := k) (n := 2)) = hnfC2 k hk j := by
  funext x
  rcases x with b | b
  · simp only [Function.comp_apply, finSumFinEquiv_apply_left, hnfColSel, hnfC2, Sum.elim_inl,
      Fin.val_castAdd]
    rw [dif_pos ⟨by omega, by omega⟩]
  · fin_cases b
    · simp [hnfColSel, hnfC2, hk]
    · simp [hnfColSel, hnfC2]

/-- The one-row borders inside the two-row border. -/
theorem hnfR1_eq (s : List (Fin r)) (p i : Fin r) (a : Fin 2) :
    hnfRowSel s (![p, i] a) (s.length + 1) ∘ finSumFinEquiv =
      hnfR2 s p i ∘ Sum.map id (fun _ : Fin 1 => a) := by
  funext x
  rcases x with b | b
  · simp only [Function.comp_apply, finSumFinEquiv_apply_left, hnfRowSel, hnfR2, Sum.elim_inl,
      Fin.val_castAdd, Sum.map_inl, id]
    rw [List.getD_eq_getElem _ _ b.isLt, List.getD_eq_getElem _ _ b.isLt]
  · fin_cases b
    simp only [Function.comp_apply, finSumFinEquiv_apply_right, hnfRowSel, hnfR2, Sum.elim_inr,
      Sum.map_inr]
    rw [List.getD_eq_default _ _ (by simp)]

theorem hnfC1_eq (k : ℕ) (hk : k < c) (j : Fin c) (b : Fin 2) :
    hnfColSel k (![⟨k, hk⟩, j] b) (k + 1) ∘ finSumFinEquiv =
      hnfC2 k hk j ∘ Sum.map id (fun _ : Fin 1 => b) := by
  funext x
  rcases x with a | a
  · simp only [Function.comp_apply, finSumFinEquiv_apply_left, hnfColSel, hnfC2, Sum.elim_inl,
      Fin.val_castAdd, Sum.map_inl, id]
    rw [dif_pos ⟨a.isLt, by omega⟩]
  · fin_cases a
    simp [hnfColSel, hnfC2]

/-- **The Bareiss step.** For `k = |s| < c` with nonzero leading minor `d`,
`d · bord(s ++ [p], i, j) = bord(s, p, k) · bord(s, i, j) - bord(s, i, k) · bord(s, p, j)`. -/
theorem hnfBord_step (A : Matrix (Fin r) (Fin c) ℤ) (s : List (Fin r)) (hk : s.length < c)
    (p i x : Fin r) (j y : Fin c) (hd : hnfLead A s x y ≠ 0) :
    hnfLead A s x y * hnfBord A (s ++ [p]) i j =
      hnfBord A s p ⟨s.length, hk⟩ * hnfBord A s i j -
        hnfBord A s i ⟨s.length, hk⟩ * hnfBord A s p j := by
  let N : Matrix (Fin s.length ⊕ Fin 2) (Fin s.length ⊕ Fin 2) ℤ :=
    A.submatrix (hnfR2 s p i) (hnfC2 s.length hk j)
  have h11 : N.toBlocks₁₁.det = hnfLead A s x y := by
    simp only [hnfMin]
    congr 1
    ext a b
    simp only [N, toBlocks₁₁, of_apply, submatrix_apply, hnfR2, hnfC2, Sum.elim_inl, hnfRowSel,
      hnfColSel]
    rw [List.getD_eq_getElem _ _ a.isLt, List.getD_eq_getElem _ _ a.isLt]
    simp [show (b : ℕ) < c by omega]
  have hN : N.det = hnfBord A (s ++ [p]) i j := by
    have e : (s ++ [p]).length = s.length + 1 := by simp
    unfold hnfBord
    rw [e]
    unfold hnfMin
    rw [← Matrix.det_submatrix_equiv_self (finSumFinEquiv (m := s.length) (n := 2)),
      Matrix.submatrix_submatrix, hnfR2_eq, hnfC2_eq]
  have h1 : ∀ a b : Fin 2,
      (hnfSub2 N a b).det = hnfBord A s (![p, i] a) (![⟨s.length, hk⟩, j] b) := by
    intro a b
    unfold hnfBord hnfMin
    rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv, Matrix.submatrix_submatrix, hnfR1_eq,
      hnfC1_eq]
    rfl
  have hS := hnfSylvesterZ N (h11 ▸ hd)
  rw [h11, hN, h1, h1, h1, h1] at hS
  simpa using hS

/-! ### A pivot exists -/

/-- The bordered minor in column `k` through the one-row border formula: it is
`A i k · d - Σ_b A i b · w b`, where `w = adj(A₁₁) · (column k on the rows s)`. -/
theorem hnfBord_eq_border (A : Matrix (Fin r) (Fin c) ℤ) (s : List (Fin r)) (hk : s.length < c)
    (x : Fin r) (y : Fin c) (hd : hnfLead A s x y ≠ 0) (i : Fin r) :
    hnfBord A s i ⟨s.length, hk⟩ = A i ⟨s.length, hk⟩ * hnfLead A s x y -
      ∑ b : Fin s.length, A i ⟨b, by omega⟩ *
        ((A.submatrix (hnfRowSel s x s.length) (hnfColSel s.length y s.length)).adjugate.mulVec
          (fun a => A (hnfRowSel s x s.length a) ⟨s.length, hk⟩)) b := by
  set A11 := A.submatrix (hnfRowSel s x s.length) (hnfColSel s.length y s.length) with hA11
  have e : (A.submatrix (hnfRowSel s i (s.length + 1)) (hnfColSel s.length ⟨s.length, hk⟩
      (s.length + 1))).submatrix (finSumFinEquiv (m := s.length) (n := 1))
      (finSumFinEquiv (m := s.length) (n := 1)) =
      fromBlocks A11 (fun a _ => A (hnfRowSel s x s.length a) ⟨s.length, hk⟩)
        (fun _ b => A i ⟨b, by omega⟩) (fun _ _ => A i ⟨s.length, hk⟩) := by
    ext (a | a) (b | b)
    · simp only [submatrix_apply, finSumFinEquiv_apply_left, fromBlocks_apply₁₁, hA11,
        hnfRowSel, hnfColSel, Fin.val_castAdd]
      rw [List.getD_eq_getElem _ _ a.isLt, List.getD_eq_getElem _ _ a.isLt]
      simp [show (b : ℕ) < c by omega]
    · simp only [submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        fromBlocks_apply₁₂, hnfRowSel, hnfColSel, Fin.val_castAdd, Fin.val_natAdd]
      rw [List.getD_eq_getElem _ _ a.isLt, List.getD_eq_getElem _ _ a.isLt]
      simp
    · simp only [submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        fromBlocks_apply₂₁, hnfRowSel, hnfColSel, Fin.val_castAdd, Fin.val_natAdd]
      rw [List.getD_eq_default _ _ (by simp)]
      simp [show (b : ℕ) < c by omega]
    · simp only [submatrix_apply, finSumFinEquiv_apply_right, fromBlocks_apply₂₂, hnfRowSel,
        hnfColSel, Fin.val_natAdd]
      rw [List.getD_eq_default _ _ (by simp)]
      simp
  unfold hnfBord hnfMin
  rw [← Matrix.det_submatrix_equiv_self (finSumFinEquiv (m := s.length) (n := 1)), e,
    hnfBorder1 _ _ _ _ hd]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, hnfMin, hA11]
  simp only [Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

/-- **A pivot exists.** If `A` has full column rank, `k = |s| < c` and the leading minor is
nonzero, some bordered minor in column `k` is nonzero. Otherwise column `k` would be a rational
combination of the first `k` columns. -/
theorem hnfPivot_exists (A : Matrix (Fin r) (Fin c) ℤ) (hA : Function.Injective A.mulVec)
    (s : List (Fin r)) (hk : s.length < c) (x : Fin r) (y : Fin c)
    (hd : hnfLead A s x y ≠ 0) : ∃ i, hnfBord A s i ⟨s.length, hk⟩ ≠ 0 := by
  by_contra hall
  push Not at hall
  set w := (A.submatrix (hnfRowSel s x s.length) (hnfColSel s.length y s.length)).adjugate.mulVec
    (fun a => A (hnfRowSel s x s.length a) ⟨s.length, hk⟩) with hw
  let z : Fin c → ℤ := fun t =>
    if h : (t : ℕ) < s.length then w ⟨t, h⟩ else if (t : ℕ) = s.length then -hnfLead A s x y else 0
  have hz : A.mulVec z = 0 := by
    funext i
    have hb := hall i
    rw [hnfBord_eq_border A s hk x y hd i] at hb
    rw [← hw] at hb
    let f : ℕ → ℤ := fun t => if h : t < c then A i ⟨t, h⟩ * z ⟨t, h⟩ else 0
    have h1 : A.mulVec z i = ∑ t ∈ Finset.range c, f t := by
      rw [← Fin.sum_univ_eq_sum_range]
      simp [Matrix.mulVec, dotProduct, f]
    have h2 : ∑ t ∈ Finset.range c, f t = ∑ t ∈ Finset.range (s.length + 1), f t := by
      rw [← Finset.sum_range_add_sum_Ico _ (show s.length + 1 ≤ c by omega)]
      rw [Finset.sum_eq_zero (s := Finset.Ico _ _) (fun t ht => ?_), add_zero]
      have := Finset.mem_Ico.mp ht
      simp [f, z, show ¬ t < s.length by omega, show t ≠ s.length by omega]
    have h3 : ∑ t ∈ Finset.range s.length, f t = ∑ b : Fin s.length, A i ⟨b, by omega⟩ * w b := by
      rw [← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp [f, z, show (b : ℕ) < c by omega]
    rw [h1, h2, Finset.sum_range_succ, h3]
    simp only [f, z, dif_pos hk, lt_irrefl, dite_false, if_true, Pi.zero_apply]
    linarith
  have hz0 : z = 0 := hA (by rw [hz, Matrix.mulVec_zero])
  have := congrFun hz0 ⟨s.length, hk⟩
  simp [z] at this
  exact hd this

/-! ### The algorithm -/

/-- The state of Bareiss elimination: the chosen rows, the last pivot and the working
matrix. -/
structure HnfBar (r c : ℕ) where
  s : List (Fin r)
  d : ℤ
  W : Matrix (Fin r) (Fin c) ℤ

/-- The first row with a nonzero entry in column `k`. -/
def hnfPivot (W : Matrix (Fin r) (Fin c) ℤ) (k : Fin c) : Option (Fin r) :=
  (List.finRange r).find? fun i => W i k ≠ 0

/-- One Bareiss update with pivot `(p, k)` and previous pivot `d`. -/
def hnfBarUpd (W : Matrix (Fin r) (Fin c) ℤ) (d : ℤ) (p : Fin r) (k : Fin c) :
    Matrix (Fin r) (Fin c) ℤ :=
  fun i j => (W p k * W i j - W i k * W p j) / d

/-- Step `k` of Bareiss elimination. -/
def hnfBarStep (st : HnfBar r c) (k : Fin c) : HnfBar r c :=
  match hnfPivot st.W k with
  | none => st
  | some p => ⟨st.s ++ [p], st.W p k, hnfBarUpd st.W st.d p k⟩

/-- The state after `k` steps. -/
def hnfBarIter (A : Matrix (Fin r) (Fin c) ℤ) : ℕ → HnfBar r c
  | 0 => ⟨[], 1, A⟩
  | k + 1 => if h : k < c then hnfBarStep (hnfBarIter A k) ⟨k, h⟩ else hnfBarIter A k

/-- The invariant after `k` steps: `k` rows are chosen, `d` is the nonzero leading minor and
`W` holds the bordered minors. -/
def HnfBarInv (A : Matrix (Fin r) (Fin c) ℤ) (k : ℕ) (st : HnfBar r c) : Prop :=
  st.s.length = k ∧ (∀ x y, st.d = hnfLead A st.s x y) ∧ st.d ≠ 0 ∧
    ∀ i j, st.W i j = hnfBord A st.s i j

theorem hnfBarInv_zero (A : Matrix (Fin r) (Fin c) ℤ) : HnfBarInv A 0 (hnfBarIter A 0) := by
  refine ⟨rfl, fun x y => ?_, one_ne_zero, fun i j => ?_⟩
  · simp [hnfBarIter, hnfMin, Matrix.det_isEmpty]
  · simp [hnfBarIter, hnfMin, hnfRowSel, hnfColSel]

theorem hnfBarStep_inv (A : Matrix (Fin r) (Fin c) ℤ) (hA : Function.Injective A.mulVec)
    {k : ℕ} (hk : k < c) {st : HnfBar r c} (h : HnfBarInv A k st) :
    HnfBarInv A (k + 1) (hnfBarStep st ⟨k, hk⟩) := by
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · subst h0
      exfalso
      have := hA (a₁ := 0) (a₂ := fun _ => 1) (funext fun i => i.elim0)
      exact one_ne_zero (congrFun this ⟨0, by omega⟩).symm
    · exact h0
  obtain ⟨hlen, hlead, hd, hW⟩ := h
  subst hlen
  obtain ⟨x, hx⟩ := hnfPivot_exists A hA st.s hk (st.s.getD 0 ⟨0, hr⟩) ⟨0, by omega⟩
    (hlead _ _ ▸ hd)
  have hpiv : ∃ p, hnfPivot st.W ⟨st.s.length, hk⟩ = some p ∧ st.W p ⟨st.s.length, hk⟩ ≠ 0 := by
    cases hp : hnfPivot st.W ⟨st.s.length, hk⟩ with
    | none =>
      exfalso
      have := List.find?_eq_none.mp hp x (List.mem_finRange x)
      simp only [ne_eq, decide_not, Bool.not_eq_true', decide_eq_false_iff_not, not_not] at this
      exact hx (hW x _ ▸ this)
    | some p =>
      refine ⟨p, rfl, ?_⟩
      have := List.find?_some hp
      simpa using this
  obtain ⟨p, hp, hpne⟩ := hpiv
  simp only [hnfBarStep, hp]
  refine ⟨by simp, fun x' y' => ?_, hpne, fun i j => ?_⟩
  · rw [hnfLead_append A st.s p x' y' hk, hW]
  · simp only [hnfBarUpd]
    rw [hW p, hW i, hW i, hW p, ← hnfBord_step A st.s hk p i (st.s.getD 0 ⟨0, hr⟩)
      j ⟨0, by omega⟩ (hlead _ _ ▸ hd), ← hlead]
    exact Int.mul_ediv_cancel_left _ hd

/-- **Bareiss elimination.** For `A` of full column rank, after `k ≤ c` steps the invariant
holds. -/
theorem hnfBarIter_spec (A : Matrix (Fin r) (Fin c) ℤ) (hA : Function.Injective A.mulVec) :
    ∀ k, k ≤ c → HnfBarInv A k (hnfBarIter A k) := by
  intro k
  induction k with
  | zero => exact fun _ => hnfBarInv_zero A
  | succ k ih =>
    intro hk
    have h := hnfBarStep_inv A hA (by omega) (ih (by omega))
    simpa [hnfBarIter, show k < c by omega] using h

end GI.Proved
