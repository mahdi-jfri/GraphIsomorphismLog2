import Workspace.Proved.SNFPot
import Workspace.Impl.HNFMain

/-!
# Alternating Hermite forms make a nonsingular matrix diagonal (Smith form)

This is the first half of algorithm SNF of [KB79, Section 3]. The state is `(H, P, Q)`, started
at `(A, 1, 1)`. One step takes the Hermite form `H' = U Hᵀ` of the transpose, computed by the
Hermite program (`snfU`, `snfH`), and moves to `(H', U Qᵀ, Pᵀ)` (`snfStep`). If `H = P X Q`, then
`H' = (U Qᵀ) Xᵀ Pᵀ`, so the state after `t` steps satisfies `H = P X Q` with `X = A` for even `t`
and `X = Aᵀ` for odd `t` (`snfIt_inv`).

Why the matrix becomes diagonal. For `t ≥ 1`, `H_t` is a square Hermite form. By
`Proved/SNFPot.lean`, either the diagonal does not change in the next step, and then `H_{t+1}` is
diagonal, or the potential `snfPhi` (the product of all prefix products of the diagonal) at
least halves (`snf_step_dich`). A diagonal state is fixed (`snf_step_diag`). The potential of
`H_1` is at most `d^(n+1)` with `d = |det A|`, so `H_t` is diagonal once `d^(n+1) < 2^(t-1)`
(`snfIt_diag`).
-/

namespace GI.Proved

open _root_.Matrix GI.Cited GI.Impl

variable {n : ℕ}

theorem snf_inj_of_det {M : Matrix (Fin n) (Fin n) ℤ} (h : M.det ≠ 0) :
    Function.Injective M.mulVec := by
  intro u v huv
  have := eq_zero_of_mulVec_eq_zero h (v := u - v) (by rw [mulVec_sub, huv, sub_self])
  exact sub_eq_zero.mp this

/-- The transform of the Hermite program on a square matrix. -/
def snfU (M : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ := hnfRectU M (hnfTn M : ℤ)

/-- The Hermite form of the Hermite program on a square matrix. -/
def snfH (M : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  hnfRectH M le_rfl (hnfTn M : ℤ)

theorem snf_hnf_spec {M : Matrix (Fin n) (Fin n) ℤ} (hn : 0 < n) (hM : M.det ≠ 0) :
    IsUnit (snfU M).det ∧ snfU M * M = snfH M ∧ IsHermiteForm (snfH M) ∧
      ∀ i j, |snfU M i j| < hnfK n (hnfTn M : ℤ) := by
  have hT1 : (1 : ℤ) ≤ (hnfTn M : ℤ) := by unfold hnfTn; omega
  obtain ⟨h1, h2, h3, h4, -⟩ := hnfRect_spec M (snf_inj_of_det hM) hn le_rfl hT1 (hnf_abs_le_Tn M)
  exact ⟨h1, h2, h3, h4⟩

/-- The state of the alternation. -/
structure SnfSt (n : ℕ) where
  H : Matrix (Fin n) (Fin n) ℤ
  P : Matrix (Fin n) (Fin n) ℤ
  Q : Matrix (Fin n) (Fin n) ℤ

/-- One step: the Hermite form of the transpose. -/
def snfStep (s : SnfSt n) : SnfSt n := ⟨snfH s.Hᵀ, snfU s.Hᵀ * s.Qᵀ, s.Pᵀ⟩

/-- The state after `t` steps from `(A, 1, 1)`. -/
def snfIt (A : Matrix (Fin n) (Fin n) ℤ) (t : ℕ) : SnfSt n := snfStep^[t] ⟨A, 1, 1⟩

/-- `A` for even `t`, `Aᵀ` for odd `t`. -/
def snfX (A : Matrix (Fin n) (Fin n) ℤ) (t : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  if t % 2 = 0 then A else Aᵀ

theorem snfX_succ (A : Matrix (Fin n) (Fin n) ℤ) (t : ℕ) : snfX A (t + 1) = (snfX A t)ᵀ := by
  unfold snfX
  by_cases h : t % 2 = 0
  · have h' : ¬ (t + 1) % 2 = 0 := by omega
    rw [if_neg h', if_pos h]
  · have h' : (t + 1) % 2 = 0 := by omega
    rw [if_pos h', if_neg h, transpose_transpose]

theorem snfIt_succ (A : Matrix (Fin n) (Fin n) ℤ) (t : ℕ) :
    snfIt A (t + 1) = snfStep (snfIt A t) := by
  unfold snfIt; rw [Function.iterate_succ_apply']

theorem snf_isUnit_transpose {M : Matrix (Fin n) (Fin n) ℤ} (h : IsUnit M.det) :
    IsUnit Mᵀ.det := by rwa [det_transpose]

/-- The invariant of the alternation: `H = P X Q` with `P, Q` unimodular, and from step one on
`H` is a Hermite form. -/
theorem snfIt_inv (hn : 0 < n) {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.det ≠ 0) (t : ℕ) :
    (snfIt A t).H = (snfIt A t).P * snfX A t * (snfIt A t).Q ∧ IsUnit (snfIt A t).P.det ∧
      IsUnit (snfIt A t).Q.det ∧ (1 ≤ t → IsHermiteForm (snfIt A t).H) := by
  induction t with
  | zero =>
    refine ⟨?_, by simp [snfIt], by simp [snfIt], fun h => absurd h (by omega)⟩
    simp [snfIt, snfX]
  | succ t ih =>
    obtain ⟨e, hP, hQ, -⟩ := ih
    set s := snfIt A t
    have hdetX : (snfX A t).det ≠ 0 := by
      unfold snfX; split_ifs <;> simp [hA]
    have hdetH : s.Hᵀ.det ≠ 0 := by
      rw [det_transpose, e, det_mul, det_mul]
      refine mul_ne_zero (mul_ne_zero ?_ hdetX) ?_
      · exact hP.ne_zero
      · exact hQ.ne_zero
    obtain ⟨hU, hUH, hHf, -⟩ := snf_hnf_spec hn hdetH
    rw [snfIt_succ]
    refine ⟨?_, ?_, snf_isUnit_transpose hP, fun _ => hHf⟩
    · show snfH s.Hᵀ = snfU s.Hᵀ * s.Qᵀ * snfX A (t + 1) * s.Pᵀ
      rw [← hUH, e, snfX_succ]
      simp only [transpose_mul, Matrix.mul_assoc]
    · show IsUnit (snfU s.Hᵀ * s.Qᵀ).det
      rw [det_mul]
      exact hU.mul (snf_isUnit_transpose hQ)

/-! ### The potential -/

/-- The product of all prefix products of the diagonal. -/
def snfPhi (M : Matrix (Fin n) (Fin n) ℤ) : ℤ :=
  ∏ k : Fin (n + 1), snfPre k (Nat.lt_succ_iff.mp k.isLt) M

theorem snfPre_succ {l : ℕ} (hl : l + 1 ≤ n) (M : Matrix (Fin n) (Fin n) ℤ) :
    snfPre (l + 1) hl M = snfPre l (by omega) M * M ⟨l, by omega⟩ ⟨l, by omega⟩ := by
  unfold snfPre
  rw [Fin.prod_univ_castSucc]
  rfl

/-- Equal prefix products give equal diagonals. -/
theorem snf_diag_eq_of_pre {M M' : Matrix (Fin n) (Fin n) ℤ} (hpos : ∀ l, 0 < M l l)
    (h : ∀ k (hk : k ≤ n), snfPre k hk M' = snfPre k hk M) (l : Fin n) : M' l l = M l l := by
  have e := h (l + 1) l.isLt
  rw [snfPre_succ, snfPre_succ, h l (by omega)] at e
  have hp := snfPre_pos (k := l) (by omega) hpos
  exact mul_left_cancel₀ hp.ne' e

/-- `M` is diagonal. -/
def SnfDiag (M : Matrix (Fin n) (Fin n) ℤ) : Prop := ∀ i j : Fin n, i ≠ j → M i j = 0

/-- An inverse of a unimodular matrix, with `V U = 1`. -/
theorem snf_left_inv {U : Matrix (Fin n) (Fin n) ℤ} (hU : IsUnit U.det) :
    (U.det • adjugate U) * U = 1 := by
  rw [Matrix.smul_mul, adjugate_mul, smul_smul]
  rcases Int.isUnit_iff.mp hU with h | h <;> rw [h] <;> simp

/-- **One step either makes the matrix diagonal or halves the potential.** -/
theorem snf_step_dich {H : Matrix (Fin n) (Fin n) ℤ} (hn : 0 < n) (hHf : IsHermiteForm H)
    (hdet : H.det ≠ 0) :
    (snfH Hᵀ = _root_.Matrix.diagonal (fun l => H l l)) ∨ 2 * snfPhi (snfH Hᵀ) ≤ snfPhi H := by
  have hdetT : Hᵀ.det ≠ 0 := by rwa [det_transpose]
  obtain ⟨hU, hUH, hH'f, -⟩ := snf_hnf_spec hn hdetT
  set H' := snfH Hᵀ
  set U := snfU Hᵀ
  have hN : SnfLower Hᵀ := snfLower_transpose hHf.1
  have hH' : SnfUpper H' := hH'f.1
  have hNVH : Hᵀ = (U.det • adjugate U) * H' := by
    rw [← hUH, ← Matrix.mul_assoc, snf_left_inv hU, Matrix.one_mul]
  have hpos : ∀ l, 0 < H l l := fun l => hHf.2.1 l l rfl
  have hpos' : ∀ l, 0 < H' l l := fun l => hH'f.2.1 l l rfl
  have hdvd : ∀ k (hk : k ≤ n), snfPre k hk H' ∣ snfPre k hk H := fun k hk =>
    snfPre_dvd hN hH' hNVH k hk
  by_cases hall : ∀ k (hk : k ≤ n), snfPre k hk H' = snfPre k hk H
  · left
    have heq : ∀ l, H' l l = Hᵀ l l := fun l => snf_diag_eq_of_pre hpos hall l
    have hcol := snf_col_dvd hN hH' hNVH hpos' heq
    have := snf_hnf_diag hU hUH.symm hH'f hN (fun l => hpos l) hcol
    rw [this]
    rfl
  · right
    push Not at hall
    obtain ⟨k, hk, hne⟩ := hall
    have hle : ∀ k (hk : k ≤ n), snfPre k hk H' ≤ snfPre k hk H := fun k hk =>
      Int.le_of_dvd (snfPre_pos hk hpos) (hdvd k hk)
    have hlt : snfPhi H' < snfPhi H :=
      Finset.prod_lt_prod (fun k _ => snfPre_pos _ hpos') (fun k _ => hle _ _)
        ⟨⟨k, by omega⟩, Finset.mem_univ _, lt_of_le_of_ne (hle k hk) hne⟩
    have hd : snfPhi H' ∣ snfPhi H :=
      Finset.prod_dvd_prod_of_dvd _ _ fun k _ => hdvd _ _
    have hp' : 0 < snfPhi H' := Finset.prod_pos fun k _ => snfPre_pos _ hpos'
    obtain ⟨c, hc⟩ := hd
    rw [hc] at hlt ⊢
    have hc2 : 2 ≤ c := by
      by_contra h
      have : c ≤ 1 := by omega
      nlinarith
    nlinarith

/-- **A diagonal Hermite form is fixed by a step.** -/
theorem snf_step_diag {H : Matrix (Fin n) (Fin n) ℤ} (hn : 0 < n) (hHf : IsHermiteForm H)
    (hdet : H.det ≠ 0) (hD : SnfDiag H) : snfH Hᵀ = H := by
  have hdetT : Hᵀ.det ≠ 0 := by rwa [det_transpose]
  obtain ⟨hU, hUH, hH'f, -⟩ := snf_hnf_spec hn hdetT
  have hN : SnfLower Hᵀ := snfLower_transpose hHf.1
  have hpos : ∀ l, 0 < H l l := fun l => hHf.2.1 l l rfl
  have hcol : ∀ i j, Hᵀ j j ∣ Hᵀ i j := by
    intro i j
    by_cases h : i = j
    · rw [h]
    · simp only [transpose_apply]; rw [hD j i (Ne.symm h)]; exact dvd_zero _
  rw [snf_hnf_diag hU hUH.symm hH'f hN hpos hcol]
  ext i j
  rw [diagonal_apply]
  by_cases h : i = j
  · rw [if_pos h, h]; rfl
  · rw [if_neg h, hD i j h]

theorem snfDiag_diagonal (d : Fin n → ℤ) : SnfDiag (_root_.Matrix.diagonal d) := fun i j h => by
  rw [diagonal_apply, if_neg h]

/-- The potential of a Hermite form is at most `|det|^(n+1)`. -/
theorem snfPhi_le {H : Matrix (Fin n) (Fin n) ℤ} (hHf : IsHermiteForm H) :
    snfPhi H ≤ |H.det| ^ (n + 1) := by
  have hpos : ∀ l, 0 < H l l := fun l => hHf.2.1 l l rfl
  have hdet : H.det = snfPre n le_rfl H := by
    rw [← snfLead_det_upper le_rfl hHf.1]; rfl
  have hk : ∀ k (hk : k ≤ n), snfPre k hk H ≤ |H.det| := by
    intro k hk
    rw [hdet, abs_of_pos (snfPre_pos _ hpos)]
    -- the prefix product divides the full product
    have : snfPre k hk H ∣ snfPre n le_rfl H := by
      have h := Finset.prod_dvd_prod_of_subset (Finset.univ.map (Fin.castLEEmb hk)) Finset.univ
        (fun l => H l l) (Finset.subset_univ _)
      rw [Finset.prod_map] at h
      exact h
    exact Int.le_of_dvd (snfPre_pos _ hpos) this
  unfold snfPhi
  calc ∏ k : Fin (n + 1), snfPre k _ H ≤ ∏ _k : Fin (n + 1), |H.det| :=
        Finset.prod_le_prod (fun k _ => (snfPre_pos _ hpos).le) (fun k _ => hk _ _)
    _ = |H.det| ^ (n + 1) := by simp

/-- **After enough steps the matrix is diagonal.** -/
theorem snfIt_diag (hn : 0 < n) {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.det ≠ 0) {t : ℕ}
    (ht : 1 ≤ t) (hbig : |A.det| ^ (n + 1) < 2 ^ (t - 1)) : SnfDiag (snfIt A t).H := by
  have hdetH : ∀ s, ((snfIt A s).H.det) ≠ 0 ∧ |(snfIt A s).H.det| = |A.det| := by
    intro s
    obtain ⟨e, hP, hQ, -⟩ := snfIt_inv hn hA s
    have hX : |(snfX A s).det| = |A.det| := by unfold snfX; split_ifs <;> simp
    have hP1 : |(snfIt A s).P.det| = 1 := by
      rcases Int.isUnit_iff.mp hP with h | h <;> rw [h] <;> simp
    have hQ1 : |(snfIt A s).Q.det| = 1 := by
      rcases Int.isUnit_iff.mp hQ with h | h <;> rw [h] <;> simp
    have h : |(snfIt A s).H.det| = |A.det| := by
      rw [e, det_mul, det_mul, abs_mul, abs_mul, hP1, hQ1, hX, one_mul, mul_one]
    exact ⟨fun h0 => hA (abs_eq_zero.mp (h ▸ (by rw [h0, abs_zero]))), h⟩
  have hHf : ∀ s, 1 ≤ s → IsHermiteForm (snfIt A s).H := fun s hs => (snfIt_inv hn hA s).2.2.2 hs
  -- either diagonal, or the potential has halved `s - 1` times
  have key : ∀ s, 1 ≤ s → SnfDiag (snfIt A s).H ∨
      2 ^ (s - 1) * snfPhi (snfIt A s).H ≤ snfPhi (snfIt A 1).H := by
    intro s hs
    induction s with
    | zero => omega
    | succ s ih =>
      rcases Nat.eq_zero_or_pos s with rfl | hs0
      · right; simp
      rcases ih hs0 with hD | hle
      · left
        rw [snfIt_succ]
        show SnfDiag (snfH (snfIt A s).Hᵀ)
        rw [snf_step_diag hn (hHf s hs0) (hdetH s).1 hD]
        exact hD
      · rcases snf_step_dich hn (hHf s hs0) (hdetH s).1 with hD | h2
        · left
          rw [snfIt_succ]
          show SnfDiag (snfH (snfIt A s).Hᵀ)
          rw [hD]; exact snfDiag_diagonal _
        · right
          rw [snfIt_succ]
          show 2 ^ (s + 1 - 1) * snfPhi (snfH (snfIt A s).Hᵀ) ≤ _
          have e : s + 1 - 1 = (s - 1) + 1 := by omega
          rw [e, pow_succ]
          calc 2 ^ (s - 1) * 2 * snfPhi (snfH (snfIt A s).Hᵀ)
              = 2 ^ (s - 1) * (2 * snfPhi (snfH (snfIt A s).Hᵀ)) := by ring
            _ ≤ 2 ^ (s - 1) * snfPhi (snfIt A s).H :=
                mul_le_mul_of_nonneg_left h2 (by positivity)
            _ ≤ _ := hle
  rcases key t ht with hD | hle
  · exact hD
  · exfalso
    have h1 := snfPhi_le (hHf 1 le_rfl)
    rw [(hdetH 1).2] at h1
    have hpos : 0 < snfPhi (snfIt A t).H := by
      have hp : ∀ l, 0 < (snfIt A t).H l l := fun l => (hHf t ht).2.1 l l rfl
      exact Finset.prod_pos fun k _ => snfPre_pos _ hp
    have : (2 : ℤ) ^ (t - 1) * 1 ≤ 2 ^ (t - 1) * snfPhi (snfIt A t).H :=
      mul_le_mul_of_nonneg_left (by omega) (by positivity)
    have hb : |A.det| ^ (n + 1) < (2 : ℤ) ^ (t - 1) := by exact_mod_cast hbig
    linarith

end GI.Proved
