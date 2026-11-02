import Workspace.Cited.AlgoTerminal
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Triangular matrices under a Hermite step (Smith form)

Let `N` be lower triangular and `H` upper triangular with `N = V H` for an integer matrix `V`.
Since `H` is upper triangular, the leading `k × k` blocks satisfy `N_k = V_k H_k`
(`snfLead_mul`). Taking determinants, the prefix products of the diagonal of `H` divide those
of `N` (`snfPre_dvd`). If the diagonals agree, then `det V_k = 1` and `H_k = adj(V_k) N_k`;
reading entry `(i, j)` with `k = j + 1` shows `N_jj ∣ N_ij` (`snf_col_dvd`). Finally, if
`N_jj ∣ N_ij` for all `i, j` and `H = U N` is a Hermite form with `U` unimodular, then every
entry of column `l` of `H` is a multiple of `N_ll`, the determinants force `H_ll = N_ll`, and
the reduction condition forces `H` to be diagonal (`snf_hnf_diag`).

These three facts drive the alternation of Hermite forms in `Proved/SNFAlt.lean`.
-/

namespace GI.Proved

open Matrix GI.Cited

variable {n : ℕ}

/-- `M` is upper triangular. -/
def SnfUpper (M : Matrix (Fin n) (Fin n) ℤ) : Prop := ∀ i j : Fin n, (j : ℕ) < i → M i j = 0

/-- `M` is lower triangular. -/
def SnfLower (M : Matrix (Fin n) (Fin n) ℤ) : Prop := ∀ i j : Fin n, (i : ℕ) < j → M i j = 0

/-- The leading `k × k` block. -/
def snfLead (k : ℕ) (hk : k ≤ n) (M : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin k) (Fin k) ℤ :=
  M.submatrix (Fin.castLE hk) (Fin.castLE hk)

/-- The product of the first `k` diagonal entries. -/
def snfPre (k : ℕ) (hk : k ≤ n) (M : Matrix (Fin n) (Fin n) ℤ) : ℤ :=
  ∏ l : Fin k, M (Fin.castLE hk l) (Fin.castLE hk l)

theorem snfLower_transpose {M : Matrix (Fin n) (Fin n) ℤ} (h : SnfUpper M) : SnfLower Mᵀ :=
  fun i j hij => h j i hij

theorem snfUpper_of_hermite {M : Matrix (Fin n) (Fin n) ℤ} (h : IsHermiteForm M) : SnfUpper M :=
  h.1

/-- Entry `(i, c)` of `V H` with `c < k` only uses the first `k` rows of `H`. -/
theorem snf_trunc {k : ℕ} (hk : k ≤ n) (V H : Matrix (Fin n) (Fin n) ℤ) (hH : SnfUpper H)
    (i c : Fin n) (hc : (c : ℕ) < k) :
    (V * H) i c = ∑ m : Fin k, V i (Fin.castLE hk m) * H (Fin.castLE hk m) c := by
  rw [mul_apply, ← Finset.sum_subset (Finset.subset_univ (Finset.univ.map (Fin.castLEEmb hk))),
    Finset.sum_map]
  · rfl
  · intro m _ hm
    have hkm : k ≤ (m : ℕ) := by
      by_contra h
      exact hm (Finset.mem_map.mpr ⟨⟨m, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    rw [hH m c (by omega), mul_zero]

theorem snfLead_mul {k : ℕ} (hk : k ≤ n) (V H : Matrix (Fin n) (Fin n) ℤ) (hH : SnfUpper H) :
    snfLead k hk (V * H) = snfLead k hk V * snfLead k hk H := by
  ext i j
  simp only [snfLead, submatrix_apply]
  rw [snf_trunc hk V H hH _ _ (by simp), mul_apply]
  rfl

theorem snfLead_det_upper {k : ℕ} (hk : k ≤ n) {H : Matrix (Fin n) (Fin n) ℤ} (hH : SnfUpper H) :
    (snfLead k hk H).det = snfPre k hk H := by
  rw [det_of_upperTriangular]
  · rfl
  · intro i j hij
    exact hH _ _ hij

theorem snfLead_det_lower {k : ℕ} (hk : k ≤ n) {N : Matrix (Fin n) (Fin n) ℤ} (hN : SnfLower N) :
    (snfLead k hk N).det = snfPre k hk N := by
  rw [← det_transpose, det_of_upperTriangular]
  · rfl
  · intro i j hij
    exact hN _ _ hij

/-- **Prefix products divide.** -/
theorem snfPre_dvd {N V H : Matrix (Fin n) (Fin n) ℤ} (hN : SnfLower N) (hH : SnfUpper H)
    (hNVH : N = V * H) (k : ℕ) (hk : k ≤ n) : snfPre k hk H ∣ snfPre k hk N := by
  have e := congrArg det (snfLead_mul hk V H hH)
  rw [← hNVH, det_mul] at e
  rw [← snfLead_det_upper hk hH, ← snfLead_det_lower hk hN, e]
  exact Dvd.intro_left _ rfl

theorem snfPre_pos {k : ℕ} (hk : k ≤ n) {M : Matrix (Fin n) (Fin n) ℤ} (h : ∀ l, 0 < M l l) :
    0 < snfPre k hk M :=
  Finset.prod_pos fun _ _ => h _

/-- **Equal diagonals give divisible columns.** -/
theorem snf_col_dvd {N V H : Matrix (Fin n) (Fin n) ℤ} (hN : SnfLower N) (hH : SnfUpper H)
    (hNVH : N = V * H) (hpos : ∀ l, 0 < H l l) (heq : ∀ l, H l l = N l l) (i j : Fin n) :
    N j j ∣ N i j := by
  rcases lt_trichotomy (i : ℕ) j with hij | hij | hij
  · rw [hN i j hij]; exact dvd_zero _
  · rw [Fin.ext hij]
  have hk : (j : ℕ) + 1 ≤ n := j.isLt
  set k := (j : ℕ) + 1 with hkdef
  set Vk := snfLead k hk V
  have hmul := snfLead_mul hk V H hH
  rw [← hNVH] at hmul
  -- `det V_k = 1`
  have hpre : snfPre k hk H = snfPre k hk N := by
    unfold snfPre; exact Finset.prod_congr rfl fun l _ => heq _
  have hdet : Vk.det = 1 := by
    have e := congrArg det hmul
    rw [det_mul, snfLead_det_upper hk hH, snfLead_det_lower hk hN, hpre] at e
    have hp := snfPre_pos hk (M := N) fun l => (heq l) ▸ hpos l
    have : snfPre k hk N * 1 = snfPre k hk N * Vk.det := by rw [mul_one]; exact e.trans (mul_comm _ _)
    exact (mul_left_cancel₀ hp.ne' this).symm
  -- `H_k = adj(V_k) N_k`
  have hHk : snfLead k hk H = adjugate Vk * snfLead k hk N := by
    rw [hmul, ← Matrix.mul_assoc, adjugate_mul, hdet, one_smul, Matrix.one_mul]
  set j' : Fin k := ⟨j, by omega⟩
  have hj' : Fin.castLE hk j' = j := Fin.ext rfl
  set r : Fin k → ℤ := fun m => V i (Fin.castLE hk m)
  have h1 : N i j = (r ᵥ* snfLead k hk H) j' := by
    rw [hNVH, snf_trunc hk V H hH i j (by omega)]
    simp only [vecMul, dotProduct, snfLead, submatrix_apply, hj', r]
  rw [hHk, ← vecMul_vecMul] at h1
  have h2 : (r ᵥ* adjugate Vk ᵥ* snfLead k hk N) j' =
      (r ᵥ* adjugate Vk) j' * N j j := by
    simp only [vecMul, dotProduct]
    rw [Finset.sum_eq_single j']
    · simp only [snfLead, submatrix_apply, hj']
    · intro l _ hl
      have hl' : (l : ℕ) < j := by
        have := l.isLt
        have : (l : ℕ) ≠ j := fun h => hl (Fin.ext h)
        omega
      simp only [snfLead, submatrix_apply, hj']
      rw [hN _ _ (by simpa using hl'), mul_zero]
    · simp
  rw [h1, h2]
  exact Dvd.intro_left _ rfl

/-- If `a ≤ b` pointwise, all positive, with equal products, then `a = b`. -/
theorem snf_eq_of_prod_eq {a b : Fin n → ℤ} (ha : ∀ l, 0 < a l) (hab : ∀ l, a l ≤ b l)
    (hp : ∏ l, a l = ∏ l, b l) (l : Fin n) : a l = b l := by
  by_contra hne
  have hlt : ∏ l, a l < ∏ l, b l :=
    Finset.prod_lt_prod (fun l _ => ha l) (fun i _ => hab i)
      ⟨l, Finset.mem_univ _, lt_of_le_of_ne (hab l) hne⟩
  omega

/-- **A Hermite form of a matrix with divisible columns is diagonal.** -/
theorem snf_hnf_diag {N U H : Matrix (Fin n) (Fin n) ℤ} (hU : IsUnit U.det) (hUN : H = U * N)
    (hHf : IsHermiteForm H) (hN : SnfLower N) (hpos : ∀ l, 0 < N l l)
    (hdvd : ∀ i j, N j j ∣ N i j) : H = diagonal (fun l => N l l) := by
  obtain ⟨hlow, hdiag, hred⟩ := hHf
  have hcol : ∀ i l, N l l ∣ H i l := by
    intro i l
    rw [hUN, mul_apply]
    exact Finset.dvd_sum fun m _ => Dvd.dvd.mul_left (hdvd m l) _
  have hHpos : ∀ l, 0 < H l l := fun l => hdiag l l rfl
  have hle : ∀ l, N l l ≤ H l l := fun l => Int.le_of_dvd (hHpos l) (hcol l l)
  have hdetH : H.det = ∏ l, H l l := det_of_upperTriangular fun i j hij => hlow i j hij
  have hdetN : N.det = ∏ l, N l l := by
    rw [← det_transpose, det_of_upperTriangular]
    · rfl
    · intro i j hij; exact hN j i hij
  have hu : U.det = 1 ∨ U.det = -1 := Int.isUnit_iff.mp hU
  have hprod : ∏ l, N l l = ∏ l, H l l := by
    have e := congrArg det hUN
    rw [det_mul, hdetH, hdetN] at e
    have h1 : 0 < ∏ l, H l l := Finset.prod_pos fun l _ => hHpos l
    have h2 : 0 < ∏ l, N l l := Finset.prod_pos fun l _ => hpos l
    rcases hu with h | h
    · rw [h, one_mul] at e; exact e.symm
    · rw [h] at e; nlinarith
  have heq : ∀ l, H l l = N l l := fun l => (snf_eq_of_prod_eq hpos hle hprod l).symm
  ext i l
  rw [diagonal_apply]
  rcases lt_trichotomy (i : ℕ) l with hil | hil | hil
  · have hne : i ≠ l := fun h => by rw [h] at hil; exact lt_irrefl _ hil
    rw [if_neg hne]
    obtain ⟨h0, h1⟩ := hred i l l hil rfl
    rw [heq l] at h1
    exact Int.eq_zero_of_dvd_of_nonneg_of_lt h0 h1 (hcol i l)
  · rw [Fin.ext hil, if_pos rfl, heq]
  · have hne : i ≠ l := fun h => by rw [h] at hil; exact lt_irrefl _ hil
    rw [if_neg hne]
    exact hlow i l hil

end GI.Proved
