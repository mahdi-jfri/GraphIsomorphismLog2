module

public import Workspace.Proved.SNFMath

@[expose] public section

/-!
# Sizes of the numbers in the Smith form algorithm

Fix `E ≥ 2` with `n ≤ E`, all entries of `A` below `2^E` and `|det A| < 2^E` (`SnfE`). Then:

* every Hermite form `H_t` has entries in `[0, |det A|]` (`snf_hermite_le`), so below `2^E`;
* every Hermite transform has entries below `K ≤ 2^β` with `β = 4E² + E + 2` (`hnfKn_le`);
* a product of matrices with entries below `2^a` and `2^b` has entries below `2^(a + b + E)`
  (`snfBits_mul`), so after `t` alternation steps `P, Q` have entries below `2^(1 + t (β + E))`
  (`snfIt_bits`);
* in a pair step, `L` and `R` have entries below `2^(β + E)` (`snfL_bits`, `snfR_bits`), so each
  pair step adds `β + 2E` bits (`snfFix_bits`).

The bit bounds add up along the products, which is enough since the number of steps is
polynomial.
-/

namespace GI.Proved

open _root_.Matrix GI.Cited GI.Impl

variable {n : ℕ}

/-- All entries are below `2^B` in absolute value. -/
def SnfBits (B : ℕ) (M : _root_.Matrix (Fin n) (Fin n) ℤ) : Prop := ∀ i j, (M i j).natAbs < 2 ^ B

theorem snfBits_mono {a b : ℕ} (h : a ≤ b) {M : _root_.Matrix (Fin n) (Fin n) ℤ} (hM : SnfBits a M) :
    SnfBits b M := fun i j => lt_of_lt_of_le (hM i j) (Nat.pow_le_pow_right (by decide) h)

theorem snfBits_transpose {a : ℕ} {M : _root_.Matrix (Fin n) (Fin n) ℤ} (hM : SnfBits a M) :
    SnfBits a Mᵀ := fun i j => hM j i

theorem snfBits_mul {a b c : ℕ} {X Y : _root_.Matrix (Fin n) (Fin n) ℤ} (hX : SnfBits a X)
    (hY : SnfBits b Y) (hn : n < 2 ^ c) : SnfBits (a + b + c) (X * Y) := by
  intro i j
  rw [mul_apply]
  have h1 : (∑ k, X i k * Y k j).natAbs ≤ ∑ k, (X i k).natAbs * (Y k j).natAbs := by
    refine (Int.natAbs_sum_le _ _).trans (le_of_eq ?_)
    simp [Int.natAbs_mul]
  have h2 : ∑ k, (X i k).natAbs * (Y k j).natAbs ≤ ∑ _k : Fin n, 2 ^ a * 2 ^ b :=
    Finset.sum_le_sum fun k _ => Nat.mul_le_mul (hX i k).le (hY k j).le
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h2
  have h3 : n * (2 ^ a * 2 ^ b) < 2 ^ c * (2 ^ a * 2 ^ b) :=
    Nat.mul_lt_mul_of_pos_right hn (by positivity)
  have e : 2 ^ (a + b + c) = 2 ^ c * (2 ^ a * 2 ^ b) := by rw [pow_add, pow_add]; ring
  omega

theorem snfBits_one {n : ℕ} : SnfBits 1 (1 : _root_.Matrix (Fin n) (Fin n) ℤ) := by
  intro i j
  rw [one_apply]; split_ifs <;> simp

/-- **Entries of a square Hermite form are at most `|det|`.** -/
theorem snf_hermite_le {H : _root_.Matrix (Fin n) (Fin n) ℤ} (hHf : IsHermiteForm H) (i j : Fin n) :
    0 ≤ H i j ∧ H i j ≤ |H.det| := by
  have hpos : ∀ l, 0 < H l l := fun l => hHf.2.1 l l rfl
  have hdet : H.det = ∏ l, H l l := det_of_upperTriangular fun i j hij => hHf.1 i j hij
  have hdp : 0 < H.det := by rw [hdet]; exact Finset.prod_pos fun l _ => hpos l
  have hdiag : ∀ l, H l l ≤ |H.det| := by
    intro l
    rw [abs_of_pos hdp]
    exact Int.le_of_dvd hdp (hdet ▸ Finset.dvd_prod_of_mem _ (Finset.mem_univ l))
  rcases lt_trichotomy (i : ℕ) j with h | h | h
  · obtain ⟨h0, h1⟩ := hHf.2.2 i j j h rfl
    exact ⟨h0, h1.le.trans (hdiag j)⟩
  · rw [Fin.ext h]; exact ⟨(hpos j).le, hdiag j⟩
  · rw [hHf.1 i j h]; exact ⟨le_rfl, abs_nonneg _⟩

/-- The hypotheses on the size parameter `E`. -/
structure SnfE (E : ℕ) (A : _root_.Matrix (Fin n) (Fin n) ℤ) : Prop where
  two_le : 2 ≤ E
  n_le : n ≤ E
  entries : SnfBits E A
  det : A.det.natAbs < 2 ^ E

/-- The bit bound of a Hermite transform. -/
def snfBeta (E : ℕ) : ℕ := 4 * E * E + E + 2

theorem snf_le_beta (E : ℕ) : E ≤ snfBeta E := by unfold snfBeta; nlinarith

theorem snfBits_of_hermite {E : ℕ} {H : _root_.Matrix (Fin n) (Fin n) ℤ} (hHf : IsHermiteForm H)
    (hd : H.det.natAbs < 2 ^ E) : SnfBits E H := by
  intro i j
  obtain ⟨h0, h1⟩ := snf_hermite_le hHf i j
  have : (H i j).natAbs ≤ H.det.natAbs := by
    have : ((H i j).natAbs : ℤ) ≤ (H.det.natAbs : ℤ) := by
      rw [Int.natCast_natAbs, Int.natCast_natAbs, abs_of_nonneg h0]; exact h1
    exact_mod_cast this
  omega

/-- The transform of the Hermite program on a matrix with small entries. -/
theorem snfU_bits {E : ℕ} {M : _root_.Matrix (Fin n) (Fin n) ℤ} (hn : 0 < n) (hM : M.det ≠ 0)
    (hnE : n ≤ E) (hME : SnfBits E M) : SnfBits (snfBeta E) (snfU M) := by
  intro i j
  have h1 := (snf_hnf_spec hn hM).2.2.2 i j
  rw [← hnfKn_eq] at h1
  have h2 := hnfKn_le M hnE le_rfl hME
  have h3 : ((snfU M i j).natAbs : ℤ) < (hnfKn M : ℤ) := by rwa [Int.natCast_natAbs]
  have h4 : (snfU M i j).natAbs < hnfKn M := by exact_mod_cast h3
  unfold snfBeta
  omega

/-- The absolute value of the determinant along the alternation. -/
theorem snfIt_det (hn : 0 < n) {A : _root_.Matrix (Fin n) (Fin n) ℤ} (hA : A.det ≠ 0) (t : ℕ) :
    (snfIt A t).H.det.natAbs = A.det.natAbs := by
  obtain ⟨e, hP, hQ, -⟩ := snfIt_inv hn hA t
  have hX : (snfX A t).det.natAbs = A.det.natAbs := by unfold snfX; split_ifs <;> simp
  rw [e, det_mul, det_mul, Int.natAbs_mul, Int.natAbs_mul, hX, Int.isUnit_iff_natAbs_eq.mp hP,
    Int.isUnit_iff_natAbs_eq.mp hQ, one_mul, mul_one]

/-- **The entries of the alternation.** -/
theorem snfIt_bits (hn : 0 < n) {A : _root_.Matrix (Fin n) (Fin n) ℤ} (hA : A.det ≠ 0) {E : ℕ}
    (hE : SnfE E A) (t : ℕ) :
    SnfBits E (snfIt A t).H ∧ SnfBits (1 + t * (snfBeta E + E)) (snfIt A t).P ∧
      SnfBits (1 + t * (snfBeta E + E)) (snfIt A t).Q := by
  have hHE : ∀ s, SnfBits E (snfIt A s).H := by
    intro s
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · exact hE.entries
    · exact snfBits_of_hermite ((snfIt_inv hn hA s).2.2.2 hs) (by rw [snfIt_det hn hA]; exact hE.det)
  have hnE : n < 2 ^ E := lt_of_le_of_lt hE.n_le Nat.lt_two_pow_self
  induction t with
  | zero => exact ⟨hHE 0, by simpa [snfIt] using snfBits_one, by simpa [snfIt] using snfBits_one⟩
  | succ t ih =>
    obtain ⟨-, hP, hQ⟩ := ih
    refine ⟨hHE _, ?_, ?_⟩
    · rw [snfIt_succ]
      show SnfBits _ (snfU (snfIt A t).Hᵀ * (snfIt A t).Qᵀ)
      have hdet : (snfIt A t).Hᵀ.det ≠ 0 := by
        rw [det_transpose]; intro h0
        have := snfIt_det hn hA t; rw [h0] at this; simp at this; exact hA (by omega)
      have hU := snfU_bits hn hdet hE.n_le (snfBits_transpose (hHE t))
      refine snfBits_mono ?_ (snfBits_mul hU (snfBits_transpose hQ) hnE)
      nlinarith
    · rw [snfIt_succ]
      exact snfBits_mono (by nlinarith) (snfBits_transpose hP)

/-! ### Pair steps -/

theorem snfM2_bits {a b : ℤ} {e : ℕ} (ha : a.natAbs < 2 ^ e) (hb : b.natAbs < 2 ^ e) :
    ∀ i j, (snfM2 a b i j).natAbs < 2 ^ e := by
  intro i j; unfold snfM2; split_ifs <;> assumption

theorem snf_xy_bits {E : ℕ} (hE2 : 2 ≤ E) {a b : ℤ} (ha : 0 < a) (hb : 0 < b)
    (haE : a.natAbs < 2 ^ E) (hbE : b.natAbs < 2 ^ E) :
    (snfBx a b).natAbs < 2 ^ snfBeta E ∧ (snfBy a b).natAbs < 2 ^ snfBeta E := by
  obtain ⟨-, -, -, -, hx, hy⟩ := snf_bezout ha hb
  rw [← hnfKn_eq] at hx hy
  have h2 := hnfKn_le (snfM2 a b) (W := E) hE2 (by norm_num) (snfM2_bits haE hbE)
  have hx' : (snfBx a b).natAbs < hnfKn (snfM2 a b) := by
    have : ((snfBx a b).natAbs : ℤ) < (hnfKn (snfM2 a b) : ℤ) := by rwa [Int.natCast_natAbs]
    exact_mod_cast this
  have hy' : (snfBy a b).natAbs < hnfKn (snfM2 a b) := by
    have : ((snfBy a b).natAbs : ℤ) < (hnfKn (snfM2 a b) : ℤ) := by rwa [Int.natCast_natAbs]
    exact_mod_cast this
  unfold snfBeta
  constructor <;> omega

theorem snfEmb_bits {B : ℕ} {p q : Fin n} (hpq : p ≠ q) {α β γ δ : ℤ} (h1 : α.natAbs < 2 ^ B)
    (h2 : β.natAbs < 2 ^ B) (h3 : γ.natAbs < 2 ^ B) (h4 : δ.natAbs < 2 ^ B) (hB : 1 ≤ B) :
    SnfBits B (snfEmb (n := n) p q α β γ δ) := by
  have h0 : 1 < 2 ^ B := Nat.one_lt_two_pow (by omega)
  intro i j
  unfold snfEmb
  split_ifs <;> first | omega | (simp; omega) | simp

/-- The diagonal entries of a positive diagonal matrix, through quotients by a divisor. -/
theorem snf_quot_le {a g : ℤ} (ha : 0 < a) (hg : 0 < g) : (a / g).natAbs ≤ a.natAbs := by
  have h1 : 0 ≤ a / g := Int.ediv_nonneg ha.le hg.le
  have h2 : a / g ≤ a := Int.ediv_le_self _ ha.le
  omega

theorem snfLR_bits {E : ℕ} (hE2 : 2 ≤ E) {H : _root_.Matrix (Fin n) (Fin n) ℤ} (hpos : ∀ l, 0 < H l l)
    (hHE : SnfBits E H) {p q : Fin n} (hpq : p ≠ q) :
    SnfBits (snfBeta E + E) (snfL H p q) ∧ SnfBits (snfBeta E + E) (snfR H p q) := by
  obtain ⟨hx, hy⟩ := snf_xy_bits hE2 (hpos p) (hpos q) (hHE p p) (hHE q q)
  obtain ⟨-, hg, -, -, -⟩ := snf_bezout (hpos p) (hpos q)
  have hqa := snf_quot_le (hpos p) hg
  have hqb := snf_quot_le (hpos q) hg
  have hbE := snf_le_beta E
  have hpE : 2 ^ snfBeta E ≤ 2 ^ (snfBeta E + E) := Nat.pow_le_pow_right (by decide) (by omega)
  have hEE : 2 ^ E ≤ 2 ^ (snfBeta E + E) := Nat.pow_le_pow_right (by decide) (by omega)
  have hp := hHE p p
  have hq := hHE q q
  have e : 2 ^ (snfBeta E + E) = 2 ^ snfBeta E * 2 ^ E := pow_add _ _ _
  constructor
  · refine snfEmb_bits hpq (by omega) (by omega) ?_ (by omega) (by omega)
    rw [Int.natAbs_neg]; omega
  · have hm1 : (snfBy (H p p) (H q q) * (H q q / snfBg (H p p) (H q q))).natAbs <
        2 ^ (snfBeta E + E) := by
      rw [Int.natAbs_mul, e]
      exact Nat.mul_lt_mul_of_lt_of_le hy (by omega) (by positivity)
    have hm2 : (snfBx (H p p) (H q q) * (H p p / snfBg (H p p) (H q q))).natAbs <
        2 ^ (snfBeta E + E) := by
      rw [Int.natAbs_mul, e]
      exact Nat.mul_lt_mul_of_lt_of_le hx (by omega) (by positivity)
    refine snfEmb_bits hpq (by simp; omega) (by rw [Int.natAbs_neg]; exact hm1) (by simp; omega)
      hm2 (by omega)

/-- The entries of a positive diagonal matrix with `|det| = d` are at most `d`. -/
theorem snf_diag_le {D : _root_.Matrix (Fin n) (Fin n) ℤ} (hD : SnfDiag D) (hpos : ∀ l, 0 < D l l)
    (i j : Fin n) : (D i j).natAbs ≤ D.det.natAbs := by
  have hdet : D.det = ∏ l, D l l := det_of_upperTriangular fun i j hij => hD i j (by
    intro e; rw [e] at hij; exact lt_irrefl _ hij)
  by_cases h : i = j
  · subst h
    have hdp : 0 < D.det := by rw [hdet]; exact Finset.prod_pos fun l _ => hpos l
    have := Int.le_of_dvd hdp (hdet ▸ Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
    have := hpos i
    omega
  · rw [hD i j h]; simp

/-- **The entries of the pair loop.** -/
theorem snfFix_bits {E B : ℕ} (hE2 : 2 ≤ E) (hnE : n ≤ E) {A : _root_.Matrix (Fin n) (Fin n) ℤ}
    {s : SnfSt n} (hrel : s.H = s.P * A * s.Q) (hP : IsUnit s.P.det) (hQ : IsUnit s.Q.det)
    (hD : SnfDiag s.H) (hpos : ∀ l, 0 < s.H l l) (hd : A.det.natAbs < 2 ^ E)
    (hPB : SnfBits B s.P) (hQB : SnfBits B s.Q) (k : ℕ) (hk : k ≤ n * n) :
    SnfBits E (snfFix s k).H ∧ SnfBits (B + k * (snfBeta E + 2 * E)) (snfFix s k).P ∧
      SnfBits (B + k * (snfBeta E + 2 * E)) (snfFix s k).Q := by
  have hn2 : n < 2 ^ E := lt_of_le_of_lt hnE Nat.lt_two_pow_self
  have hHE : ∀ k, k ≤ n * n → SnfBits E (snfFix s k).H := by
    intro k hk
    obtain ⟨e, hP', hQ'⟩ := snfFix_rel hrel hP hQ hD hpos k hk
    obtain ⟨hD', hpos', -, -⟩ := snfFix_inv hD hpos k hk
    have hdet : (snfFix s k).H.det.natAbs = A.det.natAbs := by
      rw [e, det_mul, det_mul, Int.natAbs_mul, Int.natAbs_mul, Int.isUnit_iff_natAbs_eq.mp hP',
        Int.isUnit_iff_natAbs_eq.mp hQ', one_mul, mul_one]
    intro i j
    have := snf_diag_le hD' hpos' i j
    omega
  induction k with
  | zero => exact ⟨hHE 0 hk, by simpa [snfFix] using hPB, by simpa [snfFix] using hQB⟩
  | succ k ih =>
    obtain ⟨-, hP1, hQ1⟩ := ih (by omega)
    obtain ⟨-, hpos', -, -⟩ := snfFix_inv hD hpos k (by omega)
    refine ⟨hHE _ hk, ?_⟩
    show SnfBits _ (snfFixK (snfFix s k) k).P ∧ SnfBits _ (snfFixK (snfFix s k) k).Q
    unfold snfFixK
    rw [dif_pos (show k < n * n by omega)]
    unfold snfPair
    have hmono : B + k * (snfBeta E + 2 * E) ≤ B + (k + 1) * (snfBeta E + 2 * E) := by nlinarith
    split_ifs with hpq
    · obtain ⟨hL, hR⟩ := snfLR_bits hE2 hpos' (hHE k (by omega)) (ne_of_lt hpq)
      constructor
      · refine snfBits_mono ?_ (snfBits_mul hL hP1 hn2)
        nlinarith
      · refine snfBits_mono ?_ (snfBits_mul hQ1 hR hn2)
        nlinarith
    · exact ⟨snfBits_mono hmono hP1, snfBits_mono hmono hQ1⟩

end GI.Proved
