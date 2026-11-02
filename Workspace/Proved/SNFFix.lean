import Workspace.Proved.SNFEmb

/-!
# From a diagonal matrix to the Smith form (Smith form)

This is the second half of algorithm SNF of [KB79, Section 3]: the diagonal is made a divisor
chain. For the pairs `p < q` in lexicographic order, with `a = D_pp` and `b = D_qq`, the Hermite
program on the column `[a; b]` gives `x, y` and `g` with `x a + y b = g`, `g ∣ a`, `g ∣ b`
(`snf_bezout`). With `a = g a'` and `b = g b'` we have `x a' + y b' = 1`, so the matrices

  `L = [[x, y], [-b', a']]`,  `R = [[1, -y b'], [1, x a']]`

(on rows and columns `p, q`, `snfL`, `snfR`) have determinant `1`, and `L D R` is `D` with
`D_pp, D_qq` replaced by `g, a' b` (`snfPair_H`). The loop runs over `k < n²` with
`p = k / n`, `q = k % n` (`snfFix`). After the pairs `(p, q')` with `q' < q` and all pairs of
smaller first index, `D_ii` divides `D_jj` for `i < p < ... `, `i < j`, and `D_pp` divides
`D_jj` for `p < j < q` (`SnfFixInv`). This is the usual argument: `gcd` and `lcm` of two
multiples of `D_ii` are multiples of `D_ii`.
-/

namespace GI.Proved

open _root_.Matrix GI.Cited GI.Impl

variable {n : ℕ}

/-! ### Bezout coefficients from the Hermite program -/

/-- The column `[a; b]`. -/
def snfM2 (a b : ℤ) : _root_.Matrix (Fin 2) (Fin 1) ℤ := fun i _ => if (i : ℕ) = 0 then a else b

/-- The transform of the Hermite program on `[a; b]`. -/
def snfBU (a b : ℤ) : _root_.Matrix (Fin 2) (Fin 2) ℤ :=
  hnfRectU (snfM2 a b) (hnfTn (snfM2 a b) : ℤ)

/-- The Hermite form of the Hermite program on `[a; b]`. -/
def snfBH (a b : ℤ) : _root_.Matrix (Fin 2) (Fin 1) ℤ :=
  hnfRectH (snfM2 a b) (by norm_num) (hnfTn (snfM2 a b) : ℤ)

def snfBx (a b : ℤ) : ℤ := snfBU a b 0 0
def snfBy (a b : ℤ) : ℤ := snfBU a b 0 1
def snfBg (a b : ℤ) : ℤ := snfBH a b 0 0

theorem snfM2_inj {a b : ℤ} (ha : a ≠ 0) : Function.Injective (snfM2 a b).mulVec := by
  intro u v h
  have h0 := congrFun h 0
  simp only [mulVec, dotProduct, snfM2, Fin.sum_univ_one, Fin.isValue, Fin.coe_ofNat_eq_mod,
    Nat.zero_mod, if_pos] at h0
  have : u 0 = v 0 := mul_left_cancel₀ ha h0
  funext j
  rw [Subsingleton.elim j 0]
  exact this

/-- **Bezout coefficients.** -/
theorem snf_bezout {a b : ℤ} (ha : 0 < a) (hb : 0 < b) :
    snfBx a b * a + snfBy a b * b = snfBg a b ∧ 0 < snfBg a b ∧ snfBg a b ∣ a ∧
      snfBg a b ∣ b ∧ |snfBx a b| < hnfK 2 (hnfTn (snfM2 a b) : ℤ) ∧
      |snfBy a b| < hnfK 2 (hnfTn (snfM2 a b) : ℤ) := by
  have hT1 : (1 : ℤ) ≤ (hnfTn (snfM2 a b) : ℤ) := by unfold hnfTn; omega
  obtain ⟨hU, hUA, hHf, hUb, -⟩ := hnfRect_spec (snfM2 a b) (snfM2_inj ha.ne') (by norm_num)
    (by norm_num) hT1 (hnf_abs_le_Tn _)
  have e00 := congrFun (congrFun hUA 0) 0
  have e10 := congrFun (congrFun hUA 1) 0
  rw [mul_apply, Fin.sum_univ_two] at e00 e10
  have hm0 : snfM2 a b 0 0 = a := rfl
  have hm1 : snfM2 a b 1 0 = b := rfl
  rw [hm0, hm1] at e00 e10
  have hg : 0 < snfBH a b 0 0 := hHf.2.1 0 0 rfl
  have h10 : snfBH a b 1 0 = 0 := hHf.1 1 0 (by norm_num)
  -- `[a; b] = V H` with `V U = 1`
  have hV := snf_left_inv hU
  set V := (snfBU a b).det • adjugate (snfBU a b)
  have hMVH : snfM2 a b = V * snfBH a b := by
    rw [snfBH, ← hUA, ← Matrix.mul_assoc]
    show snfM2 a b = (V * snfBU a b) * snfM2 a b
    rw [show V * snfBU a b = 1 from hV, Matrix.one_mul]
  have f0 := congrFun (congrFun hMVH 0) 0
  have f1 := congrFun (congrFun hMVH 1) 0
  rw [mul_apply, Fin.sum_univ_two, h10, mul_zero, add_zero, hm0] at f0
  rw [mul_apply, Fin.sum_univ_two, h10, mul_zero, add_zero, hm1] at f1
  refine ⟨e00, hg, ⟨V 0 0, by rw [mul_comm]; exact f0⟩, ⟨V 1 0, by rw [mul_comm]; exact f1⟩, hUb 0 0, hUb 0 1⟩

/-! ### The pair step -/

/-- The left matrix of the pair step. -/
def snfL (H : _root_.Matrix (Fin n) (Fin n) ℤ) (p q : Fin n) : _root_.Matrix (Fin n) (Fin n) ℤ :=
  snfEmb p q (snfBx (H p p) (H q q)) (snfBy (H p p) (H q q))
    (-(H q q / snfBg (H p p) (H q q))) (H p p / snfBg (H p p) (H q q))

/-- The right matrix of the pair step. -/
def snfR (H : _root_.Matrix (Fin n) (Fin n) ℤ) (p q : Fin n) : _root_.Matrix (Fin n) (Fin n) ℤ :=
  snfEmb p q 1 (-(snfBy (H p p) (H q q) * (H q q / snfBg (H p p) (H q q)))) 1
    (snfBx (H p p) (H q q) * (H p p / snfBg (H p p) (H q q)))

/-- The pair step on the state. -/
def snfPair (s : SnfSt n) (p q : Fin n) : SnfSt n :=
  if p < q then ⟨snfL s.H p q * s.H * snfR s.H p q, snfL s.H p q * s.P, s.Q * snfR s.H p q⟩
  else s

/-- The diagonal after a pair step. -/
def snfPairD (H : _root_.Matrix (Fin n) (Fin n) ℤ) (p q : Fin n) : _root_.Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if i = j then
    (if i = p then snfBg (H p p) (H q q)
      else if i = q then H p p / snfBg (H p p) (H q q) * H q q else H i i)
    else 0

theorem snfPair_facts {H : _root_.Matrix (Fin n) (Fin n) ℤ} (hpos : ∀ l, 0 < H l l) (p q : Fin n) :
    ∃ a' b' : ℤ, H p p = snfBg (H p p) (H q q) * a' ∧ H q q = snfBg (H p p) (H q q) * b' ∧
      0 < snfBg (H p p) (H q q) ∧ 0 < a' ∧ 0 < b' ∧
      snfBx (H p p) (H q q) * a' + snfBy (H p p) (H q q) * b' = 1 ∧
      H p p / snfBg (H p p) (H q q) = a' ∧ H q q / snfBg (H p p) (H q q) = b' := by
  obtain ⟨e, hg, ⟨a', ha'⟩, ⟨b', hb'⟩, -, -⟩ := snf_bezout (hpos p) (hpos q)
  set g := snfBg (H p p) (H q q)
  set x := snfBx (H p p) (H q q)
  set y := snfBy (H p p) (H q q)
  have hap : 0 < a' := by
    have := hpos p; rw [ha'] at this; exact pos_of_mul_pos_right this hg.le
  have hbp : 0 < b' := by
    have := hpos q; rw [hb'] at this; exact pos_of_mul_pos_right this hg.le
  have e1 : x * a' + y * b' = 1 := by
    have e' := e
    rw [ha', hb'] at e'
    have : g * (x * a' + y * b') = g * 1 := by linear_combination e'
    exact mul_left_cancel₀ hg.ne' this
  refine ⟨a', b', ha', hb', hg, hap, hbp, e1, ?_, ?_⟩
  · rw [ha', Int.mul_ediv_cancel_left _ hg.ne']
  · rw [hb', Int.mul_ediv_cancel_left _ hg.ne']

/-- **The pair step on the diagonal.** -/
theorem snfPair_H {H : _root_.Matrix (Fin n) (Fin n) ℤ} (hD : SnfDiag H) (hpos : ∀ l, 0 < H l l)
    {p q : Fin n} (hpq : p ≠ q) : snfL H p q * H * snfR H p q = snfPairD H p q := by
  obtain ⟨a', b', ha, hb, hg, -, -, e1, ea, eb⟩ := snfPair_facts hpos p q
  have hqp : q ≠ p := Ne.symm hpq
  ext i j
  simp only [snfL, snfR, snfPairD, snfEmb_right hpq, snfEmb_left hpq, ea, eb]
  set g := snfBg (H p p) (H q q)
  set x := snfBx (H p p) (H q q)
  set y := snfBy (H p p) (H q q)
  have hpq0 : H p q = 0 := hD p q hpq
  have hqp0 : H q p = 0 := hD q p hqp
  by_cases hip : i = p
  · subst hip
    by_cases hjp : j = i
    · subst hjp; simp only [↓reduceIte, hpq0, hqp0, if_pos rfl, hpq0, mul_zero, add_zero, zero_add]
      rw [hb, ha]; linear_combination g * e1
    by_cases hjq : j = q
    · subst hjq; simp only [↓reduceIte, hpq0, hqp0, if_pos rfl, if_neg hjp, if_neg hpq, hpq0, mul_zero, add_zero,
        zero_add]
      rw [ha, hb]; ring
    simp only [↓reduceIte, hpq0, hqp0, if_pos rfl, if_neg hjp, if_neg hjq, if_neg (Ne.symm hjp), hD i j (Ne.symm hjp),
      hD q j (Ne.symm hjq), mul_zero, add_zero]
  by_cases hiq : i = q
  · subst hiq
    by_cases hjp : j = p
    · subst hjp; simp only [↓reduceIte, hpq0, hqp0, if_neg hip, if_pos rfl, if_neg hqp, hqp0, mul_zero, add_zero, zero_add]
      rw [ha, hb]; ring
    by_cases hjq : j = i
    · subst hjq; simp only [↓reduceIte, hpq0, hqp0, if_neg hip, if_pos rfl, if_neg hjp, hqp0, mul_zero, add_zero, zero_add]
      rw [ha, hb]; linear_combination (g * a' * b') * e1
    simp only [↓reduceIte, hpq0, hqp0, if_neg hip, if_pos rfl, if_neg hjp, if_neg hjq, if_neg (Ne.symm hjq),
      hD p j (Ne.symm hjp), hD i j (Ne.symm hjq), mul_zero, add_zero]
  simp only [↓reduceIte, hpq0, hqp0, if_neg hip, if_neg hiq, hD i p hip, hD i q hiq, zero_mul, add_zero]
  by_cases hjp : j = p
  · subst hjp; simp only [↓reduceIte, hpq0, hqp0, if_pos rfl, if_neg hip]
  by_cases hjq : j = q
  · subst hjq; simp only [↓reduceIte, hpq0, hqp0, if_pos rfl, if_neg hjp, if_neg hiq]
  simp only [↓reduceIte, if_neg hjp, if_neg hjq]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, hD i j hij]

theorem snfL_isUnit {H : _root_.Matrix (Fin n) (Fin n) ℤ} (hpos : ∀ l, 0 < H l l) {p q : Fin n}
    (hpq : p ≠ q) : IsUnit (snfL H p q).det := by
  obtain ⟨a', b', -, -, -, -, -, e1, ea, eb⟩ := snfPair_facts hpos p q
  unfold snfL
  rw [ea, eb]
  exact snfEmb_isUnit hpq (by linear_combination e1)

theorem snfR_isUnit {H : _root_.Matrix (Fin n) (Fin n) ℤ} (hpos : ∀ l, 0 < H l l) {p q : Fin n}
    (hpq : p ≠ q) : IsUnit (snfR H p q).det := by
  obtain ⟨a', b', -, -, -, -, -, e1, ea, eb⟩ := snfPair_facts hpos p q
  unfold snfR
  rw [ea, eb]
  exact snfEmb_isUnit hpq (by linear_combination e1)

/-! ### The loop over the pairs -/

theorem snf_pos_of_lt {k : ℕ} (h : k < n * n) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with rfl | h0
  · simp at h
  · exact h0

/-- Step `k` of the loop: the pair `(k / n, k % n)`. -/
def snfFixK (s : SnfSt n) (k : ℕ) : SnfSt n :=
  if h : k < n * n then
    snfPair s ⟨k / n, Nat.div_lt_of_lt_mul h⟩ ⟨k % n, Nat.mod_lt _ (snf_pos_of_lt h)⟩
  else s

/-- The first `k` steps of the loop. -/
def snfFix (s : SnfSt n) : ℕ → SnfSt n
  | 0 => s
  | k + 1 => snfFixK (snfFix s k) k

/-- The invariant of the loop at step `k`, with `p = k / n` and `q = k % n`. -/
def SnfFixInv (k : ℕ) (D : _root_.Matrix (Fin n) (Fin n) ℤ) : Prop :=
  SnfDiag D ∧ (∀ l, 0 < D l l) ∧
    (∀ i j : Fin n, i < j → (i : ℕ) < k / n → D i i ∣ D j j) ∧
    (∀ (j : Fin n) (hp : k / n < n), k / n < (j : ℕ) → (j : ℕ) < k % n →
      D ⟨k / n, hp⟩ ⟨k / n, hp⟩ ∣ D j j)

theorem snfPairD_diag (H : _root_.Matrix (Fin n) (Fin n) ℤ) (p q : Fin n) : SnfDiag (snfPairD H p q) :=
  fun i j h => by simp only [snfPairD, if_neg h]

theorem snf_divmod_succ {k : ℕ} (hn : 0 < n) :
    ((k % n + 1 < n) → (k + 1) / n = k / n ∧ (k + 1) % n = k % n + 1) ∧
    ((k % n + 1 = n) → (k + 1) / n = k / n + 1 ∧ (k + 1) % n = 0) := by
  have hk := Nat.div_add_mod k n
  constructor
  · intro h
    have e : k + 1 = n * (k / n) + (k % n + 1) := by omega
    rw [e, Nat.mul_add_div hn, Nat.div_eq_of_lt h, Nat.mul_add_mod, Nat.mod_eq_of_lt h]
    simp
  · intro h
    have e : k + 1 = n * (k / n + 1) := by rw [Nat.mul_add]; omega
    rw [e, Nat.mul_div_cancel_left _ hn, Nat.mul_mod_right]
    exact ⟨rfl, rfl⟩

/-- **The loop keeps the invariant.** -/
theorem snfFixK_inv {k : ℕ} (hk : k < n * n) {s : SnfSt n} (h : SnfFixInv k s.H) :
    SnfFixInv (k + 1) (snfFixK s k).H := by
  have hn := snf_pos_of_lt hk
  obtain ⟨hD, hpos, h3, h4⟩ := h
  obtain ⟨hs1, hs2⟩ := snf_divmod_succ (k := k) hn
  set p : Fin n := ⟨k / n, Nat.div_lt_of_lt_mul hk⟩ with hpdef
  set q : Fin n := ⟨k % n, Nat.mod_lt _ hn⟩ with hqdef
  have hpv : (p : ℕ) = k / n := rfl
  have hqv : (q : ℕ) = k % n := rfl
  have hstep : snfFixK s k = snfPair s p q := by unfold snfFixK; rw [dif_pos hk]
  rw [hstep]
  by_cases hpq : p < q
  · have hne : p ≠ q := ne_of_lt hpq
    unfold snfPair
    rw [if_pos hpq]
    show SnfFixInv (k + 1) (snfL s.H p q * s.H * snfR s.H p q)
    rw [snfPair_H hD hpos hne]
    obtain ⟨a', b', ha, hb, hg, hap, hbp, -, ea, -⟩ := snfPair_facts hpos p q
    set g := snfBg (s.H p p) (s.H q q)
    -- the new diagonal entries
    have dp : snfPairD s.H p q p p = g := by simp only [snfPairD, ↓reduceIte] <;> rfl
    have dq : snfPairD s.H p q q q = s.H p p / g * s.H q q := by
      simp only [snfPairD, ↓reduceIte, if_neg (Ne.symm hne)]; rfl
    have dj : ∀ j : Fin n, j ≠ p → j ≠ q → snfPairD s.H p q j j = s.H j j := by
      intro j h1 h2; simp [snfPairD, h1, h2]
    have hgq : g ∣ s.H p p / g * s.H q q := by rw [ea, hb]; exact ⟨a' * b', by ring⟩
    have hga : g ∣ s.H p p := ⟨a', ha⟩
    refine ⟨snfPairD_diag _ _ _, ?_, ?_, ?_⟩
    · intro l
      by_cases h1 : l = p
      · rw [h1, dp]; exact hg
      by_cases h2 : l = q
      · rw [h2, dq, ea]; exact mul_pos hap (hpos q)
      rw [dj l h1 h2]; exact hpos l
    · intro i j hij hi
      -- `D_ii` for `i < p` divides both old entries, so both new ones
      have hdvd_old : ∀ (i : Fin n), (i : ℕ) < k / n → ∀ j : Fin n, i < j →
          snfPairD s.H p q i i ∣ snfPairD s.H p q j j := by
        intro i hi j hij
        have hip : i ≠ p := fun e => by rw [e] at hi; omega
        have hiq : i ≠ q := fun e => by
          have : (p : ℕ) < q := hpq; rw [e] at hi; omega
        rw [dj i hip hiq]
        have hpi : i < p := Fin.lt_def.mpr (by omega)
        have hqi : i < q := lt_trans hpi hpq
        by_cases h1 : j = p
        · rw [h1, dp]
          have e2 : snfBx (s.H p p) (s.H q q) * s.H p p + snfBy (s.H p p) (s.H q q) * s.H q q = g :=
            (snf_bezout (hpos p) (hpos q)).1
          rw [← e2]
          exact dvd_add (Dvd.dvd.mul_left (h3 i p hpi hi) _) (Dvd.dvd.mul_left (h3 i q hqi hi) _)
        by_cases h2 : j = q
        · rw [h2, dq]; exact Dvd.dvd.mul_left (h3 i q hqi hi) _
        rw [dj j h1 h2]; exact h3 i j hij hi
      by_cases hq1 : k % n + 1 < n
      · rw [(hs1 hq1).1] at hi
        exact hdvd_old i hi j hij
      · have hq1' : k % n + 1 = n := by have := Nat.mod_lt k hn; omega
        rw [(hs2 hq1').1] at hi
        by_cases hi' : (i : ℕ) < k / n
        · exact hdvd_old i hi' j hij
        have hip : i = p := Fin.ext (by rw [hpv]; omega)
        rw [hip, dp]
        by_cases h2 : j = q
        · rw [h2, dq]; exact hgq
        have hjp : j ≠ p := fun e => by rw [e, hip] at hij; exact lt_irrefl _ hij
        rw [dj j hjp h2]
        have hjq : (j : ℕ) < k % n := by
          have := j.isLt
          have : (j : ℕ) ≠ k % n := fun e => h2 (Fin.ext e)
          omega
        have hpj : k / n < (j : ℕ) := by rw [hip] at hij; exact hij
        exact dvd_trans hga (h4 j p.isLt hpj hjq)
    · intro j hp' hpj hjq
      by_cases hq1 : k % n + 1 < n
      · obtain ⟨e1, e2⟩ := hs1 hq1
        have hp'' : (⟨(k + 1) / n, hp'⟩ : Fin n) = p := Fin.ext (by rw [hpv]; exact e1)
        rw [hp'', dp]
        rw [e1] at hpj
        rw [e2] at hjq
        by_cases h2 : j = q
        · rw [h2, dq]; exact hgq
        have hjp : j ≠ p := fun e => by rw [e] at hpj; exact lt_irrefl _ hpj
        rw [dj j hjp h2]
        have hjq' : (j : ℕ) < k % n := by
          have : (j : ℕ) ≠ k % n := fun e => h2 (Fin.ext e)
          omega
        exact dvd_trans hga (h4 j p.isLt hpj hjq')
      · have hq1' : k % n + 1 = n := by have := Nat.mod_lt k hn; omega
        rw [(hs2 hq1').2] at hjq
        omega
  · unfold snfPair
    rw [if_neg hpq]
    have hqp : (q : ℕ) ≤ p := by have := not_lt.mp hpq; exact this
    refine ⟨hD, hpos, ?_, ?_⟩
    · intro i j hij hi
      by_cases hq1 : k % n + 1 < n
      · rw [(hs1 hq1).1] at hi; exact h3 i j hij hi
      · have hq1' : k % n + 1 = n := by have := Nat.mod_lt k hn; omega
        rw [(hs2 hq1').1] at hi
        by_cases hi' : (i : ℕ) < k / n
        · exact h3 i j hij hi'
        exfalso
        have : (j : ℕ) < n := j.isLt
        have : (i : ℕ) < j := hij
        omega
    · intro j hp' hpj hjq
      by_cases hq1 : k % n + 1 < n
      · obtain ⟨e1, e2⟩ := hs1 hq1
        rw [e1] at hpj; rw [e2] at hjq
        omega
      · have hq1' : k % n + 1 = n := by have := Nat.mod_lt k hn; omega
        rw [(hs2 hq1').2] at hjq
        omega

theorem snfFix_inv {s : SnfSt n} (hD : SnfDiag s.H) (hpos : ∀ l, 0 < s.H l l) (k : ℕ)
    (hk : k ≤ n * n) : SnfFixInv k (snfFix s k).H := by
  induction k with
  | zero =>
    refine ⟨hD, hpos, fun i j _ hi => by simp at hi, fun j hp hpj hjq => by simp at hjq⟩
  | succ k ih =>
    exact snfFixK_inv (by omega) (ih (by omega))

/-- **After all pairs the matrix is in Smith form.** -/
theorem snfFix_smith {s : SnfSt n} (hD : SnfDiag s.H) (hpos : ∀ l, 0 < s.H l l) :
    IsSmithForm (snfFix s (n * n)).H := by
  obtain ⟨hD', hpos', h3, -⟩ := snfFix_inv hD hpos (n * n) le_rfl
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  have e : n * n / n = n := Nat.mul_div_cancel _ hn
  refine ⟨fun i j h => hD' i j (fun e => h (congrArg Fin.val e)), fun i j h => ?_, ?_⟩
  · rw [Fin.ext h]; exact (hpos' j).le
  · intro i j i' j' hij hij' hii'
    rw [Fin.ext hij, Fin.ext hij']
    exact h3 j j' (Fin.lt_def.mpr (by omega)) (by rw [e]; exact j.isLt)

/-! ### The relation and unimodularity -/

theorem snfFix_rel {A : _root_.Matrix (Fin n) (Fin n) ℤ} {s : SnfSt n} (hrel : s.H = s.P * A * s.Q)
    (hP : IsUnit s.P.det) (hQ : IsUnit s.Q.det) (hD : SnfDiag s.H) (hpos : ∀ l, 0 < s.H l l)
    (k : ℕ) (hk : k ≤ n * n) :
    (snfFix s k).H = (snfFix s k).P * A * (snfFix s k).Q ∧ IsUnit (snfFix s k).P.det ∧
      IsUnit (snfFix s k).Q.det := by
  induction k with
  | zero => exact ⟨hrel, hP, hQ⟩
  | succ k ih =>
    obtain ⟨e, hP', hQ'⟩ := ih (by omega)
    obtain ⟨-, hpos', -, -⟩ := snfFix_inv hD hpos k (by omega)
    show (snfFixK (snfFix s k) k).H = (snfFixK (snfFix s k) k).P * A * (snfFixK (snfFix s k) k).Q ∧
      IsUnit (snfFixK (snfFix s k) k).P.det ∧ IsUnit (snfFixK (snfFix s k) k).Q.det
    set t := snfFix s k
    unfold snfFixK
    rw [dif_pos (show k < n * n by omega)]
    unfold snfPair
    split_ifs with hpq
    · refine ⟨?_, ?_, ?_⟩
      · show snfL t.H _ _ * t.H * snfR t.H _ _ = snfL t.H _ _ * t.P * A * (t.Q * snfR t.H _ _)
        rw [e]; simp only [Matrix.mul_assoc]
      · show IsUnit (snfL t.H _ _ * t.P).det
        rw [det_mul]; exact (snfL_isUnit hpos' (ne_of_lt hpq)).mul hP'
      · show IsUnit (t.Q * snfR t.H _ _).det
        rw [det_mul]; exact hQ'.mul (snfR_isUnit hpos' (ne_of_lt hpq))
    · exact ⟨e, hP', hQ'⟩

end GI.Proved
