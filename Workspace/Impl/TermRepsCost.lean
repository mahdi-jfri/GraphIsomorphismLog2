module

public import Workspace.Impl.TermReps

@[expose] public section

/-!
# The cost of T3 is within `expLogSq`

`tmRpCost hm K D n X` is a polynomial in the number `n` of cosets and the weight bound `X`
(`tmRp_cost_poly`): at most a constant times `(n + 2)³ X^e`. With `n ≤ m^{2 log₂ m} ≤
expLogSq 3 N` and `X ≤ tmVB N` (a polynomial in `N`), it is at most `expLogSq` of a constant
(`tmRp_cost_le`), as Corollary A.22 says: `[H : R]` cosets, each in polynomial time.
-/

namespace GI.Impl

open GI.Lang GI.Algorithm
open GI.Cited (Membership)

/-- The exponent of `X` in the polynomial bound. -/
noncomputable def tmRpE (hm : Membership) (D : ℕ) : ℕ := 6 * (membershipPrim hm).k + 4 * D + 21

/-- The constant of the polynomial bound. -/
noncomputable def tmRpC1 (hm : Membership) (K D : ℕ) : ℕ :=
  10 ^ 9 + K * 4000 ^ D +
    (4 * 10 ^ 8 + (membershipPrim hm).c * 22 ^ (membershipPrim hm).k) *
      10 ^ (3 * ((membershipPrim hm).k + 2))

theorem tmRp_round_le (hm : Membership) {Y L : ℕ} (hY : 1 ≤ Y) (hL : 1 ≤ L) :
    tmRpRoundC hm Y L ≤ (2 * 10 ^ 8 + (membershipPrim hm).c * 22 ^ (membershipPrim hm).k) *
      (L ^ 2 * Y ^ ((membershipPrim hm).k + 2)) := by
  set c := (membershipPrim hm).c
  set k := (membershipPrim hm).k
  set A := L ^ 2 * Y ^ (k + 2) with hA
  have hT : tmPrimC (membershipPrim hm) (20 * Y) ≤ c * 22 ^ k * Y ^ k := by
    unfold tmPrimC
    calc c * (20 * Y + 2) ^ k ≤ c * (22 * Y) ^ k :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ = c * 22 ^ k * Y ^ k := by rw [mul_pow, mul_assoc]
  have hY2 : Y ^ 2 ≤ Y ^ (k + 2) := Nat.pow_le_pow_right hY (by omega)
  have hLL : L ≤ L ^ 2 := by nlinarith
  have m1 : L * Y ^ 2 ≤ A := Nat.mul_le_mul hLL hY2
  have m2 : L ^ 2 * Y ^ 2 ≤ A := Nat.mul_le_mul_left _ hY2
  have m3 : L * Y ^ (k + 1) ≤ A := Nat.mul_le_mul hLL (Nat.pow_le_pow_right hY (by omega))
  have e : tmRpRoundC hm Y L = 10 ^ 6 * (L * Y ^ 2) + (L * Y) * tmPrimC (membershipPrim hm) (20 * Y) +
      10 ^ 8 * (L ^ 2 * Y ^ 2) + 10 ^ 7 * (L * Y ^ 2) := by
    unfold tmRpRoundC tmRpTestC tmRpPredC; ring
  have h2 : (L * Y) * tmPrimC (membershipPrim hm) (20 * Y) ≤ c * 22 ^ k * A := by
    calc (L * Y) * tmPrimC (membershipPrim hm) (20 * Y) ≤ (L * Y) * (c * 22 ^ k * Y ^ k) :=
          Nat.mul_le_mul_left _ hT
      _ = c * 22 ^ k * (L * Y ^ (k + 1)) := by ring
      _ ≤ c * 22 ^ k * A := Nat.mul_le_mul_left _ m3
  rw [e, Nat.add_mul]
  omega

theorem tmRp_cost_poly (hm : Membership) (K D n : ℕ) {X : ℕ} (hX : 1 ≤ X) :
    tmRpCost hm K D n X ≤ tmRpC1 hm K D * ((n + 2) ^ 3 * X ^ tmRpE hm D) := by
  set c := (membershipPrim hm).c
  set k := (membershipPrim hm).k
  set L := n + 2 with hL
  set Y := 10 ^ 3 * X ^ 6 with hY
  set B := L ^ 3 * X ^ tmRpE hm D with hB
  have hY1 : 1 ≤ Y := by have := Nat.one_le_pow 6 X hX; omega
  have hR := tmRp_round_le hm hY1 (show 1 ≤ L by omega)
  have hYk : Y ^ (k + 2) = 10 ^ (3 * (k + 2)) * X ^ (6 * (k + 2)) := by
    rw [hY, mul_pow, ← pow_mul, ← pow_mul]
  have hXe : ∀ a, a ≤ tmRpE hm D → X ^ a ≤ X ^ tmRpE hm D := fun a ha => Nat.pow_le_pow_right hX ha
  have hL3 : 1 ≤ L ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hL23 : L ^ 2 ≤ L ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hLL : L ≤ L ^ 2 := by nlinarith
  -- the three parts
  have t1 : 10 ^ 9 * X ^ 9 ≤ 10 ^ 9 * B :=
    Nat.mul_le_mul_left _ ((hXe 9 (by unfold tmRpE; omega)).trans (Nat.le_mul_of_pos_left _ hL3))
  have t2 : K * (4000 * X ^ 4) ^ D ≤ K * 4000 ^ D * B := by
    rw [mul_pow, ← pow_mul, mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
      ((hXe _ (by unfold tmRpE; omega)).trans (Nat.le_mul_of_pos_left _ hL3)))
  have hYX : Y ≤ 10 ^ (3 * (k + 2)) * X ^ (6 * (k + 2)) := by
    rw [← hYk]; exact Nat.le_self_pow (by omega) Y
  have hX6 : X ^ (6 * (k + 2)) ≤ X ^ tmRpE hm D := hXe _ (by unfold tmRpE; omega)
  set G := 10 ^ (3 * (k + 2)) * X ^ (6 * (k + 2)) with hG
  have t3 : L * (tmRpRoundC hm Y L + tmRpWK * (Y + n + 10 * (L * Y) + 10)) ≤
      (4 * 10 ^ 8 + c * 22 ^ k) * (L ^ 3 * G) := by
    have hLY : L * Y ≤ L * G := Nat.mul_le_mul_left _ hYX
    have hG1 : 1 ≤ G := le_trans hY1 hYX
    have hLG : L ≤ L * G := Nat.le_mul_of_pos_right _ hG1
    have hW : tmRpWK * (Y + n + 10 * (L * Y) + 10) ≤ 2200 * (L * G) := by
      unfold tmRpWK
      have : Y ≤ L * Y := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hR' : tmRpRoundC hm Y L ≤ (2 * 10 ^ 8 + c * 22 ^ k) * (L ^ 2 * G) := by
      rw [← hYk]; exact hR
    calc L * (tmRpRoundC hm Y L + tmRpWK * (Y + n + 10 * (L * Y) + 10))
        ≤ L * ((2 * 10 ^ 8 + c * 22 ^ k) * (L ^ 2 * G) + 2200 * (L * G)) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add hR' hW)
      _ = (2 * 10 ^ 8 + c * 22 ^ k) * (L ^ 3 * G) + 2200 * (L ^ 2 * G) := by ring
      _ ≤ (2 * 10 ^ 8 + c * 22 ^ k) * (L ^ 3 * G) + 2200 * (L ^ 3 * G) :=
          Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hL23)) _
      _ ≤ (4 * 10 ^ 8 + c * 22 ^ k) * (L ^ 3 * G) := by
          rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
  have t3' : (4 * 10 ^ 8 + c * 22 ^ k) * (L ^ 3 * G) ≤
      (4 * 10 ^ 8 + c * 22 ^ k) * 10 ^ (3 * (k + 2)) * B := by
    rw [hG, hB, mul_assoc]
    refine Nat.mul_le_mul_left _ ?_
    calc L ^ 3 * (10 ^ (3 * (k + 2)) * X ^ (6 * (k + 2)))
        = 10 ^ (3 * (k + 2)) * (L ^ 3 * X ^ (6 * (k + 2))) := by ring
      _ ≤ 10 ^ (3 * (k + 2)) * (L ^ 3 * X ^ tmRpE hm D) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hX6)
  unfold tmRpCost
  unfold tmRpC1
  rw [← hL, ← hY]
  have e : (10 ^ 9 + K * 4000 ^ D + (4 * 10 ^ 8 + c * 22 ^ k) * 10 ^ (3 * (k + 2))) * B =
      10 ^ 9 * B + K * 4000 ^ D * B + (4 * 10 ^ 8 + c * 22 ^ k) * 10 ^ (3 * (k + 2)) * B := by ring
  rw [e]
  omega

/-- The constant in front of the polynomial in `N`. -/
noncomputable def tmRpCbig (hm : Membership) (K D : ℕ) : ℕ :=
  (2 * tmRpC1 hm K D + 23) * 27 * (12 * 10 ^ 6) ^ tmRpE hm D

/-- **The exponent constant of T3.** -/
noncomputable def tmRpA (hm : Membership) (K D : ℕ) : ℝ :=
  3 * (Real.log (tmRpCbig hm K D) + ((8 * tmRpE hm D : ℕ) : ℝ)) + (9 + ((3 * tmRpE hm D : ℕ) : ℝ))

/-- **The cost of T3 lies in `expLogSq`.** -/
theorem tmRp_cost_le (hm : Membership) (K D : ℕ) {N n X W : ℕ}
    (hn : (n : ℝ) ≤ expLogSq 3 N) (hX : 1 ≤ X) (hXN : X ≤ tmVB N + ⌈expLogSq 3 N⌉₊)
    (hW : W ≤ tmVB N) :
    ((2 * tmRpCost hm K D n X + 3 * W + 20 : ℕ) : ℝ) ≤ expLogSq (tmRpA hm K D) N := by
  set e := tmRpE hm D
  set V := tmVB N * (⌈expLogSq 3 N⌉₊ + 1) with hV
  set C1 := tmRpC1 hm K D
  have hVB1 : 1 ≤ tmVB N := by unfold tmVB; exact Nat.one_le_iff_ne_zero.2 (by positivity)
  have hV1 : 1 ≤ V := by rw [hV]; exact Nat.mul_pos hVB1 (by omega)
  have hXV : X ≤ V := by
    rw [hV, Nat.mul_add, Nat.mul_one]
    have : ⌈expLogSq 3 N⌉₊ ≤ tmVB N * ⌈expLogSq 3 N⌉₊ := Nat.le_mul_of_pos_left _ hVB1
    omega
  have hWV : W ≤ V := hW.trans (by rw [hV]; exact Nat.le_mul_of_pos_right _ (by omega))
  have hE1 : (1 : ℝ) ≤ expLogSq 3 N := tm_one_le_expLogSq (by norm_num) N
  have hVr : ((V ^ e : ℕ) : ℝ) ≤
      (12 * 10 ^ 6 : ℝ) ^ e * ((N : ℝ) + 2) ^ (8 * e) * expLogSq ((3 : ℕ) * e) N := by
    have hceil : ((⌈expLogSq 3 N⌉₊ + 1 : ℕ) : ℝ) ≤ 3 * expLogSq 3 N := by
      have : (⌈expLogSq 3 N⌉₊ : ℝ) < expLogSq 3 N + 1 := Nat.ceil_lt_add_one (by positivity)
      push_cast
      linarith
    have hVle : ((V : ℕ) : ℝ) ≤ (12 * 10 ^ 6 : ℝ) * ((N : ℝ) + 2) ^ 8 * expLogSq 3 N := by
      have h1 : ((tmVB N : ℕ) : ℝ) = (4 * 10 ^ 6 : ℝ) * ((N : ℝ) + 2) ^ 8 := by
        unfold tmVB; push_cast; norm_num
      calc ((V : ℕ) : ℝ) = ((tmVB N : ℕ) : ℝ) * ((⌈expLogSq 3 N⌉₊ + 1 : ℕ) : ℝ) := by
            rw [hV]; push_cast; rfl
        _ ≤ ((4 * 10 ^ 6 : ℝ) * ((N : ℝ) + 2) ^ 8) * (3 * expLogSq 3 N) := by
            rw [← h1]; exact mul_le_mul_of_nonneg_left hceil (Nat.cast_nonneg _)
        _ = (12 * 10 ^ 6 : ℝ) * ((N : ℝ) + 2) ^ 8 * expLogSq 3 N := by ring
    calc ((V ^ e : ℕ) : ℝ) = ((V : ℕ) : ℝ) ^ e := by push_cast; rfl
      _ ≤ ((12 * 10 ^ 6 : ℝ) * ((N : ℝ) + 2) ^ 8 * expLogSq 3 N) ^ e :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hVle e
      _ = (12 * 10 ^ 6 : ℝ) ^ e * ((N : ℝ) + 2) ^ (8 * e) * (expLogSq 3 N) ^ e := by
          rw [mul_pow, mul_pow, ← pow_mul]
      _ = (12 * 10 ^ 6 : ℝ) ^ e * ((N : ℝ) + 2) ^ (8 * e) * expLogSq ((3 : ℕ) * e) N := by
          rw [tm_expLogSq_pow 3 e N]; push_cast; ring_nf
  clear_value V
  have hP : tmRpCost hm K D n X ≤ C1 * ((n + 2) ^ 3 * X ^ e) := tmRp_cost_poly hm K D n hX
  have hXe : X ^ e ≤ V ^ e := Nat.pow_le_pow_left hXV e
  have hVe : 1 ≤ V ^ e := Nat.one_le_pow _ _ (by omega)
  have hn3 : 1 ≤ (n + 2) ^ 3 := Nat.one_le_pow _ _ (by omega)
  -- a natural bound
  have hnat : 2 * tmRpCost hm K D n X + 3 * W + 20 ≤ (2 * C1 + 23) * ((n + 2) ^ 3 * V ^ e) := by
    have h1 : (n + 2) ^ 3 * X ^ e ≤ (n + 2) ^ 3 * V ^ e := Nat.mul_le_mul_left _ hXe
    have h2 : 1 ≤ (n + 2) ^ 3 * V ^ e := by simpa using Nat.mul_le_mul hn3 hVe
    have h3 : V ≤ (n + 2) ^ 3 * V ^ e := by
      calc V ≤ V ^ e := by
            rcases Nat.eq_zero_or_pos e with h0 | h0
            · exfalso; unfold e tmRpE at h0; omega
            · exact Nat.le_self_pow (by omega) V
        _ ≤ (n + 2) ^ 3 * V ^ e := Nat.le_mul_of_pos_left _ (by omega)
    have h4 : C1 * ((n + 2) ^ 3 * X ^ e) ≤ C1 * ((n + 2) ^ 3 * V ^ e) := Nat.mul_le_mul_left _ h1
    have e2 : (2 * C1 + 23) * ((n + 2) ^ 3 * V ^ e) =
        2 * (C1 * ((n + 2) ^ 3 * V ^ e)) + 23 * ((n + 2) ^ 3 * V ^ e) := by ring
    rw [e2]
    omega
  have hL : ((n : ℝ) + 2) ≤ 3 * expLogSq 3 N := by linarith
  have hL3 : ((n : ℝ) + 2) ^ 3 ≤ 27 * expLogSq 9 N := by
    have : ((n : ℝ) + 2) ^ 3 ≤ (3 * expLogSq 3 N) ^ 3 := pow_le_pow_left₀ (by positivity) hL 3
    have e9 : expLogSq 3 N ^ 3 = expLogSq ((3 : ℕ) * 3) N := tm_expLogSq_pow 3 3 N
    rw [mul_pow, e9] at this
    norm_num at this ⊢
    linarith
  have hCb1 : (1 : ℝ) ≤ (tmRpCbig hm K D : ℝ) := by
    have : 0 < tmRpCbig hm K D := by
      unfold tmRpCbig
      exact Nat.mul_pos (Nat.mul_pos (by omega) (by norm_num)) (pow_pos (by norm_num) _)
    exact_mod_cast this
  have hpe := pow_le_expLogSq hCb1 (8 * e) N
  have hcast : ((2 * tmRpCost hm K D n X + 3 * W + 20 : ℕ) : ℝ) ≤
      ((2 * C1 + 23 : ℕ) : ℝ) * (((n : ℝ) + 2) ^ 3 * ((V ^ e : ℕ) : ℝ)) := by
    have := (Nat.cast_le (α := ℝ)).2 hnat
    push_cast at this ⊢
    linarith
  have hCb : (tmRpCbig hm K D : ℝ) = ((2 * C1 + 23 : ℕ) : ℝ) * 27 * (12 * 10 ^ 6 : ℝ) ^ e := by
    unfold tmRpCbig; push_cast; ring
  have heA : tmRpA hm K D =
      3 * (Real.log (tmRpCbig hm K D) + ((8 * e : ℕ) : ℝ)) + (9 + ((3 * e : ℕ) : ℝ)) := rfl
  clear_value e C1
  have hC0 : (0 : ℝ) ≤ ((2 * C1 + 23 : ℕ) : ℝ) := Nat.cast_nonneg _
  refine hcast.trans ?_
  calc ((2 * C1 + 23 : ℕ) : ℝ) * (((n : ℝ) + 2) ^ 3 * ((V ^ e : ℕ) : ℝ))
      ≤ ((2 * C1 + 23 : ℕ) : ℝ) * ((27 * expLogSq 9 N) *
          ((12 * 10 ^ 6 : ℝ) ^ e * ((N : ℝ) + 2) ^ (8 * e) * expLogSq ((3 : ℕ) * e) N)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul hL3 hVr (Nat.cast_nonneg _)
            (mul_nonneg (by norm_num) (expLogSq_nonneg _ _))) hC0
    _ = ((tmRpCbig hm K D : ℝ) * ((N : ℝ) + 2) ^ (8 * e)) *
          (expLogSq 9 N * expLogSq ((3 : ℕ) * e) N) := by rw [hCb]; ring
    _ ≤ expLogSq (3 * (Real.log (tmRpCbig hm K D) + ((8 * e : ℕ) : ℝ))) N *
          (expLogSq 9 N * expLogSq ((3 : ℕ) * e) N) :=
        mul_le_mul_of_nonneg_right hpe (mul_nonneg (expLogSq_nonneg _ _) (expLogSq_nonneg _ _))
    _ = expLogSq (tmRpA hm K D) N := by
        rw [tm_expLogSq_mul, tm_expLogSq_mul, heA]; push_cast; rfl

end GI.Impl
