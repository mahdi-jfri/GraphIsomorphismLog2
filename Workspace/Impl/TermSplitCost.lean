module

public import Workspace.Impl.AggCombExact
public import Workspace.Impl.TermLift

@[expose] public section

/-!
# Polynomial bounds for the split of the row terminal

`CombineExact` (`ce_spec`) costs `ceCost hm n W`. For the split over the radical cosets its
input has quasi-polynomial weight, so we need an explicit polynomial bound:
`ceCost hm n W ≤ tmCeK hm * Z ^ tmCeD hm` for `n, W ≤ Z` (`tm_ceCost_le`). We also collect the
facts about `expLogSq` used to absorb products (`tm_expLogSq_mul`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val Membership)

/-- The constant of the bound of `ceCost`. -/
noncomputable def tmCeK (hm : Membership) : ℕ :=
  10 ^ 60 + 10 ^ 7 * ((membershipPrim hm).c * 25600 ^ (membershipPrim hm).k)

/-- The degree of the bound of `ceCost`. -/
noncomputable def tmCeD (hm : Membership) : ℕ := 31 + 6 * (membershipPrim hm).k

theorem tm_memCost_le (hm : Membership) {n Z : ℕ} (hZ : 1 ≤ Z) (hn : n ≤ Z) :
    memCost hm n ≤ (membershipPrim hm).c * 25600 ^ (membershipPrim hm).k *
      Z ^ (6 * (membershipPrim hm).k) := by
  unfold memCost
  set c := (membershipPrim hm).c
  set kk := (membershipPrim hm).k
  have h1 : 400 * (n + 1) ^ 6 ≤ 25600 * Z ^ 6 := by
    have : (n + 1) ^ 6 ≤ (2 * Z) ^ 6 := Nat.pow_le_pow_left (by omega) 6
    have e : (2 * Z) ^ 6 = 64 * Z ^ 6 := by ring
    omega
  have h2 := Nat.pow_le_pow_left h1 kk
  have e : (25600 * Z ^ 6) ^ kk = 25600 ^ kk * Z ^ (6 * kk) := by rw [mul_pow, ← pow_mul]
  rw [e] at h2
  calc c * (400 * (n + 1) ^ 6) ^ kk ≤ c * (25600 ^ kk * Z ^ (6 * kk)) := Nat.mul_le_mul_left _ h2
    _ = _ := by ring

/-- **`CombineExact` costs a polynomial**: `ceCost hm n W ≤ tmCeK hm * Z ^ tmCeD hm` for
`n, W ≤ Z`. -/
theorem tm_ceCost_le (hm : Membership) {n W Z : ℕ} (hZ : 1 ≤ Z) (hn : n ≤ Z) (hW : W ≤ Z) :
    ceCost hm n W ≤ tmCeK hm * Z ^ tmCeD hm := by
  set kk := (membershipPrim hm).k
  set D := tmCeD hm with hD
  have pw : ∀ a, a ≤ D → Z ^ a ≤ Z ^ D := fun a ha => Nat.pow_le_pow_right hZ ha
  have hD30 : 30 ≤ D := by rw [hD]; unfold tmCeD; omega
  have z1 : 1 ≤ Z ^ D := Nat.one_le_pow _ _ hZ
  -- the pieces
  have hin : ceInW W ≤ 32 * Z := by unfold ceInW; omega
  have hM : combM n (ceInW W) ≤ 500000 * Z ^ 4 := by
    unfold combM
    have h1 : (ceInW W + 2) * (n + 1) ≤ 68 * Z ^ 2 := by
      have := Nat.mul_le_mul (show ceInW W + 2 ≤ 34 * Z by omega) (show n + 1 ≤ 2 * Z by omega)
      have e : 34 * Z * (2 * Z) = 68 * Z ^ 2 := by ring
      omega
    have h2 := Nat.pow_le_pow_left h1 2
    have e : (68 * Z ^ 2) ^ 2 = 4624 * Z ^ 4 := by ring
    omega
  have hO : ceOutW n W ≤ 500000 * Z ^ 4 := by
    unfold ceOutW
    have h1 : (ceInW W + 2) * (n + 1) ≤ 68 * Z ^ 2 := by
      have := Nat.mul_le_mul (show ceInW W + 2 ≤ 34 * Z by omega) (show n + 1 ≤ 2 * Z by omega)
      have e : 34 * Z * (2 * Z) = 68 * Z ^ 2 := by ring
      omega
    have h2 := Nat.pow_le_pow_left h1 2
    have e : (68 * Z ^ 2) ^ 2 = 4624 * Z ^ 4 := by ring
    omega
  have z4 : Z ^ 4 ≤ Z ^ D := pw 4 (by omega)
  have zn4 : (n + 1) ^ 4 ≤ 16 * Z ^ 4 := by
    have : (n + 1) ^ 4 ≤ (2 * Z) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have e : (2 * Z) ^ 4 = 16 * Z ^ 4 := by ring
    omega
  have zZ4 : Z ≤ Z ^ 4 := Nat.le_self_pow (by norm_num) _
  have hC : combCost n (ceInW W) ≤ 10 ^ 22 * Z ^ 9 := by
    unfold combCost
    have h1 : 4 * ceInW W + 2 * combM n (ceInW W) + 7 + (n + 1) ^ 4 ≤ 1100000 * Z ^ 4 := by
      omega
    have h2 := Nat.pow_le_pow_left h1 2
    have e2 : (1100000 * Z ^ 4) ^ 2 = 1210000000000 * Z ^ 8 := by ring
    have h3 : 2 * ceInW W + combM n (ceInW W) + 1 ≤ 600000 * Z ^ 4 := by omega
    have z48 : Z ^ 4 ≤ Z ^ 8 := Nat.pow_le_pow_right hZ (by omega)
    have h4 : combK * (4 * ceInW W + 2 * combM n (ceInW W) + 7 + (n + 1) ^ 4) ^ 2 +
        loopModK * (2 * ceInW W + combM n (ceInW W) + 1) ≤ 2 * 10 ^ 19 * Z ^ 8 := by
      unfold combK loopModK; omega
    have h5 := Nat.mul_le_mul (show ceInW W + 1 ≤ 33 * Z by omega) h4
    have e5 : 33 * Z * (2 * 10 ^ 19 * Z ^ 8) = 66 * 10 ^ 19 * Z ^ 9 := by ring
    omega
  have hR : cosetNFCost hm n (ceOutW n W) ≤ 10 ^ 50 * Z ^ 30 +
      10 ^ 6 * ((membershipPrim hm).c * 25600 ^ kk * Z ^ (6 * kk + 4)) := by
    have hNF := cosetNFCost_mono hm n hO
    refine hNF.trans ?_
    unfold cosetNFCost reduceCost
    have hmem := tm_memCost_le hm hZ hn
    have h1 : (500000 * Z ^ 4 + 1) * memCost hm n ≤
        10 ^ 6 * ((membershipPrim hm).c * 25600 ^ kk * Z ^ (6 * kk + 4)) := by
      have := Nat.mul_le_mul (show 500000 * Z ^ 4 + 1 ≤ 10 ^ 6 * Z ^ 4 by
        have := Nat.one_le_pow 4 Z hZ; omega) hmem
      have e : 10 ^ 6 * Z ^ 4 * ((membershipPrim hm).c * 25600 ^ kk * Z ^ (6 * kk)) =
          10 ^ 6 * ((membershipPrim hm).c * 25600 ^ kk * Z ^ (6 * kk + 4)) := by ring
      exact this.trans (le_of_eq e)
    have h2 : ((500000 * Z ^ 4 + 2) * (n + 1)) ^ 6 ≤ (2 * 10 ^ 6) ^ 6 * Z ^ 30 := by
      have := Nat.mul_le_mul (show 500000 * Z ^ 4 + 2 ≤ 10 ^ 6 * Z ^ 4 by
        have := Nat.one_le_pow 4 Z hZ; omega) (show n + 1 ≤ 2 * Z by omega)
      have h3 := Nat.pow_le_pow_left this 6
      have e : (10 ^ 6 * Z ^ 4 * (2 * Z)) ^ 6 = (2 * 10 ^ 6) ^ 6 * Z ^ 30 := by ring
      omega
    have h6 : (n + 1) ^ 6 ≤ 64 * Z ^ 6 := by
      have : (n + 1) ^ 6 ≤ (2 * Z) ^ 6 := Nat.pow_le_pow_left (by omega) 6
      have e : (2 * Z) ^ 6 = 64 * Z ^ 6 := by ring
      omega
    have z6 : Z ^ 6 ≤ Z ^ 30 := Nat.pow_le_pow_right hZ (by omega)
    have z430 : Z ^ 4 ≤ Z ^ 30 := Nat.pow_le_pow_right hZ (by omega)
    unfold reduceK
    omega
  have hA : ansW n ≤ 64000 * Z ^ 6 := by
    have := ansW_le n
    have : (n + 1) ^ 6 ≤ (2 * Z) ^ 6 := Nat.pow_le_pow_left (by omega) 6
    have e : (2 * Z) ^ 6 = 64 * Z ^ 6 := by ring
    omega
  have hL : loopModK * (W + 1) * (3 * W + 1) ≤ 10 ^ 4 * Z ^ 2 := by
    have := Nat.mul_le_mul (show W + 1 ≤ 2 * Z by omega) (show 3 * W + 1 ≤ 4 * Z by omega)
    have e : 2 * Z * (4 * Z) = 8 * Z ^ 2 := by ring
    unfold loopModK
    have e2 : 1000 * (W + 1) * (3 * W + 1) = 1000 * ((W + 1) * (3 * W + 1)) := by ring
    omega
  have hcc := combCost_mono n (le_refl (ceInW W))
  unfold ceCost
  have z2 := pw 2 (by omega)
  have z6 := pw 6 (by omega)
  have z9 := pw 9 (by omega)
  have z30 := pw 30 (by omega)
  have zk : Z ^ (6 * kk + 4) ≤ Z ^ D := pw _ (by rw [hD]; unfold tmCeD; omega)
  have zz : Z ≤ Z ^ D := (Nat.le_self_pow (by omega) Z).trans (pw 1 (by omega)) |>.trans' (by simp)
  have hck := Nat.mul_le_mul_left ((membershipPrim hm).c * 25600 ^ kk) zk
  unfold tmCeK
  rw [Nat.add_mul]
  have e3 : 10 ^ 7 * ((membershipPrim hm).c * 25600 ^ kk) * Z ^ D =
      10 ^ 7 * ((membershipPrim hm).c * 25600 ^ kk * Z ^ D) := by ring
  rw [e3]
  omega

/-- `expLogSq` turns products into sums of the constants. -/
theorem tm_expLogSq_mul (a b : ℝ) (N : ℕ) :
    expLogSq a N * expLogSq b N = expLogSq (a + b) N := by
  unfold expLogSq
  rw [← Real.exp_add]
  ring_nf

theorem tm_expLogSq_mono {a b : ℝ} (h : a ≤ b) (N : ℕ) : expLogSq a N ≤ expLogSq b N := by
  unfold expLogSq
  apply Real.exp_le_exp.2
  have : 0 ≤ Real.log ((N : ℝ) + 2) ^ 2 := sq_nonneg _
  nlinarith

theorem tm_one_le_expLogSq {a : ℝ} (ha : 0 ≤ a) (N : ℕ) : 1 ≤ expLogSq a N := by
  unfold expLogSq
  have : 0 ≤ a * Real.log ((N : ℝ) + 2) ^ 2 := mul_nonneg ha (sq_nonneg _)
  simpa using Real.one_le_exp this |>.trans' (le_refl _)

/-- **The index bound in `expLogSq` form**: `b^{2 log₂ b} ≤ exp(3 log²(N + 2))` for `b ≤ N`. -/
theorem tm_rpow_le_expLogSq {b N : ℕ} (hb : b ≤ N) :
    (b : ℝ) ^ (2 * Real.logb 2 b) ≤ expLogSq 3 N := by
  rcases Nat.eq_zero_or_pos b with rfl | hb0
  · have := tm_one_le_expLogSq (a := 3) (by norm_num) N
    simpa [Real.logb_zero] using this
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb0
  have hbpos : (0 : ℝ) < b := by linarith
  unfold expLogSq
  rw [Real.rpow_def_of_pos hbpos]
  apply Real.exp_le_exp.2
  have hl0 : 0 ≤ Real.log b := Real.log_nonneg hb1
  have hlN : Real.log b ≤ Real.log ((N : ℝ) + 2) :=
    Real.log_le_log hbpos (by have : (b : ℝ) ≤ N := (by exact_mod_cast hb); linarith)
  have hl2 : (2 : ℝ) / 3 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  rw [Real.logb]
  have hl2p : 0 < Real.log 2 := by linarith
  have key : Real.log b * (2 * (Real.log b / Real.log 2)) =
      2 * Real.log b ^ 2 / Real.log 2 := by ring
  rw [key, div_le_iff₀ hl2p]
  have h1 : Real.log b ^ 2 ≤ Real.log ((N : ℝ) + 2) ^ 2 := pow_le_pow_left₀ hl0 hlN 2
  have h2 : 0 ≤ Real.log ((N : ℝ) + 2) ^ 2 := sq_nonneg _
  nlinarith

end GI.Impl
