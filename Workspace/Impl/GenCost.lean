import Workspace.Impl.GenEnum
import Workspace.Impl.PolyBd
import Workspace.Impl.Weights

/-!
# Polynomial bounds on the own costs of the general dispatcher

The own cost of each part of the general dispatcher of `Continue` is a sum of products of
powers of the weights, of the bound `B` on the order of the quotient group, and of the cost
bounds of the cited algorithms. Each is at most `C * X ^ D` for `X = W + B + k + 2`, with
constants `C` and `D` that depend only on the cited algorithms. With `B ≤ d ^ (b ⌊log₂ d⌋)` for
a small quotient, this is at most `exp(A (log (N + 2))²)`, the work allowed at a dispatcher node
(`Rest.Req`).
-/

namespace GI.Impl

open GI.Lang GI.Paper GI.Algorithm
open GI.Cited (Val Membership Preimage)

/-- **The own cost of the enumeration step is polynomial** in `W + B + k`. -/
theorem enumCost_poly (hp : Preimage) (hm : Membership) :
    PBU fun k W B => enumCost hp hm k W B := by
  have pgroup : PBU fun k _ _ => groupW k :=
    PBU.smul 40 (PBU.pow (PBU.mul (PBU.addc (PBU.pow PBU.k 2) 2) PBU.k1) 2)
  have pans : PBU fun k _ _ => ansW k :=
    PBU.addc (PBU.smul 2 (PBU.add (PBU.smul 4 (PBU.pow PBU.k1 2)) pgroup)) 6
  have ppairs : PBU fun k _ B => pairsW k B :=
    PBU.addc (PBU.mul PBU.B (PBU.addc (PBU.smul 2
      (PBU.addc (PBU.smul 16 (PBU.pow PBU.k1 2)) 6)) 1)) 4
  have pT : PBU fun k W B => tailInW k W B :=
    PBU.addc (PBU.smul 2 (PBU.add (PBU.addc (PBU.smul 2 (PBU.add PBU.W pgroup)) 7) ppairs)) 6
  have ppiece : PBU fun k _ _ => pieceW k :=
    PBU.addc (PBU.smul 2 (PBU.add (PBU.smul 4 (PBU.pow PBU.k1 2)) pans)) 6
  have ppieces : PBU fun k W B => piecesW k (tailInW k W B) :=
    PBU.addc (PBU.mul pT (PBU.addc (PBU.smul 2 ppiece) 1)) 4
  have pin : PBU fun k W B => combInW k (tailInW k W B) := PBU.addc (PBU.smul 2 ppieces) 30
  have pout : PBU fun k W B => combOutW k (tailInW k W B) :=
    PBU.smul 100 (PBU.pow (PBU.mul (PBU.addc pin 2) PBU.k1) 2)
  have pcombM : PBU fun k W B => combM k (combInW k (tailInW k W B)) :=
    PBU.smul 100 (PBU.pow (PBU.mul (PBU.addc pin 2) PBU.k1) 2)
  have pcomb : PBU fun k W B => combCost k (combInW k (tailInW k W B)) :=
    PBU.mul (PBU.addc pin 1) (PBU.add
      (PBU.smul combK (PBU.pow (PBU.add (PBU.addc (PBU.add (PBU.smul 4 pin)
        (PBU.smul 2 pcombM)) 7) (PBU.pow PBU.k1 4)) 2))
      (PBU.smul loopModK (PBU.addc (PBU.add (PBU.smul 2 pin) pcombM) 1)))
  have pmem : PBU fun k _ _ => memCost hm k :=
    PBU.smul (membershipPrim hm).c
      (PBU.pow (PBU.smul 400 (PBU.pow PBU.k1 6)) (membershipPrim hm).k)
  have pnf : PBU fun k W B => cosetNFCost hm k (combOutW k (tailInW k W B)) :=
    PBU.add (PBU.add (PBU.add (PBU.mul (PBU.addc pout 1) pmem)
      (PBU.smul reduceK (PBU.pow (PBU.mul (PBU.addc pout 2) PBU.k1) 6)))
      (PBU.smul 20 pout)) (PBU.smul 2000 (PBU.pow PBU.k1 6))
  have pchild : PBU fun k W B =>
      enumChildB (10 * tailInW k W B + ansW k + 20 * (k + 1) ^ 2 + 40) :=
    PBU.smul (10 ^ 7) (PBU.pow (PBU.addc (PBU.addc (PBU.add (PBU.add
      (PBU.smul 10 pT) pans) (PBU.smul 20 (PBU.pow PBU.k1 2))) 40) 1) 3)
  have ptail : PBU fun k W B => tailCost hm k (tailInW k W B) :=
    PBU.addc (PBU.add (PBU.add (PBU.add (PBU.add (PBU.add (PBU.add
      (PBU.mul pT pchild)
      (PBU.mul (PBU.smul mapQK (PBU.addc pT 1)) (PBU.addc (PBU.add pT ppieces) 1)))
      pcomb) pnf) (PBU.smul 6 pin)) (PBU.smul 2 pout)) (PBU.smul 2 pans)) 100
  have pT6 : PBU fun _ W _ => 2 * W + 6 := PBU.addc (PBU.smul 2 PBU.W) 6
  have pker : PBU fun k W _ => kerNFCost hp hm k (2 * W + 6) :=
    PBU.add (PBU.add (PBU.add (PBU.add
      (PBU.smul (preimagePrim hp).c (PBU.pow (PBU.addc (PBU.smul 3 pT6) 2) (preimagePrim hp).k))
      (PBU.smul kerK (PBU.pow pT6 9)))
      (PBU.add (PBU.mul (PBU.addc (PBU.smul 320 (PBU.pow PBU.k1 6)) 1) pmem)
        (PBU.smul reduceK (PBU.pow (PBU.mul (PBU.addc (PBU.smul 320 (PBU.pow PBU.k1 6)) 2)
          PBU.k1) 6))))
      (PBU.smul 1000 (PBU.pow PBU.k1 6))) (PBU.smul 10 pT6)
  have pcos : PBU fun k W B => cosetsK * (W + B + 4 * (k + 1) ^ 2 + 20) ^ 6 :=
    PBU.smul cosetsK (PBU.pow (PBU.addc (PBU.add (PBU.add PBU.W PBU.B)
      (PBU.smul 4 (PBU.pow PBU.k1 2))) 20) 6)
  exact PBU.addc (PBU.add (PBU.add (PBU.add (PBU.add (PBU.add (PBU.add
    (PBU.add pcos pker) ptail) (PBU.smul 20 pT)) (PBU.smul 200 PBU.W)) (PBU.smul 4 pgroup))
    (PBU.smul 4 ppairs)) (PBU.smul 4 pans)) 1000

/-- `L log 2 ≤ log n` for `L = ⌊log₂ n⌋` and `n ≥ 1`. -/
theorem natLog_mul_log_two_le {n : ℕ} (hn : 1 ≤ n) :
    (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
  have h2L : ((2 ^ Nat.log 2 n : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have := Real.log_le_log (by positivity) h2L
  rwa [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] at this

/-- **A uniformly polynomial cost fits in `E_N`** when `k ≤ N`, the weight is polynomial in `N`
and `B ≤ (N + 2) ^ (b ⌊log₂ (N + 2)⌋)` (the bound of the integer small test). -/
theorem PBU.le_expLogSq {f : ℕ → ℕ → ℕ → ℕ} (hf : PBU f) (a d b : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ k W B N : ℕ, k ≤ N → W ≤ a * (N + 2) ^ d →
      B ≤ (N + 2) ^ (b * Nat.log 2 (N + 2)) → (f k W B : ℝ) ≤ expLogSq A N := by
  obtain ⟨C, D, h⟩ := hf
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨3 * (Real.log ((C * (a + 3) ^ D : ℕ) + 1 : ℝ) + ((d + 1) * D : ℕ)) +
    (b * D : ℝ) / Real.log 2, ?_, fun k W B N hk hW hB => ?_⟩
  · have : 0 ≤ Real.log ((C * (a + 3) ^ D : ℕ) + 1 : ℝ) :=
      Real.log_nonneg (by have := (Nat.cast_nonneg (α := ℝ) (C * (a + 3) ^ D)); linarith)
    have : (0 : ℝ) ≤ (b * D : ℝ) / Real.log 2 := by positivity
    positivity
  set L2 := Nat.log 2 (N + 2) with hL2
  set e := d + b * L2 + 1 with he
  have hN1 : 1 ≤ N + 2 := by omega
  have hpe : ∀ j, j ≤ e → (N + 2) ^ j ≤ (N + 2) ^ e := fun j hj => Nat.pow_le_pow_right hN1 hj
  have hX : W + B + k + 2 ≤ (a + 3) * (N + 2) ^ e := by
    have h1 := Nat.mul_le_mul_left a (hpe d (by omega))
    have h2 := hpe (b * L2) (by omega)
    have h3 : N + 2 ≤ (N + 2) ^ e := by
      have := hpe 1 (by omega); simpa using this
    nlinarith
  have hf1 := (h k W B).trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hX D))
  have hsplit : C * ((a + 3) * (N + 2) ^ e) ^ D =
      (C * (a + 3) ^ D * (N + 2) ^ ((d + 1) * D)) * (N + 2) ^ (b * L2 * D) := by
    rw [mul_pow, ← pow_mul, ← mul_assoc, mul_assoc _ ((N + 2) ^ ((d + 1) * D)), ← pow_add, he]
    ring_nf
  rw [hsplit] at hf1
  have hR : (f k W B : ℝ) ≤ ((C * (a + 3) ^ D : ℕ) + 1 : ℝ) * ((N : ℝ) + 2) ^ ((d + 1) * D) *
      ((N : ℝ) + 2) ^ (b * L2 * D) := by
    have := (Nat.cast_le (α := ℝ)).mpr hf1
    push_cast at this ⊢
    have hp1 : (0 : ℝ) ≤ ((N : ℝ) + 2) ^ ((d + 1) * D) * ((N : ℝ) + 2) ^ (b * L2 * D) := by
      positivity
    nlinarith
  have hA1 := pow_le_expLogSq (A := ((C * (a + 3) ^ D : ℕ) + 1 : ℝ))
    (by have := (Nat.cast_nonneg (α := ℝ) (C * (a + 3) ^ D)); linarith) ((d + 1) * D) N
  -- the second factor
  have hL : (L2 : ℝ) * Real.log 2 ≤ Real.log ((N : ℝ) + 2) := by
    have := natLog_mul_log_two_le (n := N + 2) (by omega)
    push_cast at this; exact this
  have hLpos : 0 ≤ Real.log ((N : ℝ) + 2) := Real.log_nonneg (by linarith [N.cast_nonneg (α := ℝ)])
  have hA2 : ((N : ℝ) + 2) ^ (b * L2 * D) ≤ expLogSq ((b * D : ℝ) / Real.log 2) N := by
    unfold expLogSq
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity), Real.exp_le_exp]
    push_cast
    have hb : (0 : ℝ) ≤ b * D := by positivity
    have hL' : (L2 : ℝ) ≤ Real.log ((N : ℝ) + 2) / Real.log 2 := by
      rw [le_div_iff₀ hl2]; exact hL
    calc Real.log ((N : ℝ) + 2) * (b * L2 * D)
        = (b * D) * L2 * Real.log ((N : ℝ) + 2) := by ring
      _ ≤ (b * D) * (Real.log ((N : ℝ) + 2) / Real.log 2) * Real.log ((N : ℝ) + 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL' hb) hLpos
      _ = (b * D : ℝ) / Real.log 2 * Real.log ((N : ℝ) + 2) ^ 2 := by ring
  rw [expLogSq_add]
  calc (f k W B : ℝ) ≤ _ := hR
    _ ≤ _ := mul_le_mul hA1 hA2 (by positivity) (expLogSq_nonneg _ _)

end GI.Impl
