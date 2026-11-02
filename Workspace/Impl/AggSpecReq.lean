import Workspace.Impl.AggSpecLayout
import Workspace.Impl.GenNormStepCost

/-!
# The work of the aggregation round is polynomial in `N`

`Rest.Req` (through `AsmOpenReq`) asks `Wa nd ≤ A (N + 2)^D` at every aggregation node that fits
its phase (`|Ω| ≤ N`, `Small`). For `Wa = asWa … X` (`AggSpecLayout.lean`) this holds when the
phase bound `X` is polynomial (`asWa_le`):

* the input weight bound `2 (stateW k S + labWStd k N) + 6` is polynomial in `N`
  (`stateW_le_of_small`);
* `asOwn k W` is a uniformly polynomial function of `k` and `W` when `X` is (`asOwn_poly`): every
  part (the overhead, `LiftAndContinue` through `lcB`, `CombineExact` through `ceCost`) is a
  polynomial in the weights, with the cited primitives through their constants and exponents.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Paper
open GI.Cited (PointwiseStab Preimage NormalizedFactor Membership)

/-- The largest value up to `W` of a uniformly polynomial function is uniformly polynomial. -/
theorem asMax_pbu {f : ℕ → ℕ → ℕ} (hf : PBU fun k W _ => f k W) :
    PBU fun k W _ => asMax (f k) W := by
  obtain ⟨C, D, h⟩ := hf
  refine ⟨C, D, fun k W B => ?_⟩
  unfold PB asMax
  refine Finset.sup_le fun m hm => ?_
  have hm' : m ≤ W := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
  exact (h k m B).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))

/-- The own cost of one continuation is polynomial in the weight. -/
theorem lcB_pbu (hst : PointwiseStab) (hpre : Preimage) (hfac : NormalizedFactor) :
    PBU fun _ M _ => lcB (preimagePrim hpre) (normalizedFactorPrim hfac) (abKrC hst) M := by
  unfold lcB lcX abKrC liftLabCost Prim.boundSize
  norm_poly

/-- The cost of `CombineExact` is polynomial in `k` and the weight. -/
theorem ceCost_pbu (hm : Membership) : PBU fun k W _ => ceCost hm k W := by
  simp only [ceCost, ceInW, ceOutW, combCost, combM, cosetNFCost, reduceCost, memCost, ansW,
    groupW]
  norm_poly

/-- `asOwn` with the phase bound as the third variable. -/
noncomputable def asOwnY (hst : PointwiseStab) (hpre : Preimage) (hfac : NormalizedFactor)
    (hm : Membership) (k W Y : ℕ) : ℕ :=
  100 * (W + Y + asWl Y + asWw k Y + asWc k Y + ansW k + 10) +
    Y * asMax (lcB (preimagePrim hpre) (normalizedFactorPrim hfac) (abKrC hst)) (2 * asWl Y + 6) +
    mapQK * (Y + 1) * (asWl Y + asWw k Y + 1) +
    asMax (ceCost hm k) (asWc k Y)

theorem asOwnY_pbu (hst : PointwiseStab) (hpre : Preimage) (hfac : NormalizedFactor)
    (hm : Membership) : PBU fun k W Y => asOwnY hst hpre hfac hm k W Y := by
  have hA : PBU fun k _ _ => ansW k := by unfold ansW groupW; norm_poly
  have hl : PBU fun _ _ Y => asWl Y := by unfold asWl; norm_poly
  have hw : PBU fun k _ Y => asWw k Y := by unfold asWw asEW ansW groupW; norm_poly
  have hc : PBU fun k _ Y => asWc k Y := by unfold asWc asWw asEW ansW groupW; norm_poly
  have hL : PBU fun k _ Y => asMax (lcB (preimagePrim hpre) (normalizedFactorPrim hfac)
      (abKrC hst)) (2 * asWl Y + 6) :=
    normPoly_subst (asMax_pbu (f := fun _ M => lcB (preimagePrim hpre) (normalizedFactorPrim hfac)
      (abKrC hst) M) (lcB_pbu hst hpre hfac)) PBU.k (PBU.addc (PBU.smul 2 hl) 6) PBU.B
  have hC : PBU fun k _ Y => asMax (ceCost hm k) (asWc k Y) :=
    normPoly_subst (asMax_pbu (f := fun k W => ceCost hm k W) (ceCost_pbu hm)) PBU.k hc PBU.B
  unfold asOwnY
  exact PBU.add (PBU.add (PBU.add (PBU.smul 100 (PBU.addc (PBU.add (PBU.add (PBU.add (PBU.add
    (PBU.add PBU.W PBU.B) hl) hw) hc) hA) 10)) (PBU.mul PBU.B hL))
    (PBU.mul (PBU.smul mapQK (PBU.addc PBU.B 1)) (PBU.addc (PBU.add hl hw) 1))) hC

/-- **`asOwn` is uniformly polynomial** in `k` and the weight, when the phase bound is. -/
theorem asOwn_poly (hst : PointwiseStab) (hpre : Preimage) (hfac : NormalizedFactor)
    (hm : Membership) {X : ℕ → ℕ} (hX : PBU fun _ W _ => X W) :
    PBU fun k W _ => asOwn hpre hfac hm (abKrC hst) X k W :=
  normPoly_subst (asOwnY_pbu hst hpre hfac hm) PBU.k PBU.W hX

/-- **The work of the aggregation round is polynomial in `N`** at every fitting node, when the
phase bound `X` is polynomial. -/
theorem asWa_le (hst : PointwiseStab) (hm : Membership) (hpre : Preimage)
    (hfac : NormalizedFactor) {X : ℕ → ℕ} (hX : PBU fun _ W _ => X W) :
    ∃ A D : ℕ, ∀ nd : Node P₀, Nat.card nd.Ω ≤ nd.S.N → Small nd.S →
      asWa hst hm hpre hfac X nd ≤ A * ((nd.S.N : ℝ) + 2) ^ D := by
  obtain ⟨C, D, h⟩ := asOwn_poly hst hpre hfac hm hX
  refine ⟨C * (10 ^ 6) ^ D, 6 * D, fun nd hk hs => ?_⟩
  set k := Nat.card nd.Ω
  set N := nd.S.N
  have hW : stateW k nd.S ≤ 10 ^ 4 * (N + 2) ^ 6 := stateW_le_of_small hk hs
  have h1 : 2 * (stateW k nd.S + labWStd k N) + 6 + 0 + k + 2 ≤ 10 ^ 6 * (N + 2) ^ 6 := by
    have e1 : (k + 1) ^ 4 ≤ (N + 2) ^ 6 :=
      (Nat.pow_le_pow_left (by omega) 4).trans (Nat.pow_le_pow_right (by omega) (by omega))
    have e2 : N + 2 ≤ (N + 2) ^ 6 := Nat.le_self_pow (by omega) _
    unfold labWStd
    omega
  have h2 := h k (2 * (stateW k nd.S + labWStd k N) + 6) 0
  unfold PB at h2
  have h3 : asOwn hpre hfac hm (abKrC hst) X k (2 * (stateW k nd.S + labWStd k N) + 6) ≤
      C * (10 ^ 6) ^ D * (N + 2) ^ (6 * D) := by
    refine h2.trans ?_
    calc C * (2 * (stateW k nd.S + labWStd k N) + 6 + 0 + k + 2) ^ D
        ≤ C * (10 ^ 6 * (N + 2) ^ 6) ^ D := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _)
      _ = C * (10 ^ 6) ^ D * (N + 2) ^ (6 * D) := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_assoc]
  unfold asWa
  exact_mod_cast h3

end GI.Impl
