module

public import Workspace.Assembly.GenReq
public import Workspace.Impl.AggSpecReq

@[expose] public section

/-!
# Stage 2 up to the row step and the four phases of the aggregation round

`final_modulo_agg`: with the general dispatcher of `gsGen` and the aggregation round of `asAgg`
(`as_asm_agg`, work `asWa`), the trusted statement follows from

* the step specification of the row step and its work bounds (as in `final_modulo_gen`);
* the contracts of the reading, the certificate phase, the comparison phase and the items of the
  aggregation round (`AsReadOK`, `AsCertOK`, `AsCompOK`, `AsItemsOK`), with a phase bound `X`
  that is uniformly polynomial (then `asWa_le` gives the work bound of the round).
-/

namespace GI.Assembly

open GI.Algorithm GI.Lang GI.Paper GI.Impl
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership MinimalBlocks GroupOrder
  CameronRecognition)

/-- **Stage 2 up to the row step and the phases of the aggregation round.** -/
theorem final_modulo_agg (hst : PointwiseStab) (hm : Membership) (hpre : Preimage)
    (hfac : NormalizedFactor) (hmb : MinimalBlocks) (hO : GroupOrder) (hC : CameronRecognition)
    (row : List Expr) (Wr : Node P₀ → ℝ) (H : AsHand) (X : ℕ → ℕ) (rd cr cm it : Expr)
    (rest : List Expr) (hrowl : row.length ≤ asmSlot)
    (hrow : (asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC) Wr
      (asWa hst hm hpre hfac X)).iface.RowSpec
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC) gsGen row (asAgg rd cr cm it rest)) asmF
        asmRowBase)
    (hr : AsReadOK (asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC) Wr
      (asWa hst hm hpre hfac X)).iface
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC) gsGen row (asAgg rd cr cm it rest)) asmF H X
        (asb 1))
    (hc : AsCertOK (asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC) Wr
      (asWa hst hm hpre hfac X)).iface
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC) gsGen row (asAgg rd cr cm it rest)) asmF H X
        (asb 2))
    (hcm : AsCompOK (asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC) Wr
      (asWa hst hm hpre hfac X)).iface
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC) gsGen row (asAgg rd cr cm it rest)) asmF H X
        (asb 3))
    (hi : AsItemsOK (asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC) Wr
      (asWa hst hm hpre hfac X)).iface
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC) gsGen row (asAgg rd cr cm it rest)) asmF H X
        (asb 4))
    (hX : PBU fun _ W _ => X W)
    (hrr : ∃ A D : ℕ, ∀ nd : Node P₀, nd.m ≠ .solve → Nat.card nd.Ω ≤ nd.S.N → Small nd.S →
      (nd.run.kind = .rowTerminal → Wr nd ≤ expLogSq A nd.S.N) ∧
      (nd.run.kind = .rowColumns → Wr nd ≤ A * ((nd.S.N : ℝ) + 2) ^ D)) :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime := by
  refine final_modulo_gen hst hm hpre hfac hmb hO hC row (asAgg rd cr cm it rest) Wr
    (asWa hst hm hpre hfac X) hrow
    (as_asm_agg hst hm hpre hfac _ gsGen row _ _ H X rd cr cm it rest
      (by rw [length_gsGen]; unfold asmSlot; omega) hrowl hr hc hcm hi) ?_
  obtain ⟨A₁, D₁, h₁⟩ := hrr
  obtain ⟨A₂, D₂, h₂⟩ := asWa_le hst hm hpre hfac hX
  refine ⟨A₁ + A₂, max D₁ D₂, fun nd hnd hk hs => ⟨fun hk' => ?_, fun hk' => ?_, fun _ => ?_⟩⟩
  · refine ((h₁ nd hnd hk hs).1 hk').trans (asm_expLogSq_mono ?_ _)
    exact_mod_cast Nat.le_add_right _ _
  · have hX1 : (1 : ℝ) ≤ (nd.S.N : ℝ) + 2 := by have := (Nat.cast_nonneg nd.S.N : (0:ℝ) ≤ _); linarith
    refine ((h₁ nd hnd hk hs).2 hk').trans ?_
    have e1 : ((nd.S.N : ℝ) + 2) ^ D₁ ≤ ((nd.S.N : ℝ) + 2) ^ max D₁ D₂ :=
      pow_le_pow_right₀ hX1 (le_max_left _ _)
    have e2 : (A₁ : ℝ) ≤ ((A₁ + A₂ : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right _ _
    exact mul_le_mul e2 e1 (by positivity) (by positivity)
  · have hX1 : (1 : ℝ) ≤ (nd.S.N : ℝ) + 2 := by have := (Nat.cast_nonneg nd.S.N : (0:ℝ) ≤ _); linarith
    refine (h₂ nd hk hs).trans ?_
    have e1 : ((nd.S.N : ℝ) + 2) ^ D₂ ≤ ((nd.S.N : ℝ) + 2) ^ max D₁ D₂ :=
      pow_le_pow_right₀ hX1 (le_max_right _ _)
    have e2 : (A₂ : ℝ) ≤ ((A₁ + A₂ : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left _ _
    exact mul_le_mul e2 e1 (by positivity) (by positivity)

/-- **`final_modulo_agg` with more primitives** `ext` after `gsExtra`. -/
theorem final_modulo_agg_ext
    (hst : PointwiseStab) (hm : Membership) (hpre : Preimage)
    (hfac : NormalizedFactor) (hmb : MinimalBlocks) (hO : GroupOrder) (hC : CameronRecognition)
    (ext : List Prim) (row : List Expr) (Wr : Node P₀ → ℝ) (H : AsHand) (X : ℕ → ℕ) (rd cr cm it : Expr)
    (rest : List Expr) (hrowl : row.length ≤ asmSlot)
    (hrow : (asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC) Wr
      (asWa hst hm hpre hfac X)).iface.RowSpec
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC ++ ext) gsGen row (asAgg rd cr cm it rest)) asmF
        asmRowBase)
    (hr : AsReadOK (asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC) Wr
      (asWa hst hm hpre hfac X)).iface
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC ++ ext) gsGen row (asAgg rd cr cm it rest)) asmF H X
        (asb 1))
    (hc : AsCertOK (asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC) Wr
      (asWa hst hm hpre hfac X)).iface
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC ++ ext) gsGen row (asAgg rd cr cm it rest)) asmF H X
        (asb 2))
    (hcm : AsCompOK (asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC) Wr
      (asWa hst hm hpre hfac X)).iface
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC ++ ext) gsGen row (asAgg rd cr cm it rest)) asmF H X
        (asb 3))
    (hi : AsItemsOK (asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC) Wr
      (asWa hst hm hpre hfac X)).iface
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC ++ ext) gsGen row (asAgg rd cr cm it rest)) asmF H X
        (asb 4))
    (hX : PBU fun _ W _ => X W)
    (hrr : ∃ A D : ℕ, ∀ nd : Node P₀, nd.m ≠ .solve → Nat.card nd.Ω ≤ nd.S.N → Small nd.S →
      (nd.run.kind = .rowTerminal → Wr nd ≤ expLogSq A nd.S.N) ∧
      (nd.run.kind = .rowColumns → Wr nd ≤ A * ((nd.S.N : ℝ) + 2) ^ D)) :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime := by
  refine final_modulo_gen_ext hst hm hpre hfac hmb hO hC ext row (asAgg rd cr cm it rest) Wr
    (asWa hst hm hpre hfac X) hrow
    (as_asm_agg hst hm hpre hfac _ gsGen row _ _ H X rd cr cm it rest
      (by rw [length_gsGen]; unfold asmSlot; omega) hrowl hr hc hcm hi) ?_
  obtain ⟨A₁, D₁, h₁⟩ := hrr
  obtain ⟨A₂, D₂, h₂⟩ := asWa_le hst hm hpre hfac hX
  refine ⟨A₁ + A₂, max D₁ D₂, fun nd hnd hk hs => ⟨fun hk' => ?_, fun hk' => ?_, fun _ => ?_⟩⟩
  · refine ((h₁ nd hnd hk hs).1 hk').trans (asm_expLogSq_mono ?_ _)
    exact_mod_cast Nat.le_add_right _ _
  · have hX1 : (1 : ℝ) ≤ (nd.S.N : ℝ) + 2 := by have := (Nat.cast_nonneg nd.S.N : (0:ℝ) ≤ _); linarith
    refine ((h₁ nd hnd hk hs).2 hk').trans ?_
    have e1 : ((nd.S.N : ℝ) + 2) ^ D₁ ≤ ((nd.S.N : ℝ) + 2) ^ max D₁ D₂ :=
      pow_le_pow_right₀ hX1 (le_max_left _ _)
    have e2 : (A₁ : ℝ) ≤ ((A₁ + A₂ : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right _ _
    exact mul_le_mul e2 e1 (by positivity) (by positivity)
  · have hX1 : (1 : ℝ) ≤ (nd.S.N : ℝ) + 2 := by have := (Nat.cast_nonneg nd.S.N : (0:ℝ) ≤ _); linarith
    refine (h₂ nd hk hs).trans ?_
    have e1 : ((nd.S.N : ℝ) + 2) ^ D₂ ≤ ((nd.S.N : ℝ) + 2) ^ max D₁ D₂ :=
      pow_le_pow_right₀ hX1 (le_max_right _ _)
    have e2 : (A₂ : ℝ) ≤ ((A₁ + A₂ : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left _ _
    exact mul_le_mul e2 e1 (by positivity) (by positivity)

end GI.Assembly
