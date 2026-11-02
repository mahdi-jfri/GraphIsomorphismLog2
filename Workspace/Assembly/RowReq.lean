import Workspace.Impl.RowReq
import Workspace.Assembly.GenReq
import Workspace.Assembly.AggReq

/-!
# Stage 2 up to the aggregation round and the open pieces of the row terminal

`final_modulo_row` proves the trusted statement for the program
`asmProg … (gsExtra …) gsGen (rlRow rad cos) agg`: the general dispatcher of `gsGen`
(`gs_asm_general`) and the row step of `rlRow` (`rq_rowSpec`) are proved. What is left as
hypotheses:

* the aggregation round: its step specification `AggSpec` at `asmAggBase` and the bound
  `A (N + 2)^D` on its work `Wa` at `aggregate` nodes;
* the two open pieces of the row terminal (Theorem A.23), as specifications of the code `rad` and
  `cos` placed in the row list: T2, the radical preimage (`TermRadSpec`, paragraph after
  Lemma A.21), and T4–T6, one radical coset (`TermCosetSpec`, Theorem A.20 inside a coset of the
  radical preimage, then the labels of A.23).

`final_modulo_row_agg` is the same with the aggregation round (`asAgg` at
`asmAggBase`, `final_modulo_agg`): the aggregation side is then its four phase contracts
(`AsReadOK`, `AsCertOK`, `AsCompOK`, `AsItemsOK`) and a polynomial bound on its weight function
`X`, and the only other open hypotheses are `TermRadSpec` and `TermCosetSpec`.

The work of the row step is `rqWr` with the terminal constant `rqAa`; its bounds are
`rq_wr_bound`.
-/

namespace GI.Assembly

open GI.Algorithm GI.Lang GI.Paper GI.Impl
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership MinimalBlocks GroupOrder
  CameronRecognition)

/-- **Stage 2 up to the aggregation round and two pieces of the row terminal.** -/
theorem final_modulo_row (hcite : GI.Cited.TransitiveAffected) (hst : PointwiseStab)
    (hm : Membership) (hpre : Preimage) (hfac : NormalizedFactor) (hmb : MinimalBlocks)
    (hO : GroupOrder) (hC : CameronRecognition) (hAb : GI.Cited.GMPAbelianFactors)
    (hOut : GI.Cited.GMPOutBound) (hTr : GI.Cited.GMPTransitiveNonabelian)
    (rad cos agg : List Expr) (hr : rad.length ≤ rlCosOff - rlRadOff)
    (hc : cos.length ≤ asmSlot - rlCosOff) {K D : ℕ} {Ac : ℝ} (Wa : Node P₀ → ℝ)
    (hrad : Iface.TermRadSpec
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC) gsGen (rlRow rad cos) agg) K D
      (rlb rlRadOff))
    (hcos : Iface.TermCosetSpec
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC) gsGen (rlRow rad cos) agg) Ac
      (rlb rlCosOff))
    (hagg : (asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC)
      (rqWr hst hfac (rqAa hst hm hpre hfac K D Ac)) Wa).iface.AggSpec
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC) gsGen (rlRow rad cos) agg) asmF asmAggBase)
    (hWa : ∃ A D : ℕ, ∀ nd : Node P₀, nd.m ≠ .solve → Nat.card nd.Ω ≤ nd.S.N → Small nd.S →
      nd.run.kind = .aggregate → Wa nd ≤ A * ((nd.S.N : ℝ) + 2) ^ D) :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime := by
  have hg : gsGen.length ≤ asmSlot := by rw [length_gsGen]; unfold asmSlot; omega
  refine final_modulo_gen hst hm hpre hfac hmb hO hC (rlRow rad cos) agg _ Wa
    (rq_rowSpec hcite hst hm hpre hfac hAb hOut hTr hg hr hc hrad hcos _ Wa) hagg ?_
  obtain ⟨A₁, D₁, h₁⟩ := rq_wr_bound hst hfac (rqAa_nonneg hst hm hpre hfac K D Ac)
  obtain ⟨A₂, D₂, h₂⟩ := hWa
  refine ⟨A₁ + A₂, D₁ + D₂, fun nd hnd hk hs => ⟨fun hk' => ?_, fun hk' => ?_, fun hk' => ?_⟩⟩
  · refine ((h₁ nd).1 hk').trans (asm_expLogSq_mono ?_ _)
    exact_mod_cast Nat.le_add_right _ _
  · have hX1 : (1 : ℝ) ≤ (nd.S.N : ℝ) + 2 := by
      have := Nat.cast_nonneg (α := ℝ) nd.S.N; linarith
    have hp : ((nd.S.N : ℝ) + 2) ^ D₁ ≤ ((nd.S.N : ℝ) + 2) ^ (D₁ + D₂) :=
      pow_le_pow_right₀ hX1 (Nat.le_add_right _ _)
    have hA : (A₁ : ℝ) ≤ ((A₁ + A₂ : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right _ _
    exact ((h₁ nd).2 hk').trans (mul_le_mul hA hp (pow_nonneg (by linarith) _) (by positivity))
  · have hX1 : (1 : ℝ) ≤ (nd.S.N : ℝ) + 2 := by
      have := Nat.cast_nonneg (α := ℝ) nd.S.N; linarith
    have hp : ((nd.S.N : ℝ) + 2) ^ D₂ ≤ ((nd.S.N : ℝ) + 2) ^ (D₁ + D₂) :=
      pow_le_pow_right₀ hX1 (Nat.le_add_left _ _)
    have hA : (A₂ : ℝ) ≤ ((A₁ + A₂ : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left _ _
    exact (h₂ nd hnd hk hs hk').trans
      (mul_le_mul hA hp (pow_nonneg (by linarith) _) (by positivity))

/-- **Stage 2 up to the four phase contracts of the aggregation round and two pieces of the row
terminal.** The row step of `rlRow` and the aggregation round of `asAgg` in one program. -/
theorem final_modulo_row_agg (hcite : GI.Cited.TransitiveAffected) (hst : PointwiseStab)
    (hm : Membership) (hpre : Preimage) (hfac : NormalizedFactor) (hmb : MinimalBlocks)
    (hO : GroupOrder) (hC : CameronRecognition) (hAb : GI.Cited.GMPAbelianFactors)
    (hOut : GI.Cited.GMPOutBound) (hTr : GI.Cited.GMPTransitiveNonabelian)
    (rad cos : List Expr) (hr : rad.length ≤ rlCosOff - rlRadOff)
    (hc : cos.length ≤ asmSlot - rlCosOff) {K D : ℕ} {Ac : ℝ}
    (H : AsHand) (X : ℕ → ℕ) (rd cr cm it : Expr) (rest : List Expr)
    (hrad : Iface.TermRadSpec
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC) gsGen (rlRow rad cos)
        (asAgg rd cr cm it rest)) K D (rlb rlRadOff))
    (hcos : Iface.TermCosetSpec
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC) gsGen (rlRow rad cos)
        (asAgg rd cr cm it rest)) Ac (rlb rlCosOff))
    (hrd : AsReadOK (asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC)
      (rqWr hst hfac (rqAa hst hm hpre hfac K D Ac)) (asWa hst hm hpre hfac X)).iface
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC) gsGen (rlRow rad cos)
        (asAgg rd cr cm it rest)) asmF H X (asb 1))
    (hct : AsCertOK (asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC)
      (rqWr hst hfac (rqAa hst hm hpre hfac K D Ac)) (asWa hst hm hpre hfac X)).iface
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC) gsGen (rlRow rad cos)
        (asAgg rd cr cm it rest)) asmF H X (asb 2))
    (hcm : AsCompOK (asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC)
      (rqWr hst hfac (rqAa hst hm hpre hfac K D Ac)) (asWa hst hm hpre hfac X)).iface
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC) gsGen (rlRow rad cos)
        (asAgg rd cr cm it rest)) asmF H X (asb 3))
    (hi : AsItemsOK (asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC)
      (rqWr hst hfac (rqAa hst hm hpre hfac K D Ac)) (asWa hst hm hpre hfac X)).iface
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC) gsGen (rlRow rad cos)
        (asAgg rd cr cm it rest)) asmF H X (asb 4))
    (hX : PBU fun _ W _ => X W) :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime := by
  have hg : gsGen.length ≤ asmSlot := by rw [length_gsGen]; unfold asmSlot; omega
  have hl : (rlRow rad cos).length ≤ asmSlot := by
    rw [length_rlRow hr]; unfold asmSlot rlCosOff at *; omega
  refine final_modulo_agg hst hm hpre hfac hmb hO hC (rlRow rad cos) _ H X rd cr cm it rest hl
    (rq_rowSpec hcite hst hm hpre hfac hAb hOut hTr hg hr hc hrad hcos _ _) hrd hct hcm hi hX ?_
  obtain ⟨A, D', h⟩ := rq_wr_bound hst hfac (rqAa_nonneg hst hm hpre hfac K D Ac)
  exact ⟨A, D', fun nd _ _ _ => h nd⟩

/-- **`final_modulo_row_agg` with more primitives** `ext` after `gsExtra`. -/
theorem final_modulo_row_agg_ext (hcite : GI.Cited.TransitiveAffected) (hst : PointwiseStab)
    (hm : Membership) (hpre : Preimage) (hfac : NormalizedFactor) (hmb : MinimalBlocks)
    (hO : GroupOrder) (hC : CameronRecognition) (hAb : GI.Cited.GMPAbelianFactors)
    (hOut : GI.Cited.GMPOutBound) (hTr : GI.Cited.GMPTransitiveNonabelian)
    (ext : List Prim) (rad cos : List Expr) (hr : rad.length ≤ rlCosOff - rlRadOff)
    (hc : cos.length ≤ asmSlot - rlCosOff) {K D : ℕ} {Ac : ℝ}
    (H : AsHand) (X : ℕ → ℕ) (rd cr cm it : Expr) (rest : List Expr)
    (hrad : Iface.TermRadSpec
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC ++ ext) gsGen (rlRow rad cos)
        (asAgg rd cr cm it rest)) K D (rlb rlRadOff))
    (hcos : Iface.TermCosetSpec
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC ++ ext) gsGen (rlRow rad cos)
        (asAgg rd cr cm it rest)) Ac (rlb rlCosOff))
    (hrd : AsReadOK (asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC)
      (rqWr hst hfac (rqAa hst hm hpre hfac K D Ac)) (asWa hst hm hpre hfac X)).iface
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC ++ ext) gsGen (rlRow rad cos)
        (asAgg rd cr cm it rest)) asmF H X (asb 1))
    (hct : AsCertOK (asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC)
      (rqWr hst hfac (rqAa hst hm hpre hfac K D Ac)) (asWa hst hm hpre hfac X)).iface
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC ++ ext) gsGen (rlRow rad cos)
        (asAgg rd cr cm it rest)) asmF H X (asb 2))
    (hcm : AsCompOK (asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC)
      (rqWr hst hfac (rqAa hst hm hpre hfac K D Ac)) (asWa hst hm hpre hfac X)).iface
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC ++ ext) gsGen (rlRow rad cos)
        (asAgg rd cr cm it rest)) asmF H X (asb 3))
    (hi : AsItemsOK (asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC)
      (rqWr hst hfac (rqAa hst hm hpre hfac K D Ac)) (asWa hst hm hpre hfac X)).iface
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC ++ ext) gsGen (rlRow rad cos)
        (asAgg rd cr cm it rest)) asmF H X (asb 4))
    (hX : PBU fun _ W _ => X W) :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime := by
  have hg : gsGen.length ≤ asmSlot := by rw [length_gsGen]; unfold asmSlot; omega
  have hl : (rlRow rad cos).length ≤ asmSlot := by
    rw [length_rlRow hr]; unfold asmSlot rlCosOff at *; omega
  refine final_modulo_agg_ext hst hm hpre hfac hmb hO hC ext (rlRow rad cos) _ H X rd cr cm it rest hl
    (rq_rowSpec hcite hst hm hpre hfac hAb hOut hTr hg hr hc hrad hcos _ _) hrd hct hcm hi hX ?_
  obtain ⟨A, D', h⟩ := rq_wr_bound hst hfac (rqAa_nonneg hst hm hpre hfac K D Ac)
  exact ⟨A, D', fun nd _ _ _ => h nd⟩

end GI.Assembly
