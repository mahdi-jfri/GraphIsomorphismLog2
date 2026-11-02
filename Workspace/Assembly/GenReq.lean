import Workspace.Impl.GenSpecLayout
import Workspace.Impl.GenCost
import Workspace.Impl.GenNormPoly
import Workspace.Assembly.Stage2

/-!
# The work of the general dispatcher fits in `E_N`

`AsmOpenReq` asks `Wg ≤ exp(A log²(N + 2))` at every `dispatch` and `normalize` node that fits
its phase (`|Ω| ≤ N`, `Small`). For `Wg = gsWg` (`GenSpecLayout.lean`) this holds
(`gsWg_le_expLogSq`):

* the weight bound of the state value is polynomial in `N` (`stateW_le_of_small`);
* `gsOwn k Ws` is a uniformly polynomial function of `k`, `Ws` and `B = gsBk k`
  (`gsOwnB_poly`), since every part (the exposure, the cited calls, the case decision, the
  enumeration, the product step, the normalization) is;
* `gsBk k ≤ (N + 2)^(72000 ⌊log₂ (N + 2)⌋)`: the order of a small quotient
  (`|ρ(G)| ≤ exp(a log² d)`, Section 7.2) and `r!` with `r ≤ log₂ d` (Section 7.3) are
  quasipolynomial, so `PBU.le_expLogSq` applies.

`final_modulo_gen`: the trusted statement from the row step and the aggregation round alone
(their step specifications and work bounds), with the general dispatcher of `gsGen`.
-/

namespace GI.Assembly

open GI.Algorithm GI.Lang GI.Paper GI.Impl
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership MinimalBlocks GroupOrder
  CameronRecognition)

/-- The own cost of the branch with the order bound `B` as a variable. -/
noncomputable def gsBrB (hp : Preimage) (hm : Membership) (Cn : ℕ → ℕ → ℕ) (k Wb B : ℕ) : ℕ :=
  enumCost hp hm k (2 * Wb + 10) B + prodCost hp hm k Wb B + Cn k Wb + 40 * Wb + 3 * ansW k + 400

/-- The part of `gsOwn` before the branch, for the exposure bound `X`. -/
noncomputable def gsTop (hO : GroupOrder) (hC : CameronRecognition) (k X W : ℕ) : ℕ :=
  100 * (W + X + (k + 2) ^ 2 + gsWc k + ansW k + 100) +
    2 * (groupOrderPrim hO).c * (X + 2) ^ (groupOrderPrim hO).k + gsCase hO hC k X +
    10 * gsWb k W X

theorem gsOwn_eq (hmb : MinimalBlocks) (hO : GroupOrder) (hC : CameronRecognition)
    (hp : Preimage) (hm : Membership) (Cn : ℕ → ℕ → ℕ) (k W : ℕ) :
    gsOwn hmb hO hC hp hm Cn k W = gsTop hO hC k (gsX hmb W) W +
      gsBrB hp hm Cn k (gsWb k W (gsX hmb W)) (gsBk k) := rfl

theorem prodCost_poly (hp : Preimage) (hm : Membership) :
    PBU fun k W B => prodCost hp hm k W B := by
  simp only [prodCost, prodY, pkerCost, pkerW, kerNFCost, tailCost, enumChildB, piecesW, pieceW,
    combInW, combOutW, combCost, combM, cosetNFCost, reduceCost, memCost, ansW, groupW,
    Prim.boundSize]
  norm_poly

theorem gsBrB_poly (hp : Preimage) (hm : Membership) {Cn : ℕ → ℕ → ℕ}
    (hCn : PBU fun k W _ => Cn k W) : PBU fun k W B => gsBrB hp hm Cn k W B := by
  have he : PBU fun k W B => enumCost hp hm k (2 * W + 10) B :=
    gs_pbu_compW (enumCost_poly hp hm) (PBU.addc (PBU.smul 2 PBU.W) 10)
  have hA : PBU fun k _ _ => ansW k := by unfold ansW groupW; norm_poly
  exact PBU.addc (PBU.add (PBU.add (PBU.add (PBU.add he (prodCost_poly hp hm)) hCn)
    (PBU.smul 40 PBU.W)) (PBU.smul 3 hA)) 400

theorem gsX_poly (hmb : MinimalBlocks) : PBU fun _ W _ => gsX hmb W := by
  unfold gsX; norm_poly

theorem gsTop_poly (hO : GroupOrder) (hC : CameronRecognition) :
    PBU fun k X W => gsTop hO hC k X W := by
  unfold gsTop gsWc ansW groupW gsCase caseZ gsWb gsWc
  norm_poly

/-- **`gsOwn` is uniformly polynomial** in `k`, the weight and the order bound. -/
theorem gsOwnB_poly (hmb : MinimalBlocks) (hO : GroupOrder) (hC : CameronRecognition)
    (hp : Preimage) (hm : Membership) {Cn : ℕ → ℕ → ℕ} (hCn : PBU fun k W _ => Cn k W) :
    PBU fun k W B => gsTop hO hC k (gsX hmb W) W +
      gsBrB hp hm Cn k (gsWb k W (gsX hmb W)) B := by
  have h1 : PBU fun k W _ => gsTop hO hC k (gsX hmb W) W :=
    normPoly_subst (gsTop_poly hO hC) PBU.k (gsX_poly hmb) PBU.W
  have hwb : PBU fun k W _ => gsWb k W (gsX hmb W) := by
    have : PBU fun k W X => gsWb k W X := by unfold gsWb gsWc; norm_poly
    exact normPoly_subst this PBU.k PBU.W (gsX_poly hmb)
  have h2 : PBU fun k W B => gsBrB hp hm Cn k (gsWb k W (gsX hmb W)) B :=
    normPoly_subst (gsBrB_poly hp hm hCn) PBU.k hwb PBU.B
  exact PBU.add h1 h2

/-- `gsBk k` for `k ≤ N` has the form that `PBU.le_expLogSq` takes. -/
theorem gsBk_le_N {k N : ℕ} (h : k ≤ N) :
    gsBk k ≤ (N + 2) ^ (72000 * Nat.log 2 (N + 2)) := gsBk_mono h

/-- **The work of the general dispatcher fits in `E_N`** at every fitting node. -/
theorem gsWg_le_expLogSq (hst : PointwiseStab) (hm : Membership) (hpre : Preimage)
    (hmb : MinimalBlocks) (hO : GroupOrder) (hC : CameronRecognition) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ nd : Node P₀, Nat.card nd.Ω ≤ nd.S.N → Small nd.S →
      gsWg hst hm hpre hmb hO hC nd ≤ expLogSq A nd.S.N := by
  obtain ⟨A, hA, h⟩ := (gsOwnB_poly hmb hO hC hpre hm (gsCn_poly hpre hst hm)).le_expLogSq
    (10 ^ 4) 6 72000
  refine ⟨A, hA, fun nd hk hs => ?_⟩
  have hW := stateW_le_of_small hk hs
  have hmono := gsOwn_mono hmb hO hC hpre hm (Cn := gsCn hpre hst hm)
    (fun h => gsCn_mono hpre hst hm h) (Nat.card nd.Ω) hW
  have h2 := h (Nat.card nd.Ω) (10 ^ 4 * (nd.S.N + 2) ^ 6) (gsBk (Nat.card nd.Ω)) nd.S.N hk le_rfl
    (gsBk_le_N hk)
  rw [← gsOwn_eq] at h2
  unfold gsWg
  exact (Nat.cast_le.mpr hmono).trans h2

/-- **`AsmOpenReq` for the general dispatcher**, given the bounds on the row step and the
aggregation round. -/
theorem asmOpenReq_gen (hst : PointwiseStab) (hm : Membership) (hpre : Preimage)
    (hmb : MinimalBlocks) (hO : GroupOrder) (hC : CameronRecognition) {Wr Wa : Node P₀ → ℝ}
    (hra : ∃ A D : ℕ, ∀ nd : Node P₀, nd.m ≠ .solve → Nat.card nd.Ω ≤ nd.S.N → Small nd.S →
      (nd.run.kind = .rowTerminal → Wr nd ≤ expLogSq A nd.S.N) ∧
      (nd.run.kind = .rowColumns → Wr nd ≤ A * ((nd.S.N : ℝ) + 2) ^ D) ∧
      (nd.run.kind = .aggregate → Wa nd ≤ A * ((nd.S.N : ℝ) + 2) ^ D)) :
    AsmOpenReq (gsWg hst hm hpre hmb hO hC) Wr Wa := by
  obtain ⟨A₀, hA₀, hg⟩ := gsWg_le_expLogSq hst hm hpre hmb hO hC
  obtain ⟨A, D, h⟩ := hra
  refine ⟨A + ⌈A₀⌉₊, D, fun nd hnd hk hs => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h nd hnd hk hs
  have hA1 : (A : ℝ) ≤ ((A + ⌈A₀⌉₊ : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right _ _
  have hA2 : A₀ ≤ ((A + ⌈A₀⌉₊ : ℕ) : ℝ) := by
    push_cast; have := Nat.le_ceil A₀; have : (0 : ℝ) ≤ A := Nat.cast_nonneg _; linarith
  have hX : (0 : ℝ) ≤ ((nd.S.N : ℝ) + 2) ^ D := by positivity
  refine ⟨fun _ => (hg nd hk hs).trans (asm_expLogSq_mono hA2 _),
    fun hk' => (h1 hk').trans (asm_expLogSq_mono hA1 _), fun hk' => (h2 hk').trans ?_,
    fun hk' => (h3 hk').trans ?_⟩
  · exact mul_le_mul_of_nonneg_right hA1 hX
  · exact mul_le_mul_of_nonneg_right hA1 hX

/-- **Stage 2 up to the row step and the aggregation round.** With the general dispatcher of
`gsGen` (and the cited `MinimalBlocks`, `GroupOrder`, `CameronRecognition`), the step
specifications of the row step and the aggregation round and their work bounds give the trusted
statement. -/
theorem final_modulo_gen (hst : PointwiseStab) (hm : Membership) (hpre : Preimage)
    (hfac : NormalizedFactor) (hmb : MinimalBlocks) (hO : GroupOrder) (hC : CameronRecognition)
    (row agg : List Expr) (Wr Wa : Node P₀ → ℝ)
    (hrow : (asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC) Wr Wa).iface.RowSpec
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC) gsGen row agg) asmF asmRowBase)
    (hagg : (asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC) Wr Wa).iface.AggSpec
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC) gsGen row agg) asmF asmAggBase)
    (hra : ∃ A D : ℕ, ∀ nd : Node P₀, nd.m ≠ .solve → Nat.card nd.Ω ≤ nd.S.N → Small nd.S →
      (nd.run.kind = .rowTerminal → Wr nd ≤ expLogSq A nd.S.N) ∧
      (nd.run.kind = .rowColumns → Wr nd ≤ A * ((nd.S.N : ℝ) + 2) ^ D) ∧
      (nd.run.kind = .aggregate → Wa nd ≤ A * ((nd.S.N : ℝ) + 2) ^ D)) :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime :=
  final_modulo hst hm hpre hfac (gsExtra hmb hO hC) gsGen row agg (gsWg hst hm hpre hmb hO hC)
    Wr Wa (gs_asm_general hst hm hpre hfac hmb hO hC row agg Wr Wa) hrow hagg
    (asmOpenReq_gen hst hm hpre hmb hO hC hra)

/-- **`final_modulo_gen` with more primitives.** The same, for the primitive table
`[pst, mem, pre, fac] ++ gsExtra ++ ext`: any list `ext` of further primitives may follow
`gsExtra`, from index `7` on. -/
theorem final_modulo_gen_ext (hst : PointwiseStab) (hm : Membership) (hpre : Preimage)
    (hfac : NormalizedFactor) (hmb : MinimalBlocks) (hO : GroupOrder) (hC : CameronRecognition)
    (ext : List Prim) (row agg : List Expr) (Wr Wa : Node P₀ → ℝ)
    (hrow : (asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC) Wr Wa).iface.RowSpec
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC ++ ext) gsGen row agg) asmF asmRowBase)
    (hagg : (asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC) Wr Wa).iface.AggSpec
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC ++ ext) gsGen row agg) asmF asmAggBase)
    (hra : ∃ A D : ℕ, ∀ nd : Node P₀, nd.m ≠ .solve → Nat.card nd.Ω ≤ nd.S.N → Small nd.S →
      (nd.run.kind = .rowTerminal → Wr nd ≤ expLogSq A nd.S.N) ∧
      (nd.run.kind = .rowColumns → Wr nd ≤ A * ((nd.S.N : ℝ) + 2) ^ D) ∧
      (nd.run.kind = .aggregate → Wa nd ≤ A * ((nd.S.N : ℝ) + 2) ^ D)) :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime :=
  final_modulo hst hm hpre hfac (gsExtra hmb hO hC ++ ext) gsGen row agg
    (gsWg hst hm hpre hmb hO hC) Wr Wa
    (gs_asm_general_ext hst hm hpre hfac hmb hO hC ext row agg Wr Wa) hrow hagg (asmOpenReq_gen hst hm hpre hmb hO hC hra)

end GI.Assembly
