module

public import Workspace.Impl.LayoutAsm
public import Workspace.Assembly.ReqChildren

@[expose] public section

/-!
# Stage 2 up to the three missing steps

`final_modulo` proves the trusted statement `GraphIsomorphismInQuasipolynomialTime` from

* the cited algorithms that the implemented steps call (`PointwiseStab`, `Membership`,
  `Preimage`, `NormalizedFactor`), as hypotheses;
* for three function lists `gen`, `row`, `agg` (placed at `asmGenBase`, `asmRowBase`,
  `asmAggBase` of the program `asmProg`, `Workspace/Impl/LayoutAsm.lean`) and any further
  primitives `extra` (at index `4` on), their step specifications `GeneralSpec`, `RowSpec`,
  `AggSpec` for the concrete interface `asmRest … Wg Wr Wa`;
* the bounds that `Rest.Req` asks for the works `Wg, Wr, Wa` of these steps (`AsmOpenReq`).

Every other clause of `Rest.Req` is proved here (`asmRest_req`): the selector bounds come from
`restSelB_le` and `giantSelWStd_le`, and the bounds on the children of the row and aggregation
nodes hold for every run (`asmChildReq`, from `req_children`,
`Workspace/Assembly/ReqChildren.lean`).
-/

namespace GI.Assembly

open GI.Algorithm GI.Lang GI.Paper GI.Impl
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership)

/-- **What `Rest.Req` asks of the three missing steps.** There are `A, D` such that at every
`Continue` or `GiantStep` node that fits its phase (`|Ω| ≤ N`, `Small`), with `X = N + 2`:

* the general dispatcher does work `Wg ≤ exp(A (log X)²)` at `dispatch` and `normalize` nodes;
* the row terminal does work `Wr ≤ exp(A (log X)²)` at `rowTerminal` nodes (Theorem
  `thm:transitive-gat-terminal`: `exp(O(log²(b+2) + log(m+2) log(b+2)))` extra work);
* the column step does work `Wr ≤ A X^D` at `rowColumns` nodes;
* the aggregation round does work `Wa ≤ A X^D` at `aggregate` nodes.

The bounds on the children of these nodes do not depend on the step programs; they are
`AsmChildReq`, proved for every run (`asmChildReq`). -/
def AsmOpenReq (Wg Wr Wa : Node P₀ → ℝ) : Prop :=
  ∃ A D : ℕ, ∀ nd : Node P₀, nd.m ≠ .solve → Nat.card nd.Ω ≤ nd.S.N → Small nd.S →
    (nd.run.kind = .dispatch ∨ nd.run.kind = .normalize → Wg nd ≤ expLogSq A nd.S.N) ∧
    (nd.run.kind = .rowTerminal → Wr nd ≤ expLogSq A nd.S.N) ∧
    (nd.run.kind = .rowColumns → Wr nd ≤ A * ((nd.S.N : ℝ) + 2) ^ D) ∧
    (nd.run.kind = .aggregate → Wa nd ≤ A * ((nd.S.N : ℝ) + 2) ^ D)

/-- **The children of the row and aggregation nodes.** There are `A, D` such that every node of
kind `rowTerminal`, `rowColumns` or `aggregate` that is not a `Solve` node and has `s ≤ N` has
at most `A (N+2)^D` children, and each of its `Solve` children has a state whose canonical
weight bound `stateW` is at most `A (N+2)^D`. -/
def AsmChildReq : Prop :=
  ∃ A D : ℕ, ∀ nd : Node P₀, nd.m ≠ .solve → nd.S.size ≤ nd.S.N →
    (nd.run.kind = .rowTerminal ∨ nd.run.kind = .rowColumns ∨ nd.run.kind = .aggregate →
      nd.run.children.length ≤ A * (nd.S.N + 2) ^ D ∧
      ∀ c ∈ nd.run.children, c.m = .solve → stateW (Nat.card c.Ω) c.S ≤ A * (nd.S.N + 2) ^ D)

/-- **`AsmChildReq` holds**, with `A = 10⁴` and `D = 36000` (`req_children`). -/
theorem asmChildReq : AsmChildReq := by
  refine ⟨10 ^ 4, 36000, fun nd hm hsz hk => ?_⟩
  obtain ⟨hl, hc⟩ := req_children nd hm hsz hk
  have hp : (nd.S.N + 2) ^ 6 ≤ (nd.S.N + 2) ^ 36000 := Nat.pow_le_pow_right (by omega) (by omega)
  exact ⟨hl.trans (Nat.mul_le_mul_right _ (by norm_num)),
    fun c hc' hcm => (hc c hc' hcm).trans (Nat.mul_le_mul_left _ hp)⟩

/-- A node that is neither `Solve` nor of an implemented or general kind is a row or
aggregation node. -/
theorem asm_kind_rest (nd : Node P₀) (hm : nd.m ≠ .solve) (h1 : nd.run.kind ∉ implKinds)
    (h2 : nd.run.kind ∉ generalKinds) :
    nd.run.kind = .rowTerminal ∨ nd.run.kind = .rowColumns ∨ nd.run.kind = .aggregate := by
  obtain ⟨m, Ω, C, S, L, A, r⟩ := nd
  cases r <;> simp_all [Run.kind, implKinds, generalKinds]

theorem asm_poly_mono {x : ℝ} {N A D A' D' : ℕ} (h : x ≤ A * ((N : ℝ) + 2) ^ D) (hA : A ≤ A')
    (hD : D ≤ D') : x ≤ A' * ((N : ℝ) + 2) ^ D' := by
  have h1 : ((N : ℝ) + 2) ^ D ≤ ((N : ℝ) + 2) ^ D' := pow_le_pow_N hD
  have h2 : (A : ℝ) ≤ A' := by exact_mod_cast hA
  have h3 : (0 : ℝ) ≤ ((N : ℝ) + 2) ^ D := by positivity
  have h4 : (0 : ℝ) ≤ A' := Nat.cast_nonneg _
  calc x ≤ A * ((N : ℝ) + 2) ^ D := h
    _ ≤ A' * ((N : ℝ) + 2) ^ D := mul_le_mul_of_nonneg_right h2 h3
    _ ≤ A' * ((N : ℝ) + 2) ^ D' := mul_le_mul_of_nonneg_left h1 h4

theorem asm_poly_mono_nat {x N A D A' D' : ℕ} (h : x ≤ A * (N + 2) ^ D) (hA : A ≤ A')
    (hD : D ≤ D') : x ≤ A' * (N + 2) ^ D' :=
  h.trans (Nat.mul_le_mul hA (Nat.pow_le_pow_right (by omega) hD))

theorem asm_expLogSq_mono {a b : ℝ} (h : a ≤ b) (N : ℕ) : expLogSq a N ≤ expLogSq b N := by
  unfold expLogSq
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right h (sq_nonneg _))

/-- **`Rest.Req` for the concrete interface**, from the bounds on the three missing steps. The
clauses of the selectors are proved (`restSelB_le`, `giantSelWStd_le`). -/
theorem asmRest_req (hst : PointwiseStab) (hm : Membership) (hpre : Preimage)
    (hfac : NormalizedFactor) {Wg Wr Wa : Node P₀ → ℝ} (h : AsmOpenReq Wg Wr Wa) :
    (asmRest hst hm hpre hfac Wg Wr Wa).Req := by
  obtain ⟨A, D, hA⟩ := h
  obtain ⟨A₀, D₀, hA₀⟩ := asmChildReq
  set A₁ : ℕ := restSelK * (10 ^ 4 + 1) ^ 15
  set A₂ : ℕ := (preimagePrim hpre).c * (1000 * 30000 ^ 6 + 2) ^ (preimagePrim hpre).k +
    (natCostK + badK + 10) * 30000 ^ 16
  set D₂ : ℕ := 36 * (preimagePrim hpre).k + 96
  refine ⟨A + A₁ + A₂ + A₀, D + 90 + D₂ + D₀, fun nd hnd hsz hk hs => ?_⟩
  obtain ⟨hg, hrT, hr, ha⟩ := hA nd hnd hk hs
  have hle : A ≤ A + A₁ + A₂ + A₀ := by omega
  have hle' : (A : ℝ) ≤ ((A + A₁ + A₂ + A₀ : ℕ) : ℝ) := Nat.cast_le.2 hle
  refine ⟨fun _ => ?_, fun _ => ?_, fun hkd => ?_, fun hkd => ?_, fun hkd => ?_, fun hkd => ?_,
    fun h1 h2 => ?_⟩
  · exact asm_poly_mono (restSelB_le hk hs) (by omega) (by omega)
  · exact asm_poly_mono (giantSelWStd_le hpre hk hs)
      ((Nat.le_add_left A₂ (A + A₁)).trans (Nat.le_add_right _ A₀))
      ((Nat.le_add_left D₂ (D + 90)).trans (Nat.le_add_right _ D₀))
  · exact (hg hkd).trans (asm_expLogSq_mono hle' _)
  · exact (hrT hkd).trans (asm_expLogSq_mono hle' _)
  · exact asm_poly_mono (hr hkd) (by omega) (by omega)
  · exact asm_poly_mono (ha hkd) (by omega) (by omega)
  · obtain ⟨hl, hc⟩ := hA₀ nd hnd hsz (asm_kind_rest nd hnd h1 h2)
    exact ⟨asm_poly_mono_nat hl (by omega) (by omega),
      fun c hc' hcm => asm_poly_mono_nat (hc c hc' hcm) (by omega) (by omega)⟩

/-- **Stage 2 up to the three missing steps.** If the general dispatcher, the row step and the
aggregation round, given as function lists `gen`, `row`, `agg` of the program `asmProg` (with
any further primitives `extra`), meet their step specifications for the concrete interface,
and their works meet the bounds of `AsmOpenReq`, then graph isomorphism is in
quasipolynomial time. -/
theorem final_modulo (hst : PointwiseStab) (hm : Membership) (hpre : Preimage)
    (hfac : NormalizedFactor) (extra : List Prim) (gen row agg : List Expr)
    (Wg Wr Wa : Node P₀ → ℝ)
    (hgen : (asmRest hst hm hpre hfac Wg Wr Wa).iface.GeneralSpec
      (asmProg hst hm hpre hfac extra gen row agg) asmF asmGenBase)
    (hrow : (asmRest hst hm hpre hfac Wg Wr Wa).iface.RowSpec
      (asmProg hst hm hpre hfac extra gen row agg) asmF asmRowBase)
    (hagg : (asmRest hst hm hpre hfac Wg Wr Wa).iface.AggSpec
      (asmProg hst hm hpre hfac extra gen row agg) asmF asmAggBase)
    (hreq : AsmOpenReq Wg Wr Wa) :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime :=
  Rest.final (asmRest hst hm hpre hfac Wg Wr Wa)
    (asm_layoutOK hst hm hpre hfac Wg Wr Wa extra gen row agg hgen hrow hagg)
    (fm := 347) (graphWrapper_of_hasAt (asm_block 347 rfl)) (asmRest_req hst hm hpre hfac hreq)

end GI.Assembly
