module

public import Workspace.Impl.RowLayout
public import Workspace.Impl.GenNormPoly

@[expose] public section

/-!
# The row step of the concrete program meets `RowSpec`

With the layout of `RowLayout.lean`, the row step of `asmProg … (rlRow rad cos) agg` meets
`Iface.RowSpec` (`rq_rowSpec`). The proof chains the results for the row step and the terminal:

* T3 (`tm_termRepsSpec`) from T2 (`TermRadSpec`, open, a hypothesis on the code `rad`);
* the split over the radical cosets (`tm_termDomSpec`) from T3 and one radical coset
  (`TermCosetSpec`, open, a hypothesis on the code `cos`);
* T7 (`tm_termAsmSpec`), then the terminal function (`tm_rowTermSpec`);
* the row step (`Iface.rowSpec`), with the label form `hLab` true by definition: the label
  values of `Rest.iface` are `LabValStd`.

The work of the row step is `rqWr` (`tmWt + rsPre` at `rowTerminal` nodes, `colBrPoly + rsPre`
at `rowColumns` nodes). `rq_wr_bound`: it is at most `expLogSq A N` at `rowTerminal` nodes and
at most `A (N + 2)^D` at `rowColumns` nodes, since `rsPre` and `colBrPoly` are polynomials in `N`
whose constants come from the cited `PointwiseStab` and `NormalizedFactor` (`rq_poly`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership)

/-! ### Raising the constant of the open hypotheses -/

private theorem rq_exp_mono {a b : ℝ} (h : a ≤ b) (N : ℕ) : expLogSq a N ≤ expLogSq b N := by
  unfold expLogSq
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right h (sq_nonneg _))

theorem rq_repsSpec_mono {Pg : Program} {A A' : ℝ} (hA : A ≤ A') {g : ℕ}
    (h : Iface.TermRepsSpec Pg A g) : Iface.TermRepsSpec Pg A' g := by
  intro Ω C _ S k e c hc sv lv L hsv hlv hq0 hgood hrow label hnat hq m h0 E hP σH σN σS hH hNg hS
    htr hlH hlN hlS hcard hsN hN hqα us vs hus hvs
  refine (h S k e c hc sv lv L hsv hlv hq0 hgood hrow label hnat hq h0 E hP σH σN σS hH hNg hS
    htr hlH hlN hlS hcard hsN hN hqα us vs hus hvs).mono ?_
  rintro u cost ⟨R', hRH, hNR, hsolv, uR, reps, h1, h2, h3, h4, h5, h6, h7⟩
  exact ⟨R', hRH, hNR, hsolv, uR, reps, h1, h2, h3, h4, h5, h6, h7.trans (rq_exp_mono hA _)⟩

theorem rq_cosetSpec_mono {Pg : Program} {A A' : ℝ} (hA : A ≤ A') {g : ℕ}
    (h : Iface.TermCosetSpec Pg A g) : Iface.TermCosetSpec Pg A' g := by
  intro Ω C _ S k e c hc sv lv L hsv hlv hq0 hgood hrow label hnat hq m h0 E hP σH σN σS hH hNg hS
    htr hlH hlN hlS hcard hsN hN hqα us vs hus hvs R' hRH hNR hsolv hidx uR hGensR r hr
  refine (h S k e c hc sv lv L hsv hlv hq0 hgood hrow label hnat hq h0 E hP σH σN σS hH hNg hS
    htr hlH hlN hlS hcard hsN hN hqα us vs hus hvs R' hRH hNR hsolv hidx uR hGensR r hr).mono ?_
  rintro u cost ⟨h1, h2⟩
  exact ⟨h1, h2.trans (rq_exp_mono hA _)⟩

/-! ### The constants -/

/-- The common constant of T3 and of one radical coset. -/
noncomputable def rqA0 (hm : Membership) (K D : ℕ) (Ac : ℝ) : ℝ := max (max (tmRpA hm K D) Ac) 0

/-- **The constant of the terminal assembly** (`TermAsmSpec`): T7 over the split. -/
noncomputable def rqAa (hst : PointwiseStab) (hm : Membership) (hpre : Preimage)
    (hfac : NormalizedFactor) (K D : ℕ) (Ac : ℝ) : ℝ :=
  tmLiftA (pointwiseStabPrim hst) (preimagePrim hpre) (normalizedFactorPrim hfac)
    (tmSplitA hm (rqA0 hm K D Ac))

theorem rqA0_nonneg (hm : Membership) (K D : ℕ) (Ac : ℝ) : 0 ≤ rqA0 hm K D Ac := le_max_right _ _

theorem rq_tmSplitA_nonneg (hm : Membership) {A : ℝ} (hA : 0 ≤ A) : 0 ≤ tmSplitA hm A := by
  have hKP1 : (1 : ℝ) ≤ tmSplitKP hm := by
    have : 1 ≤ tmSplitKP hm := Nat.one_le_iff_ne_zero.2 (by unfold tmSplitKP; positivity)
    exact_mod_cast this
  have h1 := Real.log_nonneg hKP1
  have h2 : 0 ≤ Real.log (5 * 10 ^ 10) := Real.log_nonneg (by norm_num)
  have h3 : (0 : ℝ) ≤ tmCeD hm := Nat.cast_nonneg _
  unfold tmSplitA tmSplitM
  positivity

theorem rq_tmLiftA_nonneg (pst pp pf : Prim) {A : ℝ} (hA : 0 ≤ A) : 0 ≤ tmLiftA pst pp pf A := by
  have hK : (1 : ℝ) ≤ tmLKN pst pp pf := by
    have : 1 ≤ tmLKN pst pp pf := by
      unfold tmLKN tmLK
      exact Nat.one_le_iff_ne_zero.2 (by positivity)
    exact_mod_cast this
  have := Real.log_nonneg hK
  unfold tmLiftA
  positivity

theorem rqAa_nonneg (hst : PointwiseStab) (hm : Membership) (hpre : Preimage)
    (hfac : NormalizedFactor) (K D : ℕ) (Ac : ℝ) : 0 ≤ rqAa hst hm hpre hfac K D Ac :=
  rq_tmLiftA_nonneg _ _ _ (rq_tmSplitA_nonneg hm (rqA0_nonneg hm K D Ac))

/-! ### The work of the row step -/

/-- **The work of the row step**: `tmWt + rsPre` at `rowTerminal` nodes, `colBrPoly + rsPre`
otherwise (only `rowColumns` nodes use it then). -/
noncomputable def rqWr (hst : PointwiseStab) (hfac : NormalizedFactor) (Aa : ℝ) (nd : Node P₀) :
    ℝ :=
  match nd.run.kind with
  | .rowTerminal => Iface.tmWt hst Aa nd + (rsPre hst hfac nd.S.N : ℝ)
  | _ => ((colBrPoly nd.S.N + rsPre hst hfac nd.S.N : ℕ) : ℝ)

/-- **`RowW` for `rqWr`.** -/
theorem rq_rowW (hst : PointwiseStab) (hm : Membership) (hpre : Preimage)
    (hfac : NormalizedFactor) (Wg Wa : Node P₀ → ℝ) (Aa : ℝ) :
    (asmRest hst hm hpre hfac Wg (rqWr hst hfac Aa) Wa).iface.RowW hst hfac (Iface.tmWt hst Aa) := by
  intro nd
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · show _ ≤ Rest.W _ nd
    simp only [Rest.W, hk, asmRest, rqWr, le_refl]
  · show _ ≤ Rest.W _ nd
    simp only [Rest.W, hk, asmRest, rqWr, le_refl]

/-! ### The row step meets `RowSpec` -/

/-- **The row step of the concrete program meets its step specification**, given the open
pieces of the terminal: T2 (`TermRadSpec`, for the code `rad`) and one radical coset
(`TermCosetSpec`, for the code `cos`). Cited: `PointwiseStab`,
`Membership`, `Preimage`, `NormalizedFactor` and the [GMP] bound `GMPTransitiveNonabelian`. -/
theorem rq_rowSpec (hst : PointwiseStab)
    (hm : Membership) (hpre : Preimage) (hfac : NormalizedFactor)
    (hTr : GI.Cited.GMPTransitiveNonabelian) {extra : List Prim} {gen rad cos agg : List Expr}
    (hg : gen.length ≤ asmSlot) (hr : rad.length ≤ rlCosOff - rlRadOff)
    (hc : cos.length ≤ asmSlot - rlCosOff) {K D : ℕ} {Ac : ℝ}
    (hrad : Iface.TermRadSpec (asmProg hst hm hpre hfac extra gen (rlRow rad cos) agg) K D
      (rlb rlRadOff))
    (hcos : Iface.TermCosetSpec (asmProg hst hm hpre hfac extra gen (rlRow rad cos) agg) Ac
      (rlb rlCosOff))
    (Wg Wa : Node P₀ → ℝ) :
    (asmRest hst hm hpre hfac Wg (rqWr hst hfac (rqAa hst hm hpre hfac K D Ac)) Wa).iface.RowSpec
      (asmProg hst hm hpre hfac extra gen (rlRow rad cos) agg) asmF asmRowBase := by
  set Pg := asmProg hst hm hpre hfac extra gen (rlRow rad cos) agg with hPg
  set I := (asmRest hst hm hpre hfac Wg (rqWr hst hfac (rqAa hst hm hpre hfac K D Ac)) Wa).iface
  have hA0 := rqA0_nonneg hm K D Ac
  have hreps : Iface.TermRepsSpec Pg (tmRpA hm K D) (rlb 12) :=
    Iface.tm_termRepsSpec Pg hm hTr (rl_repsAt hg hr hc) hrad
  have hreps' : Iface.TermRepsSpec Pg (rqA0 hm K D Ac) (rlb 12) :=
    rq_repsSpec_mono ((le_max_left _ _).trans (le_max_left _ _)) hreps
  have hcos' : Iface.TermCosetSpec Pg (rqA0 hm K D Ac) (rlb rlCosOff) :=
    rq_cosetSpec_mono ((le_max_right _ _).trans (le_max_left _ _)) hcos
  have hdom : Iface.TermDomSpec Pg (tmSplitA hm (rqA0 hm K D Ac)) (rlb 9) :=
    Iface.tm_termDomSpec Pg hm hTr (rl_splitAt hg hr hc) asmProg_prim_mem hA0
    hreps' hcos'
  have hasm : Iface.TermAsmSpec Pg (rqAa hst hm hpre hfac K D Ac) (rlb 8) :=
    Iface.tm_termAsmSpec Pg hst hpre hfac (rl_liftAt hg hr hc) asmProg_prim_pst
    asmProg_prim_pre asmProg_prim_fac (rq_tmSplitA_nonneg hm hA0) hdom
  have hT : I.RowTermSpec Pg asmF (Iface.tmWt hst (rqAa hst hm hpre hfac K D Ac)) (rlb 1) :=
    Iface.tm_rowTermSpec I Pg asmF hst (rl_tmFuns hg hr hc) hasm
  have h : I.RowSpec Pg asmF (rlb 0) := Iface.rowSpec I Pg asmF hst hfac (fun _ _ _ _ h => h) (rl_rsAt hg hr hc) hT
    (rq_rowW hst hm hpre hfac Wg Wa _)
  exact @h

/-! ### The work fits the requirement of `Rest.Req` -/

/-- **The steps of the row step before the branch call and the column branch are polynomial in
`N`**, with constants from the cited `PointwiseStab` and `NormalizedFactor`. -/
theorem rq_poly (hst : PointwiseStab) (hfac : NormalizedFactor) :
    PBU fun N _ _ => rsPre hst hfac N + colBrPoly N := by
  unfold rsPre rsV rsB coordCost rowStepCost liftWinCost liftLabCost a18Cost rowKerCost colBrPoly
    colBrX
  norm_poly

/-- **The work of the row step fits `Rest.Req`**: at most `expLogSq A N` at `rowTerminal` nodes
and at most `A (N + 2)^D` at `rowColumns` nodes. -/
theorem rq_wr_bound (hst : PointwiseStab) (hfac : NormalizedFactor) {Aa : ℝ} (hAa : 0 ≤ Aa) :
    ∃ A D : ℕ, ∀ nd : Node P₀,
      (nd.run.kind = .rowTerminal → rqWr hst hfac Aa nd ≤ expLogSq A nd.S.N) ∧
      (nd.run.kind = .rowColumns → rqWr hst hfac Aa nd ≤ A * ((nd.S.N : ℝ) + 2) ^ D) := by
  obtain ⟨C, Dp, hP⟩ := rq_poly hst hfac
  have hpoly : ∀ N : ℕ, ((colBrPoly N + rsPre hst hfac N : ℕ) : ℝ) ≤
      ((C + 1 : ℕ) : ℝ) * ((N : ℝ) + 2) ^ Dp := by
    intro N
    have h := hP N 0 0
    simp only [PB, Nat.zero_add] at h
    have h' : colBrPoly N + rsPre hst hfac N ≤ (C + 1) * (N + 2) ^ Dp :=
      (Nat.add_comm _ _).le.trans <| h.trans (Nat.mul_le_mul_right _ (Nat.le_succ C))
    exact_mod_cast h'
  have hC1 : (1 : ℝ) ≤ ((C + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 C
  set b : ℝ := 3 * (Real.log ((C + 1 : ℕ) : ℝ) + Dp) with hb
  have hb0 : 0 ≤ b := by have := Real.log_nonneg hC1; positivity
  have ha0 : 0 ≤ tmA hst Aa := by
    have hK : (1 : ℝ) ≤ tmKN hst := by
      have : 1 ≤ tmKN hst := by unfold tmKN; omega
      exact_mod_cast this
    have := Real.log_nonneg hK
    unfold tmA
    positivity
  refine ⟨⌈tmA hst Aa + b + 3⌉₊ + (C + 1), Dp, fun nd => ⟨fun hk => ?_, fun hk => ?_⟩⟩
  · have e : rqWr hst hfac Aa nd = Iface.tmWt hst Aa nd + (rsPre hst hfac nd.S.N : ℝ) := by
      simp only [rqWr, hk]
    rw [e]
    have h1 := tmWt_le hst hAa nd
    have h2 : (rsPre hst hfac nd.S.N : ℝ) ≤ expLogSq b nd.S.N := by
      refine le_trans ?_ ((hpoly nd.S.N).trans (pow_le_expLogSq hC1 Dp nd.S.N))
      exact_mod_cast Nat.le_add_left _ _
    have h3 := expLogSq_add_le ha0 hb0 nd.S.N
    refine (add_le_add h1 h2).trans (h3.trans (rq_exp_mono ?_ _))
    have := Nat.le_ceil (tmA hst Aa + b + 3)
    push_cast
    linarith
  · have e : rqWr hst hfac Aa nd = ((colBrPoly nd.S.N + rsPre hst hfac nd.S.N : ℕ) : ℝ) := by
      simp only [rqWr, hk]
    rw [e]
    have hX : (0 : ℝ) ≤ ((nd.S.N : ℝ) + 2) ^ Dp :=
      pow_nonneg (by have := Nat.cast_nonneg (α := ℝ) nd.S.N; linarith) _
    have hA : ((C + 1 : ℕ) : ℝ) ≤ ((⌈tmA hst Aa + b + 3⌉₊ + (C + 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_left _ _
    exact (hpoly nd.S.N).trans (mul_le_mul_of_nonneg_right hA hX)

end GI.Impl
