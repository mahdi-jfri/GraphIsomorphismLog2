import Workspace.Impl.AggItemStepRun
import Workspace.Impl.AggItemOKHand
import Workspace.Impl.PolyBd

/-!
# `AsItemsOK` from the case contracts

The program of the items, `itSItemsF fstr frun`, runs the structure step at `fstr` on the
hand-over state, and then the rest of the items at `frun` (`itSRunF`, `AggItemStepRun.lean`).

* `ItSStrOK`: what the structure step must do (`it_str_spec` meets it with a polynomial bound:
  `AggItemOKStr.lean`).
* `itS_asItemsOK`: with the hand-over `ItHandB`, the structure step, the three case contracts
  `ItSCaseOK` (Case 1, Case 2a, Cases 2b and 3) with a common bound `Xc`, and the programs of
  `ItSRunAt`, the items meet `AsItemsOK` with the bound `itSX Xs Xc`.
* `itS_X_pbu`: this bound is polynomial when `Xs` and `Xc` are.

The bound does not depend on the interface `I`: it is built from `Xs`, `Xc` and fixed
polynomials.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens encGroup encKColoring)

variable {Ω C : Type} {k : ℕ}

/-- **The program of the items**: the structure step, then the rest. -/
def itSItemsF (fstr frun : ℕ) : Expr :=
  .letE (.call fstr (.var 0)) (.call frun (.var 1))

/-- **What the structure step must do** at `fstr`, with the bound `Xs`: on the hand-over state of
a round `Ag` of the labels, return `[st, [d, d'], code, src]` as `ItStrOut` says, at cost and
weight at most `Xs W₀`. -/
def ItSStrOK (I : Iface) (Pg : Program) (F : Funs) (fstr : ℕ) (Xs : ℕ → ℕ) : Prop :=
  ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C) (sv lv : Val)
    (L : SuppliedLabels S), AsCall I Pg F e c S sv lv L →
    ∀ (Ag : Aggregation P₀ S L.toGiantLabels) (sv' : Val)
      (ps fx fy : List (Perm (Fin k) × Perm (Fin L.q))) (O : TestTupleOrder L.q P₀.κ),
    Ag ∈ asRounds L → Canon e c sv' S →
    PairGens e L.toGiantLabels (itCertLift Ag.fin S Ag.πd P₀.κ S.x) fx →
    ps.length ≤ (k + L.q) ^ 2 → fx.length ≤ (k + L.q) ^ 2 → fy.length ≤ (k + L.q) ^ 2 →
    FunAll Pg fstr (itSt sv' k L.q ps fx fy O.tuples (itCr Ag.fin S Ag.πd P₀.κ)) (fun v cost =>
      ItStrOut Ag (itSt sv' k L.q ps fx fy O.tuples (itCr Ag.fin S Ag.πd P₀.κ)) v ∧
      cost ≤ Xs (I.inW .giant S) ∧ v.wt ≤ Xs (I.inW .giant S))

/-- **The bound of the items**, for the bound `Xs` of the structure step and the common bound
`Xc` of the case contracts. -/
noncomputable def itSX (Xs Xc : ℕ → ℕ) (W : ℕ) : ℕ :=
  3 * Xs W + 3 * cmOutB (2 * W + 3) + itSRunX W (Xc W) + 3 * itSStB W (Xc W) + 10

/-- A case contract at a context of its case. -/
theorem itS_caseAt (I : Iface) (Pg : Program) (F : Funs) {Xc : ℕ → ℕ} {i₁ i₂ i₃ b₁ b₂ b₃ : ℕ}
    (h1 : ItSCaseOK I Pg F (· = .one) i₁ b₁ Xc) (h2 : ItSCaseOK I Pg F (· = .twoA) i₂ b₂ Xc)
    (h3 : ItSCaseOK I Pg F (fun a => a = .twoB ∨ a = .three) i₃ b₃ Xc)
    {e : Ω ≃ Fin k} {c : C → ℕ} {S : State Ω C} {sv lv : Val} {L : SuppliedLabels S}
    (hc : AsCall I Pg F e c S sv lv L) (K : ItSCtx k S L) (hK : K.OK e c) :
    ∃ R : ItSCaseRel, ItSCaseAt Pg R (itSCaseF i₁ i₂ i₃ K.case) (itSCaseF b₁ b₂ b₃ K.case) e c S L K
      (Xc (I.inW .giant S)) := by
  obtain ⟨R1, hR1⟩ := h1
  obtain ⟨R2, hR2⟩ := h2
  obtain ⟨R3, hR3⟩ := h3
  rcases hcase : K.case with _ | _ | _ | _
  · exact ⟨R1, hR1 e c S sv lv L hc K hK hcase⟩
  · exact ⟨R2, hR2 e c S sv lv L hc K hK hcase⟩
  · exact ⟨R3, hR3 e c S sv lv L hc K hK (Or.inl hcase)⟩
  · exact ⟨R3, hR3 e c S sv lv L hc K hK (Or.inr hcase)⟩

set_option maxHeartbeats 1000000 in
/-- **`AsItemsOK` from the case contracts.** -/
theorem itS_asItemsOK (I : Iface) (Pg : Program) (F : Funs) (H : AsHand)
    (hH : ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C)
      (L : SuppliedLabels S) Cs st, H.items e c S L Cs st → ItHandB e c S L Cs st)
    {fi fstr frun fts di0 drun dloop mv m0 m1 m3 db fac app i₁ i₂ i₃ b₁ b₂ b₃ : ℕ}
    (hfi : Pg.funs[fi]? = some (itSItemsF fstr frun)) {Xs Xc : ℕ → ℕ}
    (hstr : ItSStrOK I Pg F fstr Xs)
    (hP : ItSRunAt Pg F frun fts di0 drun dloop mv m0 m1 m3 db fac app i₁ i₂ i₃ b₁ b₂ b₃)
    (h1 : ItSCaseOK I Pg F (· = .one) i₁ b₁ Xc) (h2 : ItSCaseOK I Pg F (· = .twoA) i₂ b₂ Xc)
    (h3 : ItSCaseOK I Pg F (fun a => a = .twoB ∨ a = .three) i₃ b₃ Xc) :
    AsItemsOK I Pg F H (itSX Xs Xc) fi := by
  intro Ω C k e c S sv lv L hc Cs st hst
  obtain ⟨hsub, Ag₀, h0, hcl, sv', ps, fx, fy, O, rfl, hcan, hps, hfx, hfy, lps, lfx, lfy⟩ :=
    hH e c S L Cs st hst
  refine FunAll.intro hfi ?_
  unfold itSItemsF
  refine EvalAll.letE (Ra := fun v cv =>
      ItStrOut Ag₀ (itSt sv' k L.q ps fx fy O.tuples (itCr Ag₀.fin S Ag₀.πd P₀.κ)) v ∧
      cv ≤ 3 * (itSt sv' k L.q ps fx fy O.tuples (itCr Ag₀.fin S Ag₀.πd P₀.κ)).wt +
        Xs (I.inW .giant S) + 3 + v.wt ∧ v.wt ≤ Xs (I.inW .giant S))
    (EvalAll.call_funAll (Det.var' (i := 0) rfl) fun v ca hv => ?_) fun v cv hv => ?_
  · obtain ⟨rfl, hca⟩ := hv
    exact FunAll.mono (hstr e c S sv lv L hc Ag₀ sv' ps fx fy O (hsub h0) hcan hfx lps lfx lfy)
      fun w cst ⟨h1, h2, h3⟩ => ⟨h1, by omega, h3⟩
  obtain ⟨⟨d, d', hJ, hd, hd', rfl⟩, hcv, hvw⟩ := hv
  -- the context of the branches
  let K : ItSCtx k S L := ⟨Cs, Ag₀, sv', ps, fx, fy, O, d, d',
    (haveI := Ag₀.fin
     letI : Fintype S.dom := Fintype.ofFinite _
     letI : DecidableEq S.dom := Classical.decEq _
     stSetJ Ag₀.hK L.q P₀.κ _ _ d d' hJ)⟩
  have hK : K.OK e c := ⟨hsub, h0, hcl, hcan, hps, hfx, hfy, lps, lfx, lfy, hd, hd', hJ, rfl⟩
  obtain ⟨R, hA⟩ := itS_caseAt I Pg F h1 h2 h3 hc K hK
  have hrun := itS_run I Pg F hP hc hK hA
  have hstW := itS_stW I Pg F hc hK
  have eSt : K.st = itSt sv' k L.q ps fx fy O.tuples (itCr Ag₀.fin S Ag₀.πd P₀.κ) := rfl
  rw [eSt] at hstW
  refine EvalAll.call_funAll (Det.var' (i := 1) (v := K.v) rfl) fun v' ca hv' => ?_
  obtain ⟨rfl, hca⟩ := hv'
  refine FunAll.mono hrun fun w cost h => ?_
  obtain ⟨Ag, hAg, a, ex, ⟨pcs, os, rfl, hO1, hO2, hO3, hO4⟩, hw, hcost⟩ := h
  have eKv : K.v.wt = (Val.list [itSt sv' k L.q ps fx fy O.tuples (itCr Ag₀.fin S Ag₀.πd P₀.κ),
      .list [encKColoring d, encKColoring d'],
      .nat (AggCase.code (aggCase (itX0 Ag₀ (haveI := Ag₀.fin
        letI : Fintype S.dom := Fintype.ofFinite _
        letI : DecidableEq S.dom := Classical.decEq _
        stSetJ Ag₀.hK L.q P₀.κ _ _ d d' hJ)).grp)),
      natList (stL fun i => (itSrc Ag₀ (haveI := Ag₀.fin
        letI : Fintype S.dom := Fintype.ofFinite _
        letI : DecidableEq S.dom := Classical.decEq _
        stSetJ Ag₀.hK L.q P₀.κ _ _ d d' hJ) i : ℕ))]).wt := rfl
  refine ⟨Ag, hAg, a.pieces, os, a.overs, pcs, ex, hO1, rfl, hO2, hO3, hO4, ?_, ?_⟩
  · have hnat : cv + (ca + cost + (itSOutV pcs os).wt + 1) + (itSOutV pcs os).wt + 1 ≤
        cv + ca + 2 * (itSOutV pcs os).wt + 2 + cost := by omega
    have hb : cv + ca + 2 * (itSOutV pcs os).wt + 2 ≤
        3 * Xs (I.inW .giant S) + 3 * cmOutB (2 * I.inW .giant S + 3) +
          3 * itSStB (I.inW .giant S) (Xc (I.inW .giant S)) + 10 := by omega
    have hR : ((cv + (ca + cost + (itSOutV pcs os).wt + 1) + (itSOutV pcs os).wt + 1 : ℕ) : ℝ) ≤
        ((cv + ca + 2 * (itSOutV pcs os).wt + 2 : ℕ) : ℝ) + (cost : ℝ) := by
      rw [← Nat.cast_add]; exact Nat.cast_le.mpr hnat
    have hb' : ((cv + ca + 2 * (itSOutV pcs os).wt + 2 : ℕ) : ℝ) + itSRunX (I.inW .giant S)
        (Xc (I.inW .giant S)) ≤ (itSX Xs Xc (I.inW .giant S) : ℝ) := by
      rw [← Nat.cast_add]
      refine Nat.cast_le.mpr ?_
      unfold itSX
      omega
    linarith
  · unfold itSX
    omega

/-! ### The bound is polynomial -/

/-- **Putting a polynomial into the third slot.** If `P W B` is polynomial in `W, B` and `X W` is
polynomial in `W`, then `P W (X W)` is polynomial in `W`. -/
theorem itS_pbu_subst {P : ℕ → ℕ → ℕ} {X : ℕ → ℕ} (hP : PBU fun _ W B => P W B)
    (hX : PBU fun _ W _ => X W) : PBU fun _ W _ => P W (X W) := by
  obtain ⟨C, D, h⟩ := hP
  refine (PBU.smul C (PBU.pow (PBU.addc (PBU.add (PBU.add PBU.W hX) PBU.k) 2) D)).mono ?_
  intro k W B
  exact h k W (X W)

/-- The bound of the run is polynomial in `W, B`. -/
theorem itS_runX_pbu : PBU fun _ W B => itSRunX W B + 3 * itSStB W B := by
  simp only [itSRunX, itSStB, itSStepB, itSBm, itSBw, itSAccB, itSCd, itSDispC, itSM1C, itSM3C,
    itSMvC, itSFacC, cpLoopC, itSNb, itSTvB, itSVB, cmOutB, cmPb, cmNb, itTsC, itTvC, itTvW, mapK,
    stDPowK, stDDecK, runK]
  norm_poly

/-- **The bound of the items is polynomial** when the bounds of the structure step and of the
cases are. -/
theorem itS_X_pbu {Xs Xc : ℕ → ℕ} (hs : PBU fun _ W _ => Xs W) (hc : PBU fun _ W _ => Xc W) :
    PBU fun _ W _ => itSX Xs Xc W := by
  have h1 : PBU fun _ W _ => 3 * cmOutB (2 * W + 3) + 10 := by
    simp only [cmOutB, cmPb, cmNb]
    norm_poly
  have h2 := itS_pbu_subst itS_runX_pbu hc
  refine (PBU.add (PBU.add (PBU.smul 3 hs) h1) h2).mono fun k W B => ?_
  unfold itSX
  omega

end GI.Impl
