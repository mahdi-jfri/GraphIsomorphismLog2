module

public import Workspace.Degree.RunD
public import Workspace.Degree.RoundMass
public import Workspace.Impl.AggItemOK

@[expose] public section

/-!
# The items of the degree algorithm

The text of `itS_run` and `itS_asItemsOK` of the general algorithm, over the runner `run_specCD`.
The step and the case contracts are those of the general algorithm.
-/

set_option linter.unusedSectionVars false

namespace GI.Degree

open GI.Algorithm GI.Assembly GI.Impl GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens encKColoring)

variable {k : ℕ} {Ω C : Type}

section Run

variable (I : Iface) (Pg : Program) (F : Funs) {e : Ω ≃ Fin k} {c : C → ℕ} {S : State Ω C}
  {sv lv : Val} {L : SuppliedLabels S}

set_option maxHeartbeats 1000000 in
/-- **The items after the structure step.** -/
theorem itS_runD (J : CostT) (F₀ : Funs) {frun fts di0 drun dloop mv m0 m1 m3 db fac app i₁ i₂ i₃ b₁ b₂ b₃ : ℕ}
    (hP : ItSRunAt Pg F frun fts di0 drun dloop mv m0 m1 m3 db fac app i₁ i₂ i₃ b₁ b₂ b₃)
    (hc : AsCall I Pg F₀ e c S sv lv L)
    (hih : DIH Pg F J (RoundP P₀ S L.q) (measure P₀ .giant S)) {K : ItSCtx k S L} (hK : K.OK e c) {R : ItSCaseRel}
    {B : ℕ} (hA : ItSCaseAt Pg R (itSCaseF i₁ i₂ i₃ K.case) (itSCaseF b₁ b₂ b₃ K.case) e c S L K B) :
    FunAll Pg frun K.v (fun w cost => ∃ Ag ∈ K.Cs, ∃ (a : Branches Ω) (ex : DX Ag.itemsScript a),
      ItSFin e L.toGiantLabels a w ∧ w.wt ≤ itSStB (I.inW .giant S) B ∧
      (cost : ℝ) ≤ itSRunX (I.inW .giant S) B + ex.cost J) := by
  obtain ⟨hkq, hκ, -, hq0, -, -⟩ := itS_size I Pg F₀ hc
  obtain ⟨hn, hq65⟩ := itS_n_le I Pg F₀ hc
  have hV := itS_vW I Pg F₀ hc hK
  have hT := itS_tv_wt I Pg F₀ hc
  have hs := itS_stepOKC hP.hmv hA hV hT hn hP.hloop
    (fun bst Q h => itS_disp_spec hP.hdb K.case bst h)
  have eV : K.v = .list [K.st, .list [encKColoring K.d, encKColoring K.d'],
      .nat (AggCase.code K.case), natList (stL fun i => (itSrc K.Ag₀ K.J i : ℕ))] := rfl
  have eS : K.st = .list [K.sv, .list [.nat k, .nat L.q], .list (K.ps.map pairV),
      .list (K.fx.map pairV), .list (K.fy.map pairV),
      stCv K.O.tuples (itCr K.Ag₀.fin S K.Ag₀.πd P₀.κ)] := rfl
  have eVw : (Val.list [K.st, .list [encKColoring K.d, encKColoring K.d'],
      .nat (AggCase.code K.case), natList (stL fun i => (itSrc K.Ag₀ K.J i : ℕ))]).wt = K.v.wt := rfl
  have eSw : (Val.list [K.sv, .list [.nat k, .nat L.q], .list (K.ps.map pairV),
      .list (K.fx.map pairV), .list (K.fy.map pairV),
      stCv K.O.tuples (itCr K.Ag₀.fin S K.Ag₀.πd P₀.κ)]).wt = K.st.wt := rfl
  have wst : K.st.wt < K.v.wt := by rw [eV]; exact wt_le_wt_list (by simp)
  have wkq : (Val.list [.nat k, .nat L.q]).wt < K.st.wt := by rw [eS]; exact wt_le_wt_list (by simp)
  have wq : (Val.nat L.q).wt < (Val.list [.nat k, .nat L.q]).wt := wt_le_wt_list (by simp)
  have wcode : (Val.nat (AggCase.code K.case)).wt ≤ 5 :=
    (wt_nat_le _).trans (by have := it_code_le K.case; omega)
  refine FunAll.intro hP.hf ?_
  unfold itSRunF
  -- the branch tuples
  have dv : Det Pg [K.v] (.var 0) (.list [K.st, .list [encKColoring K.d, encKColoring K.d'],
      .nat (AggCase.code K.case), natList (stL fun i => (itSrc K.Ag₀ K.J i : ℕ))]) _ :=
    Det.var' (i := 0) rfl
  have dst : Det Pg [K.v] (.get (.var 0) (.nat 0)) (.list [K.sv, .list [.nat k, .nat L.q],
      .list (K.ps.map pairV), .list (K.fx.map pairV), .list (K.fy.map pairV),
      stCv K.O.tuples (itCr K.Ag₀.fin S K.Ag₀.πd P₀.κ)]) _ := Det.get' dv (Det.nat 0) rfl
  have dkq := Det.get' dst (Det.nat 1) (v := .list [.nat k, .nat L.q]) rfl
  have dq := Det.get' dkq (Det.nat 1) (v := .nat L.q) rfl
  have dts := Det.call (Det.mk2 dq (Det.nat 65)) (hP.hts L.q hq0)
  refine EvalAll.letE dts fun tv ct ⟨htv, hct⟩ => ?_
  subst htv
  -- the init program of the case
  have dcode : Det Pg ([K.v] ++ [itSTv L.q]) (.get (.var 0) (.nat 2)) (.nat (AggCase.code K.case)) _ :=
    Det.get' (Det.var' (i := 0) (v := .list [K.st, .list [encKColoring K.d, encKColoring K.d'],
      .nat (AggCase.code K.case), natList (stL fun i => (itSrc K.Ag₀ K.J i : ℕ))]) rfl) (Det.nat 2) rfl
  have dv0 : Det Pg ([K.v] ++ [itSTv L.q]) (.var 0) K.v _ := Det.var' (i := 0) rfl
  have hinit := itS_disp_spec hP.hdi0 K.case K.v (FunAll.wt_lt hA.init)
  have w2 := wt_list2_le (.nat (AggCase.code K.case)) K.v
  have hdc : itSDispC (Val.list [.nat (AggCase.code K.case), K.v]).wt ≤
      itSDispC (2 * itSVB (I.inW .giant S) + 16) := by unfold itSDispC; omega
  refine EvalAll.letE (Ra := fun w cw => ∃ D, D ⊆ itSBase K ∧ R.Kc e c S L K w D ∧
      cw ≤ 5 * B + itSDispC (2 * itSVB (I.inW .giant S) + 16) + 20 * itSVB (I.inW .giant S) + 200)
    (EvalAll.call_funAll (Det.mk2 dcode dv0) fun v ca hv => ?_) fun w0 ci hw0 => ?_
  · obtain ⟨rfl, hca⟩ := hv
    refine FunAll.mono hinit fun w cst h => ?_
    obtain ⟨c', ⟨⟨D, h1, h2, h3⟩, hwc⟩, hcst⟩ := h
    have := hA.wtK w D h2
    exact ⟨D, h1, h2, by omega⟩
  obtain ⟨D0, hD0, hK0, hci⟩ := hw0
  have hw0B := hA.wtK w0 D0 hK0
  -- the runner
  have dH := Det.itSMk6 (Det.nat 0) (Det.var' (i := 0) (v := K.v) rfl)
    (Det.var' (i := 1) (v := itSTv L.q) rfl) (Det.nat 0) (Det.mk2 Det.nil Det.nil)
    (Det.var' (i := 2) (v := w0) rfl) (P := Pg) (env := [K.v] ++ [itSTv L.q] ++ [w0])
  have dst0 := Det.mk2 dH (Det.nat 0)
  refine EvalAll.call_funAll dst0 fun st0 ca hst0 => ?_
  obtain ⟨rfl, hca⟩ := hst0
  have hSs : (fun Ag => itSW Ag [] ((itSTups L.q).drop 0)) '' D0 =
      (fun Ag => Ag.itemsScript) '' D0 := by
    refine Set.image_congr fun Ag hAg => ?_
    rw [List.drop_zero, itSW_start, (hD0 hAg).2.1]
  have hrep : itSRep R e c S L K B (3 * ((itSTups L.q).length - 0) + 1)
      (.list [itSH 0 K.v 0 [] [] w0, .nat 0]) ((fun Ag => Ag.itemsScript) '' D0)
      ((itSTups L.q).length * B) :=
    Or.inl ⟨0, [], [], [], w0, D0, rfl, Nat.zero_le _, hK0, hD0, hSs.symm,
      itSOut_nil e L.toGiantLabels, ⟨by simp, by simp, by simp, by simp⟩, by simp, rfl⟩
  have hBw := itS_rep_wt hA hV hT hn hrep
  refine (run_specCD hP.hrun hs hih _ _ _ ⟨_, hrep⟩ ?_).mono ?_
  · rintro _ ⟨Ag, -, rfl⟩
    exact Ag.itemsScript_roundP
  rintro out cr ⟨s, ⟨Ag, hAg, rfl⟩, a, ex, hout, hwt, hlen, hcr⟩
  refine ⟨Ag, itSBase_sub (hD0 hAg), a, ex, hout, hwt, ?_⟩
  have eB : itSStepB (itSVB (I.inW .giant S)) (itSTvB (I.inW .giant S)) (itSNb (I.inW .giant S)) B =
    itSStB (I.inW .giant S) B := rfl
  rw [eB] at hcr hwt
  have hlen' : ex.n ≤ (itSTups L.q).length * B := hlen
  have hcr' : (cr : ℝ) ≤ ((ex.n : ℝ) + 1) * (runK * ((itSStB (I.inW .giant S) B : ℝ) + 1)) +
      ex.cost J := hcr
  -- the calls
  have hcl : ex.n + 1 ≤ itSNb (I.inW .giant S) * B + 1 := by
    have := Nat.mul_le_mul_right B hn
    omega
  have hcalls : ((ex.n : ℝ) + 1) * (runK * ((itSStB (I.inW .giant S) B : ℝ) + 1)) ≤
      ((itSNb (I.inW .giant S) * B + 1 : ℕ) : ℝ) * (runK * ((itSStB (I.inW .giant S) B : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_right (by rw [← Nat.cast_one, ← Nat.cast_add]; exact Nat.cast_le.mpr hcl)
      (mul_nonneg (Nat.cast_nonneg _) (add_nonneg (Nat.cast_nonneg _) zero_le_one))
  -- the costs before the run
  have hts : itTsC (L.q ^ 65 + L.q + 65 + 10) ≤
      itTsC (itSNb (I.inW .giant S) + (2 * I.inW .giant S + 3) + 75) :=
    itS_tsC_mono (by omega)
  have h2q := wt_list2_le (.nat L.q) (.nat 65)
  have := wt_nat_le 65
  have := wt_nat_le 0
  have := wt_nat_le 2
  have hnil := wt_list2_le (.list []) (.list [])
  have enil : (Val.list []).wt = 4 := rfl
  have hHs := wt_list6_lt (.nat 0) K.v (itSTv L.q) (.nat 0) (.list [.list [], .list []]) w0
  have eH0 : (itSH (k := k) (q := L.q) 0 K.v 0 [] [] w0).wt =
    (Val.list [.nat 0, K.v, itSTv L.q, .nat 0, .list [.list [], .list []], w0]).wt := rfl
  have hH0 : (itSH (k := k) (q := L.q) 0 K.v 0 [] [] w0).wt < (Val.list [itSH (k := k) (q := L.q) 0 K.v 0 [] [] w0, .nat 0]).wt :=
    wt_le_wt_list (by simp)
  have eH1 : (Val.list [Val.list [.nat 0, K.v, itSTv L.q, .nat 0, .list [.list [], .list []], w0],
    .nat 0]).wt = (Val.list [itSH (k := k) (q := L.q) 0 K.v 0 [] [] w0, .nat 0]).wt := rfl
  have hBV : itSVB (I.inW .giant S) + itSTvB (I.inW .giant S) + B ≤
      itSBw (itSVB (I.inW .giant S)) (itSTvB (I.inW .giant S)) (itSNb (I.inW .giant S)) B := by
    unfold itSBw; omega
  have hnat : ct + ci + ca + 3 * out.wt + 3 +
      (itSNb (I.inW .giant S) * B + 1) * (runK * (itSStB (I.inW .giant S) B + 1)) ≤
      itSRunX (I.inW .giant S) B := by
    unfold itSRunX
    omega
  have hnatR : ((ct + ci + ca + 3 * out.wt + 3 +
      (itSNb (I.inW .giant S) * B + 1) * (runK * (itSStB (I.inW .giant S) B + 1)) : ℕ) : ℝ) ≤
      (itSRunX (I.inW .giant S) B : ℝ) := Nat.cast_le.mpr hnat
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at hnatR hcalls ⊢
  linarith

end Run

/-- **The items** at `fi`, as `AsItemsOK` of the general algorithm. -/
def AsItemsD (I : Iface) (J : CostT) (Pg : Program) (F₀ F : Funs) (H : AsHand) (X : ℕ → ℕ)
    (fi : ℕ) : Prop :=
  ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C) (sv lv : Val)
    (L : SuppliedLabels S), AsCall I Pg F₀ e c S sv lv L →
    DIH Pg F J (RoundP P₀ S L.q) (measure P₀ .giant S) →
    ∀ (Cs : Set (Aggregation P₀ S L.toGiantLabels)) (st : Val), H.items e c S L Cs st →
    FunAll Pg fi st (fun w cost => ∃ Ag ∈ Cs, ∃ (pieces : List (Set (Perm Ω)))
      (os : List (LcOver L.q)) (ovs : List (Perm Ω × Subgroup (Perm Ω)))
      (pcs : List (Perm (Fin k) × Acc k)) (ex : DX Ag.itemsScript ⟨pieces, ovs⟩),
      List.Forall₂ (asOvAt L.toGiantLabels) os ovs ∧
      w = .list [.list (pcs.map encPiece), .list (os.map fun o => lcOv (o.1 : Perm (Fin L.q)) o.2.2)] ∧
      pcs.length = pieces.length ∧
      (∀ i (h1 : i < pcs.length) (h2 : i < pieces.length), ceSet pcs[i] = toFin e '' pieces[i]) ∧
      (∀ o ∈ os, gens o.2.2 = o.2.1.map (alternatingGroup (Fin L.q)).subtype) ∧
      (cost : ℝ) ≤ X (I.inW .giant S) + ex.cost J ∧ w.wt ≤ X (I.inW .giant S))

set_option maxHeartbeats 1000000 in
/-- **`AsItemsOK` from the case contracts.** -/
theorem itS_asItemsD (I : Iface) (J : CostT) (Pg : Program) (F₀ F : Funs) (H : AsHand)
    (hH : ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C)
      (L : SuppliedLabels S) Cs st, H.items e c S L Cs st → ItHandB e c S L Cs st)
    {fi fstr frun fts di0 drun dloop mv m0 m1 m3 db fac app i₁ i₂ i₃ b₁ b₂ b₃ : ℕ}
    (hfi : Pg.funs[fi]? = some (itSItemsF fstr frun)) {Xs Xc : ℕ → ℕ}
    (hstr : ItSStrOK I Pg F₀ fstr Xs)
    (hP : ItSRunAt Pg F frun fts di0 drun dloop mv m0 m1 m3 db fac app i₁ i₂ i₃ b₁ b₂ b₃)
    (h1 : ItSCaseOK I Pg F₀ (· = .one) i₁ b₁ Xc) (h2 : ItSCaseOK I Pg F₀ (· = .twoA) i₂ b₂ Xc)
    (h3 : ItSCaseOK I Pg F₀ (fun a => a = .twoB ∨ a = .three) i₃ b₃ Xc) :
    AsItemsD I J Pg F₀ F H (itSX Xs Xc) fi := by
  intro Ω C k e c S sv lv L hc hih Cs st hst
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
  obtain ⟨R, hA⟩ := itS_caseAt I Pg F₀ h1 h2 h3 hc K hK
  have hrun := itS_runD I Pg F J F₀ hP hc hih hK hA
  have hstW := itS_stW I Pg F₀ hc hK
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

end GI.Degree
