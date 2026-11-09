module

public import Workspace.Degree.RunD
public import Workspace.Degree.RoundMass
public import Workspace.Impl.AggCertOK

@[expose] public section

/-!
# The certificate phase of the degree algorithm

The text of `cert_phase_spec`, `cp_phase_spec`, `cp_cert_core` and `asCertOK_of` of the general
algorithm, over the runner `run_specCD`. The move function and all the hand-over relations are those
of the general algorithm. `J` is the table of costs of the calls, and `F` holds the functions that
the driver calls.
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly GI.Impl GI.Lang GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens PointwiseStab Preimage Membership)
open scoped Pointwise

section Phase

variable {k : ℕ} {Ω C : Type} [DecidableEq Ω] {e : Ω ≃ Fin k} {S : State Ω C} [Fintype S.dom]
  {L : GiantLabels S} {πd : S.domGroup →* alternatingGroup (Fin L.q)}

/-- **The certificate phase, from a move function.** -/
theorem cert_phase_specD (J : CostT) (Pg : Program) (F : Funs) {d stp mv : ℕ} (hd : Pg.funs[d]? = some (runBody F d stp))
    (hstp : Pg.funs[stp]? = some (cpLoopBody stp mv)) {par : Val} {D Bm Bw M₀ NT : ℕ}
    (hmv : ∀ m st Ss f, CpRep e πd par D Bw M₀ NT m st Ss f → FunAll Pg mv st (fun w c =>
      c ≤ Bm ∧ (Iface.StepPostC (measure P₀ .giant S) (CpOut e S L πd)
          (fun st Ss f => ∃ m, CpRep e πd par D Bw M₀ NT m st Ss f) Ss f w ∨
        ∃ m' st' Ss', m' < m ∧ Ss' ⊆ Ss ∧ CpRep e πd par D Bw M₀ NT m' st' Ss' f ∧
          w = .list [.nat 2, st'])))
    {Pr : ∀ {Ω' C' : Type}, Mode → State Ω' C' → Prop} (ih : DIH Pg F J Pr (measure P₀ .giant S))
    (κ : ℕ) (O : TestSetOrder L.q κ)
    (hPr : ∀ R, (certPhase S πd κ O R (dstr S S.x) (dstr S S.y)).CallsExact Pr)
    {st₀ : Val} {m₀ f₀ : ℕ}
    (h₀ : CpRep e πd par D Bw M₀ NT m₀ st₀
      ((fun R => certPhase S πd κ O R (dstr S S.x) (dstr S S.y)) '' Cands []) f₀) :
    FunAll Pg d st₀ (fun out cost => ∃ R : CosetRepFn S.dom, ∃ (a : List (StagePair S))
      (ex : DX (certPhase S πd κ O R (dstr S S.x) (dstr S S.y)) a), CpOut e S L πd a out ∧
      ex.n ≤ f₀ ∧
      (cost : ℝ) ≤ ((ex.n : ℝ) + 1) *
        (runK * (((M₀ + 1) * cpLoopC Bm Bw + Bw : ℕ) + 1)) + ex.cost J) := by
  have hs := stepOKC_of_move (M := M₀) hstp hmv (fun m st Ss f h => by
      obtain ⟨_, _, _, _, _, hw, _⟩ := h; exact hw)
    (fun m st Ss f h => by obtain ⟨_, _, _, hm, _, _, hM, _⟩ := h; omega)
  refine (run_specCD hd hs ih f₀ st₀ _ ⟨m₀, h₀⟩ ?_).mono ?_
  · rintro _ ⟨R, -, rfl⟩
    exact hPr R
  rintro out cost ⟨s, ⟨R, -, rfl⟩, a, ex, hout, -, hlen, hc⟩
  exact ⟨R, a, ex, hout, hlen, by exact_mod_cast hc⟩

end Phase

section Entry

variable {k : ℕ} {Ω C : Type} [Finite Ω] [DecidableEq Ω] {e : Ω ≃ Fin k} {c : C → ℕ}
  {S : State Ω C} [Fintype S.dom] {L : GiantLabels S}
  {πd : S.domGroup →* alternatingGroup (Fin L.q)}
  (hst : PointwiseStab) (hpre : Preimage) (hm : Membership)


theorem cp_phase_specD (J : CostT) (Pg : Program) (F : Funs) {d stp b jp jpre jm : ℕ}
    (hd : Pg.funs[d]? = some (runBody F d stp)) (hstp : Pg.funs[stp]? = some (cpLoopBody stp b))
    (hat : CpMvAt Pg b jp jpre jm)
    (hjp : Pg.prims[jp]? = some (pointwiseStabPrim hst))
    (hjpre : Pg.prims[jpre]? = some (preimagePrim hpre))
    (hjm : Pg.prims[jm]? = some (membershipPrim hm))
    {sv : Val} {gp : GPairs k L.q} {osA : List (Fin (k + L.q))} {D : ℕ}
    (ctx : CpCtx e c S L πd sv gp osA D)
    {Pr : ∀ {Ω' C' : Type}, Mode → State Ω' C' → Prop} (ih : DIH Pg F J Pr (measure P₀ .giant S))
    (O : TestSetOrder L.q P₀.κ)
    (hPr : ∀ R, (certPhase S πd P₀.κ O R (dstr S S.x) (dstr S S.y)).CallsExact Pr)
    {T : Finset (Fin L.q)} {Ts : List (Finset (Fin L.q))}
    (hO : O.sets = T :: Ts) {p0 : GPairs k L.q}
    (hp0 : PairGens e L (S.liftGroup (Pgrp S.domGroup πd T)) p0)
    (hp0l : p0.length ≤ (k + L.q) ^ 2) {Bw W : ℕ}
    (hBw : cpBw k L.q (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA)).wt
      (Ts.length + 1) ((2 * Ts.length + 2) * (Fintype.card S.dom + 1) * (D + 2)) D ≤ Bw)
    (hW : 10 ^ 4 * (Bw + 2) ^ 2 ≤ W) :
    FunAll Pg d (.list [(CpSt.init T Ts p0 osA).val
        (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA)) (.list []), .nat 0])
      (fun out cost => ∃ R : CosetRepFn S.dom, ∃ (a : List (StagePair S))
        (ex : DX (certPhase S πd P₀.κ O R (dstr S S.x) (dstr S S.y)) a), CpOut e S L πd a out ∧
        ex.n ≤ (2 * Ts.length + 2) * (Fintype.card S.dom + 1) * (D + 2) ∧
        (cost : ℝ) ≤ ((ex.n : ℝ) + 1) *
          (runK * ((((2 * Ts.length + 2) * (Fintype.card S.dom + 1) * (D + 2) + 1) *
            cpLoopC (cpBm hst hpre hm W) Bw + Bw : ℕ) + 1)) + ex.cost J) := by
  have hcard : ∀ T' ∈ O.sets, T'.card = P₀.κ := fun T' h => (O.mem T').1 h
  have hA := ctx.hosA
  have hlen : CpLen D (CpSt.init T Ts p0 osA) :=
    ⟨Nat.zero_le _, cpAll_length hA, hp0l, by simp [CpSt.init], hp0l, by simp [CpSt.init],
      by simp [CpSt.init]⟩
  have hwt := cp_wt_new (par := cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA))
    hlen ⟨rfl, cpLgLen_nil, cpLgLen_nil, fun l h => by simp [CpSt.init] at h⟩ (NT := Ts.length + 1) (M₀ := (2 * Ts.length + 2) * (Fintype.card S.dom + 1) * (D + 2))
    (by simp [CpSt.init]) (by simp [CpSt.init]) (by simp [CpSt.init]) hBw
  have h0 := cpRep_init (e := e) (πd := πd) O hO hcard hp0 hA hlen hwt
  exact cert_phase_specD J Pg F hd hstp (cp_hmv hst hpre hm hat hjp hjpre hjm ctx hBw hW) ih
    P₀.κ O hPr h0

end Entry

variable {Ω C : Type} {k : ℕ}

section Core

variable (hst : PointwiseStab) (hpre : Preimage) (hm : Membership)

/-- **The core of `AsCertOK`.** From a program state for the candidates `Cs` (`CpHand`), the
runner of the certificate phase returns the graph forms of the final stages (`CpOut`) of a run of
the certificate script of a member `Ag` of `Cs`. The cost is at most
`(calls + 1) runK (cpPhaseB … + 1)` plus the cost of the calls, for the weight `P` of the parent
data, `NT = binom(q, κ)` test sets and `D = κ!/2`. -/
theorem cp_cert_coreD (J : CostT) (Pg : Program) (F : Funs) {d stp b jp jpre jm : ℕ}
    (hd : Pg.funs[d]? = some (runBody F d stp)) (hstp : Pg.funs[stp]? = some (cpLoopBody stp b))
    (hat : CpMvAt Pg b jp jpre jm)
    (hjp : Pg.prims[jp]? = some (pointwiseStabPrim hst))
    (hjpre : Pg.prims[jpre]? = some (preimagePrim hpre))
    (hjm : Pg.prims[jm]? = some (membershipPrim hm))
    {e : Ω ≃ Fin k} {c : C → ℕ} {S : State Ω C} {L : SuppliedLabels S}
    {Cs : Set (Aggregation P₀ S L.toGiantLabels)} {st : Val} (h : CpHand e c S L Cs st)
    (ih : DIH Pg F J (RoundP P₀ S L.q) (measure P₀ .giant S)) :
    FunAll Pg d st (fun out cost => ∃ Ag ∈ Cs, ∃ (a : List (StagePair S))
      (ex : DX Ag.certScript a),
      (haveI : Finite Ω := Finite.of_equiv _ e.symm
       letI : Fintype S.dom := Fintype.ofFinite _
       letI : DecidableEq Ω := Classical.decEq _
       CpOut e S L.toGiantLabels (L.toGiantLabels.domMap L.con.onDomain) a out) ∧
      ∃ P n : ℕ, P < st.wt ∧ n ≤ k ∧
      ex.n ≤ (2 * (L.q.choose P₀.κ - 1) + 2) * (n + 1) * (P₀.κ.factorial / 2 + 2) ∧
      (cost : ℝ) ≤ ((ex.n : ℝ) + 1) * (runK *
        (cpPhaseB hst hpre hm k L.q P (L.q.choose P₀.κ) n (P₀.κ.factorial / 2) + 1)) +
          ex.cost J) := by
  haveI : Finite Ω := Finite.of_equiv _ e.symm
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq Ω := Classical.decEq _
  obtain ⟨rfl, ⟨Ag₀, hAg₀⟩, sv, gp, osA, T, Ts, p0, hO, ctx, hp0, hp0l, rfl⟩ := h
  have hNT : Ts.length + 1 = L.q.choose P₀.κ := by
    rw [← (sbOrder L.q P₀.κ).length_eq, hO, List.length_cons]
  have hsE : ∀ R, (cpWith Ag₀ (sbOrder L.q P₀.κ) R).certScript =
      certPhase S (L.toGiantLabels.domMap L.con.onDomain) P₀.κ (sbOrder L.q P₀.κ) R
        (dstr S S.x) (dstr S S.y) := fun R => by
    rw [cpWith_certScript]; show certPhase S Ag₀.πd _ _ _ _ _ = _; rw [cp_πd_eq hAg₀]
  refine (cp_phase_specD hst hpre hm J Pg F hd hstp hat hjp hjpre hjm ctx ih
    (sbOrder L.q P₀.κ) (fun R => hsE R ▸ (cpWith Ag₀ (sbOrder L.q P₀.κ) R).certScript_roundP)
    hO hp0 hp0l le_rfl le_rfl).mono ?_
  rintro out cost ⟨R, a, ex, hout, hcl, hc⟩
  have hmem := cpWith_mem_asRounds hAg₀ (sbOrder L.q P₀.κ) R
  obtain ⟨ex', hex', hcost'⟩ := DX.cast (hsE R).symm ex
  have hcost : ex'.cost J = ex.cost J := hcost' J
  refine ⟨_, hmem, a, ex', hout, (cpParV k L.q (Fintype.card S.dom) (P₀.κ.factorial / 2) sv
    (gpV gp) (encPts osA)).wt, Fintype.card S.dom, ?_, cp_card_dom_le e, ?_, ?_⟩
  · exact (cp_wt_get (vs := (CpSt.init T Ts p0 osA).vals _ (.list [])) (j := 0) rfl).trans
      (cp_wt_get (vs := [(CpSt.init T Ts p0 osA).val _ (.list []), .nat 0]) (j := 0) rfl)
  · rw [hex', ← hNT, Nat.add_sub_cancel]; exact hcl
  · rw [hcost, hex', ← hNT]
    simp only [cpPhaseB, Nat.add_sub_cancel]
    exact hc

end Core

/-- **The certificate phase** at `fc`, as `AsCertOK` of the general algorithm. -/
def AsCertD (I : Iface) (J : CostT) (Pg : Program) (F₀ F : Funs) (H : AsHand) (X : ℕ → ℕ) (fc : ℕ) :
    Prop :=
  ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C) (sv lv : Val)
    (L : SuppliedLabels S), AsCall I Pg F₀ e c S sv lv L →
    DIH Pg F J (RoundP P₀ S L.q) (measure P₀ .giant S) →
    ∀ (Cs : Set (Aggregation P₀ S L.toGiantLabels)) (st : Val), H.cert e c S L Cs st →
    FunAll Pg fc st (fun w cost => ∃ Ag ∈ Cs, ∃ (a : List (StagePair S))
      (ex : DX Ag.certScript a),
      H.comp e c S L {Ag' | Ag' ∈ Cs ∧ Ag'.certScript = Ag.certScript} w ∧
      (cost : ℝ) ≤ X (I.inW .giant S) + ex.cost J ∧ w.wt ≤ X (I.inW .giant S))

section Rounds

variable (hst : PointwiseStab) (hpre : Preimage) (hm : Membership)


set_option maxHeartbeats 4000000 in
/-- **`AsCertOK`** for the function `cpCertE d f` at `fc`, from the hand-over relations: the
state of the certificate phase satisfies `CpHand`, and `CmHand` gives the state of the
comparison phase. The own cost is at most `cpCertX W₀`. -/
theorem asCertOK_ofD (I : Iface) (J : CostT) (Pg : Program) (F₀ F : Funs) (H : AsHand) (X : ℕ → ℕ)
    {fc d stp b jp jpre jm f : ℕ}
    (hfc : Pg.funs[fc]? = some (cpCertE d f))
    (hd : Pg.funs[d]? = some (runBody F d stp)) (hstp : Pg.funs[stp]? = some (cpLoopBody stp b))
    (hat : CpMvAt Pg b jp jpre jm) (hfz : CpFzAt Pg f b)
    (hjp : Pg.prims[jp]? = some (pointwiseStabPrim hst))
    (hjpre : Pg.prims[jpre]? = some (preimagePrim hpre))
    (hjm : Pg.prims[jm]? = some (membershipPrim hm))
    (hcp : ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C)
      (L : SuppliedLabels S) Cs st, H.cert e c S L Cs st → CpHand e c S L Cs st)
    (hcm : ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C)
      (L : SuppliedLabels S) Cs st, CmHand e c S L Cs st → H.comp e c S L Cs st)
    (hX : ∀ W, cpCertX hst hpre hm W ≤ X W) : AsCertD I J Pg F₀ F H X fc := by
  intro Ω C k e c S sv' lv L hcall hih Cs st hstH
  have hh := hcp e c S L Cs st hstH
  have hcore := cp_cert_coreD hst hpre hm J Pg F hd hstp hat hjp hjpre hjm hh hih
  haveI : Finite Ω := Finite.of_equiv _ e.symm
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq Ω := Classical.decEq _
  obtain ⟨hCs, -, sv, gp, osA, T, Ts, p0, hO, ctx, hp0, hp0l, hstv⟩ := hh
  set W₀ := I.inW .giant S with hW₀
  -- the sizes, bounded by `W₀`
  have hW0 : 2 * (stateW k S + I.labW k S.N) + 6 = W₀ := by
    rw [hW₀]; simp only [Iface.inW, Iface.card_eq e]
  have hkS : k ≤ stateW k S := by unfold stateW; omega
  have hsv : sv.wt ≤ stateW k S := ctx.canon.wt_le
  have hq : L.q ≤ k + 2 := GiantLabels.q_le e L.toGiantLabels
  have hn : Fintype.card S.dom ≤ k := cp_card_dom_le e
  have hkN : k ≤ cpNW W₀ := by unfold cpNW; omega
  have hqN : L.q ≤ cpNW W₀ := by unfold cpNW; omega
  have hNT : L.q.choose P₀.κ ≤ cpNTW W₀ :=
    (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left hqN _)
  have hNTs : Ts.length + 1 = L.q.choose P₀.κ := by
    rw [← (sbOrder L.q P₀.κ).length_eq, hO, List.length_cons]
  have hpow : (k + L.q + 1) ^ 4 ≤ (2 * cpNW W₀ + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have hpow6 : (k + L.q + 1) ^ 6 ≤ (2 * cpNW W₀ + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have hY : 1 ≤ (2 * cpNW W₀ + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  set par := cpParV k L.q (Fintype.card S.dom) (P₀.κ.factorial / 2) sv (gpV gp) (encPts osA)
    with hpar
  have hparw : par.wt ≤ cpPW W₀ := by
    have := cp_wt_parV (n := Fintype.card S.dom) (D := P₀.κ.factorial / 2) (sv := sv) ctx.hgpl
      (cpAll_length ctx.hosA)
    exact this.trans (by unfold cpPW cpDc; omega)
  have hlen : CpLen (P₀.κ.factorial / 2) (CpSt.init T Ts p0 osA) :=
    ⟨Nat.zero_le _, cpAll_length ctx.hosA, hp0l, by simp [CpSt.init], hp0l, by simp [CpSt.init],
      by simp [CpSt.init]⟩
  have hstw : st.wt ≤ cpSW W₀ := by
    rw [hstv]; unfold cpInitV
    refine cp_wt_new (par := par) hlen
      ⟨rfl, cpLgLen_nil, cpLgLen_nil, fun l h => by simp [CpSt.init] at h⟩ (NT := Ts.length + 1)
      (M₀ := 0) (by simp [CpSt.init]) (by simp [CpSt.init]) (by simp [CpSt.init]) ?_
    exact cpBw_mono hkN hqN hparw (by omega) le_rfl
  set A := ((2 * cpNTW W₀ + 2) * (cpNW W₀ + 1) * (cpDc + 2) + 1) *
    (runK * (cpPhaseB hst hpre hm (cpNW W₀) (cpNW W₀) (cpSW W₀) (cpNTW W₀) (cpNW W₀) cpDc + 1))
    with hA
  refine FunAll.intro hfc ?_
  unfold cpCertE
  refine EvalAll.letE (Ra := fun out cst => ∃ Ag ∈ Cs, ∃ (a : List (StagePair S))
      (ex : DX Ag.certScript a),
      CpOut e S L.toGiantLabels (L.toGiantLabels.domMap L.con.onDomain) a out ∧
      (cst : ℝ) ≤ (A : ℝ) + ((st.wt + out.wt + 2 : ℕ) : ℝ) + ex.cost J) ?_ ?_
  · -- the runner
    refine EvalAll.call_funAll (Det.var' (P := Pg) (env := [st]) (i := 0) rfl) fun v ca hv => ?_
    obtain ⟨hv1, hca⟩ := hv
    subst v
    refine hcore.mono ?_
    rintro out cost ⟨Ag, hAg, a, ex, hout, P, n, hP, hn', hcalls, hcost⟩
    refine ⟨Ag, hAg, a, ex, hout, ?_⟩
    have hPS : P ≤ cpSW W₀ := by omega
    have hph := cpPhaseB_mono hst hpre hm hkN hqN hPS hNT (show n ≤ cpNW W₀ by omega)
      (D := P₀.κ.factorial / 2)
    have hcl : ex.n + 1 ≤
        (2 * cpNTW W₀ + 2) * (cpNW W₀ + 1) * (cpDc + 2) + 1 := by
      have : (2 * (L.q.choose P₀.κ - 1) + 2) * (n + 1) * (P₀.κ.factorial / 2 + 2) ≤
          (2 * cpNTW W₀ + 2) * (cpNW W₀ + 1) * (cpDc + 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) le_rfl
      omega
    have hN : (ex.n + 1) * (runK * (cpPhaseB hst hpre hm k L.q P (L.q.choose P₀.κ) n
        (P₀.κ.factorial / 2) + 1)) ≤ A :=
      Nat.mul_le_mul hcl (Nat.mul_le_mul_left _ (Nat.add_le_add_right hph 1))
    have hR : ((ex.n : ℝ) + 1) * (runK * (cpPhaseB hst hpre hm k L.q P
        (L.q.choose P₀.κ) n (P₀.κ.factorial / 2) + 1)) ≤ (A : ℝ) := by exact_mod_cast hN
    have hca' : (ca : ℝ) ≤ (st.wt : ℝ) + 1 := by exact_mod_cast hca
    push_cast
    linarith
  · -- the programs for `F_x`, `F_y` and the state of the comparison phase
    rintro out ca ⟨Ag, hAg, a, ex, ⟨res, logs, rfl, -, hord, hstgs, hlg, hrel, hlens⟩, hca⟩
    have hAgR : Ag ∈ asRounds L := hCs ▸ hAg
    have hin : CpFzIn e S L.toGiantLabels (L.toGiantLabels.domMap L.con.onDomain) res logs :=
      ⟨hrel, hlens, hstgs, hlg, hord⟩
    have hlogsl : logs.length = L.q.choose P₀.κ := by
      obtain ⟨O, hO'⟩ := hord
      have := congrArg List.length hO'
      rw [List.length_map, O.length_eq] at this
      exact this
    have hresl : res.length = L.q.choose P₀.κ := hin.length.trans hlogsl
    have hres : (Val.list (res.map resV)).wt ≤ cpNTW W₀ * (421 * (2 * cpNW W₀ + 1) ^ 4) + 4 := by
      have h1 := cp_wt_list (vs := res.map resV) (n := cpNTW W₀)
        (c := 210 * (2 * cpNW W₀ + 1) ^ 4) (by rw [List.length_map]; omega) (by
          simp only [List.mem_map]; rintro _ ⟨r, hr, rfl⟩
          exact (cp_wt_res (hlens r hr).1 (hlens r hr).2).trans (by omega))
      have : cpNTW W₀ * (2 * (210 * (2 * cpNW W₀ + 1) ^ 4) + 1) ≤
          cpNTW W₀ * (421 * (2 * cpNW W₀ + 1) ^ 4) := Nat.mul_le_mul_left _ (by omega)
      omega
    have hlgs : (Val.list (logs.map cpLogV)).wt ≤ cpNTW W₀ * (2801 * (2 * cpNW W₀ + 1) ^ 6) + 4 := by
      have h1 := cp_wt_logs (NT := cpNTW W₀) (by omega) hlg
      have : cpNTW W₀ * (2801 * (k + L.q + 1) ^ 6) ≤ cpNTW W₀ * (2801 * (2 * cpNW W₀ + 1) ^ 6) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    have hout : (cpOutV res logs).wt ≤ cpOW W₀ := by
      have := wt_list2_le (.list (res.map resV)) (.list (logs.map cpLogV))
      unfold cpOutV cpOW; omega
    have hBs : ∀ s ≤ 1, (Val.list [par, cpOutV res logs, .nat s]).wt ≤
        2 * (cpPW W₀ + cpOW W₀ + 3) + 7 := by
      intro s hs
      have := wt_list3_le par (cpOutV res logs) (.nat s)
      have := wt_nat_le s
      omega
    have hWs : ∀ s ≤ 1, cpFzW k L.q (Val.list [par, cpOutV res logs, .nat s]).wt logs.length
        (P₀.κ.factorial / 2) ≤ cpWW W₀ := fun s hs =>
      (cpFzW_mono hkN hqN (hBs s hs) (by omega)).trans (Nat.le_add_right _ _)
    have hSW : cpSW W₀ ≤ cpWW W₀ := Nat.le_add_left _ _
    have hOW : cpOW W₀ ≤ cpWW W₀ := by unfold cpWW cpFzW; omega
    have hrest := cp_cert_rest hst hpre hm hat hfz hjp hjpre ctx hin (st := st) (u := .nat 0)
      (by rw [hstv]; rfl) (hstw.trans hSW) hWs
    refine EvalAll.mono hrest fun w cb ⟨⟨fx, fy, hw, hfxl, hfyl, hfxg, hfyg⟩, hww, hcb⟩ => ?_
    have hXW := hX W₀
    unfold cpCertX at hXW
    rw [← hA] at hXW
    refine ⟨Ag, hAg, a, ex, hcm e c S L _ _ ⟨fun Ag' h => hCs ▸ h.1, Ag, ⟨hAg, rfl⟩,
      fun Ag' hA' hs => ⟨hCs ▸ hA', hs⟩, sv, gp, fx, fy, logs.map cpCmLog, hw, ctx.canon,
      ctx.hgp, ?_, ?_, ctx.hgpl, hfxl, hfyl, ?_⟩, ?_, by omega⟩
    · rw [← cp_itCertLift hAgR]; exact hfxg
    · rw [← cp_itCertLift hAgR]; exact hfyg
    · rw [cp_πd_eq hAgR]
      exact cp_cmLogsOK e _ hord hstgs
    · have hN : A + (st.wt + (cpOutV res logs).wt + 2) + cb + w.wt + 1 ≤ X W₀ := by omega
      have hR : ((A + (st.wt + (cpOutV res logs).wt + 2) + cb + w.wt + 1 : ℕ) : ℝ) ≤ X W₀ := by
        exact_mod_cast hN
      rw [show Val.list [.list (res.map resV), .list (logs.map cpLogV)] = cpOutV res logs from rfl]
        at hca
      push_cast at hR hca ⊢
      linarith

end Rounds

end GI.Degree
