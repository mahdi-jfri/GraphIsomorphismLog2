module

public import Workspace.Impl.AggCertBound
public import Workspace.Impl.GenNormPoly

@[expose] public section

/-!
# The certificate phase: `AsCertOK`

The function at `fc` (`cpCertE d f`) runs the certificate phase in three steps.

1. The runner at `d` plays the certificate script on the start state `st` (`cp_cert_core`). It
   returns the graph forms of the final stages and the stage logs (`CpOut`).
2. The program at `f` computes the graph forms of the lifts of `F_x` and `F_y` from this output
   (`cp_fz_spec`), once for each string.
3. The function returns the state of the comparison phase,
   `cmSt sv k q gp fx fy (logs.map cpCmLog)`, which satisfies `CmHand`.

`asCertOK_of` proves `AsCertOK` from the hand-over relations `CpHand` and `CmHand`, with the bound
`cpCertX W₀` (`AggCertBound.lean`). `cpCertX_pbu` shows that this bound is uniformly polynomial.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens PointwiseStab Preimage Membership)

/-! ### The program -/

/-- The parent data of the start state, `st[0][0]`. -/
def cpParE : Expr := .get (.get (.var 0) (.nat 0)) (.nat 0)

/-- **The certificate phase** at `fc`: the runner at `d`, the program for `F_x`, `F_y` at `f`,
and the state of the comparison phase. -/
def cpCertE (d f : ℕ) : Expr :=
  .letE (.call d (.var 0))
    (.letE (.call f (mk3 cpParE (.var 1) (.nat 0)))
      (.letE (.call f (mk3 cpParE (.var 1) (.nat 1)))
        (Expr.mkList [.get cpParE (.nat 0), .get cpParE (.nat 1), .get cpParE (.nat 2), .var 2,
          .var 3, .get (.var 1) (.nat 1)])))

/-! ### After the runner -/

section Rest

variable {P : Program} {env : List Val}

/-- Reading the parent data from the start state. -/
theorem cp_det_par {st par u : Val} {rest : List Val} {W : ℕ} (h0 : env[0]? = some st)
    (hst : st = .list [.list (par :: rest), u]) (hw : st.wt ≤ W) :
    Det P env cpParE par (3 * (W + 20)) := by
  subst hst
  have h1 := cp_wt_get (vs := [.list (par :: rest), u]) (j := 0) rfl
  have h2 := cp_wt_get (vs := par :: rest) (j := 0) rfl
  exact (Det.get' (Det.get' (Det.var' h0) (Det.nat 0) (v := .list (par :: rest)) rfl) (Det.nat 0)
    (v := par) rfl).mono (by omega)

variable {k : ℕ} {Ω C : Type} [DecidableEq Ω] {e : Ω ≃ Fin k} {col : C → ℕ} {S : State Ω C}
  [Fintype S.dom] {L : GiantLabels S} {πd : S.domGroup →* alternatingGroup (Fin L.q)}
  (hst : PointwiseStab) (hpre : Preimage) (hm : Membership)

set_option maxHeartbeats 2000000 in
/-- **The part after the runner**: the two programs for `F_x`, `F_y` and the state of the
comparison phase. -/
theorem cp_cert_rest {Pg : Program} {f b jp jpre jm : ℕ} (hat : CpMvAt Pg b jp jpre jm)
    (hfz : CpFzAt Pg f b) (hjp : Pg.prims[jp]? = some (pointwiseStabPrim hst))
    (hjpre : Pg.prims[jpre]? = some (preimagePrim hpre))
    {sv : Val} {gp : GPairs k L.q} {osA : List (Fin (k + L.q))} {D : ℕ}
    (ctx : CpCtx e col S L πd sv gp osA D)
    {res : List (GPairs k L.q × GPairs k L.q)}
    {logs : List (Finset (Fin L.q) × List (CpStgD k L.q) × List (CpStgD k L.q))}
    (hin : CpFzIn e S L πd res logs) {st u : Val} {rest : List Val}
    (hst0 : st = .list [.list (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA) :: rest),
      u]) {W : ℕ} (hstw : st.wt ≤ W)
    (hW : ∀ s ≤ 1, cpFzW k L.q (Val.list [cpParV k L.q (Fintype.card S.dom) D sv (gpV gp)
      (encPts osA), cpOutV res logs, .nat s]).wt logs.length D ≤ W) :
    CpEB Pg [st, cpOutV res logs]
      (.letE (.call f (mk3 cpParE (.var 1) (.nat 0)))
        (.letE (.call f (mk3 cpParE (.var 1) (.nat 1)))
          (Expr.mkList [.get cpParE (.nat 0), .get cpParE (.nat 1), .get cpParE (.nat 2), .var 2,
            .var 3, .get (.var 1) (.nat 1)]))) W
      (2 * cpFzB hst hpre hm W + 100 * (W + 20))
      (fun w => ∃ fx fy : GPairs k L.q, w = cmSt sv k L.q gp fx fy (logs.map cpCmLog) ∧
        fx.length ≤ (k + L.q) ^ 2 ∧ fy.length ≤ (k + L.q) ^ 2 ∧
        PairGens e L (S.liftGroup (certGroup S πd P₀.κ (dstr S S.x))) fx ∧
        PairGens e L (S.liftGroup (certGroup S πd P₀.κ (dstr S S.y))) fy) := by
  set par := cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA) with hpar
  set out := cpOutV res logs with hout
  set pvs : List Val := [sv, .list [.nat k, .nat L.q], gpV gp, .nat (Fintype.card S.dom), .nat D,
    encPts osA, pSplitCtx k L.q, .nat (k + L.q)] with hpvs
  have ep : (Val.list pvs).wt = par.wt := rfl
  have hsvw : sv.wt < par.wt := cp_wt_get (vs := pvs) (j := 0) rfl
  have hkqw : (Val.list [.nat k, .nat L.q]).wt < par.wt := cp_wt_get (vs := pvs) (j := 1) rfl
  have hgpw : (gpV gp).wt < par.wt := cp_wt_get (vs := pvs) (j := 2) rfl
  have hlgw : (Val.list (logs.map cpLogV)).wt < out.wt :=
    cp_wt_get (vs := [.list (res.map resV), .list (logs.map cpLogV)]) (j := 1) rfl
  have eo : (Val.list [.list (res.map resV), .list (logs.map cpLogV)]).wt = out.wt := rfl
  have hpst : par.wt < st.wt := by
    rw [hst0]
    exact (cp_wt_get (vs := par :: rest) (j := 0) rfl).trans
      (cp_wt_get (vs := [.list (par :: rest), u]) (j := 0) rfl)
  have hB : ∀ s : ℕ, par.wt + out.wt + (Val.nat s).wt ≤ (Val.list [par, out, .nat s]).wt := by
    intro s
    have := wt_list_eq [par, out, .nat s]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at this
    omega
  have hW0 := hW 0 (by omega)
  have hW1 := hW 1 (by omega)
  have hB0 := hB 0
  have hB1 := hB 1
  have w1 : 1 ≤ (k + L.q + 1) ^ 12 := Nat.one_le_pow _ _ (by omega)
  have w4 : (k + L.q + 1) ^ 4 ≤ (k + L.q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  unfold cpFzW at hW0 hW1
  -- one call of the program for `F_z`
  have hF : ∀ (s : ℕ), s ≤ 1 → ∀ (rest' : List Val),
      CpEB Pg ([st, out] ++ rest') (.call f (mk3 cpParE (.var 1) (.nat s))) W
        (10 * (W + 20) + cpFzB hst hpre hm W + W + 1)
        (fun w => ∃ fz : GPairs k L.q, w = gpV fz ∧ fz.length ≤ (k + L.q) ^ 2 ∧
          PairGens e L (S.liftGroup (certGroup S πd P₀.κ (dstr S (cpSel s S.x S.y)))) fz) := by
    intro s hs rest'
    have hsW := hW s hs
    have hBs := hB s
    unfold cpFzW at hsW
    have hsw : (Val.nat s).wt ≤ 3 := (wt_nat_le s).trans (by omega)
    have dA := Det.mk3 (cp_det_par (P := Pg) (env := [st, out] ++ rest') (rest := rest) (u := u)
      (par := par) rfl hst0 hstw) (Det.var' (P := Pg) (env := [st, out] ++ rest') (i := 1) rfl)
      (Det.nat (P := Pg) (env := [st, out] ++ rest') s)
    refine CpEB.call (CpEB.det dA (by omega) (by omega)
      (Q := fun v => v = .list [par, out, .nat s]) rfl) fun v hv _ => ?_
    subst hv
    exact cp_fz_spec hst hpre hm hat hfz hjp hjpre ctx hin hs (hW s hs)
  refine (CpEB.letE (hF 0 (by omega) [])
    (Cb := (10 * (W + 20) + cpFzB hst hpre hm W + W + 1) + 50 * (W + 20) + W + 1)
    fun v ⟨fx, hfx, hfxl, hfxg⟩ _ => ?_).mono (by omega) fun _ h => h
  subst hfx
  refine CpEB.letE (hF 1 (by omega) [gpV fx]) fun v ⟨fy, hfy, hfyl, hfyg⟩ _ => ?_
  subst hfy
  -- the state of the comparison phase
  set E : List Val := [st, out, gpV fx, gpV fy] with hE
  have hfxw := cp_wt_gp hfxl
  have hfyw := cp_wt_gp hfyl
  have hP := cp_det_par (P := Pg) (env := E) (rest := rest) (u := u) (par := par) rfl hst0 hstw
  have hv : Val.list [sv, .list [.nat k, .nat L.q], gpV gp, gpV fx, gpV fy,
      .list (logs.map cpLogV)] = cmSt sv k L.q gp fx fy (logs.map cpCmLog) := by
    unfold cmSt; rw [cp_cmLogV]; rfl
  have hvw := wt_list_le [sv, .list [.nat k, .nat L.q], gpV gp, gpV fx, gpV fy,
    .list (logs.map cpLogV)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at hvw
  have hwv : (Val.list [sv, .list [.nat k, .nat L.q], gpV gp, gpV fx, gpV fy,
      .list (logs.map cpLogV)]).wt ≤ W := by omega
  have hlist := cp_mkList' (P := Pg) (env := E) (W := W) (c := 5 * (W + 20))
    [(.get cpParE (.nat 0), sv), (.get cpParE (.nat 1), .list [.nat k, .nat L.q]),
      (.get cpParE (.nat 2), gpV gp), (.var 2, gpV fx), (.var 3, gpV fy),
      (.get (.var 1) (.nat 1), .list (logs.map cpLogV))] hv (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (Det.get' hP (Det.nat 0) (v := sv) rfl).mono (by omega)
      · exact (Det.get' hP (Det.nat 1) (v := .list [.nat k, .nat L.q]) rfl).mono (by omega)
      · exact (Det.get' hP (Det.nat 2) (v := gpV gp) rfl).mono (by omega)
      · exact (Det.var' (P := Pg) (env := E) (i := 2) rfl).mono (by omega)
      · exact (Det.var' (P := Pg) (env := E) (i := 3) rfl).mono (by omega)
      · have hos : out.wt < st.wt + out.wt + 1 := by omega
        exact (Det.get' (Det.var' (P := Pg) (env := E) (i := 1) rfl) (Det.nat 1)
          (v := .list (logs.map cpLogV)) rfl).mono (by
            have : out.wt ≤ (Val.list [par, out, .nat 0]).wt := by omega
            omega))
    (hv ▸ hwv)
  refine CpEB.det hlist (by simp only [List.length_cons, List.length_nil]; omega) (hv ▸ hwv)
    ⟨fx, fy, rfl, hfxl, hfyl, hfxg, hfyg⟩

end Rest

/-! ### The phase -/

section Phase

variable (hst : PointwiseStab) (hpre : Preimage) (hm : Membership)

/-- The lift of `F_z` of the labels is the lift of `F_z` of a round (`itCertLift`); the two use
different, but equal, instances. -/
theorem cp_itCertLift {Ω C : Type} {S : State Ω C} {L : SuppliedLabels S}
    {Ag : Aggregation P₀ S L.toGiantLabels} (hAg : Ag ∈ asRounds L) (z : Ω → C) :
    (haveI : Finite Ω := Ag.fin
     letI : Fintype S.dom := Fintype.ofFinite _
     letI : DecidableEq Ω := Classical.decEq _
     S.liftGroup (certGroup S (L.toGiantLabels.domMap L.con.onDomain) P₀.κ (dstr S z))) =
      itCertLift Ag.fin S Ag.πd P₀.κ z := by
  unfold itCertLift
  rw [cp_πd_eq hAg]
  congr 1
  haveI : Finite Ω := Ag.fin
  have h : ∀ (i j : DecidableEq S.dom), @certGroup Ω C S (Fintype.ofFinite _) i L.q
      (L.toGiantLabels.domMap L.con.onDomain) P₀.κ (dstr S z) =
      @certGroup Ω C S (Fintype.ofFinite _) j L.q
      (L.toGiantLabels.domMap L.con.onDomain) P₀.κ (dstr S z) := by
    intro i j; rw [Subsingleton.elim i j]
  exact h _ _


set_option maxHeartbeats 4000000 in
/-- **`AsCertOK`** for the function `cpCertE d f` at `fc`, from the hand-over relations: the
state of the certificate phase satisfies `CpHand`, and `CmHand` gives the state of the
comparison phase. The own cost is at most `cpCertX W₀`. -/
theorem asCertOK_of (I : Iface) (Pg : Program) (F : Funs) (H : AsHand) (X : ℕ → ℕ)
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
    (hX : ∀ W, cpCertX hst hpre hm W ≤ X W) : AsCertOK I Pg F H X fc := by
  intro Ω C k e c S sv' lv L hcall Cs st hstH
  have hh := hcp e c S L Cs st hstH
  have hcore := cp_cert_core hst hpre hm I Pg F hd hstp hat hjp hjpre hjm hh hcall.ih.below
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
      (ex : Exec P₀ Ag.certScript a),
      CpOut e S L.toGiantLabels (L.toGiantLabels.domMap L.con.onDomain) a out ∧
      (cst : ℝ) ≤ (A : ℝ) + ((st.wt + out.wt + 2 : ℕ) : ℝ) + I.execCost ex) ?_ ?_
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
    have hcl : ex.calls.length + 1 ≤
        (2 * cpNTW W₀ + 2) * (cpNW W₀ + 1) * (cpDc + 2) + 1 := by
      have : (2 * (L.q.choose P₀.κ - 1) + 2) * (n + 1) * (P₀.κ.factorial / 2 + 2) ≤
          (2 * cpNTW W₀ + 2) * (cpNW W₀ + 1) * (cpDc + 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) le_rfl
      omega
    have hN : (ex.calls.length + 1) * (runK * (cpPhaseB hst hpre hm k L.q P (L.q.choose P₀.κ) n
        (P₀.κ.factorial / 2) + 1)) ≤ A :=
      Nat.mul_le_mul hcl (Nat.mul_le_mul_left _ (Nat.add_le_add_right hph 1))
    have hR : ((ex.calls.length : ℝ) + 1) * (runK * (cpPhaseB hst hpre hm k L.q P
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

/-- An upper bound of `cpCertX` with no subtraction. -/
noncomputable def cpCertXU (hst : PointwiseStab) (hpre : Preimage) (hm : Membership) (W₀ : ℕ) :
    ℕ :=
  ((2 * cpNTW W₀ + 2) * (cpNW W₀ + 1) * (cpDc + 2) + 1) *
      (runK * (cpPhaseB hst hpre hm (cpNW W₀) (cpNW W₀) (cpSW W₀) (cpNTW W₀ + 1) (cpNW W₀) cpDc +
        1)) +
    2 * cpFzB hst hpre hm (cpWW W₀) + 1000 * (cpWW W₀ + 20)

theorem cpCertX_le (W₀ : ℕ) : cpCertX hst hpre hm W₀ ≤ cpCertXU hst hpre hm W₀ := by
  unfold cpCertX cpCertXU
  have := cpPhaseB_mono hst hpre hm (le_refl (cpNW W₀)) (le_refl (cpNW W₀)) (le_refl (cpSW W₀))
    (Nat.le_add_right (cpNTW W₀) 1) (le_refl (cpNW W₀)) (D := cpDc)
  have := Nat.mul_le_mul_left ((2 * cpNTW W₀ + 2) * (cpNW W₀ + 1) * (cpDc + 2) + 1)
    (Nat.mul_le_mul_left runK (Nat.add_le_add_right this 1))
  omega

/-- **The bound of the certificate phase is uniformly polynomial.** -/
theorem cpCertX_pbu : PBU fun _ W _ => cpCertX hst hpre hm W := by
  refine PBU.mono ?_ fun _ W _ => cpCertX_le hst hpre hm W
  unfold cpCertXU cpPhaseB
  simp only [Nat.add_sub_cancel]
  simp only [cpLoopC, cpBm, cpG, cardCost, ckFindCost, ckTestCost, Prim.boundSize, cpBw, cpFzB,
    cpFzStepB, cpFzOutB, cpWW, cpFzW, cpSW, cpOW, cpPW, cpNW, cpNTW, cpDc, runK, loopModK, imgCardK]
  norm_poly

end Phase

end GI.Impl
