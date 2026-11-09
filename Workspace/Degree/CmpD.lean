module

public import Workspace.Degree.RunD
public import Workspace.Degree.RoundMass
public import Workspace.Impl.AggCmpRun

@[expose] public section

/-!
# The comparison phase of the degree algorithm

The text of `cm_phase_spec`, `cm_setup_spec` and `cm_runOK` of the general algorithm, over the
runner `run_specCD`. The move function and all the hand-over relations are those of the general
algorithm.
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly GI.Impl GI.Lang GI.Endpoint GI.LocalGroups GI.LocalCertificates Equiv
  Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens PointwiseStab Preimage Membership)

variable {k : ℕ} {Ω C : Type}

/-- As `cm_out_eq` of the general algorithm. -/
theorem cm_out_eqD {S : State Ω C} {L : SuppliedLabels S} {Ag : Aggregation P₀ S L.toGiantLabels}
    {a : List Bool} (ex : DX Ag.compScript a) (sv : Val) (ps fx fy : GPairs k L.q) :
    cmOutV sv k ps fx fy Ag.tests.tuples a =
      itSt sv k L.q ps fx fy Ag.tests.tuples (itCr Ag.fin S Ag.πd P₀.κ) := by
  have ha := ex.exact.symm
  rw [st_compTable] at ha
  unfold cmOutV itSt stCv
  rw [ha]
  haveI := Ag.fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq Ω := Classical.decEq _
  have hcr : ∀ x y, stCr S Ag.πd P₀.κ (dstr S S.x) (dstr S S.y) x y =
      itCr Ag.fin S Ag.πd P₀.κ x y := by
    intro x y
    unfold itCr stCr
    congr 1
    convert rfl
  have hfun : stCr S Ag.πd P₀.κ (dstr S S.x) (dstr S S.y) = itCr Ag.fin S Ag.πd P₀.κ :=
    funext fun x => funext fun y => hcr x y
  rw [hfun]

/-- As `cm_out_itHand` of the general algorithm. -/
theorem cm_out_itHandD {e : Ω ≃ Fin k} {c : C → ℕ} {S : State Ω C} {L : SuppliedLabels S}
    {Cs : Set (Aggregation P₀ S L.toGiantLabels)} {Ag₀ : Aggregation P₀ S L.toGiantLabels}
    (hAg₀ : Ag₀ ∈ Cs) (hsub : Cs ⊆ asRounds L)
    (hcl : ∀ Ag ∈ asRounds L, Ag.certScript = Ag₀.certScript → Ag ∈ Cs)
    {sv : Val} {ps fx fy : GPairs k L.q} (hcan : Canon e c sv S)
    (hps : PairGens e L.toGiantLabels S.G ps)
    (hfx : PairGens e L.toGiantLabels (itCertLift Ag₀.fin S Ag₀.πd P₀.κ S.x) fx)
    (hfy : PairGens e L.toGiantLabels (itCertLift Ag₀.fin S Ag₀.πd P₀.κ S.y) fy)
    {O : TestTupleOrder L.q P₀.κ} {rec : List (Set (Perm S.dom) × Option (Perm S.dom))}
    {Ag : Aggregation P₀ S L.toGiantLabels} (hAg : Ag ∈ CmCands Cs Ag₀ O rec) {a : List Bool}
    (ex : DX Ag.compScript a) :
    ItHand e c S L {Ag' | Ag' ∈ Cs ∧ Ag'.compScript = Ag.compScript}
      (cmOutV sv k ps fx fy O.tuples a) := by
  obtain ⟨hCs, hcert, htests, -⟩ := hAg
  refine ⟨fun Ag' h => hsub h.1, Ag, ⟨hCs, rfl⟩, fun Ag' h' h1 h2 => ⟨hcl Ag' h' (h1.trans hcert),
    h2⟩, sv, ps, fx, fy, O, ?_, hcan, hps, ?_, ?_⟩
  · rw [← htests]
    exact cm_out_eqD ex sv ps fx fy
  · rwa [cm_certLift_eq (hsub hCs) (hsub hAg₀)]
  · rwa [cm_certLift_eq (hsub hCs) (hsub hAg₀)]

/-- As `cm_phase_spec` of the general algorithm. -/
theorem cm_phase_specD (J : CostT) (Pg : Program) (F : Funs) {S : State Ω C} {L : SuppliedLabels S} {d stp mv : ℕ}
    (hd : Pg.funs[d]? = some (runBody F d stp)) (hstp : Pg.funs[stp]? = some (cpLoopBody stp mv))
    {Out : List Bool → Val → Prop} {Rep' : ℕ → Val → Set (Script (List Bool)) → ℕ → Prop}
    {Bm Bw M₀ : ℕ}
    (hmv : ∀ m st Ss f, Rep' m st Ss f → FunAll Pg mv st (fun w c => c ≤ Bm ∧
      (Iface.StepPostC (measure P₀ .giant S) Out (fun st Ss f => ∃ m, Rep' m st Ss f) Ss f w ∨
        ∃ m' st' Ss', m' < m ∧ Ss' ⊆ Ss ∧ Rep' m' st' Ss' f ∧ w = .list [.nat 2, st'])))
    (hwt : ∀ m st Ss f, Rep' m st Ss f → st.wt ≤ Bw)
    (hM : ∀ m st Ss f, Rep' m st Ss f → m ≤ M₀)
    (ih : DIH Pg F J (RoundP P₀ S L.q) (measure P₀ .giant S))
    (Ds : Set (Aggregation P₀ S L.toGiantLabels)) {st₀ : Val} {m₀ f₀ : ℕ}
    (h₀ : Rep' m₀ st₀ ((fun Ag => Ag.compScript) '' Ds) f₀) :
    FunAll Pg d st₀ (fun out cost => ∃ Ag ∈ Ds, ∃ (a : List Bool)
      (ex : DX Ag.compScript a), Out a out ∧ ex.n ≤ f₀ ∧
      (cost : ℝ) ≤ ((ex.n : ℝ) + 1) *
        (runK * (((M₀ + 1) * cpLoopC Bm Bw + Bw : ℕ) + 1)) + ex.cost J) := by
  have hs := stepOKC_of_move (M := M₀) hstp hmv hwt hM
  refine (run_specCD hd hs ih f₀ st₀ _ ⟨m₀, h₀⟩ ?_).mono ?_
  · rintro _ ⟨Ag, -, rfl⟩
    exact Ag.compScript_roundP
  rintro out cost ⟨s, ⟨Ag, hAg, rfl⟩, a, ex, hout, -, hlen, hc⟩
  exact ⟨Ag, hAg, a, ex, hout, hlen, by exact_mod_cast hc⟩

section Setup

variable {k : ℕ} {Ω C : Type} [DecidableEq Ω] {e : Ω ≃ Fin k} {S : State Ω C} [Fintype S.dom]
  {L : SuppliedLabels S} {Cs : Set (Aggregation P₀ S L.toGiantLabels)}
  {Ag₀ : Aggregation P₀ S L.toGiantLabels}

set_option maxHeartbeats 4000000 in
/-- **The setup of the comparison phase.** -/
theorem cm_setup_specD (J : CostT) (Pg : Program) (F : Funs) (hst : PointwiseStab) (hpre : Preimage) (hm : Membership)
    {fm b d stp tb jm jp : ℕ} (hset : CmSetAt Pg F hst hm fm b d stp tb jm jp)
    {c : C → ℕ} (hci : Function.Injective c) {sv : Val} (hS : Canon e c sv S)
    (hgood : Good P₀ .giant S) (htr : S.Transitive)
    (hAg₀ : Ag₀ ∈ Cs) (hsub : Cs ⊆ asRounds L)
    (hcl : ∀ Ag ∈ asRounds L, Ag.certScript = Ag₀.certScript → Ag ∈ Cs)
    (ih : DIH Pg F J (RoundP P₀ S L.q) (measure P₀ .giant S)) (hq : 0 < L.q)
    {ps fx fy : GPairs k L.q} {logs : List (CmLog k L.q)}
    (hps : PairGens e L.toGiantLabels S.G ps) (hpl : ps.length ≤ (k + L.q) ^ 2)
    (hlogs : CmLogsOK e Ag₀.πd logs) {Bw W : ℕ}
    (hBw : cmBw (cmParV sv ps fx fy logs (cmTupOrder L.q P₀.κ hq).tuples
      (Fintype.card S.dom)).wt k L.q
      (2 * ((cmTupOrder L.q P₀.κ hq).tuples.length * (cmTupOrder L.q P₀.κ hq).tuples.length *
        (Fintype.card S.dom + 2) + 1))
      ((cmTupOrder L.q P₀.κ hq).tuples.length * (cmTupOrder L.q P₀.κ hq).tuples.length) ≤ Bw)
    (hW : 100 * Bw + 1000 ≤ W) (hW2 : 10 ^ 10 * (k + L.q + 1) ^ 12 ≤ W)
    (hY : 2 * L.q ^ P₀.κ + L.q + P₀.κ + 10 ≤ W) :
    FunAll Pg fm (cmSt sv k L.q ps fx fy logs) (fun w cost =>
      ∃ Ag ∈ CmCands Cs Ag₀ (cmTupOrder L.q P₀.κ hq) [], ∃ (a : List Bool)
        (ex : DX Ag.compScript a),
        w = cmOutV sv k ps fx fy (cmTupOrder L.q P₀.κ hq).tuples a ∧
        ex.n ≤ (cmTupOrder L.q P₀.κ hq).tuples.length *
          (cmTupOrder L.q P₀.κ hq).tuples.length * (Fintype.card S.dom + 2) + 1 ∧
        (cost : ℝ) ≤ ((cmSetC W + 3 * w.wt : ℕ) : ℝ) + ((ex.n : ℝ) + 1) *
          (runK * (((2 * ((cmTupOrder L.q P₀.κ hq).tuples.length *
            (cmTupOrder L.q P₀.κ hq).tuples.length * (Fintype.card S.dom + 2) + 1) + 1) *
            cpLoopC (cmMvCost hm W (cmStCost hst hpre hm W) (cmClCost hst hpre hm W)) Bw +
              Bw : ℕ) + 1)) + ex.cost J) := by
  set O := cmTupOrder L.q P₀.κ hq with hO
  set N := O.tuples.length with hN
  set n := Fintype.card S.dom with hn
  set M₀ := 2 * (N * N * (n + 2) + 1) with hM₀
  set par := cmParV sv ps fx fy logs O.tuples n with hpar
  obtain ⟨gv0, dv0, xv, yv, hv, rv, -, hdv0, -, -, -, -, hsv⟩ := hS.val
  have hπ : ∀ g : S.G, Ag₀.πd ⟨S.domHom g, g, rfl⟩ = L.toGiantLabels.π g := Ag₀.πd_spec
  -- the moves
  have hmv := cm_mv_spec (O := O) hm hAg₀ hsub hcl hset.mv hset.hjm hBw hW
    (cm_start_ok hst hpre hm hset.mv hset.st hset.hjp hset.hjm hπ hps hpl hBw hW hW2 _)
    (cm_call_ok hst hpre hm hset.st hset.cl hset.hjp hci hS hgood htr hAg₀ hsub hcl hπ hlogs hBw
      hW hW2 _)
  -- the start state
  have hwt0 : (Val.list [(CmSt.init (k := k)).val par, .list []]).wt ≤ Bw :=
    (cm_wt_state (q := L.q) (M₀ := M₀) (L := N * N) (σ := CmSt.init)
      (by simp [CmSt.init]) (by simp [CmSt.init]) (by simp [CmSt.init])
      (by simp [CmSt.init]) (by simp [CmSt.init]) cm_wt_nil_le).trans hBw
  have h₀ := cmRep_init (e := e) hAg₀ hsub O par hwt0
  have hph := cm_phase_specD J Pg F hset.run hset.loop (Rep' := fun m st Ss f =>
      CmRep e par Cs Ag₀ O Ag₀.πd Bw M₀ m st Ss f) hmv (fun _ _ _ _ h => cmRep_wt e h)
    (fun _ _ _ _ h => cmRep_le e h) ih (CmCands Cs Ag₀ O []) h₀
  -- the program
  refine FunAll.intro hset.entry ?_
  unfold cmSetF
  set svs : List Val := [.nat k, gv0, dv0, xv, yv, hv, rv, boolVal S.floor, .nat S.h, .nat S.N]
    with hsvs
  set vs : List Val := [sv, .list [.nat k, .nat L.q], .list (ps.map pairV), .list (fx.map pairV),
    .list (fy.map pairV), .list (logs.map cmLogV)] with hvs
  set TT := Val.list (O.tuples.map stTT) with hTT
  have hV : cmSt sv k L.q ps fx fy logs = .list vs := rfl
  rw [hV]
  -- weights
  have hparB : par.wt < Bw := (cm_st_sizes hBw).2
  have hVp : (Val.list vs).wt ≤ par.wt :=
    wt_list_mono (show vs <+: [sv, .list [.nat k, .nat L.q], .list (ps.map pairV),
      .list (fx.map pairV), .list (fy.map pairV), .list (logs.map cmLogV), TT, .nat n, .nat N]
      from ⟨_, rfl⟩)
  have hparL : par = .list (vs ++ [TT, .nat n, .nat N]) := rfl
  have hTp : TT.wt < par.wt := by
    rw [hparL]; exact cm_wt_lt_of_mem (List.mem_append_right _ (List.mem_cons_self ..))
  have hnp : (Val.nat n).wt < par.wt := by
    rw [hparL]
    exact cm_wt_lt_of_mem (List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hNp : (Val.nat N).wt < par.wt := by
    rw [hparL]
    exact cm_wt_lt_of_mem (List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  have hsvV : sv.wt < (Val.list vs).wt := by
    rw [hvs]; exact cm_wt_lt_of_mem (List.mem_cons_self ..)
  have hdvs : dv0.wt < sv.wt := by
    rw [hsv, hsvs]
    exact cm_wt_lt_of_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hnl := wt_nat_le n
  have hNl := wt_nat_le N
  have hk3 : k + 1 ≤ W := by
    have := Nat.le_self_pow (n := 12) (by omega) (k + L.q + 1)
    omega
  -- step 1: the tuples
  have hkq : (Val.list [.nat k, .nat L.q]).wt < (Val.list vs).wt := by
    rw [hvs]; exact cm_wt_lt_of_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have dT : Det Pg [.list vs] (.call tb (mk2 (.get (arg 1) (.nat 1)) (.nat P₀.κ))) TT
      (10 * (W + 20) + cmTK * (W + 1) ^ 5) := by
    refine (Det.call (Det.mk2 (Det.get' (Det.arg' (rest := []) (j := 1)
      (v := .list [.nat k, .nat L.q]) rfl) (Det.nat 1) (vs := [.nat k, .nat L.q]) rfl)
      (Det.nat P₀.κ)) (cmT_spec hset.tup hq hY)).mono ?_
    have := wt_list2_le (.nat L.q) (.nat P₀.κ)
    have := wt_nat_le L.q
    have := wt_nat_le P₀.κ
    have := cm_wt_lt_of_mem (vs := [Val.nat k, .nat L.q]) (v := .nat L.q) (by simp)
    have : TT.wt = (Val.list ((cmTupOrder L.q P₀.κ hq).tuples.map stTT)).wt := rfl
    have := wt_nat_le (L.q ^ P₀.κ)
    omega
  refine EvalAll.letE dT fun v1 c1 h1 => ?_
  obtain ⟨rfl, hc1⟩ := h1
  -- step 2: the size of the domain
  have hdi : dv0 = indVal e S.dom := hdv0
  have dS : Det Pg [.list vs, TT] (.get (arg 0) (.nat 2)) dv0 (5 * (W + 20)) := by
    refine (Det.get' (Det.arg' (rest := [TT]) (j := 0) (v := .list svs) (by rw [hvs, ← hsv]; rfl))
      (Det.nat 2) (vs := svs) rfl).mono ?_
    omega
  have dD := Det.length (Det.call dS (hdi ▸ domList_spec hset.cl.dom e S.dom))
  rw [List.length_map, cm_card_dom] at dD
  have hdw : (natList (domNat e S.dom)).wt ≤ 5 * (k + 1) ^ 2 := wt_domNat_le e S.dom
  have hdl := length_domNat_le e S.dom
  refine EvalAll.letE dD fun v2 c2 h2 => ?_
  obtain ⟨rfl, hc2⟩ := h2
  -- step 3: the start state and the runner
  set env := [Val.list vs, TT, Val.nat n] with henv
  have hTl : (O.tuples.map stTT).length = N := List.length_map _
  have dpar := cp_mkList' (P := Pg) (env := env) (W := W) (c := 3 * (W + 20))
    [(arg 0, sv), (arg 1, .list [.nat k, .nat L.q]), (arg 2, .list (ps.map pairV)),
      (arg 3, .list (fx.map pairV)), (arg 4, .list (fy.map pairV)),
      (arg 5, .list (logs.map cmLogV)), (.var 1, TT), (.var 2, .nat n), (.length (.var 1), .nat N)]
    (v := par) rfl (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      have hm : ∀ (j : ℕ) (x : Val), vs[j]? = some x → x.wt < (Val.list vs).wt :=
        fun _ _ hx => cm_wt_lt_of_mem (List.mem_of_getElem? hx)
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (Det.arg' (rest := [TT, .nat n]) (j := 0) rfl).mono (by have := hm 0 _ rfl; omega)
      · exact (Det.arg' (rest := [TT, .nat n]) (j := 1) rfl).mono (by have := hm 1 _ rfl; omega)
      · exact (Det.arg' (rest := [TT, .nat n]) (j := 2) rfl).mono (by have := hm 2 _ rfl; omega)
      · exact (Det.arg' (rest := [TT, .nat n]) (j := 3) rfl).mono (by have := hm 3 _ rfl; omega)
      · exact (Det.arg' (rest := [TT, .nat n]) (j := 4) rfl).mono (by have := hm 4 _ rfl; omega)
      · exact (Det.arg' (rest := [TT, .nat n]) (j := 5) rfl).mono (by have := hm 5 _ rfl; omega)
      · exact (Det.var' (v := TT) rfl).mono (by omega)
      · exact (Det.var' (v := .nat n) rfl).mono (by omega)
      · have := Det.length (Det.var' (P := Pg) (env := env) (i := 1)
          (v := .list (O.tuples.map stTT)) rfl)
        rw [hTl] at this
        refine this.mono ?_
        have := length_lt_wt_list (O.tuples.map stTT)
        rw [hTl] at this
        have : (Val.list (O.tuples.map stTT)).wt = TT.wt := rfl
        omega)
    (by omega)
  have hst0w : ((CmSt.init (k := k)).val par).wt < Bw :=
    lt_of_lt_of_le (cm_wt_lt_of_mem (by simp)) hwt0
  have dst := cp_mkList' (P := Pg) (env := env) (W := W) (c := 9 * (3 * (W + 20) + W + 1) + 5)
    [(Expr.mkList [arg 0, arg 1, arg 2, arg 3, arg 4, arg 5, .var 1, .var 2, .length (.var 1)],
      par), (.nat 0, .nat 0), (.nil, .list []), (.nil, .list []), (.nil, .list []),
      (.nat 0, .nat 0)]
    (v := (CmSt.init (k := k)).val par) rfl (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact dpar.mono (by simp only [List.length_cons, List.length_nil]; omega)
      · exact (Det.nat 0).mono (by omega)
      · exact Det.nil.mono (by omega)
      · exact Det.nil.mono (by omega)
      · exact Det.nil.mono (by omega)
      · exact (Det.nat 0).mono (by omega))
    (by omega)
  have dArg := Det.mk2 dst (Det.nil (P := Pg) (env := env))
  refine EvalAll.call_funAll dArg fun v3 c3 h3 => ?_
  obtain ⟨rfl, hc3⟩ := h3
  refine FunAll.mono hph ?_
  rintro out cost ⟨Ag, hAg, a, ex, hout, hlen, hc⟩
  refine ⟨Ag, hAg, a, ex, hout, hlen, ?_⟩
  have hsc : c1 + (c2 + (c3 + 0 + 0) + 0) + 3 ≤ cmSetC W := by
    have := wt_list2_le ((CmSt.init (k := k)).val par) (.list [])
    have : (Val.list []).wt ≤ 4 := by have := wt_list_le ([] : List Val); simpa using this
    simp only [List.length_cons, List.length_nil] at hc3
    have h3 : domListK * (k + 1) ^ 3 ≤ domListK * (W + 1) ^ 3 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
    have : 5 * (k + 1) ^ 2 ≤ 5 * (W + 1) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
    have : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have : (Val.list (List.map Val.nat (domNat e S.dom))).wt = (natList (domNat e S.dom)).wt :=
      rfl
    have := cm_card_dom e S
    have hg : (Val.list (List.map Val.nat (domNat e S.dom))).wt ≤ 5 * (k + 1) ^ 2 := hdw
    have : (k + 1) ^ 2 ≤ (k + L.q + 1) ^ 12 :=
      (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
    unfold cmSetC
    omega
  have h1 : c1 + (c2 + (c3 + cost + out.wt + 1) + out.wt + 1) + out.wt + 1 ≤
      cmSetC W + 3 * out.wt + cost := by omega
  have h2 : ((c1 + (c2 + (c3 + cost + out.wt + 1) + out.wt + 1) + out.wt + 1 : ℕ) : ℝ) ≤
      ((cmSetC W + 3 * out.wt : ℕ) : ℝ) + (cost : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).2 h1
    push_cast at this ⊢
    linarith
  linarith

end Setup

/-- As `CmRunOK` of the general algorithm. -/
def CmRunD (I : Iface) (J : CostT) (Pg : Program) (F₀ F : Funs) (X : ℕ → ℕ) (fm : ℕ) : Prop :=
  ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C) (sv' lv : Val)
    (L : SuppliedLabels S), AsCall I Pg F₀ e c S sv' lv L →
    DIH Pg F J (RoundP P₀ S L.q) (measure P₀ .giant S) →
    ∀ (Cs : Set (Aggregation P₀ S L.toGiantLabels)) (Ag₀ : Aggregation P₀ S L.toGiantLabels),
    Ag₀ ∈ Cs → Cs ⊆ asRounds L → (∀ Ag ∈ asRounds L, Ag.certScript = Ag₀.certScript → Ag ∈ Cs) →
    ∀ (sv : Val) (ps fx fy : GPairs k L.q) (logs : List (CmLog k L.q)),
    Canon e c sv S → PairGens e L.toGiantLabels S.G ps →
    PairGens e L.toGiantLabels (itCertLift Ag₀.fin S Ag₀.πd P₀.κ S.x) fx →
    PairGens e L.toGiantLabels (itCertLift Ag₀.fin S Ag₀.πd P₀.κ S.y) fy →
    ps.length ≤ (k + L.q) ^ 2 → fx.length ≤ (k + L.q) ^ 2 → fy.length ≤ (k + L.q) ^ 2 →
    (haveI := Ag₀.fin
     letI : Fintype S.dom := Fintype.ofFinite _
     letI : DecidableEq Ω := Classical.decEq _
     CmLogsOK e Ag₀.πd logs) →
    FunAll Pg fm (cmSt sv k L.q ps fx fy logs) (fun w cost => ∃ O : TestTupleOrder L.q P₀.κ,
      ∃ Ag ∈ CmCands Cs Ag₀ O [], ∃ (a : List Bool) (ex : DX Ag.compScript a),
        w = cmOutV sv k ps fx fy O.tuples a ∧
        (cost : ℝ) ≤ X (I.inW .giant S) + ex.cost J ∧ w.wt ≤ X (I.inW .giant S))

/-- The result list of a run has one entry for each pair of tuples. -/
theorem cm_res_lengthD {Ω C : Type} {S : State Ω C} {L : SuppliedLabels S}
    {Ag : Aggregation P₀ S L.toGiantLabels} {a : List Bool} (ex : DX Ag.compScript a) :
    a.length = Ag.tests.tuples.length * Ag.tests.tuples.length := by
  have ha := ex.exact.symm
  rw [st_compTable] at ha
  rw [ha, List.length_flatMap]
  simp only [List.length_map]
  rw [List.map_const', List.sum_replicate, smul_eq_mul]

set_option maxHeartbeats 4000000 in
/-- **The comparison program meets `CmRunOK`** with the polynomial bound `cmRunX`. -/
theorem cm_runD (I : Iface) (J : CostT) (Pg : Program) (F₀ F : Funs) (hst : PointwiseStab) (hpre : Preimage) (hm : Membership)
    {fm b d stp tb jm jp : ℕ} (hset : CmSetAt Pg F hst hm fm b d stp tb jm jp) :
    CmRunD I J Pg F₀ F (cmRunX hst hpre hm) fm := by
  intro Ω C k e c S sv' lv L hcall hih Cs Ag₀ hAg₀ hsub hcl sv ps fx fy logs hcan hps hfx hfy hpl
    hfxl hfyl hlogs
  haveI := Ag₀.fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq Ω := Classical.decEq _
  -- the input sizes
  set W₀ := I.inW .giant S with hW₀
  set K := 2 * W₀ + 3 with hK
  have hsvW : sv.wt ≤ W₀ := by
    have := Canon.wt_le hcan
    simp only [hW₀, Iface.inW, Iface.card_eq e]
    omega
  have hk : k ≤ sv.wt := StateVal.k_le_wt hcan.stateVal
  have hqk := GiantLabels.q_le e L.toGiantLabels
  have hq0 : 0 < L.q := by have := hcall.q₀; omega
  have hκ : P₀.κ = 64 := rfl
  have hqb : P₀.κ ≤ L.q := by
    have := hcall.q₀
    have : P₀.q₀ = 2064 := rfl
    omega
  have hkq : k + L.q + 1 ≤ K := by omega
  have hq64 : L.q ^ P₀.κ ≤ K ^ 64 := by rw [hκ]; exact Nat.pow_le_pow_left (by omega) 64
  set O := cmTupOrder L.q P₀.κ hq0 with hO
  set N := O.tuples.length with hN
  have hNb : N ≤ cmNb K := by
    have : N ≤ 2 * L.q ^ P₀.κ := by
      have := List.length_filterMap_le (cmTupOf (κ := P₀.κ) hq0) (List.range (2 * L.q ^ P₀.κ))
      rw [List.length_range] at this
      exact this
    unfold cmNb; omega
  set n := Fintype.card S.dom with hn
  have hnk : n ≤ k := by rw [hn, ← cm_card_dom e S]; exact length_domNat_le e S.dom
  -- the logs
  have hlogs' := hlogs
  obtain ⟨⟨OS, hOS⟩, hl⟩ := hlogs'
  have hll : logs.length ≤ K ^ 64 := by
    have h1 : logs.length = OS.sets.length := by rw [← hOS, List.length_map]
    rw [h1, TestSetOrder.length_eq]
    exact (Nat.choose_le_pow _ _).trans hq64
  have hstg : ∀ (T : Finset (Fin L.q)) (z : Ω → C) (ls : List (CmStage k L.q)),
      CmStgs e Ag₀.πd T z ls → CpLgLen ls := by
    intro T z ls ⟨hlen, hst'⟩
    refine ⟨by omega, fun dd hd => ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hd
    obtain ⟨-, h1, incl, hnd, -, h2⟩ := hst' j hj
    refine ⟨h1, ?_⟩
    rw [h2, List.length_map]
    exact hnd.length_le_card.trans hnk
  have hlg : ∀ l ∈ logs, CpLgLen l.lx ∧ CpLgLen l.ly := fun l hl' =>
    ⟨hstg _ _ _ (hl l hl').1, hstg _ _ _ (hl l hl').2⟩
  -- the sizes of the phase
  have hP : (cmParV sv ps fx fy logs O.tuples n).wt ≤ cmPb K :=
    cm_wt_par (by omega) hkq hpl hfxl hfyl hll hlg hNb (by omega) (by omega)
  have hBw : cmBw (cmParV sv ps fx fy logs O.tuples n).wt k L.q (2 * (N * N * (n + 2) + 1))
      (N * N) ≤ cmBwU K := by
    have hNN : N * N ≤ cmNb K * cmNb K := Nat.mul_le_mul hNb hNb
    have hM : 2 * (N * N * (n + 2) + 1) ≤ cmMb K := by
      unfold cmMb
      have := Nat.mul_le_mul hNN (show n + 2 ≤ K + 2 by omega)
      omega
    have hA : ansW k ≤ ansW K := by
      unfold ansW groupW
      have h1 : (k + 1) ^ 2 ≤ (K + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have h2 : ((k ^ 2 + 2) * (k + 1)) ^ 2 ≤ ((K ^ 2 + 2) * (K + 1)) ^ 2 :=
        Nat.pow_le_pow_left (Nat.mul_le_mul (by
          have := Nat.pow_le_pow_left (show k ≤ K by omega) 2; omega) (by omega)) 2
      omega
    have h6 : (k + L.q + 1) ^ 6 ≤ (K + K + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
    have h3 : 10 ^ 4 * (2 * (N * N * (n + 2) + 1) + N * N + 1) * (k + L.q + 1) ^ 6 ≤
        10 ^ 4 * (cmMb K + cmNb K * cmNb K + 1) * (K + K + 1) ^ 6 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) h6
    unfold cmBwU cmBw
    omega
  set W := cmWU K with hWd
  have hW : 100 * cmBwU K + 1000 ≤ W := by unfold cmWU at hWd; omega
  have hW2 : 10 ^ 10 * (k + L.q + 1) ^ 12 ≤ W := by
    have : (k + L.q + 1) ^ 12 ≤ (2 * K + 1) ^ 12 := Nat.pow_le_pow_left (by omega) 12
    unfold cmWU at hWd; omega
  have hY : 2 * L.q ^ P₀.κ + L.q + P₀.κ + 10 ≤ W := by unfold cmWU at hWd; omega
  -- the run
  have htr : S.Transitive := hcall.good.2.2.1
  refine (cm_setup_specD J Pg F hst hpre hm hset hcall.inj hcan hcall.good htr hAg₀ hsub hcl
    hih hq0 hps hpl hlogs hBw hW hW2 hY).mono ?_
  rintro w cost ⟨Ag, hAg, a, ex, rfl, hcalls, hc⟩
  have ha : a.length = N * N := by
    rw [cm_res_lengthD ex, hAg.2.2.1]
  have hwt := cm_wt_out (k := k) (sv := sv) (ps := ps) (fx := fx) (fy := fy) hP hNb ha
  have hcalls' : ex.n ≤ N * N * (n + 2) + 1 := hcalls
  have eO : (cmOutV sv k ps fx fy O.tuples a).wt =
      (cmOutV sv k ps fx fy (cmTupOrder L.q P₀.κ hq0).tuples a).wt := rfl
  refine ⟨O, Ag, hAg, a, ex, rfl, ?_, ?_⟩
  · -- the cost
    set R := runK * (((2 * (N * N * (n + 2) + 1) + 1) * cpLoopC (cmMvCost hm W
      (cmStCost hst hpre hm W) (cmClCost hst hpre hm W)) (cmBwU K) + cmBwU K) + 1) with hR
    set R' := runK * (((cmMb K + 1) * cpLoopC (cmMvCost hm W (cmStCost hst hpre hm W)
      (cmClCost hst hpre hm W)) (cmBwU K) + cmBwU K) + 1) with hR'
    have hRR : R ≤ R' := by
      have hM : 2 * (N * N * (n + 2) + 1) ≤ cmMb K := by
        unfold cmMb
        have := Nat.mul_le_mul (Nat.mul_le_mul hNb hNb) (show n + 2 ≤ K + 2 by omega)
        omega
      rw [hR, hR']
      gcongr
    have hcl' : ex.n + 1 ≤ cmNb K * cmNb K * (K + 2) + 2 := by
      have := Nat.mul_le_mul (Nat.mul_le_mul hNb hNb) (show n + 2 ≤ K + 2 by omega)
      omega
    have hnat : cmSetC W + 3 * (cmOutV sv k ps fx fy O.tuples a).wt +
        (ex.n + 1) * R ≤ cmRunX hst hpre hm W₀ := by
      have := Nat.mul_le_mul hcl' hRR
      unfold cmRunX
      rw [← hK, ← hWd, ← hR']
      omega
    have hnat' : ((cmSetC W + 3 * (cmOutV sv k ps fx fy O.tuples a).wt : ℕ) : ℝ) +
        ((ex.n : ℝ) + 1) * (R : ℝ) ≤ (cmRunX hst hpre hm W₀ : ℝ) := by
      have := (Nat.cast_le (α := ℝ)).2 hnat
      push_cast at this ⊢
      linarith
    rw [hR] at hnat'
    push_cast at hc hnat' ⊢
    linarith
  · -- the weight
    unfold cmRunX
    rw [← hK]
    omega

/-- **The comparison phase** at `fm`, as `AsCompOK` of the general algorithm. -/
def AsCompD (I : Iface) (J : CostT) (Pg : Program) (F₀ F : Funs) (H : AsHand) (X : ℕ → ℕ) (fm : ℕ) :
    Prop :=
  ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C) (sv lv : Val)
    (L : SuppliedLabels S), AsCall I Pg F₀ e c S sv lv L →
    DIH Pg F J (RoundP P₀ S L.q) (measure P₀ .giant S) →
    ∀ (Cs : Set (Aggregation P₀ S L.toGiantLabels)) (st : Val), H.comp e c S L Cs st →
    FunAll Pg fm st (fun w cost => ∃ Ag ∈ Cs, ∃ (a : List Bool) (ex : DX Ag.compScript a),
      H.items e c S L {Ag' | Ag' ∈ Cs ∧ Ag'.compScript = Ag.compScript} w ∧
      (cost : ℝ) ≤ X (I.inW .giant S) + ex.cost J ∧ w.wt ≤ X (I.inW .giant S))

/-- **`AsCompD` for the comparison program.** -/
theorem cm_asCompD (I : Iface) (J : CostT) (Pg : Program) (F₀ F : Funs) (hst : PointwiseStab)
    (hpre : Preimage) (hm : Membership) (H : AsHand)
    {fm b d stp tb jm jp : ℕ} (hset : CmSetAt Pg F hst hm fm b d stp tb jm jp)
    (hc : ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C)
      (L : SuppliedLabels S) Cs st, H.comp e c S L Cs st → CmHand e c S L Cs st)
    (hi : ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C)
      (L : SuppliedLabels S) Cs st, ItHand e c S L Cs st → H.items e c S L Cs st) :
    AsCompD I J Pg F₀ F H (cmRunX hst hpre hm) fm := by
  intro Ω C k e c S sv' lv L hcall hih Cs st hst'
  obtain ⟨hsub, Ag₀, hAg₀, hcl, sv, ps, fx, fy, logs, rfl, hcan, hps, hfx, hfy, hl1, hl2, hl3,
    hlogs⟩ := hc e c S L Cs st hst'
  refine (cm_runD I J Pg F₀ F hst hpre hm hset e c S sv' lv L hcall hih Cs Ag₀ hAg₀ hsub hcl sv ps
    fx fy logs hcan hps hfx hfy hl1 hl2 hl3 hlogs).mono ?_
  rintro w cost ⟨O, Ag, hAg, a, ex, rfl, hcost, hw⟩
  exact ⟨Ag, hAg.1, a, ex, hi e c S L _ _ (cm_out_itHandD hAg₀ hsub hcl hcan hps hfx hfy hAg ex),
    hcost, hw⟩

end GI.Degree
