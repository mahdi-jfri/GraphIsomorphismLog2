module

public import Workspace.Impl.AggCmpClOK
public import Workspace.Impl.AggCmpStart
public import Workspace.Impl.AggCmpPhase
public import Workspace.Impl.AggCmpTupProg

@[expose] public section

/-!
# The setup of the comparison phase

The function at `fm` gets the hand-over state `cmSt sv k q ps fx fy logs` of the certificate
phase. It does three things.

1. It lists the test tuples in the order `cmTupOrder q κ` (`cmT_spec`).
2. It counts the domain: the length of the list of the positions of the domain, read from the
   domain indicator of `sv` (`domList_spec`, `card_dom_eq`).
3. It builds the parent data `cmParV` and the start state `CmSt.init` (`cmRep_init`), and calls
   the runner once (`cm_phase_spec`). The moves are those of `cm_mv_spec`, with the start of a
   pair by `cm_start_ok` and the call of a stage by `cm_call_ok`.

`cm_setup_spec` gives the output of the runner: `cmOutV … a` for a run with result `a` of the
comparison script of a candidate, at a cost given by the sizes `W`, `Bw` and `M₀` of the
phase. Turning this cost into a polynomial in the input size (`CmRunOK`) is left open.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups GI.LocalCertificates Equiv
  Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens PointwiseStab Preimage Membership)

/-- **The setup**, on `cmSt sv k q ps fx fy logs`, with the tuple program at `tb` and the runner
at `d`. -/
noncomputable def cmSetF (b d tb : ℕ) : Expr :=
  .letE (.call tb (mk2 (.get (arg 1) (.nat 1)) (.nat P₀.κ)))
  (.letE (.length (.call (cmDomB b) (.get (arg 0) (.nat 2))))
    (.call d (mk2 (Expr.mkList [Expr.mkList [arg 0, arg 1, arg 2, arg 3, arg 4, arg 5, .var 1,
      .var 2, .length (.var 1)], .nat 0, .nil, .nil, .nil, .nat 0]) .nil)))

/-- **Where the comparison program sits**: the setup at `fm`, the tuple program at `tb`, the
runner at `d` with its loop at `stp`, the moves at `b`, and the primitives. -/
structure CmSetAt (Pg : Program) (F : Funs) (hst : PointwiseStab) (hm : Membership)
    (fm b d stp tb jm jp : ℕ) : Prop where
  entry : Pg.funs[fm]? = some (cmSetF b d tb)
  tup : Pg.HasAt tb (cmTFuns tb)
  run : Pg.funs[d]? = some (runBody F d stp)
  loop : Pg.funs[stp]? = some (cpLoopBody stp b)
  mv : CmMvAt0 Pg b jm
  st : CmStAt Pg b jp
  cl : CmClAt Pg b
  hjm : Pg.prims[jm]? = some (membershipPrim hm)
  hjp : Pg.prims[jp]? = some (pointwiseStabPrim hst)

/-- The cost of the setup before the runner. -/
def cmSetC (W : ℕ) : ℕ := cmTK * (W + 1) ^ 5 + domListK * (W + 1) ^ 3 + 1000 * (W + 20)

section Setup

variable (I : Iface) (Pg : Program) (F : Funs)
  {k : ℕ} {Ω C : Type} [DecidableEq Ω] {e : Ω ≃ Fin k} {S : State Ω C} [Fintype S.dom]
  {L : SuppliedLabels S} {Cs : Set (Aggregation P₀ S L.toGiantLabels)}
  {Ag₀ : Aggregation P₀ S L.toGiantLabels}

theorem cm_card_dom (e : Ω ≃ Fin k) (S : State Ω C) [Fintype S.dom] :
    (domNat e S.dom).length = Fintype.card S.dom := by
  rw [length_domNat, ← card_dom_eq, Nat.card_eq_fintype_card]

set_option maxHeartbeats 4000000 in
/-- **The setup of the comparison phase.** -/
theorem cm_setup_spec (hst : PointwiseStab) (hpre : Preimage) (hm : Membership)
    {fm b d stp tb jm jp : ℕ} (hset : CmSetAt Pg F hst hm fm b d stp tb jm jp)
    {c : C → ℕ} (hci : Function.Injective c) {sv : Val} (hS : Canon e c sv S)
    (hgood : Good P₀ .giant S) (htr : S.Transitive)
    (hAg₀ : Ag₀ ∈ Cs) (hsub : Cs ⊆ asRounds L)
    (hcl : ∀ Ag ∈ asRounds L, Ag.certScript = Ag₀.certScript → Ag ∈ Cs)
    (ih : I.IHBelow Pg F (measure P₀ .giant S)) (hq : 0 < L.q)
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
        (ex : Exec P₀ Ag.compScript a),
        w = cmOutV sv k ps fx fy (cmTupOrder L.q P₀.κ hq).tuples a ∧
        ex.calls.length ≤ (cmTupOrder L.q P₀.κ hq).tuples.length *
          (cmTupOrder L.q P₀.κ hq).tuples.length * (Fintype.card S.dom + 2) + 1 ∧
        (cost : ℝ) ≤ ((cmSetC W + 3 * w.wt : ℕ) : ℝ) + ((ex.calls.length : ℝ) + 1) *
          (runK * (((2 * ((cmTupOrder L.q P₀.κ hq).tuples.length *
            (cmTupOrder L.q P₀.κ hq).tuples.length * (Fintype.card S.dom + 2) + 1) + 1) *
            cpLoopC (cmMvCost hm W (cmStCost hst hpre hm W) (cmClCost hst hpre hm W)) Bw +
              Bw : ℕ) + 1)) + I.execCost ex) := by
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
  have hph := cm_phase_spec I Pg F hset.run hset.loop (Rep' := fun m st Ss f =>
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

end GI.Impl
