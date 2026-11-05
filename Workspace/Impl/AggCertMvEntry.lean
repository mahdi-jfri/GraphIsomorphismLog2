module

public import Workspace.Impl.AggCertMvStart

@[expose] public section

/-!
# The move program: the entry, and the condition of `cert_phase_spec`

`cpMvF` (at `b`) looks at `inner` (entry 10 of `kst`). It is empty at the start of a round,
and then the move is `cpRoundF` (`cp_round_spec`, with the first window call `cp_start_spec`).
Inside a round it is not empty, and the move is `cpWinF` (`cp_win_spec`).

`cp_mv_spec` says that every move from a program state standing for some candidates
(`CpRep`) costs at most `cpBm W` and returns what a move must return (`CpMvPost`). This is the
condition `hmv` of `cert_phase_spec` (`cp_hmv`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens PointwiseStab Preimage Membership)

/-- **The cost bound of one move**, for values of weight at most `W`. -/
noncomputable def cpBm (hst : PointwiseStab) (hpre : Preimage) (hm : Membership) (W : ℕ) : ℕ :=
  30 * cpG hst hpre hm W + 20000 * (W + 20)

/-- **The number `D` of representatives of one round**: a test set of size `κ ≥ 5` has an
alternating group of order `κ! / 2` (the field `hD` of `CpCtx`). -/
theorem cp_card_alt {q : ℕ} (T : Finset (Fin q)) (hT : T.card = P₀.κ) :
    Nat.card (alternatingGroup T) = P₀.κ.factorial / 2 := by
  have h5 : 5 ≤ T.card := hT ▸ P₀_terminating.κ_five
  have : Nontrivial T := Fintype.one_lt_card_iff_nontrivial.1 (by rw [Fintype.card_coe]; omega)
  have h := two_mul_nat_card_alternatingGroup (α := T)
  rw [Nat.card_perm, Nat.card_eq_fintype_card (α := T), Fintype.card_coe, hT] at h
  omega

section Entry

variable {k : ℕ} {Ω C : Type} [Finite Ω] [DecidableEq Ω] {e : Ω ≃ Fin k} {c : C → ℕ}
  {S : State Ω C} [Fintype S.dom] {L : GiantLabels S}
  {πd : S.domGroup →* alternatingGroup (Fin L.q)}
  (hst : PointwiseStab) (hpre : Preimage) (hm : Membership)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- **One move.** From a program state that stands for some candidates, the move program
returns what a move must return, at cost at most `cpBm W`. -/
theorem cp_mv_spec {Pg : Program} {b jp jpre jm : ℕ} (hat : CpMvAt Pg b jp jpre jm)
    (hjp : Pg.prims[jp]? = some (pointwiseStabPrim hst))
    (hjpre : Pg.prims[jpre]? = some (preimagePrim hpre))
    (hjm : Pg.prims[jm]? = some (membershipPrim hm))
    {sv : Val} {gp : GPairs k L.q} {osA : List (Fin (k + L.q))} {D : ℕ}
    (ctx : CpCtx e c S L πd sv gp osA D) {NT M₀ Bw W : ℕ}
    (hBw : cpBw k L.q (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA)).wt NT M₀ D
      ≤ Bw) (hW : 10 ^ 4 * (Bw + 2) ^ 2 ≤ W)
    {m : ℕ} {st : Val} {Ss : Set (Script (List (StagePair S)))} {f : ℕ}
    (h : CpRep e πd (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA)) D Bw M₀ NT
      m st Ss f) :
    CpFB Pg b st W (cpBm hst hpre hm W)
      (CpMvPost e S L πd (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA)) D Bw M₀
        NT m Ss f) := by
  set par := cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA) with hpar
  obtain ⟨hW1, -, -, -, -⟩ := cp_W_facts hBw hW
  obtain ⟨pos, σ, rec, hm', hmf, hwt, hM, hNT, hlen, rfl, hpos⟩ := h
  refine CpFB.intro hat.mv ?_
  unfold cpMvF
  match pos, hpos with
  | .fin _, hpos => exact hpos.elim
  | .round acc T Ts s t, ⟨hT, hTs, hs, ht, hR, u, hst'⟩ =>
    subst hTs hs ht hst'
    set ks := σ.vals par (.list []) with hks
    have hsv : σ.val par (.list []) = .list ks := rfl
    have hwW : (Val.list [.list ks, u]).wt ≤ W := by rw [← hsv]; omega
    have h0 : ∀ rest : List Val, (Val.list [.list ks, u] :: rest)[0]? =
        some (.list [.list ks, u]) := fun _ => rfl
    have dl := Det.length (cp_rdK (P := Pg) (h0 []) hwW (j := 10) (v := .list []) rfl (by omega))
    simp only [List.length_nil] at dl
    refine (CpEB.ite dl (Ct := 0) (Ce := 19 * cpG hst hpre hm W + 9200 * (W + 20))
      (fun hne => absurd rfl hne) fun _ => ?_).mono (by unfold cpBm; omega) fun _ h => h
    rw [hsv] at hwt
    refine (CpEB.call (Cb := 19 * cpG hst hpre hm W + 9100 * (W + 20)) (CpEB.det (Det.rv (P := Pg) (env := [.list [.list ks, u]]) (i := 0) rfl hwW)
      le_rfl hwW (Q := fun v => v = .list [.list ks, u]) rfl) fun v hv _ => ?_).mono (by omega) fun _ h => h
    subst hv
    have hr := cp_round_spec hst hpre hm hat hjp hjpre ctx hBw hW hR hT hm' hmf hM hNT hlen
      (Cs := 16 * cpG hst hpre hm W + 7000 * (W + 20)) (u := u) (by rw [hsv]; exact hwt)
      fun incl hnd hinc hne ht' => by
        subst hT
        exact cp_start_spec hst hpre hm hat hjp hjm ctx hBw hW hR rfl hm' hmf hM hNT hlen hnd
          hinc hne ht'
    rw [hsv] at hr
    exact hr.mono (by omega) fun _ h => h
  | .win acc T Ts s t τs acc', ⟨hT, hTs, hs, ht, inner, u, hst', hWI, hin⟩ =>
    subst hTs hs ht hst'
    have hWI0 := hWI
    obtain ⟨-, -, -, dn, a, as, hs, dv, incl, rfl, -⟩ := hWI0
    set inner := cpInnerV as (stageGens dn) hs dv (incl.map (domPos e L.q)) a with hinner
    set ks := σ.vals par inner with hks
    have hsv : σ.val par inner = .list ks := rfl
    have hwW : (Val.list [.list ks, u]).wt ≤ W := by rw [← hsv]; omega
    have h0 : ∀ rest : List Val, (Val.list [.list ks, u] :: rest)[0]? =
        some (.list [.list ks, u]) := fun _ => rfl
    have dl := Det.length (cp_rdK (P := Pg) (h0 []) hwW (j := 10)
      (v := .list [.list (as.map encPerm), .list ((stageGens dn).map encPerm), encGroup hs, dv,
        encPts (incl.map (domPos e L.q)), encPerm a]) rfl (by omega))
    simp only [List.length_cons, List.length_nil] at dl
    refine (CpEB.ite dl (Ct := 7 * cpG hst hpre hm W + 6400 * (W + 20)) (Ce := 0)
      (fun _ => ?_) fun he => absurd he (by omega)).mono (by unfold cpBm; omega)
      fun _ h => h
    refine (CpEB.call (Cb := 6 * cpG hst hpre hm W + 6200 * (W + 20)) (CpEB.det (Det.rv (P := Pg) (env := [.list [.list ks, u]]) (i := 0) rfl hwW)
      le_rfl hwW (Q := fun v => v = .list [.list ks, u]) rfl) fun v hv _ => ?_).mono (by omega) fun _ h => h
    subst hv
    have hr := cp_win_spec hst hpre hm hat hjpre ctx hBw hW hm' hmf hM hNT hlen hT hWI hin hwt
    rw [hsv] at hr
    exact hr

/-- **The condition `hmv` of `cert_phase_spec`**, met by the move program. -/
theorem cp_hmv {Pg : Program} {b jp jpre jm : ℕ} (hat : CpMvAt Pg b jp jpre jm)
    (hjp : Pg.prims[jp]? = some (pointwiseStabPrim hst))
    (hjpre : Pg.prims[jpre]? = some (preimagePrim hpre))
    (hjm : Pg.prims[jm]? = some (membershipPrim hm))
    {sv : Val} {gp : GPairs k L.q} {osA : List (Fin (k + L.q))} {D : ℕ}
    (ctx : CpCtx e c S L πd sv gp osA D) {NT M₀ Bw W : ℕ}
    (hBw : cpBw k L.q (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA)).wt NT M₀ D
      ≤ Bw) (hW : 10 ^ 4 * (Bw + 2) ^ 2 ≤ W) :
    ∀ m st Ss f, CpRep e πd (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA)) D Bw
      M₀ NT m st Ss f → FunAll Pg b st (fun w cost =>
      cost ≤ cpBm hst hpre hm W ∧ (Iface.StepPostC (measure P₀ .giant S) (CpOut e S L πd)
          (fun st Ss f => ∃ m, CpRep e πd (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp)
            (encPts osA)) D Bw M₀ NT m st Ss f) Ss f w ∨
        ∃ m' st' Ss', m' < m ∧ Ss' ⊆ Ss ∧ CpRep e πd (cpParV k L.q (Fintype.card S.dom) D sv
          (gpV gp) (encPts osA)) D Bw M₀ NT m' st' Ss' f ∧ w = .list [.nat 2, st'])) :=
  fun _ _ _ _ h => FunAll.mono (cp_mv_spec hst hpre hm hat hjp hjpre hjm ctx hBw hW h)
    fun _ _ h => ⟨h.2.2, h.1⟩

/-- **The certificate phase as a program.** The runner at `d`, with the loop of moves at `stp`
and the move program at `b`, on the initial program state of the test sets `O.sets = T :: Ts`,
returns the graph forms of the final stages (`CpOut`) of a run of `certPhase … R …` for some
coset representatives `R`, with at most `f₀ = (2 |Ts| + 2)(n + 1)(D + 2)` calls, at cost at most
`(calls + 1) runK ((f₀ + 1) cpLoopC (cpBm W) Bw + Bw + 1)` plus the cost of the calls. -/
theorem cp_phase_spec (I : Iface) (Pg : Program) (F : Funs) {d stp b jp jpre jm : ℕ}
    (hd : Pg.funs[d]? = some (runBody F d stp)) (hstp : Pg.funs[stp]? = some (cpLoopBody stp b))
    (hat : CpMvAt Pg b jp jpre jm)
    (hjp : Pg.prims[jp]? = some (pointwiseStabPrim hst))
    (hjpre : Pg.prims[jpre]? = some (preimagePrim hpre))
    (hjm : Pg.prims[jm]? = some (membershipPrim hm))
    {sv : Val} {gp : GPairs k L.q} {osA : List (Fin (k + L.q))} {D : ℕ}
    (ctx : CpCtx e c S L πd sv gp osA D) (ih : I.IHBelow Pg F (measure P₀ .giant S))
    (O : TestSetOrder L.q P₀.κ) {T : Finset (Fin L.q)} {Ts : List (Finset (Fin L.q))}
    (hO : O.sets = T :: Ts) {p0 : GPairs k L.q}
    (hp0 : PairGens e L (S.liftGroup (Pgrp S.domGroup πd T)) p0)
    (hp0l : p0.length ≤ (k + L.q) ^ 2) {Bw W : ℕ}
    (hBw : cpBw k L.q (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA)).wt
      (Ts.length + 1) ((2 * Ts.length + 2) * (Fintype.card S.dom + 1) * (D + 2)) D ≤ Bw)
    (hW : 10 ^ 4 * (Bw + 2) ^ 2 ≤ W) :
    FunAll Pg d (.list [(CpSt.init T Ts p0 osA).val
        (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA)) (.list []), .nat 0])
      (fun out cost => ∃ R : CosetRepFn S.dom, ∃ (a : List (StagePair S))
        (ex : Exec P₀ (certPhase S πd P₀.κ O R (dstr S S.x) (dstr S S.y)) a), CpOut e S L πd a out ∧
        ex.calls.length ≤ (2 * Ts.length + 2) * (Fintype.card S.dom + 1) * (D + 2) ∧
        (cost : ℝ) ≤ ((ex.calls.length : ℝ) + 1) *
          (runK * ((((2 * Ts.length + 2) * (Fintype.card S.dom + 1) * (D + 2) + 1) *
            cpLoopC (cpBm hst hpre hm W) Bw + Bw : ℕ) + 1)) + I.execCost ex) := by
  have hcard : ∀ T' ∈ O.sets, T'.card = P₀.κ := fun T' h => (O.mem T').1 h
  have hA := ctx.hosA
  have hlen : CpLen D (CpSt.init T Ts p0 osA) :=
    ⟨Nat.zero_le _, cpAll_length hA, hp0l, by simp [CpSt.init], hp0l, by simp [CpSt.init],
      by simp [CpSt.init]⟩
  have hwt := cp_wt_new (par := cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA))
    hlen ⟨rfl, cpLgLen_nil, cpLgLen_nil, fun l h => by simp [CpSt.init] at h⟩ (NT := Ts.length + 1) (M₀ := (2 * Ts.length + 2) * (Fintype.card S.dom + 1) * (D + 2))
    (by simp [CpSt.init]) (by simp [CpSt.init]) (by simp [CpSt.init]) hBw
  have h0 := cpRep_init (e := e) (πd := πd) O hO hcard hp0 hA hlen hwt
  exact cert_phase_spec I Pg F hd hstp (cp_hmv hst hpre hm hat hjp hjpre hjm ctx hBw hW) ih
    P₀.κ O h0

end Entry

end GI.Impl
