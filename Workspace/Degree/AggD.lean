module

public import Workspace.Degree.CertD
public import Workspace.Degree.CmpD
public import Workspace.Degree.ItemsD
public import Workspace.Degree.LcD
public import Workspace.Degree.Children
public import Workspace.Impl.AggSpecBody

@[expose] public section

/-!
# A round of `GiantStep` of the degree algorithm

The text of `as_agg_spec` of the general algorithm, with the phases of `CertD`, `CmpD`, `ItemsD` and
`LcD`. The function is `aggBodyE` of the general algorithm, at new function numbers. The result is
the exact answer. The cost is the own work plus the cost of the calls of the round's script plus the
cost of the continuations.
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly GI.Impl GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens Preimage NormalizedFactor Membership)
open scoped Pointwise

/-- `LiftAndContinue` at `blc`, as `AsLcAt` of the general algorithm, for any bound on the children.
-/
def AsLcD (Pg : Program) (F : Funs) (hpre : Preimage) (hfac : NormalizedFactor) (blc : ℕ)
    (krC : ℕ → ℕ) : Prop :=
  ∀ {Ω C : Type} {k : ℕ} (Bc : State Ω C → ℝ) {e : Ω ≃ Fin k} {c : C → ℕ} {sv : Val} {S : State Ω C},
    Canon e c sv S → ∀ {L : GiantLabels S} (_ : L.Constituent)
    {ps : List (Perm (Fin k) × Perm (Fin L.q))}, PairGens e L S.G ps →
    ∀ {sel : ℕ}, sel < S.hier.length → ∀ (cap : ℕ) (os : List (LcOver L.q)),
    (∀ o ∈ os, gens o.2.2 = o.2.1.map (alternatingGroup (Fin L.q)).subtype) →
    (∀ o ∈ os, ∀ (τ : Perm Ω) val, Canon e c val (lcChild S o.2.1 τ sel cap) →
      FunAll Pg F.cont val (ChildPost Bc (lcChild S o.2.1 τ sel cap) e)) →
    FunAll Pg blc (.list [lcCtx sv k L.q ps sel cap,
        .list (os.map fun o => lcOv (o.1 : Perm (Fin L.q)) o.2.2)])
      (fun w cost => ∃ ws : List Val, w = .list ws ∧ ws.length = os.length ∧
        (∀ i (hi : i < os.length) (hw : i < ws.length), ∃ a u, ws[i] = .list [encPerm a, u] ∧
          (toFin e).symm a ∈ L.rep os[i].1 • (L.lift os[i].2.1 : Set (Perm Ω)) ∧
          AnsC e u (lcChild S os[i].2.1 ((toFin e).symm a) sel cap).answer) ∧
        ∃ cs : ℕ → ℕ, (∀ i (hi : i < os.length), ∃ τ ∈ L.rep os[i].1 • (L.lift os[i].2.1 : Set (Perm Ω)),
          (cs i : ℝ) ≤ Bc (lcChild S os[i].2.1 τ sel cap)) ∧
        cost ≤ os.length * lcB (preimagePrim hpre) (normalizedFactorPrim hfac) krC
            (2 * (Val.list [lcCtx sv k L.q ps sel cap,
              .list (os.map fun o => lcOv (o.1 : Perm (Fin L.q)) o.2.2)]).wt + 6) +
          ∑ i ∈ Finset.range os.length, cs i +
          mapQK * (os.length + 1) *
            ((Val.list [lcCtx sv k L.q ps sel cap,
              .list (os.map fun o => lcOv (o.1 : Perm (Fin L.q)) o.2.2)]).wt + w.wt + 1))

/-- `lcMap_specD` meets `AsLcD`. -/
theorem asLcD_of {Pg : Program} {F : Funs} (hpre : Preimage) (hfac : NormalizedFactor)
    {b f bpre jpre bkr blift sb sp jfac bg bh bset : ℕ} {krC : ℕ → ℕ}
    (hb : Pg.HasAt b (mapFuns b f))
    (hf : Pg.funs[f]? = some (lcChildF F bpre bkr blift bg bh))
    (hbpre : Pg.HasAt bpre (graphPreFuns bpre jpre))
    (hjpre : Pg.prims[jpre]? = some (preimagePrim hpre))
    (hkr : LcKrOK Pg bkr krC) (hkrm : Monotone krC)
    (hlift : Pg.funs[blift]? = some (liftLabF sb sp jfac)) (hsb : ShiftAt Pg sb)
    (hsp : Pg.HasAt sp (pSplitFuns sp))
    (hjfac : Pg.prims[jfac]? = some (normalizedFactorPrim hfac))
    (hga : Pg.HasAt bg (gatherFuns bg))
    (hbh : Pg.funs[bh]? = some (lcHierF bset)) (hset : Pg.HasAt bset (setFuns bset)) :
    AsLcD Pg F hpre hfac b krC := by
  intro Ω C k Bc e c sv S hcan L con ps hps sel hsel cap os hos hcall
  obtain ⟨gv, dv, xv, yv, hv, rv, -, -, -, -, -, -, rfl⟩ := hcan.val
  exact lcMap_specD Bc hpre hfac hb hf hbpre hjpre hkr hkrm hlift hsb hsp hjfac hga hbh hset hcan
    con hps hsel cap os hos hcall

variable {Ω C : Type} {k : ℕ}

/-- As `it_union` of the general algorithm. -/
theorem it_unionD (e : Ω ≃ Fin k) {S : State Ω C} {L : GiantLabels S} {P : Params}
    (Ag : Aggregation P S L) (pieces : List (Set (Perm Ω))) (os : List (LcOver L.q))
    (ovs : List (Perm Ω × Subgroup (Perm Ω))) (hR : List.Forall₂ (asOvAt L) os ovs)
    (hb : Ag.script.evalExact = ⟨pieces, ovs⟩) (cap : ℕ)
    (pcs : List (Perm (Fin k) × Acc k)) (hl : pcs.length = pieces.length)
    (hp : ∀ i (h1 : i < pcs.length) (h2 : i < pieces.length), ceSet pcs[i] = toFin e '' pieces[i])
    (cps : List (Perm (Fin k) × Acc k)) (hcl : cps.length = os.length)
    (hc : ∀ i (h1 : i < cps.length) (h2 : i < os.length),
      (toFin e).symm cps[i].1 ∈ L.rep os[i].1 • (L.lift os[i].2.1 : Set (Perm Ω)) ∧
      ceSet cps[i] = toFin e '' ((toFin e).symm cps[i].1 •
        (lcChild S os[i].2.1 ((toFin e).symm cps[i].1) Ag.sel cap).answer)) :
    unionSet (pcs ++ cps) = toFin e '' S.answer := by
  obtain ⟨hol, hg⟩ := it_forall₂_get hR
  let b : Branches Ω := ⟨pieces, ovs⟩
  have hcov : Branches.Covers S b := by
    have h := Ag.covers
    rwa [hb] at h
  have hlen : b.overs.length = os.length := hol.symm
  let τ : Fin b.overs.length → Perm Ω := fun j => (toFin e).symm (cps[(j : ℕ)]'(by
    have := j.2; omega)).1
  let child : Fin b.overs.length → State Ω C := fun j =>
    lcChild S (os[(j : ℕ)]'(by have := j.2; omega)).2.1 (τ j) Ag.sel cap
  have hτ : ∀ j, τ j ∈ (b.overs.get j).1 • ((b.overs.get j).2 : Set (Perm Ω)) := fun j => by
    have h := (hc j (by have := j.2; omega) (by have := j.2; omega)).1
    rw [it_ov_coset (hg j _ j.2)] at h
    exact h
  have hchild : ∀ j, (child j).Inst (b.overs.get j).2 S.dom S.x (S.y ∘ τ j) := fun j => by
    have h := (hg j (by have := j.2; omega) j.2).1
    show (child j).Inst ovs[(j : ℕ)].2 S.dom S.x (S.y ∘ τ j)
    rw [h]; exact lcChild_inst S _ _ _ _
  have hans := step_aggregate b hcov τ hτ child hchild (fun j => (child j).answer) fun _ => rfl
  rw [← hans]
  exact ce_union e pieces pcs hl hp τ (fun j => (child j).answer) cps (by omega)
    fun j h => (hc j h (by have := j.2; omega)).2

set_option maxHeartbeats 2000000 in
/-- **The aggregation round meets its step specification**, given the contracts of its parts. -/
theorem as_agg_specD (I : Iface) (J : CostT) (hpre : Preimage) (hfac : NormalizedFactor)
    (hm : Membership) {Pg : Program} {F₀ F : Funs} {f fr fc fm fi blc bce : ℕ} {krC X : ℕ → ℕ}
    (H : AsHand) (hf : Pg.funs[f]? = some (aggBodyE fr fc fm fi blc bce))
    (hr : AsReadOK I Pg F₀ H X fr) (hc : AsCertD I J Pg F₀ F H X fc)
    (hcm : AsCompD I J Pg F₀ F H X fm) (hi : AsItemsD I J Pg F₀ F H X fi)
    (hlc : AsLcD Pg F hpre hfac blc krC) (hce : AsCeAt Pg hm bce)
    {Ω C : Type} {k : ℕ} {e : Ω ≃ Fin k} {c : C → ℕ} {S : State Ω C} {sv lv : Val}
    {L : SuppliedLabels S} (hcall : AsCall I Pg F₀ e c S sv lv L)
    (hih : DIH Pg F J (RoundP P₀ S L.q) (measure P₀ .giant S))
    (hlcih : ∀ (Ag : Aggregation P₀ S L.toGiantLabels), Ag.sel.val = L.sel.val →
      ∀ (o : LcOver L.q) (ov), ov ∈ Ag.script.evalExact.overs → ov.2 = L.toGiantLabels.lift o.2.1 →
      ∀ (τ : Perm Ω) (val : Val), Canon e c val (lcChild S o.2.1 τ L.sel (abCap L.toGiantLabels)) →
      FunAll Pg F.cont val (ChildPost (fun T => J .cont T)
        (lcChild S o.2.1 τ L.sel (abCap L.toGiantLabels)) e)) :
    FunAll Pg f (.list [sv, lv]) fun u cost => AnsC e u S.answer ∧
      ∃ (Ag : Aggregation P₀ S L.toGiantLabels) (os : List (LcOver L.q)) (cs : List Child),
        haveI : Finite Ω := Finite.of_equiv _ e.symm
        Ag.sel.val = L.sel.val ∧ cs.length = os.length ∧
        List.Forall₂ (fun o ov => ov.2 = L.toGiantLabels.lift o.2.1) os Ag.script.evalExact.overs ∧
        (∀ c' ∈ cs, ∃ o ∈ os, ∃ τ : Perm Ω, c' =
          ⟨Ω, C, lcChild S o.2.1 τ L.sel (abCap L.toGiantLabels), false⟩) ∧
        (cost : ℝ) ≤ asOwn hpre hfac hm krC X k (I.inW .giant S) + Ag.script.cost J +
          (cs.map fun c' => J .cont c'.T).sum := by
  haveI : Finite Ω := Finite.of_equiv _ e.symm
  obtain ⟨hinj, hcan, hlab, hq, hlw, hgood, -, hnot⟩ := id hcall
  have hvw : (Val.list [sv, lv]).wt ≤ I.inW .giant S :=
    Iface.InVal.wt_le (m := .giant) (by simp) ⟨sv, lv, L, rfl, hcan, hlab, hq, hlw⟩
  set v := Val.list [sv, lv] with hvdef
  have hr' := hr e c S sv lv L hcall
  have hc' := hc e c S sv lv L hcall hih
  have hcm' := hcm e c S sv lv L hcall hih
  have hi' := hi e c S sv lv L hcall hih
  set W₀ := I.inW .giant S with hW₀
  set Y := X W₀ with hY
  set cap := abCap L.toGiantLabels with hcap
  refine FunAll.intro hf ?_
  -- 1. reading
  have d1 : EvalAll Pg [v] (.call fr (.var 0)) (fun r c1 => ∃ (st : Val)
      (ps : List (Perm (Fin k) × Perm (Fin L.q))),
      r = .list [st, lcCtx sv k L.q ps L.sel cap] ∧ PairGens e L.toGiantLabels S.G ps ∧
      H.cert e c S L (asRounds L) st ∧ c1 ≤ v.wt + 1 + Y + r.wt + 1 ∧ r.wt ≤ Y) :=
    EvalAll.call_funAll (Det.var' rfl) fun v0 ca h0 => by
      obtain ⟨hv0, hca⟩ := h0
      subst v0
      exact hr'.mono fun w cb ⟨st, ps, h1, h2, h3, h4, h5⟩ =>
        ⟨st, ps, h1, h2, h3, by omega, h5⟩
  refine EvalAll.letE d1 fun r c1 h1 => ?_
  obtain ⟨st, ps, rfl, hps, hst, hc1, hrw⟩ := h1
  set ctx := lcCtx sv k L.q ps L.sel cap with hctx
  have wst : st.wt < (Val.list [st, ctx]).wt := wt_le_wt_list (by simp)
  have wctx : ctx.wt < (Val.list [st, ctx]).wt := wt_le_wt_list (by simp)
  -- 2. the certificate phase
  have d2 : EvalAll Pg ([v] ++ [.list [st, ctx]]) (.call fc (.get (.var 1) (.nat 0)))
      (fun o1 c2 => ∃ Ag1 ∈ asRounds L, ∃ (a1 : List (StagePair S))
        (ex1 : DX Ag1.certScript a1),
        H.comp e c S L {Ag' | Ag' ∈ asRounds L ∧ Ag'.certScript = Ag1.certScript} o1 ∧
        ∃ cb : ℕ, (cb : ℝ) ≤ Y + ex1.cost J ∧
          c2 ≤ (Val.list [st, ctx]).wt + 1 + (0 + 3) + st.wt + 1 + cb + o1.wt + 1 ∧ o1.wt ≤ Y) :=
    EvalAll.call_funAll (Det.get' (Det.var' (i := 1) rfl) (Det.nat 0) rfl) fun v0 ca h0 => by
      obtain ⟨hv0, hca⟩ := h0
      subst v0
      exact (hc' _ st hst).mono fun w cb ⟨Ag, hAg, a, ex, h1, h2, h3⟩ =>
        ⟨Ag, hAg, a, ex, h1, cb, h2, by omega, h3⟩
  refine EvalAll.letE d2 fun o1 c2 h2 => ?_
  obtain ⟨Ag1, hAg1, a1, ex1, hst2, cb2, hcb2, hc2, ho1⟩ := h2
  -- 3. the comparison phase
  have d3 : EvalAll Pg ([v] ++ [.list [st, ctx]] ++ [o1]) (.call fm (.var 2))
      (fun o2 c3 => ∃ Ag2 ∈ {Ag' | Ag' ∈ asRounds L ∧ Ag'.certScript = Ag1.certScript},
        ∃ (a2 : List Bool) (ex2 : DX Ag2.compScript a2),
        H.items e c S L {Ag' | Ag' ∈ {Ag' | Ag' ∈ asRounds L ∧ Ag'.certScript = Ag1.certScript} ∧
          Ag'.compScript = Ag2.compScript} o2 ∧
        ∃ cb : ℕ, (cb : ℝ) ≤ Y + ex2.cost J ∧ c3 ≤ o1.wt + 1 + cb + o2.wt + 1 ∧ o2.wt ≤ Y) :=
    EvalAll.call_funAll (Det.var' (i := 2) rfl) fun v0 ca h0 => by
      obtain ⟨hv0, hca⟩ := h0
      subst v0
      exact (hcm' _ o1 hst2).mono fun w cb ⟨Ag, hAg, a, ex, h1, h2, h3⟩ =>
        ⟨Ag, hAg, a, ex, h1, cb, h2, by omega, h3⟩
  refine EvalAll.letE d3 fun o2 c3 h3 => ?_
  obtain ⟨Ag2, hAg2, a2, ex2, hst3, cb3, hcb3, hc3, ho2⟩ := h3
  -- 4. the items
  have d4 : EvalAll Pg ([v] ++ [.list [st, ctx]] ++ [o1] ++ [o2]) (.call fi (.var 3))
      (fun o3 c4 => ∃ Ag3 ∈ {Ag' | Ag' ∈ {Ag' | Ag' ∈ asRounds L ∧
          Ag'.certScript = Ag1.certScript} ∧ Ag'.compScript = Ag2.compScript},
        ∃ (pieces : List (Set (Perm Ω))) (os : List (LcOver L.q))
          (ovs : List (Perm Ω × Subgroup (Perm Ω))) (pcs : List (Perm (Fin k) × Acc k))
          (ex3 : DX Ag3.itemsScript ⟨pieces, ovs⟩),
        List.Forall₂ (asOvAt L.toGiantLabels) os ovs ∧ o3 = .list [.list (pcs.map encPiece),
          .list (os.map fun o => lcOv (o.1 : Perm (Fin L.q)) o.2.2)] ∧
        pcs.length = pieces.length ∧
        (∀ i (h1 : i < pcs.length) (h2 : i < pieces.length), ceSet pcs[i] = toFin e '' pieces[i]) ∧
        (∀ o ∈ os, gens o.2.2 = o.2.1.map (alternatingGroup (Fin L.q)).subtype) ∧
        ∃ cb : ℕ, (cb : ℝ) ≤ Y + ex3.cost J ∧ c4 ≤ o2.wt + 1 + cb + o3.wt + 1 ∧ o3.wt ≤ Y) :=
    EvalAll.call_funAll (Det.var' (i := 3) rfl) fun v0 ca h0 => by
      obtain ⟨hv0, hca⟩ := h0
      subst v0
      exact (hi' _ o2 hst3).mono
        fun w cb ⟨Ag, hAg, pieces, os, ovs, pcs, ex, h0, h1, h2, h3, h4, h5, h6⟩ =>
        ⟨Ag, hAg, pieces, os, ovs, pcs, ex, h0, h1, h2, h3, h4, cb, h5, by omega, h6⟩
  refine EvalAll.letE d4 fun o3 c4 h4 => ?_
  obtain ⟨Ag3, ⟨⟨hAg3r, hAg3c⟩, hAg3m⟩, pieces, os, ovs, pcs, ex3, hR, rfl, hpl, hpcs, hos, cb4, hcb4,
    hc4, ho3⟩ := h4
  -- the run of the round's script
  have hcert : Ag1.certScript = Ag3.certScript := hAg3c.symm
  have hcomp : Ag2.compScript = Ag3.compScript := hAg3m.symm
  obtain ⟨ex1', -, hex1⟩ := DX.cast hcert ex1
  obtain ⟨ex2', -, hex2⟩ := DX.cast hcomp ex2
  have hb : (⟨pieces, ovs⟩ : Branches Ω) = Ag3.script.evalExact := by
    have e1 : Ag3.script.evalExact = Ag3.itemsScript.evalExact := by
      show (Ag3.certScript.bind fun _ => Ag3.compScript.bind fun _ => Ag3.itemsScript).evalExact = _
      rw [Script.evalExact_bind, Script.evalExact_bind]
    rw [e1]; exact ex3.exact.symm
  have hexAll : Ag3.script.cost J = ex1.cost J + ex2.cost J + ex3.cost J := by
    show (Ag3.certScript.bind fun _ => Ag3.compScript.bind fun _ => Ag3.itemsScript).cost J = _
    rw [Script.cost_bind, Script.cost_bind, ← hex1 J, ← hex2 J]
    show Ag3.certScript.cost J + (Ag3.compScript.cost J + Ag3.itemsScript.cost J) = _
    have e1 : ex1'.cost J = Ag3.certScript.cost J := rfl
    have e2 : ex2'.cost J = Ag3.compScript.cost J := rfl
    have e3 : ex3.cost J = Ag3.itemsScript.cost J := rfl
    rw [e1, e2, e3]; ring
  have hsel : Ag3.sel.val = L.sel.val := hAg3r.1
  have hcon : Ag3.con = L.con := hAg3r.2
  -- weights
  set pv := Val.list (pcs.map encPiece) with hpv
  set ov := Val.list (os.map fun o => lcOv (o.1 : Perm (Fin L.q)) o.2.2) with hov
  have wpv : pv.wt < (Val.list [pv, ov]).wt := wt_le_wt_list (by simp)
  have wov : ov.wt < (Val.list [pv, ov]).wt := wt_le_wt_list (by simp)
  have hlen : os.length ≤ Y := by
    have h0 : (os.map fun o => lcOv (o.1 : Perm (Fin L.q)) o.2.2).length < ov.wt :=
      length_lt_wt_list _
    rw [List.length_map] at h0
    omega
  -- 5. `LiftAndContinue`
  have hcallc : ∀ o ∈ os, ∀ (τ : Perm Ω) val, Canon e c val (lcChild S o.2.1 τ L.sel cap) →
      FunAll Pg F.cont val (ChildPost (fun T => J .cont T) (lcChild S o.2.1 τ L.sel cap) e) := by
    intro o ho τ val hval
    obtain ⟨ov, hov, hov2, -⟩ := it_forall₂_mem hR ho
    have hov' : ov ∈ Ag3.script.evalExact.overs := by rw [← hb]; exact hov
    exact hlcih Ag3 hsel o ov hov' hov2 τ val hval
  have d5a := Det.mk2 (Det.get' (Det.var' (P := Pg)
    (env := [v] ++ [.list [st, ctx]] ++ [o1] ++ [o2] ++ [.list [pv, ov]]) (i := 1) rfl)
    (Det.nat 1) (v := ctx) rfl)
    (Det.get' (Det.var' (i := 4) rfl) (Det.nat 1) (v := ov) rfl)
  have hlc' := hlc (fun T => J .cont T) hcan L.con hps L.sel.2 cap os hos hcallc
  have d5 : EvalAll Pg ([v] ++ [.list [st, ctx]] ++ [o1] ++ [o2] ++ [.list [pv, ov]])
      (.call blc (mk2 (.get (.var 1) (.nat 1)) (.get (.var 4) (.nat 1))))
      (fun w5 c5 => ∃ ws : List Val, w5 = .list ws ∧ ws.length = os.length ∧
        (∀ i (hi : i < os.length) (hw : i < ws.length), ∃ a u, ws[i] = .list [encPerm a, u] ∧
          (toFin e).symm a ∈ L.rep os[i].1 • (L.lift os[i].2.1 : Set (Perm Ω)) ∧
          AnsC e u (lcChild S os[i].2.1 ((toFin e).symm a) L.sel cap).answer) ∧
        ∃ cs : ℕ → ℕ, (∀ i (hi : i < os.length), ∃ τ ∈ L.rep os[i].1 • (L.lift os[i].2.1 : Set (Perm Ω)),
            (cs i : ℝ) ≤ J .cont (lcChild S os[i].2.1 τ L.sel cap)) ∧
        c5 ≤ (Val.list [st, ctx]).wt + 1 + (1 + 3) + ctx.wt + 1 +
            ((Val.list [pv, ov]).wt + 1 + (1 + 3) + ov.wt + 1) + 2 * (Val.list [ctx, ov]).wt + 7 +
          (os.length * lcB (preimagePrim hpre) (normalizedFactorPrim hfac) krC
            (2 * (Val.list [ctx, ov]).wt + 6) + ∑ i ∈ Finset.range os.length, cs i +
          mapQK * (os.length + 1) * ((Val.list [ctx, ov]).wt + w5.wt + 1)) + w5.wt + 1) :=
    EvalAll.call_funAll d5a fun v0 ca h0 => by
      obtain ⟨hv0, hca⟩ := h0
      subst v0
      refine hlc'.mono fun w cb hh => ?_
      obtain ⟨ws, h1, h2, h3, cs, h4, h5⟩ := hh
      rw [← hctx, ← hov] at h5
      exact ⟨ws, h1, h2, h3, cs, h4, by omega⟩
  refine EvalAll.letE d5 fun w5 c5 h5 => ?_
  obtain ⟨ws, rfl, hwl, hent, cs, hcs, hc5⟩ := h5
  -- the weight of the continuation pieces
  have hwe : ∀ w ∈ ws, w.wt ≤ asEW k := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
    obtain ⟨a, u', he, -, hu'⟩ := hent i (hwl ▸ hi) hi
    rw [he]
    have := wt_list2_le (encPerm a) u'
    have := wt_encPerm_le a
    have := hu'.wt_le
    unfold asEW
    omega
  have hwsw : (Val.list ws).wt ≤ asWw k Y := by
    have h1 := GI.Lang.wt_list_le_of ws hwe
    have h2 : ws.length * (2 * asEW k + 1) ≤ Y * (2 * asEW k + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    unfold asWw
    omega
  obtain ⟨cps, hws, hcl, hcps⟩ := ab_cps e os (L.sel : ℕ) cap ws hwl hent
  have hsel' : ((Ag3.sel : ℕ)) = (L.sel : ℕ) := hsel
  have hU := it_unionD e Ag3 pieces os ovs hR hb.symm cap pcs hpl hpcs cps hcl (by rw [hsel']; exact hcps)
  -- 6. `CombineExact`
  have d6a := Det.mk2 (Det.get' (Det.var' (P := Pg)
    (env := [v] ++ [.list [st, ctx]] ++ [o1] ++ [o2] ++ [.list [pv, ov]] ++ [.list ws]) (i := 4)
    rfl) (Det.nat 0) (v := pv) rfl) (Det.var' (i := 5) rfl)
  refine EvalAll.call_funAll d6a fun v0 ca h0 => ?_
  obtain ⟨hv0, hca6⟩ := h0
  subst v0
  have hce' := hce k pcs cps (by rw [hU]; exact image_answer_cases e S)
  subst hws
  refine hce'.mono fun u cb ⟨hcu, hcb⟩ => ?_
  rw [hU] at hcu
  rw [← hpv] at hcb
  have hans := ce_ansC e hcu
  refine ⟨hans, ?_⟩
  choose τ hτ hcsτ using hcs
  have hovs : ovs = Ag3.script.evalExact.overs := congrArg Branches.overs hb
  let child : Fin os.length → Child := fun j =>
    ⟨Ω, C, lcChild S os[(j : ℕ)].2.1 (τ j j.2) L.sel cap, false⟩
  have hsum : ∑ i ∈ Finset.range os.length, (cs i : ℝ) ≤
      (((List.finRange os.length).map child).map fun c' => J .cont c'.T).sum := by
    rw [List.map_map, Finset.sum_range, ← Fin.sum_univ_def]
    exact Finset.sum_le_sum fun j _ => hcsτ j j.2
  refine ⟨Ag3, os, (List.finRange os.length).map child, hsel, by simp,
    hovs ▸ hR.imp (fun _ _ h => h.1), ?_, ?_⟩
  · intro c' hc'
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hc'
    exact ⟨_, List.getElem_mem j.2, _, rfl⟩
  -- the cost
  have hu := hans.wt_le
  have wpv' : pv.wt ≤ Y := by omega
  have wov' : ov.wt ≤ Y := by omega
  have wctx' : ctx.wt ≤ Y := by omega
  have hWl : (Val.list [ctx, ov]).wt ≤ asWl Y := by
    have := wt_list2_le ctx ov
    unfold asWl; omega
  have hWc : (Val.list [pv, .list (cps.map encPiece)]).wt ≤ asWc k Y := by
    have := wt_list2_le pv (.list (cps.map encPiece))
    unfold asWc; omega
  have P1 : os.length * lcB (preimagePrim hpre) (normalizedFactorPrim hfac) krC
      (2 * (Val.list [ctx, ov]).wt + 6) ≤
      Y * asMax (lcB (preimagePrim hpre) (normalizedFactorPrim hfac) krC) (2 * asWl Y + 6) :=
    Nat.mul_le_mul hlen (le_asMax _ (by omega))
  have P2 : mapQK * (os.length + 1) * ((Val.list [ctx, ov]).wt +
      (Val.list (cps.map encPiece)).wt + 1) ≤ mapQK * (Y + 1) * (asWl Y + asWw k Y + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have P3 : ceCost hm k (Val.list [pv, .list (cps.map encPiece)]).wt ≤
      asMax (ceCost hm k) (asWc k Y) := le_asMax _ hWc
  have hN : c1 + (c2 + (c3 + (c4 + (c5 + (ca + cb + u.wt + 1) + u.wt + 1) + u.wt + 1) + u.wt + 1) +
      u.wt + 1) + u.wt + 1 + 3 * Y ≤
      (100 * (W₀ + Y + asWl Y + asWw k Y + asWc k Y + ansW k + 10) +
        Y * asMax (lcB (preimagePrim hpre) (normalizedFactorPrim hfac) krC) (2 * asWl Y + 6) +
        mapQK * (Y + 1) * (asWl Y + asWw k Y + 1) + asMax (ceCost hm k) (asWc k Y)) +
      cb2 + cb3 + cb4 + ∑ i ∈ Finset.range os.length, cs i := by
    omega
  have hR := (Nat.cast_le (α := ℝ)).2 hN
  have hown : (asOwn hpre hfac hm krC X k W₀ : ℝ) =
      ((100 * (W₀ + Y + asWl Y + asWw k Y + asWc k Y + ansW k + 10) +
        Y * asMax (lcB (preimagePrim hpre) (normalizedFactorPrim hfac) krC) (2 * asWl Y + 6) +
        mapQK * (Y + 1) * (asWl Y + asWw k Y + 1) + asMax (ceCost hm k) (asWc k Y) : ℕ) : ℝ) := rfl
  rw [hexAll, hown]
  push_cast at hR hown ⊢
  linarith

end GI.Degree
