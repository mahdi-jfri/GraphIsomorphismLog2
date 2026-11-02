import Workspace.Impl.AggItemRun

/-!
# The program of the aggregation round and its step specification

`aggBodyE fr fc fm fi blc bce` is the step function of the aggregation case of `GiantStep`. On the
input `[sv, lv]` it reads the input (`fr`), runs the certificate phase (`fc`), the comparison phase
(`fm`) and the items (`fi`), then `LiftAndContinue` on the overcosets (`blc`) and `CombineExact` on
the pieces (`bce`). The contracts of the parts are in `Workspace/Impl/AggSpecDefs.lean`.

`as_agg_spec`: if the parts meet their contracts, the step meets `Iface.AggSpec`, for every
interface whose work at an aggregation node is at least `asOwn` (the cost of the parts besides
their calls).

The proof glues the runs of the three parts of the script into one run of the round's script
(`asExecBind`), for a round `Ag` in the last candidate set; this `Ag` has the certificate and
comparison scripts of the rounds the earlier phases ran. The continuations are allowed calls
(`it_child_good_mlt`), and `it_run`, `ab_cps`, `it_union` give the run `Run.aggregate` and the
union of the pieces. The overcosets of the script are known only up to coset (`asOvAt`); the
run takes, for each overcoset, the representative that `LiftAndContinue` finds in the coset of
the program's overcoset value.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val encPerm gens Preimage NormalizedFactor Membership)
open scoped Pointwise

/-- **The step function of the aggregation round.** The environment grows as
`[v, r, o₁, o₂, o₃, ws]`: the input, the read value `[st, ctx]`, the outputs of the three phases,
the continuation pieces. -/
def aggBodyE (fr fc fm fi blc bce : ℕ) : Expr :=
  .letE (.call fr (.var 0))
  (.letE (.call fc (.get (.var 1) (.nat 0)))
  (.letE (.call fm (.var 2))
  (.letE (.call fi (.var 3))
  (.letE (.call blc (mk2 (.get (.var 1) (.nat 1)) (.get (.var 4) (.nat 1))))
    (.call bce (mk2 (.get (.var 4) (.nat 0)) (.var 5)))))))

/-- A run of a script is a run of an equal script, with the same cost. -/
theorem as_exec_cast (I : Iface) {α : Type} {s s' : Script α} {a : α} (h : s = s')
    (ex : Exec P₀ s a) : ∃ ex' : Exec P₀ s' a, I.execCost ex' = I.execCost ex := by
  subst h; exact ⟨ex, rfl⟩

variable {Ω C : Type} {k : ℕ}

set_option maxHeartbeats 2000000 in
/-- **The aggregation round meets its step specification**, given the contracts of its parts. -/
theorem as_agg_spec (I : Iface) (hpre : Preimage) (hfac : NormalizedFactor) (hm : Membership)
    {Pg : Program} {F : Funs} {f fr fc fm fi blc bce : ℕ} {krC X : ℕ → ℕ} (H : AsHand)
    (huniq : ∀ {Ω C : Type} {k : ℕ} {e : Ω ≃ Fin k} {S : State Ω C} {lv : Val}
      {L L' : SuppliedLabels S}, I.LabVal e S lv L → I.LabVal e S lv L' → L = L')
    (hf : Pg.funs[f]? = some (aggBodyE fr fc fm fi blc bce))
    (hr : AsReadOK I Pg F H X fr) (hc : AsCertOK I Pg F H X fc) (hcm : AsCompOK I Pg F H X fm)
    (hi : AsItemsOK I Pg F H X fi) (hlc : AsLcAt I Pg F hpre hfac blc krC)
    (hce : AsCeAt Pg hm bce)
    (hW : ∀ nd : Node P₀, nd.run.kind = .aggregate →
      (asOwn hpre hfac hm krC X (Nat.card nd.Ω) (I.inW .giant nd.S) : ℝ) ≤ I.W nd) :
    I.AggSpec Pg F f := by
  intro Ω C S k e c hinj v hv hgood hP hIH
  haveI : Finite Ω := Finite.of_equiv _ e.symm
  have hvw : v.wt ≤ I.inW .giant S := Iface.InVal.wt_le (m := .giant) (by simp) hv
  obtain ⟨sv, lv, L, rfl, hcan, hlab, hq, hlw⟩ := hv
  obtain ⟨sv', lv', L', hv', hlab', hnot⟩ := hP
  simp only [Val.list.injEq, List.cons.injEq, and_true] at hv'
  obtain ⟨rfl, rfl⟩ := hv'
  have hLL : L' = L := huniq hlab' hlab
  subst L'
  have hcall : AsCall I Pg F e c S sv lv L := ⟨hinj, hcan, hlab, hq, hlw, hgood, hIH, hnot⟩
  have hk : Nat.card Ω = k := Iface.card_eq e
  have hr' := hr e c S sv lv L hcall
  have hc' := hc e c S sv lv L hcall
  have hcm' := hcm e c S sv lv L hcall
  have hi' := hi e c S sv lv L hcall
  set W₀ := I.inW .giant S with hW₀
  set Y := X W₀ with hY
  set v := Val.list [sv, lv] with hvdef
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
        (ex1 : Exec P₀ Ag1.certScript a1),
        H.comp e c S L {Ag' | Ag' ∈ asRounds L ∧ Ag'.certScript = Ag1.certScript} o1 ∧
        ∃ cb : ℕ, (cb : ℝ) ≤ Y + I.execCost ex1 ∧
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
        ∃ (a2 : List Bool) (ex2 : Exec P₀ Ag2.compScript a2),
        H.items e c S L {Ag' | Ag' ∈ {Ag' | Ag' ∈ asRounds L ∧ Ag'.certScript = Ag1.certScript} ∧
          Ag'.compScript = Ag2.compScript} o2 ∧
        ∃ cb : ℕ, (cb : ℝ) ≤ Y + I.execCost ex2 ∧ c3 ≤ o1.wt + 1 + cb + o2.wt + 1 ∧ o2.wt ≤ Y) :=
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
          (ex3 : Exec P₀ Ag3.itemsScript ⟨pieces, ovs⟩),
        List.Forall₂ (asOvAt L.toGiantLabels) os ovs ∧ o3 = .list [.list (pcs.map encPiece),
          .list (os.map fun o => lcOv (o.1 : Perm (Fin L.q)) o.2.2)] ∧
        pcs.length = pieces.length ∧
        (∀ i (h1 : i < pcs.length) (h2 : i < pieces.length), ceSet pcs[i] = toFin e '' pieces[i]) ∧
        (∀ o ∈ os, gens o.2.2 = o.2.1.map (alternatingGroup (Fin L.q)).subtype) ∧
        ∃ cb : ℕ, (cb : ℝ) ≤ Y + I.execCost ex3 ∧ c4 ≤ o2.wt + 1 + cb + o3.wt + 1 ∧ o3.wt ≤ Y) :=
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
  obtain ⟨ex1', hex1⟩ := as_exec_cast I hcert ex1
  obtain ⟨ex2', hex2⟩ := as_exec_cast I hcomp ex2
  let exAll : Exec P₀ Ag3.script ⟨pieces, ovs⟩ :=
    asExecBind (fun _ => Ag3.compScript.bind fun _ => Ag3.itemsScript) Ag3.certScript ex1'
      (asExecBind (fun _ => Ag3.itemsScript) Ag3.compScript ex2' ex3)
  have hexAll : I.execCost exAll = I.execCost ex1 + I.execCost ex2 + I.execCost ex3 := by
    have h1 := asExecBind_cost I (fun _ => Ag3.compScript.bind fun _ => Ag3.itemsScript)
      Ag3.certScript ex1' (asExecBind (fun _ => Ag3.itemsScript) Ag3.compScript ex2' ex3)
    have h2 := asExecBind_cost I (fun _ => Ag3.itemsScript) Ag3.compScript ex2' ex3
    rw [← hex1, ← hex2]
    exact h1.trans (by rw [h2]; ring)
  have hb : (⟨pieces, ovs⟩ : Branches Ω) = Ag3.script.evalExact :=
    exAll.exact
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
      FunAll Pg F.cont val (I.Post .cont (lcChild S o.2.1 τ L.sel cap) e val) := by
    intro o ho τ val hval
    obtain ⟨ov, hov, hov2, -⟩ := it_forall₂_mem hR ho
    have hov' : ov ∈ Ag3.script.evalExact.overs := by rw [← hb]; exact hov
    obtain ⟨hg, hlt⟩ := it_child_good_mlt hgood L hq.le Ag3 hsel o ov hov' hov2 τ
    exact hIH .cont _ hg hlt k e c hinj val hval
  have d5a := Det.mk2 (Det.get' (Det.var' (P := Pg)
    (env := [v] ++ [.list [st, ctx]] ++ [o1] ++ [o2] ++ [.list [pv, ov]]) (i := 1) rfl)
    (Det.nat 1) (v := ctx) rfl)
    (Det.get' (Det.var' (i := 4) rfl) (Det.nat 1) (v := ov) rfl)
  have hlc' := hlc hcan L.con hps L.sel.2 cap os hos hcallc
  have d5 : EvalAll Pg ([v] ++ [.list [st, ctx]] ++ [o1] ++ [o2] ++ [.list [pv, ov]])
      (.call blc (mk2 (.get (.var 1) (.nat 1)) (.get (.var 4) (.nat 1))))
      (fun w5 c5 => ∃ ws : List Val, w5 = .list ws ∧ ws.length = os.length ∧
        (∀ i (hi : i < os.length) (hw : i < ws.length), ∃ a u, ws[i] = .list [encPerm a, u] ∧
          (toFin e).symm a ∈ L.rep os[i].1 • (L.lift os[i].2.1 : Set (Perm Ω)) ∧
          AnsC e u (lcChild S os[i].2.1 ((toFin e).symm a) L.sel cap).answer) ∧
        ∃ cs : ℕ → ℕ, (∀ i (hi : i < os.length), ∃ τ ∈ L.rep os[i].1 • (L.lift os[i].2.1 : Set (Perm Ω)),
          ∃ (A : Set (Perm Ω)) (r : Run P₀ .cont (lcChild S os[i].2.1 τ L.sel cap) none A),
            (cs i : ℝ) ≤ r.total I.work) ∧
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
  -- the run of the round
  obtain ⟨A, rr, hkind, hcc⟩ := it_run I hgood.2.2.2.1 hgood.2.2.1 L hnot hq.le Ag3 hsel hcon
    pieces os ovs hR exAll cs (by rw [hsel']; exact hcs)
  have hU := it_union e Ag3 pieces os ovs hR exAll cap pcs hpl hpcs cps hcl (by rw [hsel']; exact hcps)
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
  obtain rfl : A = S.answer := rr.exact
  refine ⟨S.answer, some L, rr, ⟨sv, lv, L, rfl, hlab, rfl⟩, by simp [hkind], hans, ?_⟩
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
  have hWn := hW rr.node (by simpa using hkind)
  have hown : (asOwn hpre hfac hm krC X (Nat.card rr.node.Ω) (I.inW .giant rr.node.S) : ℝ) =
      ((100 * (W₀ + Y + asWl Y + asWw k Y + asWc k Y + ansW k + 10) +
        Y * asMax (lcB (preimagePrim hpre) (normalizedFactorPrim hfac) krC) (2 * asWl Y + 6) +
        mapQK * (Y + 1) * (asWl Y + asWw k Y + 1) + asMax (ceCost hm k) (asWc k Y) : ℕ) : ℝ) := by
    show (asOwn hpre hfac hm krC X (Nat.card Ω) (I.inW .giant S) : ℝ) = _
    rw [hk]; rfl
  have hmax : I.W rr.node ≤ I.own .giant rr (Val.list [sv, lv]) := by
    simp only [Iface.own]; exact le_max_right _ _
  rw [hown] at hWn
  have hcc' : I.execCost ex1 + I.execCost ex2 + I.execCost ex3 +
      ∑ i ∈ Finset.range os.length, (cs i : ℝ) ≤ I.childCost rr := by rw [← hexAll]; exact hcc
  have hN : c1 + (c2 + (c3 + (c4 + (c5 + (ca + cb + u.wt + 1) + u.wt + 1) + u.wt + 1) + u.wt + 1) +
      u.wt + 1) + u.wt + 1 + 3 * Y ≤
      (100 * (W₀ + Y + asWl Y + asWw k Y + asWc k Y + ansW k + 10) +
        Y * asMax (lcB (preimagePrim hpre) (normalizedFactorPrim hfac) krC) (2 * asWl Y + 6) +
        mapQK * (Y + 1) * (asWl Y + asWw k Y + 1) + asMax (ceCost hm k) (asWc k Y)) +
      cb2 + cb3 + cb4 + ∑ i ∈ Finset.range os.length, cs i := by
    omega
  have hR := (Nat.cast_le (α := ℝ)).2 hN
  push_cast at hR hWn ⊢
  linarith

end GI.Impl
