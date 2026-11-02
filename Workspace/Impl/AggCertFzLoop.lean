import Workspace.Impl.AggCertFzStep

/-!
# The graph forms of the certificate groups: the step of the loop

`cp_fz_step`: one step of the loop over the test sets keeps `CpFzInv`, at cost at most
`cpFzStepB W`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens PointwiseStab Preimage Membership)

/-- The budget of one step of the loop over the test sets. -/
noncomputable def cpFzStepB (hst : PointwiseStab) (hpre : Preimage) (hm : Membership) (W : ℕ) :
    ℕ :=
  cpFzOutB hst hpre hm W + 4 * cpG hst hpre hm W + 400 * (W + 20)

section Step

variable {k : ℕ} {Ω C : Type} [DecidableEq Ω] {e : Ω ≃ Fin k} {col : C → ℕ} {S : State Ω C}
  [Fintype S.dom] {L : GiantLabels S} {πd : S.domGroup →* alternatingGroup (Fin L.q)}
  (hst : PointwiseStab) (hpre : Preimage) (hm : Membership)

theorem cpSel_cases {α : Type} {s : ℕ} (hs : s ≤ 1) (P : α → Prop) {a b : α} (ha : P a)
    (hb : P b) : P (cpSel s a b) := by
  unfold cpSel; split_ifs <;> assumption

theorem cpSel_get {s : ℕ} (hs : s ≤ 1) (a b : Val) : [a, b][s]? = some (cpSel s a b) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hs with rfl | rfl <;> rfl

theorem cpSel_get1 {s : ℕ} (hs : s ≤ 1) (t a b : Val) :
    [t, a, b][s + 1]? = some (cpSel s a b) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hs with rfl | rfl <;> rfl

theorem cpSel_map {α β : Type} (s : ℕ) (g : α → β) (a b : α) :
    g (cpSel s a b) = cpSel s (g a) (g b) := by
  unfold cpSel; split_ifs <;> rfl

theorem cp_wt_list5_le (a b c d f : Val) :
    (Val.list [a, b, c, d, f]).wt ≤ 2 * (a.wt + b.wt + c.wt + d.wt + f.wt) + 9 := by
  have := wt_list_le [a, b, c, d, f]; simp at this; omega

set_option maxHeartbeats 4000000 in
/-- **One test set.** -/
theorem cp_fz_step {Pg : Program} {f b jp jpre jm : ℕ} (hat : CpMvAt Pg b jp jpre jm)
    (hfz : CpFzAt Pg f b) (hjp : Pg.prims[jp]? = some (pointwiseStabPrim hst))
    {sv : Val} {gp : GPairs k L.q} {osA : List (Fin (k + L.q))} {D : ℕ}
    (ctx : CpCtx e col S L πd sv gp osA D)
    {res : List (GPairs k L.q × GPairs k L.q)}
    {logs : List (Finset (Fin L.q) × List (CpStgD k L.q) × List (CpStgD k L.q))}
    (hin : CpFzIn e S L πd res logs) {s : ℕ} (hs : s ≤ 1) {i : ℕ} (hi : i < logs.length)
    {acc : Val} (hacc : CpFzInv e S L πd logs (cpSel s S.x S.y) i acc) {W : ℕ}
    (hW : 10 * (Val.list [.list [cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA),
      cpOutV res logs, .nat s], .nat i, acc]).wt + 10 ^ 10 * (k + L.q + 1) ^ 12 + D ≤ W) :
    CpFB Pg (f + 4) (.list [.list [cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA),
      cpOutV res logs, .nat s], .nat i, acc]) W (cpFzStepB hst hpre hm W)
      (CpFzInv e S L πd logs (cpSel s S.x S.y) (i + 1)) := by
  obtain ⟨qs0, rfl, hq0l, hq0G, hq0g⟩ := hacc
  obtain ⟨osL, hnd, hall, hosA⟩ := ctx.hosA
  have hosL : osL.length ≤ k := cp_os_length_le e hnd
  set par := cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA) with hpar
  set z := cpSel s S.x S.y with hz
  have hir : i < res.length := by rw [hin.length]; exact hi
  -- the data of test set `i`
  have hrr0 := hin.rel.get hi hir
  simp only [List.get_eq_getElem] at hrr0
  obtain ⟨l, r, hlm, hrm, hrr, hTi, hrget, hlget⟩ : ∃ (l : Finset (Fin L.q) × List (CpStgD k L.q) ×
      List (CpStgD k L.q)) (r : GPairs k L.q × GPairs k L.q), l ∈ logs ∧ r ∈ res ∧
      (PairGens e L (S.liftGroup (grp (cpPhi S πd l.1) (dstr S S.x) (Fintype.card S.dom))) r.1 ∧
        PairGens e L (S.liftGroup (grp (cpPhi S πd l.1) (dstr S S.y) (Fintype.card S.dom))) r.2) ∧
      (logs.map Prod.fst).getD i ∅ = l.1 ∧
      (res.map resV)[i]? = some (.list [gpV r.1, gpV r.2]) ∧
      (logs.map cpLogV)[i]? = some (.list [tsV k l.1, .list (l.2.1.map cpSgV),
        .list (l.2.2.map cpSgV)]) :=
    ⟨logs[i], res[i], List.getElem_mem hi, List.getElem_mem hir, hrr0,
      by rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi), List.getElem_map],
      by rw [List.getElem?_map, List.getElem?_eq_getElem hir]; rfl,
      by rw [List.getElem?_map, List.getElem?_eq_getElem hi]; rfl⟩
  set pz := cpSel s r.1 r.2 with hpzd
  set stg := cpSel s l.2.1 l.2.2 with hstgd
  have hpz : PairGens e L (S.liftGroup (grp (cpPhi S πd l.1) (dstr S z) (Fintype.card S.dom)))
      pz := by
    rw [hz, hpzd]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hs with rfl | rfl
    · exact hrr.1
    · exact hrr.2
  have hpzl : pz.length ≤ (k + L.q) ^ 2 :=
    cpSel_cases hs (fun p : GPairs k L.q => p.length ≤ (k + L.q) ^ 2)
      (hin.lens r hrm).1 (hin.lens r hrm).2
  have hstg : CpStgs e πd l.1 z stg := by
    rw [hz, hstgd]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hs with rfl | rfl
    · exact (hin.stgs l hlm).1
    · exact (hin.stgs l hlm).2
  have hstgl : CpLgLen stg :=
    cpSel_cases hs (fun p : List (CpStgD k L.q) => CpLgLen p) (hin.lglen l hlm).1
      (hin.lglen l hlm).2
  have hcard : l.1.card = P₀.κ := by
    obtain ⟨O, hO⟩ := hin.ord
    exact (O.mem _).1 (hO ▸ List.mem_map_of_mem hlm)
  have hD : Nat.card (alternatingGroup l.1) = D := ctx.hD _ hcard
  -- the outside points
  obtain ⟨incls, hil, hinc, hinc2⟩ := cp_stgs_incls πd hstg
  set oL := cpOutF e L.q osL incls with hoL
  have hoLm : ∀ v, v ∈ oL ↔ v ∉ finalWin (cpPhi S πd l.1) (dstr S z) :=
    cp_mem_outF_win πd (hil.trans hstg.1) hinc hall
  have hoLl : oL.length ≤ k := (cp_outF_sublist osL incls).length_le.trans hosL
  -- weights
  set A := Val.list [.list [par, cpOutV res logs, .nat s], .nat i, gpV qs0] with hA
  set cV := Val.list [par, cpOutV res logs, .nat s] with hcV
  have hcA : cV.wt < A.wt := cp_wt_get (vs := [cV, .nat i, gpV qs0]) (j := 0) rfl
  have hiA : (Val.nat i).wt < A.wt := cp_wt_get (vs := [cV, .nat i, gpV qs0]) (j := 1) rfl
  have hqA : (gpV qs0).wt < A.wt := cp_wt_get (vs := [cV, .nat i, gpV qs0]) (j := 2) rfl
  have hpc : par.wt < cV.wt := cp_wt_get (vs := [par, cpOutV res logs, .nat s]) (j := 0) rfl
  have hoc : (cpOutV res logs).wt < cV.wt :=
    cp_wt_get (vs := [par, cpOutV res logs, .nat s]) (j := 1) rfl
  have hsc : (Val.nat s).wt < cV.wt := cp_wt_get (vs := [par, cpOutV res logs, .nat s]) (j := 2) rfl
  have h0o : (Val.list (res.map resV)).wt < (cpOutV res logs).wt :=
    cp_wt_get (vs := [.list (res.map resV), .list (logs.map cpLogV)]) (j := 0) rfl
  have h1o : (Val.list (logs.map cpLogV)).wt < (cpOutV res logs).wt :=
    cp_wt_get (vs := [.list (res.map resV), .list (logs.map cpLogV)]) (j := 1) rfl
  have hrw : (Val.list [gpV r.1, gpV r.2]).wt < (Val.list (res.map resV)).wt := cp_wt_get hrget
  have hlw : (Val.list [tsV k l.1, .list (l.2.1.map cpSgV), .list (l.2.2.map cpSgV)]).wt <
      (Val.list (logs.map cpLogV)).wt := cp_wt_get hlget
  have hpzw : (gpV pz).wt < (Val.list [gpV r.1, gpV r.2]).wt := by
    rw [hpzd, cpSel_map s gpV r.1 r.2]; exact cp_wt_get (cpSel_get hs _ _)
  have hstw : (Val.list (stg.map cpSgV)).wt <
      (Val.list [tsV k l.1, .list (l.2.1.map cpSgV), .list (l.2.2.map cpSgV)]).wt := by
    rw [hstgd, cpSel_map s (fun x : List (CpStgD k L.q) => Val.list (x.map cpSgV))]
    exact cp_wt_get (cpSel_get1 hs _ _ _)
  have htw : (tsV k l.1).wt <
      (Val.list [tsV k l.1, .list (l.2.1.map cpSgV), .list (l.2.2.map cpSgV)]).wt :=
    cp_wt_get (vs := [tsV k l.1, .list (l.2.1.map cpSgV), .list (l.2.2.map cpSgV)]) (j := 0) rfl
  have hkw : (natList (ptsKey (labPts k (tlist l.1)))).wt < (tsV k l.1).wt :=
    cp_wt_get (vs := [indT l.1, natList (ptsKey (labPts k (tlist l.1)))]) (j := 1) rfl
  set pvs : List Val := [sv, .list [.nat k, .nat L.q], gpV gp, .nat (Fintype.card S.dom), .nat D,
    encPts osA, pSplitCtx k L.q, .nat (k + L.q)] with hpvs
  have hpe : par = .list pvs := rfl
  have hkqw : (Val.list [.nat k, .nat L.q]).wt < par.wt := cp_wt_get (vs := pvs) (j := 1) rfl
  have hDw : (Val.nat D).wt < par.wt := cp_wt_get (vs := pvs) (j := 4) rfl
  have hosw : (encPts osA).wt < par.wt := cp_wt_get (vs := pvs) (j := 5) rfl

  have hsle : (Val.nat s).wt ≤ 3 := (wt_nat_le s).trans (by omega)
  -- the reads
  have g0 := fun rest : List Val => Det.arg' (P := Pg) (vs := [cV, .nat i, gpV qs0]) (rest := rest)
    (j := 0) (v := .list [par, cpOutV res logs, .nat s]) rfl
  have gO := fun rest : List Val => Det.get' (g0 rest) (Det.nat 1)
    (v := .list [.list (res.map resV), .list (logs.map cpLogV)]) rfl
  have gP := fun rest : List Val => Det.get' (g0 rest) (Det.nat 0) (v := .list pvs) rfl
  have gS := fun rest : List Val => Det.get' (g0 rest) (Det.nat 2) (v := .nat s) rfl
  have gI := fun rest : List Val => Det.arg' (P := Pg) (vs := [cV, .nat i, gpV qs0])
    (rest := rest) (j := 1) (v := .nat i) rfl
  have gKQ := fun rest : List Val => Det.get' (gP rest) (Det.nat 1)
    (v := .list [.nat k, .nat L.q]) rfl
  have gD := fun rest : List Val => Det.get' (gP rest) (Det.nat 4) (v := .nat D) rfl
  have gOs := fun rest : List Val => Det.get' (gP rest) (Det.nat 5) (v := encPts osA) rfl
  have dpz := Det.get' (Det.get' (Det.get' (gO []) (Det.nat 0) (v := .list (res.map resV)) rfl)
    (gI []) hrget) (gS []) (v := gpV pz) (by rw [hpzd, cpSel_map s gpV]; exact cpSel_get hs _ _)
  set lgv := Val.list [tsV k l.1, .list (l.2.1.map cpSgV), .list (l.2.2.map cpSgV)] with hlgv
  have dlg := Det.get' (Det.get' (gO [gpV pz]) (Det.nat 1) (v := .list (logs.map cpLogV)) rfl)
    (gI [gpV pz]) hlget
  have hstget : [tsV k l.1, Val.list (l.2.1.map cpSgV), Val.list (l.2.2.map cpSgV)][s + 1]? =
      some (.list (stg.map cpSgV)) := by
    rw [hstgd, cpSel_map s (fun x : List (CpStgD k L.q) => Val.list (x.map cpSgV))]
    exact cpSel_get1 hs _ _ _
  have dOs := Det.mk3 (Det.nat (P := Pg) (env := [A, gpV pz, lgv]) 0)
    (Det.get' (Det.var' (P := Pg) (env := [A, gpV pz, lgv]) (i := 2) rfl)
      (Det.arith' (op := .add) (gS [gpV pz, lgv]) (Det.nat 1) (z := s + 1) rfl) hstget)
    (gOs [gpV pz, lgv])
  set osv := encPts (oL.map (domPos e L.q)) with hosv
  have hosvw : osv.wt ≤ 10 * (k + L.q + 1) ^ 2 := cp_wt_pts (by rw [List.length_map]; exact hoLl)
  have dKey := Det.get' (Det.get' (Det.var' (P := Pg) (env := [A, gpV pz, lgv, osv]) (i := 2) rfl)
    (Det.nat 0) (v := .list [indT l.1, natList (ptsKey (labPts k (tlist l.1)))]) rfl) (Det.nat 1)
    (v := natList (ptsKey (labPts k (tlist l.1)))) rfl
  have dCin := Det.mk5 (gKQ [gpV pz, lgv, osv])
    (Det.var' (P := Pg) (env := [A, gpV pz, lgv, osv]) (i := 1) rfl) Det.nil dKey
    (gD [gpV pz, lgv, osv])
  set cf := cardFix (phiT S.domGroup πd l.1) (grp (cpPhi S πd l.1) (dstr S z)
    (Fintype.card S.dom)) ∅ with hcf
  have hcfD : cf ≤ D := by
    rw [hcf, ← hD]; unfold cardFix; exact card_img_le πd _
  have hcfw : (Val.nat cf).wt ≤ D + 2 := (wt_nat_le cf).trans (by omega)
  have dCnd := Det.arith' (op := .eq) (Det.var' (P := Pg) (env := [A, gpV pz, lgv, osv, .nat cf])
    (i := 4) rfl) (gD [gpV pz, lgv, osv, .nat cf]) (z := if cf = D then 1 else 0) rfl
  have hb1 : Pg.HasAt (cpInc b + 1) (imgCardFuns (cpInc b + 1) jp) := hat.inc.block 1 (by rfl)
  have hgrp : grp (cpPhi S πd l.1) (dstr S z) (Fintype.card S.dom) ≤ Pgrp S.domGroup πd l.1 :=
    grp_le _ _ _
  -- the weights
  have w12 : (k + L.q + 1) ^ 2 ≤ (k + L.q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  have w4 : (k + L.q + 1) ^ 4 ≤ (k + L.q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  have hW' : 10 ^ 10 * (k + L.q + 1) ^ 12 ≤ W := by omega
  have w1 : 1 ≤ (k + L.q + 1) ^ 12 := Nat.one_le_pow _ _ (by omega)
  have elg : (Val.list [tsV k l.1, .list (l.2.1.map cpSgV), .list (l.2.2.map cpSgV)]).wt =
    lgv.wt := rfl
  have ets : (Val.list [indT l.1, natList (ptsKey (labPts k (tlist l.1)))]).wt = (tsV k l.1).wt :=
    rfl
  have enil : (Val.list []).wt = 4 := wt_list_nil
  have eA : (Val.list [cV, .nat i, gpV qs0]).wt = A.wt := rfl
  have ecV : (Val.list [par, cpOutV res logs, .nat s]).wt = cV.wt := rfl
  have ep : (Val.list pvs).wt = par.wt := rfl
  have eo : (Val.list [.list (res.map resV), .list (logs.map cpLogV)]).wt =
    (cpOutV res logs).wt := rfl
  have hsgw := cp_wt_lg hstgl
  have w3o := wt_list3_le (.nat 0) (.list (stg.map cpSgV)) (encPts osA)
  have := wt_nat_le 0
  have w5 := cp_wt_list5_le (.list [.nat k, .nat L.q]) (gpV pz) (.list [])
    (natList (ptsKey (labPts k (tlist l.1)))) (.nat D)
  have hR : ∀ x : ℕ, x ≤ 100 * A.wt + 3 * D + 1000 * (k + L.q + 1) ^ 12 + 200 →
      x ≤ 40 * (W + 20) := fun x hx => by omega
  refine CpFB.intro hfz.step ?_
  unfold cpFzStepE
  -- the branch of a full test set
  have hT : (if cf = D then 1 else 0) ≠ 0 →
      CpEB Pg [A, gpV pz, lgv, osv, .nat cf]
        (.letE (.call (cpStab b) (mk3 (.get (.get (arg 0) (.nat 0)) (.nat 1)) (.var 1) (.var 3)))
          (.call (cpApp b) (mk2 (arg 2) (.var 5)))) W
        ((40 * (W + 20) + cpG hst hpre hm W + W + 1) +
          (40 * (W + 20) + cpG hst hpre hm W + W + 1) + W + 1)
        (CpFzInv e S L πd logs z (i + 1)) := by
    intro hx
    have hcfe : cf = D := by by_contra h; exact hx (if_neg h)
    have hfull : IsFull (cpPhi S πd l.1) (dstr S z) :=
      (cp_isFull_iff πd l.1 (dstr S z)).2 (by rw [hD]; exact hcfe)
    have dSt := Det.mk3 (gKQ [gpV pz, lgv, osv, .nat cf])
      (Det.var' (P := Pg) (env := [A, gpV pz, lgv, osv, .nat cf]) (i := 1) rfl)
      (Det.var' (P := Pg) (env := [A, gpV pz, lgv, osv, .nat cf]) (i := 3) rfl)
    have w3s := wt_list3_le (.list [.nat k, .nat L.q]) (gpV pz) osv
    refine CpEB.letE (CpEB.call (CpEB.det dSt (hR _ (by omega)) (by omega)
      (Q := fun v => v = .list [.list [.nat k, .nat L.q], gpV pz, osv]) rfl) fun v hv _ => by
        subst hv
        exact cp_bud_stabP hst hpre hm hat.stab hjp hpzl
          (by rw [List.length_map]; omega) hW') ?_
    rintro qv ⟨qs, rfl, hql, hqcl⟩ hqw
    have hK := cp_pairGens_full πd hpz hoLm hqcl
    have dAp := Det.mk2 (Det.arg' (P := Pg) (vs := [cV, .nat i, gpV qs0])
        (rest := [gpV pz, lgv, osv, .nat cf, gpV qs]) (j := 2) (v := gpV qs0) rfl)
      (Det.var' (P := Pg) (env := [A, gpV pz, lgv, osv, .nat cf, gpV qs]) (i := 5) rfl)
    have hqsw := cp_wt_gp hql
    have w2a := wt_list2_le (gpV qs0) (gpV qs)
    refine CpEB.call (CpEB.det dAp (hR _ (by omega)) (by omega)
      (Q := fun v => v = .list [gpV qs0, gpV qs]) rfl) fun v hv _ => ?_
    subst hv
    refine CpFB.mono (cp_bud_app hst hpre hm hat.app (qs0.map pairV) (qs.map pairV)
      (by omega) (by
        have : (gpV qs0).wt = (Val.list (qs0.map pairV)).wt := rfl
        have : (gpV qs).wt = (Val.list (qs.map pairV)).wt := rfl
        unfold gpV at w2a; omega)) le_rfl ?_
    rintro w rfl
    refine ⟨qs0 ++ qs, by simp [gpV], ?_, ?_, ?_⟩
    · rw [List.length_append]
      have : (i + 1 + 1) * (k + L.q) ^ 2 = (i + 1) * (k + L.q) ^ 2 + (k + L.q) ^ 2 := by ring
      omega
    · intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact hq0G p hp
      · exact cp_fst_mem_G hK hp
    · rw [cp_gens_fst_append, hq0g, cp_gens_lift hK,
        cpFzGrp_succ_full πd _ z i (by rw [hTi]; exact hfull), hTi]
  -- the branch of a test set that is not full
  have hE : (if cf = D then 1 else 0) = 0 →
      CpEB Pg [A, gpV pz, lgv, osv, .nat cf] (arg 2) W (40 * (W + 20))
        (CpFzInv e S L πd logs z (i + 1)) := by
    intro hx
    have hcfe : cf ≠ D := by intro h; rw [if_pos h] at hx; exact one_ne_zero hx
    have hnf : ¬ IsFull (cpPhi S πd l.1) (dstr S z) := fun h =>
      hcfe (by rw [← hD]; exact (cp_isFull_iff πd l.1 (dstr S z)).1 h)
    refine CpEB.det (Det.arg' (P := Pg) (vs := [cV, .nat i, gpV qs0])
        (rest := [gpV pz, lgv, osv, .nat cf]) (j := 2) (v := gpV qs0) rfl)
      (hR _ (by omega)) (by omega) ⟨qs0, rfl, ?_, hq0G, ?_⟩
    · exact hq0l.trans (Nat.mul_le_mul_right _ (by omega))
    · rw [cpFzGrp_succ_not πd _ z i (by rw [hTi]; exact hnf)]; exact hq0g
  have hIte := (CpEB.ite dCnd hT hE).mono (C' := 40 * (W + 20) +
      ((40 * (W + 20) + cpG hst hpre hm W + W + 1) +
        (40 * (W + 20) + cpG hst hpre hm W + W + 1) + W + 1) + 40 * (W + 20) + W + 1)
    (by have : (if cf = D then 1 else 0) ≤ 1 := by split_ifs <;> omega
        omega) fun _ h => h
  -- the order of the image
  have hCard := CpEB.letE (W := W) (CpEB.call (CpEB.det dCin (hR _ (by omega)) (by omega)
      (Q := fun v => v = .list [.list [.nat k, .nat L.q], gpV pz, .list [],
        natList (ptsKey (labPts k (tlist l.1))), .nat D]) rfl) fun v hv _ => by
      subst hv
      exact CpFB.det (cp_bud_card (W := W) hst hpre hm hb1 hjp ctx.hπ hgrp hpz hpzl hD.le (by omega))
        le_rfl (by rw [← hcf]; omega) (Q := fun v => v = .nat cf) rfl)
    (fun v hv _ => by subst hv; exact hIte)
  -- the points outside
  have hOs := CpEB.letE (W := W) (CpEB.call (CpEB.det dOs (hR _ (by omega)) (by omega)
      (Q := fun v => v = .list [.nat 0, .list (stg.map cpSgV), encPts osA]) rfl) fun v hv _ => by
      subst hv
      rw [hosA]
      exact cp_fz_out (W := W) hst hpre hm hat hfz hosL hstgl hil
        (fun j h1 h2 => ⟨(hinc2 j h1 h2).1, cp_os_length_le e (hinc2 j h1 h2).2⟩) hW'
        (by rw [← hosA]; omega))
    (fun v hv _ => by subst hv; exact hCard)
  have hLg := CpEB.letE (W := W) (CpEB.det dlg (hR _ (by omega)) (by omega) (Q := fun v => v = lgv) rfl)
    (fun v hv _ => by subst hv; exact hOs)
  refine (CpEB.letE (CpEB.det dpz (hR _ (by omega)) (by omega) (Q := fun v => v = gpV pz) rfl)
    (fun v hv _ => by subst hv; exact hLg)).mono ?_ fun _ h => h
  unfold cpFzStepB
  omega

end Step

end GI.Impl
