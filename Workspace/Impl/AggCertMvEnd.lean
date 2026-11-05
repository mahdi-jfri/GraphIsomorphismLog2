module

public import Workspace.Impl.AggCertMods

@[expose] public section

/-!
# The move program: the end of a string

At `t = n` the loop of the current string is over. The function `cpEndF` (at `b + 2`)

* for `x`: starts the loop of `y` (`cp_x_end_rep`);
* for `y` with more test sets: computes `P_T` of the next one (`ptGraph_spec`), drops it from the
  list (`tail`) and starts it (`cp_y_end_cons_rep`);
* for `y` and the last test set: returns the results (`cp_y_end_nil_post`).

`cp_end_spec` says that it returns what a move must return (`CpMvPost`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens PointwiseStab Preimage Membership)

/-- The entries of `kst`. -/
noncomputable def CpSt.vals {k q : ℕ} (par : Val) (σ : CpSt k q) (inner : Val) : List Val :=
  [par, .list (σ.Ts.map (tsV k)), boolVal σ.s, .list (σ.res.map resV),
    .list (σ.cache.map ckEntV), gpV σ.p0, gpV σ.px, .nat σ.t, gpV σ.ps, encPts σ.osP, inner,
    tsV k σ.T, .list (σ.lz.map cpSgV), .list (σ.lx.map cpSgV), .list (σ.logs.map cpLogV)]

theorem CpSt.val_eq {k q : ℕ} (par : Val) (σ : CpSt k q) (inner : Val) :
    σ.val par inner = .list (σ.vals par inner) := rfl

section Gen

variable {k : ℕ} {Ω C : Type} {e : Ω ≃ Fin k} {S : State Ω C} [Fintype S.dom]

theorem cpAll_length {q : ℕ} {osA : List (Fin (k + q))} (h : CpAll e S q osA) : osA.length ≤ k := by
  obtain ⟨os, hnd, -, rfl⟩ := h
  rw [List.length_map]
  exact cp_os_length_le e hnd

end Gen

/-- `cp_mkList` with the value given in another form. -/
theorem cp_mkList' {P : Program} {env : List Val} {W : ℕ} (ps : List (Expr × Val)) {c : ℕ}
    {v : Val} (hv : Val.list (ps.map Prod.snd) = v) (h : ∀ p ∈ ps, Det P env p.1 p.2 c)
    (hw : v.wt ≤ W) :
    Det P env (Expr.mkList (ps.map Prod.fst)) v (ps.length * (c + W + 1) + 5) :=
  hv ▸ cp_mkList ps h (hv ▸ hw)

/-- **The weight of a new program state with an empty `inner` and `u = 0`.** -/
theorem cp_wt_new {k q D NT M₀ Bw : ℕ} {par : Val} {σ : CpSt k q} (hlen : CpLen D σ)
    (hlog : CpLogLen σ) (hTs : σ.Ts.length ≤ NT) (hres : σ.res.length ≤ NT) (hc : σ.cache.length ≤ M₀)
    (hBw : cpBw k q par.wt NT M₀ D ≤ Bw) :
    (Val.list [σ.val par (.list []), .nat 0]).wt ≤ Bw := by
  refine (cp_wt_state hlen hlog hTs hres hc cp_wt_empty_inner ?_).trans hBw
  have : 1 ≤ (k + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have := wt_nat_le 0
  omega

section End

variable {k : ℕ} {Ω C : Type} [Finite Ω] [DecidableEq Ω] {e : Ω ≃ Fin k} {c : C → ℕ}
  {S : State Ω C} [Fintype S.dom] {L : GiantLabels S}
  {πd : S.domGroup →* alternatingGroup (Fin L.q)}
  (hst : PointwiseStab) (hpre : Preimage) (hm : Membership)

omit [Finite Ω] [DecidableEq Ω] [Fintype S.dom] in
/-- The results after the loop of `y`, read from `kst`. -/
theorem cp_resE_det {P : Program} {W : ℕ} {par u : Val} {σ : CpSt k L.q} {inner : Val}
    (hwW : (Val.list [σ.val par inner, u]).wt ≤ W)
    (hrW : (Val.list ((σ.res ++ [(σ.px, σ.ps)]).map resV)).wt ≤ W) (rest : List Val) :
    Det P (.list [σ.val par inner, u] :: rest) cpResE
      (.list ((σ.res ++ [(σ.px, σ.ps)]).map resV)) (20 * (W + 20)) := by
  have hv : σ.val par inner = .list (σ.vals par inner) := rfl
  rw [hv] at hwW ⊢
  have h0 : (Val.list [.list (σ.vals par inner), u] :: rest)[0]? =
    some (.list [.list (σ.vals par inner), u]) := rfl
  have e1 : (σ.res ++ [(σ.px, σ.ps)]).map resV = σ.res.map resV ++ [.list [gpV σ.px, gpV σ.ps]] := by
    simp [resV]
  rw [e1] at hrW ⊢
  have hx := wt_le_wt_list (vs := σ.res.map resV ++ [.list [gpV σ.px, gpV σ.ps]])
    (v := .list [gpV σ.px, gpV σ.ps]) (by simp)
  refine (Det.snoc (cp_rdK (P := P) h0 hwW (j := 3) rfl (by omega))
    (Det.mk2 (cp_rdK (P := P) h0 hwW (j := 6) rfl (by omega))
      (cp_rdK (P := P) h0 hwW (j := 8) rfl (by omega)))).mono ?_
  omega

omit [Finite Ω] [DecidableEq Ω] [Fintype S.dom] in
/-- The logs after the loop of `y`, read from `kst`. -/
theorem cp_logsE_det {P : Program} {W : ℕ} {par u : Val} {σ : CpSt k L.q} {inner : Val}
    (hwW : (Val.list [σ.val par inner, u]).wt ≤ W)
    (hrW : (Val.list ((σ.logs ++ [(σ.T, σ.lx, σ.lz)]).map cpLogV)).wt ≤ W) (rest : List Val) :
    Det P (.list [σ.val par inner, u] :: rest) cpLogsE
      (.list ((σ.logs ++ [(σ.T, σ.lx, σ.lz)]).map cpLogV)) (20 * (W + 20)) := by
  have hv : σ.val par inner = .list (σ.vals par inner) := rfl
  rw [hv] at hwW ⊢
  have h0 : (Val.list [.list (σ.vals par inner), u] :: rest)[0]? =
    some (.list [.list (σ.vals par inner), u]) := rfl
  have e1 : (σ.logs ++ [(σ.T, σ.lx, σ.lz)]).map cpLogV =
      σ.logs.map cpLogV ++ [.list [tsV k σ.T, .list (σ.lx.map cpSgV), .list (σ.lz.map cpSgV)]] := by
    simp [cpLogV]
  rw [e1] at hrW ⊢
  have hx := wt_le_wt_list (vs := σ.logs.map cpLogV ++
    [.list [tsV k σ.T, .list (σ.lx.map cpSgV), .list (σ.lz.map cpSgV)]])
    (v := .list [tsV k σ.T, .list (σ.lx.map cpSgV), .list (σ.lz.map cpSgV)]) (by simp)
  refine (Det.snoc (cp_rdK (P := P) h0 hwW (j := 14) rfl (by omega))
    (Det.mk3 (cp_rdK (P := P) h0 hwW (j := 11) rfl (by omega))
      (cp_rdK (P := P) h0 hwW (j := 13) rfl (by omega))
      (cp_rdK (P := P) h0 hwW (j := 12) rfl (by omega)))).mono ?_
  omega

set_option maxHeartbeats 4000000 in
/-- **The end of a string.** -/
theorem cp_end_spec {Pg : Program} {b jp jpre jm : ℕ} (hat : CpMvAt Pg b jp jpre jm)
    (hjpre : Pg.prims[jpre]? = some (preimagePrim hpre))
    {sv : Val} {gp : GPairs k L.q} {osA : List (Fin (k + L.q))} {D : ℕ}
    (ctx : CpCtx e c S L πd sv gp osA D) {NT M₀ Bw W : ℕ}
    (hBw : cpBw k L.q (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA)).wt NT M₀ D
      ≤ Bw) (hW : 10 ^ 4 * (Bw + 2) ^ 2 ≤ W)
    {m f : ℕ} {σ : CpSt k L.q} {acc : List (StagePair S)} {T : Finset (Fin L.q)}
    {rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))}
    (h : CpRoundInv e πd σ acc T rec) (hT : T = σ.T)
    (hm' : m = cpMeas (Fintype.card S.dom) D (.round acc T σ.Ts σ.s σ.t)) (hmf : m ≤ f)
    (hM : σ.cache.length + m ≤ M₀) (hNT : σ.res.length + σ.Ts.length + 1 ≤ NT)
    (hlen : CpLen D σ) (ht : σ.t = Fintype.card S.dom) {u : Val}
    (hst' : (Val.list [σ.val (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA))
      (.list []), u]).wt ≤ Bw) :
    CpFB Pg (b + 2) (.list [σ.val (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA))
        (.list []), u]) W (2 * cpG hst hpre hm W + 1100 * (W + 20))
      (CpMvPost e S L πd (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA)) D Bw M₀
        NT m ((fun R => cpAt S πd (dstr S S.x) (dstr S S.y) R (.round acc T σ.Ts σ.s σ.t)) ''
          Cands rec) f) := by
  set par := cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA) with hpar
  obtain ⟨hW1, hW2, -, hW4, hW5⟩ := cp_W_facts hBw hW
  have hwW0 : (Val.list [σ.val par (.list []), u]).wt ≤ W := by omega
  set ks := σ.vals par (.list []) with hks
  have hsv : σ.val par (.list []) = .list ks := rfl
  have hwW : (Val.list [.list ks, u]).wt ≤ W := by rw [← hsv]; omega
  have hksW : (Val.list ks).wt < W :=
    lt_of_lt_of_le (cp_wt_get (vs := [.list ks, u]) (j := 0) rfl) hwW
  have hp0 : ks[0]? = some (.list [sv, .list [.nat k, .nat L.q], gpV gp,
    .nat (Fintype.card S.dom), .nat D, encPts osA, pSplitCtx k L.q, .nat (k + L.q)]) := rfl
  have hos := cpAll_length ctx.hosA
  have hlen0 := hlen
  obtain ⟨hlt, hlo, hl0, hlx, hlp, hlr, hlc⟩ := hlen
  have hres : σ.res.length ≤ NT := by omega
  have hTsl : σ.Ts.length ≤ NT := by omega
  have hc : σ.cache.length ≤ M₀ := by omega
  refine CpFB.intro hat.fin ?_
  rw [hsv]
  unfold cpEndF
  have h0 : ∀ rest : List Val, (Val.list [.list ks, u] :: rest)[0]? = some (.list [.list ks, u]) :=
    fun _ => rfl
  refine (CpEB.ite (cp_rdK (P := Pg) (h0 []) hwW (j := 2) (v := boolVal σ.s) rfl (by omega))
    (Ct := 2 * cpG hst hpre hm W + 700 * (W + 20)) (Ce := 300 * (W + 20)) ?_ ?_).mono
    (by omega) fun _ h => h
  · -- the loop of `y` is over
    intro hs
    have hs' : σ.s = true := by cases hσ : σ.s <;> simp_all
    have hTsW : (Val.list (σ.Ts.map (tsV k))).wt < W :=
      (cp_wt_get (vs := ks) (j := 1) rfl).trans hksW
    refine (CpEB.ite (Det.length (cp_rdK (P := Pg) (h0 []) hwW (j := 1)
      (v := .list (σ.Ts.map (tsV k))) rfl (by omega)))
      (Ct := 2 * cpG hst hpre hm W + 500 * (W + 20)) (Ce := 100 * (W + 20)) ?_ ?_).mono
      (by have := length_lt_wt_list (σ.Ts.map (tsV k)); omega) fun _ h => h
    · -- more test sets
      intro hne
      obtain ⟨T', Ts', hTs⟩ : ∃ T' Ts', σ.Ts = T' :: Ts' := by
        cases hT' : σ.Ts with
        | nil => simp [hT'] at hne
        | cons T' Ts' => exact ⟨T', Ts', rfl⟩
      have hTsv : Val.list (σ.Ts.map (tsV k)) = .list (tsV k T' :: Ts'.map (tsV k)) := by
        rw [hTs, List.map_cons]
      have hTsW' : (Val.list (tsV k T' :: Ts'.map (tsV k))).wt < W := by rw [← hTsv]; exact hTsW
      have hT'W : (tsV k T').wt < W := (cp_wt_get (vs := tsV k T' :: Ts'.map (tsV k)) (j := 0)
        rfl).trans hTsW'
      have hparW : par.wt < W := (cp_wt_get (vs := ks) (j := 0) rfl).trans hksW
      -- the argument of the call of `P_T`
      have dA : Det Pg [.list [.list ks, u]] (mk3 (cpPf 1) (cpPf 2)
          (.get (.get (cpKf 1) (.nat 0)) (.nat 0)))
          (.list [.list [.nat k, .nat L.q], gpV gp, indT T']) (20 * (W + 20)) := by
        have r1 := cp_rdP (P := Pg) (h0 []) hwW hp0 (j := 1) (v := .list [.nat k, .nat L.q]) rfl
          (by omega)
        have r2 := cp_rdP (P := Pg) (h0 []) hwW hp0 (j := 2) (v := gpV gp) rfl (by omega)
        have hiW : (indT T').wt < W :=
          (cp_wt_get (vs := [indT T', natList (ptsKey (labPts k (tlist T')))]) (j := 0)
            rfl).trans hT'W
        have r3 : Det Pg [.list [.list ks, u]] (.get (.get (cpKf 1) (.nat 0)) (.nat 0)) (indT T')
            (5 * (W + 20)) :=
          Det.rd (a := 4) (Det.rd (a := 3) (cp_rdK (P := Pg) (h0 []) hwW (j := 1)
            (v := .list (tsV k T' :: Ts'.map (tsV k))) (by rw [← hTsv]; rfl) (by omega)) le_rfl
            rfl hT'W.le (by omega)) le_rfl rfl hiW.le (by omega)
        refine (Det.mk3 r1 r2 r3).mono ?_
        have := wt_list3_le (.list [.nat k, .nat L.q]) (gpV gp) (indT T')
        have := cp_wt_get (vs := [sv, .list [.nat k, .nat L.q], gpV gp, .nat (Fintype.card S.dom),
          .nat D, encPts osA, pSplitCtx k L.q, .nat (k + L.q)]) (j := 1) rfl
        have := cp_wt_get (vs := [sv, .list [.nat k, .nat L.q], gpV gp, .nat (Fintype.card S.dom),
          .nat D, encPts osA, pSplitCtx k L.q, .nat (k + L.q)]) (j := 2) rfl
        have := cp_wt_ts (k := k) T'
        have := cp_wt_gp ctx.hgpl
        have : (k + L.q + 1) ^ 4 ≤ (k + L.q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
        have : (k + L.q + 1) ^ 2 ≤ (k + L.q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
        have : (Val.list [.nat k, .nat L.q]).wt ≤ par.wt := by
          have := cp_wt_get (vs := [sv, .list [.nat k, .nat L.q], gpV gp,
            .nat (Fintype.card S.dom), .nat D, encPts osA, pSplitCtx k L.q, .nat (k + L.q)])
            (j := 1) rfl
          exact this.le
        omega
      have hAW : (Val.list [.list [.nat k, .nat L.q], gpV gp, indT T']).wt ≤ W := by
        have := wt_list3_le (.list [.nat k, .nat L.q]) (gpV gp) (indT T')
        have : (indT T').wt < (tsV k T').wt :=
          cp_wt_get (vs := [indT T', natList (ptsKey (labPts k (tlist T')))]) (j := 0) rfl
        have := cp_wt_ts (k := k) T'
        have := cp_wt_gp ctx.hgpl
        have : (k + L.q + 1) ^ 4 ≤ (k + L.q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
        have : (k + L.q + 1) ^ 2 ≤ (k + L.q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
        have : (Val.list [.nat k, .nat L.q]).wt ≤ par.wt :=
          (cp_wt_get (vs := [sv, .list [.nat k, .nat L.q], gpV gp,
            .nat (Fintype.card S.dom), .nat D, encPts osA, pSplitCtx k L.q, .nat (k + L.q)])
            (j := 1) rfl).le
        omega
      refine (CpEB.letE (CpEB.call (CpEB.det dA le_rfl hAW (Q := fun v =>
          v = .list [.list [.nat k, .nat L.q], gpV gp, indT T']) rfl)
        fun v hv _ => hv ▸ cp_bud_pt hst hpre hm hat.pt hjpre ctx.hgp ctx.hgpl πd ctx.hπ T' hW2)
        (Cb := cpG hst hpre hm W + 400 * (W + 20)) fun p0v hp0v hp0W => ?_).mono
        (by omega) fun _ h => h
      obtain ⟨p0, rfl, hp0l, hp0g⟩ := hp0v
      -- the remaining test sets
      have h0' : ∀ rest : List Val, (Val.list [.list ks, u] :: gpV p0 :: rest)[0]? =
          some (.list [.list ks, u]) := fun _ => rfl
      refine (CpEB.letE (CpEB.call (CpEB.det (cp_rdK (P := Pg) (h0' []) hwW (j := 1)
          (v := .list (tsV k T' :: Ts'.map (tsV k))) (by rw [← hTsv]; rfl) (by omega)) le_rfl
          hTsW'.le (Q := fun v => v = .list (tsV k T' :: Ts'.map (tsV k))) rfl)
        fun v hv hvW => hv ▸ cp_bud_tail hst hpre hm hat.tail _ _ (hv ▸ hvW))
        (Cb := 350 * (W + 20)) fun tv htv htW => ?_).mono (by omega) fun _ h => h
      subst htv
      -- the new program state
      set σ' := σ.next T' Ts' p0 osA with hσ'
      have hlen' : CpLen D σ' := by
        refine ⟨by simp [hσ', CpSt.next], by simpa [hσ', CpSt.next] using hos, hp0l, hlx, hp0l,
          ?_, hlc⟩
        intro r hr
        simp only [hσ', CpSt.next, List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | rfl
        · exact hlr r hr
        · exact ⟨hlx, hlp⟩
      have hNT' : σ'.res.length ≤ NT ∧ σ'.Ts.length ≤ NT := by
        simp only [hσ', CpSt.next, List.length_append, List.length_singleton]
        rw [hTs, List.length_cons] at hNT
        omega
      have hR' := h.y_end_cons hT hs' ht hTs hp0g ctx.hosA
      have hnew := cp_wt_new (par := par) hlen' hR'.loglen hNT'.2 hNT'.1 hc hBw
      have hK : (σ'.val par (.list [])).wt < Bw :=
        lt_of_lt_of_le (cp_wt_get (vs := [σ'.val par (.list []), .nat 0]) (j := 0) rfl) hnew
      obtain ⟨m', Ss', hlt', hsub, hrep⟩ := cp_y_end_cons_rep h hm' hmf hM hNT hs' ht hTs hT hp0g
        ctx.hosA hlen' hnew
      have hlW : (Val.list ((σ.logs ++ [(σ.T, σ.lx, σ.lz)]).map cpLogV)).wt ≤ W := by
        have := cp_wt_get (vs := σ'.vals par (.list [])) (j := 14)
          (v := .list ((σ.logs ++ [(σ.T, σ.lx, σ.lz)]).map cpLogV)) rfl
        have hK' : (Val.list (σ'.vals par (.list []))).wt < Bw := hK
        omega
      have hrW : (Val.list ((σ.res ++ [(σ.px, σ.ps)]).map resV)).wt ≤ W := by
        have := cp_wt_get (vs := σ'.vals par (.list [])) (j := 3)
          (v := .list ((σ.res ++ [(σ.px, σ.ps)]).map resV)) rfl
        have hK' : (Val.list (σ'.vals par (.list []))).wt < Bw := hK
        omega
      have h1 : ∀ rest : List Val, (Val.list [.list ks, u] :: rest)[0]? =
          some (.list [.list ks, u]) := fun _ => rfl
      set env := [Val.list [.list ks, u], gpV p0, .list (Ts'.map (tsV k))] with henv
      have dK := cp_mkList' (P := Pg) (env := env) (W := W) (c := 20 * (W + 20))
        (v := σ'.val par (.list []))
        [(cpKf 0, par), (.var 2, .list (Ts'.map (tsV k))), (.nat 0, .nat 0),
          (cpResE, .list ((σ.res ++ [(σ.px, σ.ps)]).map resV)),
          (cpKf 4, .list (σ.cache.map ckEntV)), (.var 1, gpV p0), (cpKf 6, gpV σ.px),
          (.nat 0, .nat 0), (.var 1, gpV p0), (cpPf 5, encPts osA), (.nil, .list []),
          (.get (cpKf 1) (.nat 0), tsV k T'), (.nil, .list []), (.nil, .list []),
          (cpLogsE, .list ((σ.logs ++ [(σ.T, σ.lx, σ.lz)]).map cpLogV))] rfl (by
          intro p hp
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl
          · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 0) rfl (by omega)).mono (by omega)
          · exact (Det.rv (P := Pg) (env := env) (i := 2) rfl htW).mono (by omega)
          · exact (Det.nat 0).mono (by omega)
          · have := cp_resE_det (P := Pg) (par := par) (σ := σ) (inner := .list []) (u := u)
              hwW0 hrW [gpV p0, .list (Ts'.map (tsV k))]
            exact this
          · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 4) rfl (by omega)).mono (by omega)
          · exact (Det.rv (P := Pg) (env := env) (i := 1) rfl hp0W).mono (by omega)
          · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 6) rfl (by omega)).mono (by omega)
          · exact (Det.nat 0).mono (by omega)
          · exact (Det.rv (P := Pg) (env := env) (i := 1) rfl hp0W).mono (by omega)
          · exact (cp_rdP (P := Pg) (h1 _) hwW hp0 (j := 5) rfl (by omega)).mono (by omega)
          · exact Det.nil.mono (by omega)
          · exact (Det.rd (a := 3) (cp_rdK (P := Pg) (h1 _) hwW (j := 1)
              (v := .list (tsV k T' :: Ts'.map (tsV k))) (by rw [← hTsv]; rfl) (by omega)) le_rfl
              rfl hT'W.le (by omega)).mono (by omega)
          · exact Det.nil.mono (by omega)
          · exact Det.nil.mono (by omega)
          · exact cp_logsE_det (P := Pg) (par := par) (σ := σ) (inner := .list []) (u := u)
              hwW0 hlW [gpV p0, .list (Ts'.map (tsV k))])
        (show (σ'.val par (.list [])).wt ≤ W by omega)
      refine CpEB.det (Det.mk2 (Det.nat 2) (Det.mk2 dK (Det.nat 0))) ?_ ?_
        (Or.inr ⟨m', _, Ss', hlt', hsub, hrep, rfl⟩)
      · have := wt_list2_le (σ'.val par (.list [])) (.nat 0)
        have := wt_list2_le (.nat 2) (.list [σ'.val par (.list []), .nat 0])
        have : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
        have : (Val.nat 2).wt ≤ 4 := wt_nat_le 2
        simp only [List.length_cons, List.length_nil]
        omega
      · have := wt_list2_le (σ'.val par (.list [])) (.nat 0)
        have := wt_list2_le (.nat 2) (.list [σ'.val par (.list []), .nat 0])
        have : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
        have : (Val.nat 2).wt ≤ 4 := wt_nat_le 2
        omega
    · -- the last test set: the output
      intro he
      have hTs : σ.Ts = [] := by simpa using he
      have hrB : (Val.list ((σ.res ++ [(σ.px, σ.ps)]).map resV)).wt ≤ 9 * Bw + 14 := by
        have e1 : (σ.res ++ [(σ.px, σ.ps)]).map resV =
            σ.res.map resV ++ [.list [gpV σ.px, gpV σ.ps]] := by simp [resV]
        rw [e1]
        have := wt_list_snoc_le (σ.res.map resV) (.list [gpV σ.px, gpV σ.ps])
        have := wt_list2_le (gpV σ.px) (gpV σ.ps)
        have hk : (Val.list ks).wt < Bw :=
          lt_of_lt_of_le (cp_wt_get (vs := [.list ks, u]) (j := 0) rfl) (by rw [← hsv]; exact hst')
        have := cp_wt_get (vs := ks) (j := 3) (v := .list (σ.res.map resV)) rfl
        have := cp_wt_get (vs := ks) (j := 6) (v := gpV σ.px) rfl
        have := cp_wt_get (vs := ks) (j := 8) (v := gpV σ.ps) rfl
        omega
      have hlB : (Val.list ((σ.logs ++ [(σ.T, σ.lx, σ.lz)]).map cpLogV)).wt ≤ 13 * Bw + 30 := by
        have e1 : (σ.logs ++ [(σ.T, σ.lx, σ.lz)]).map cpLogV =
            σ.logs.map cpLogV ++ [cpLogV (σ.T, σ.lx, σ.lz)] := by simp
        have e2 : cpLogV (σ.T, σ.lx, σ.lz) =
          .list [tsV k σ.T, .list (σ.lx.map cpSgV), .list (σ.lz.map cpSgV)] := rfl
        rw [e1, e2]
        have := wt_list_snoc_le (σ.logs.map cpLogV)
          (.list [tsV k σ.T, .list (σ.lx.map cpSgV), .list (σ.lz.map cpSgV)])
        have := wt_list3_le (tsV k σ.T) (.list (σ.lx.map cpSgV)) (.list (σ.lz.map cpSgV))
        have hk : (Val.list ks).wt < Bw :=
          lt_of_lt_of_le (cp_wt_get (vs := [.list ks, u]) (j := 0) rfl) (by rw [← hsv]; exact hst')
        have := cp_wt_get (vs := ks) (j := 14) (v := .list (σ.logs.map cpLogV)) rfl
        have := cp_wt_get (vs := ks) (j := 11) (v := tsV k σ.T) rfl
        have := cp_wt_get (vs := ks) (j := 13) (v := .list (σ.lx.map cpSgV)) rfl
        have := cp_wt_get (vs := ks) (j := 12) (v := .list (σ.lz.map cpSgV)) rfl
        omega
      have := wt_list2_le (.list ((σ.res ++ [(σ.px, σ.ps)]).map resV))
        (.list ((σ.logs ++ [(σ.T, σ.lx, σ.lz)]).map cpLogV))
      have := wt_list2_le (.nat 0) (.list [.list ((σ.res ++ [(σ.px, σ.ps)]).map resV),
        .list ((σ.logs ++ [(σ.T, σ.lx, σ.lz)]).map cpLogV)])
      have : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
      have hpost := cp_y_end_nil_post (μ := measure P₀ .giant S)
        (Rep := fun st Ss f => ∃ m, CpRep e πd par D Bw M₀ NT m st Ss f) (f := f) h hs' ht hTs (by
          intro r hr
          rcases List.mem_append.1 hr with hr | hr
          · exact hlr r hr
          · rw [List.mem_singleton.1 hr]; exact ⟨hlx, hlp⟩)
      subst hT
      refine CpEB.det (Det.mk2 (Det.nat 0) (Det.mk2 (cp_resE_det (P := Pg) hwW0 (by omega) [])
        (cp_logsE_det (P := Pg) hwW0 (by omega) []))) ?_ (by omega) (Or.inl hpost)
      omega
  · -- the loop of `x` is over: start `y`
    intro hs
    have hs' : σ.s = false := by cases hσ : σ.s <;> simp_all
    set σ' := σ.yStart osA with hσ'
    have hlen' : CpLen D σ' := ⟨by simp [hσ', CpSt.yStart], by simpa [hσ', CpSt.yStart] using hos,
      hl0, hlp, hl0, hlr, hlc⟩
    have hnew := cp_wt_new (par := par) hlen' (h.x_end hs' ht ctx.hosA).loglen hTsl hres hc hBw
    obtain ⟨m', Ss', hlt', hsub, hrep⟩ := cp_x_end_rep h hm' hmf hM hNT hs' ht ctx.hosA hT hlen' hnew
    have dK := cp_mkList' (P := Pg) (env := [.list [.list ks, u]]) (W := W) (c := 4 * (W + 20))
      (v := σ'.val par (.list []))
      [(cpKf 0, par), (cpKf 1, .list (σ.Ts.map (tsV k))), (.nat 1, .nat 1),
        (cpKf 3, .list (σ.res.map resV)), (cpKf 4, .list (σ.cache.map ckEntV)), (cpKf 5, gpV σ.p0),
        (cpKf 8, gpV σ.ps), (.nat 0, .nat 0), (cpKf 5, gpV σ.p0), (cpPf 5, encPts osA),
        (.nil, .list []), (cpKf 11, tsV k σ.T), (.nil, .list []),
        (cpKf 12, .list (σ.lz.map cpSgV)), (cpKf 14, .list (σ.logs.map cpLogV))] rfl (by
        intro p hp
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl
        · exact (cp_rdK (P := Pg) (h0 _) hwW (j := 0) rfl (by omega)).mono (by omega)
        · exact (cp_rdK (P := Pg) (h0 _) hwW (j := 1) rfl (by omega)).mono (by omega)
        · exact (Det.nat 1).mono (by omega)
        · exact (cp_rdK (P := Pg) (h0 _) hwW (j := 3) rfl (by omega)).mono (by omega)
        · exact (cp_rdK (P := Pg) (h0 _) hwW (j := 4) rfl (by omega)).mono (by omega)
        · exact (cp_rdK (P := Pg) (h0 _) hwW (j := 5) rfl (by omega)).mono (by omega)
        · exact (cp_rdK (P := Pg) (h0 _) hwW (j := 8) rfl (by omega)).mono (by omega)
        · exact (Det.nat 0).mono (by omega)
        · exact (cp_rdK (P := Pg) (h0 _) hwW (j := 5) rfl (by omega)).mono (by omega)
        · exact (cp_rdP (P := Pg) (h0 _) hwW hp0 (j := 5) rfl (by omega)).mono (by omega)
        · exact Det.nil.mono (by omega)
        · exact (cp_rdK (P := Pg) (h0 _) hwW (j := 11) rfl (by omega)).mono (by omega)
        · exact Det.nil.mono (by omega)
        · exact (cp_rdK (P := Pg) (h0 _) hwW (j := 12) rfl (by omega)).mono (by omega)
        · exact (cp_rdK (P := Pg) (h0 _) hwW (j := 14) rfl (by omega)).mono (by omega))
      (by
        have := cp_wt_get (vs := [σ'.val par (.list []), .nat 0]) (j := 0) rfl
        omega)
    have := wt_list2_le (σ'.val par (.list [])) (.nat 0)
    have := wt_list2_le (.nat 2) (.list [σ'.val par (.list []), .nat 0])
    have : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
    have : (Val.nat 2).wt ≤ 4 := wt_nat_le 2
    refine CpEB.det (Det.mk2 (Det.nat 2) (Det.mk2 dK (Det.nat 0))) ?_ (by omega)
      (Or.inr ⟨m', _, Ss', hlt', hsub, hrep, rfl⟩)
    simp only [List.length_cons, List.length_nil]
    omega

end End

end GI.Impl
