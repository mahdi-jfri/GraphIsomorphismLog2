module

public import Workspace.Impl.AggCertMvKey

@[expose] public section

/-!
# The move program: the first window call of a round

`cpStartF` (at `b + 3`) runs on `[kst, incP]` when the increment `incP` of the round is
nonempty. It computes, in order,

* the kernel `ker(φ_T|_A)` in graph form (`graphStabP_spec`, `pairGens_kernelIn`);
* the cache key `[⟨A⟩, ⟨ker⟩]` (`pEncMap_spec`, `mkGroup_spec`);
* the index found by the cache lookup (`ckFind_spec`);
* the representatives and the new cache (`cp_reps_spec`);
* the window group (`kr_spec`, `groupValC_of_kr`), the window indicator (`cp_ind_spec`) and the
  window colors of the first representative (`wp_spec`);
* the remaining representatives (`tail`);

and returns the first window call with the new program state. `cp_round_start` says what this
output stands for. `cp_start_spec` is the result used later (by `cp_round_spec`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens PointwiseStab Preimage Membership)
open GI.Machine (BinOp)


section Start

variable {k : ℕ} {Ω C : Type} [Finite Ω] [DecidableEq Ω] {e : Ω ≃ Fin k} {c : C → ℕ}
  {S : State Ω C} [Fintype S.dom] {L : GiantLabels S}
  {πd : S.domGroup →* alternatingGroup (Fin L.q)}
  (hst : PointwiseStab) (hpre : Preimage) (hm : Membership)

/-- **The first window call of a round.** On `[kst, incP]`, with `incP` the nonempty increment
of the round, the program returns the first window call and the new program state. -/
theorem cp_start_spec {Pg : Program} {b jp jpre jm : ℕ} (hat : CpMvAt Pg b jp jpre jm)
    (hjp : Pg.prims[jp]? = some (pointwiseStabPrim hst))
    (hjm : Pg.prims[jm]? = some (membershipPrim hm))
    {sv : Val} {gp : GPairs k L.q} {osA : List (Fin (k + L.q))} {D : ℕ}
    (ctx : CpCtx e c S L πd sv gp osA D) {NT M₀ Bw W : ℕ}
    (hBw : cpBw k L.q (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA)).wt NT M₀ D
      ≤ Bw) (hW : 10 ^ 4 * (Bw + 2) ^ 2 ≤ W)
    {m f : ℕ} {σ : CpSt k L.q} {acc : List (StagePair S)} {T : Finset (Fin L.q)}
    {rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))}
    (h : CpRoundInv e πd σ acc T rec) (hT : T = σ.T)
    (hm' : m = cpMeas (Fintype.card S.dom) D (.round acc T σ.Ts σ.s σ.t)) (hmf : m ≤ f)
    (hM : σ.cache.length + m ≤ M₀) (hNT : σ.res.length + σ.Ts.length + 1 ≤ NT)
    (hlen : CpLen D σ) {incl : List S.dom} (hnd : incl.Nodup)
    (hinc : ∀ v, v ∈ incl ↔ v ∈ inc (cpPhi S πd T) (dstr S (cpZ S σ.s)) σ.t) (hne : incl ≠ [])
    (ht : σ.t < Fintype.card S.dom) :
    CpFB Pg (b + 3) (.list [σ.val (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp)
        (encPts osA)) (.list []), encPts (incl.map (domPos e L.q))]) W
      (16 * cpG hst hpre hm W + 7000 * (W + 20))
      (CpMvPost e S L πd (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA)) D Bw M₀
        NT m ((fun R => cpAt S πd (dstr S S.x) (dstr S S.y) R
          (.round acc T σ.Ts σ.s σ.t)) '' Cands rec) f) := by
  have hcan := ctx.canon
  obtain ⟨gv0, dv0, xv, yv, hv, rv, hgv0, hdv0, hxv, hyv, hhv, hrv, hsv⟩ := ctx.canon.val
  subst hsv
  subst hT
  set par := cpParV k L.q (Fintype.card S.dom) D (.list [.nat k, gv0, dv0, xv, yv, hv, rv,
    boolVal S.floor, .nat S.h, .nat S.N]) (gpV gp) (encPts osA) with hpar
  obtain ⟨hW1, hW2, hW3, hW4, hW5⟩ := cp_W_facts hBw hW
  have hlen0 := hlen
  obtain ⟨hlt, hlo, hl0, hlx, hlp, hlr, hlc⟩ := hlen
  obtain ⟨f1, f2, f3, f24, f46, e4, e6, f8, f9, f66⟩ := cp_pow_facts k L.q
  have hk12 : k + L.q + 1 ≤ (k + L.q + 1) ^ 12 := Nat.le_self_pow (by omega) _
  have w612 : (k + L.q + 1) ^ 6 ≤ (k + L.q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  -- the size `Y` of the part of `Bw` that does not depend on `par`
  have hBwY : 4 * par.wt + 10 ^ 6 * ((NT + M₀ + 1) * (D + 1) * (k + L.q + 1) ^ 6) ≤ Bw := by
    have e1 : cpBw k L.q par.wt NT M₀ D =
        4 * par.wt + 10 ^ 6 * ((NT + M₀ + 1) * (D + 1) * (k + L.q + 1) ^ 6) := by
      unfold cpBw; ring
    omega
  have hY6 : (k + L.q + 1) ^ 6 ≤ (NT + M₀ + 1) * (D + 1) * (k + L.q + 1) ^ 6 := by
    exact Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (by omega))
  have hYM : M₀ + 1 ≤ (NT + M₀ + 1) * (D + 1) * (k + L.q + 1) ^ 6 := by
    have a1 : 1 ≤ (D + 1) * (k + L.q + 1) ^ 6 := Nat.mul_pos (by omega) (by omega)
    have a2 : (NT + M₀ + 1) * (D + 1) * (k + L.q + 1) ^ 6 =
      (NT + M₀ + 1) * ((D + 1) * (k + L.q + 1) ^ 6) := by ring
    rw [a2]
    exact (show M₀ + 1 ≤ NT + M₀ + 1 by omega).trans (Nat.le_mul_of_pos_right _ a1)
  have hkst := cp_wt_kst (par := par) (inner := .list []) (NT := NT) (M₀ := M₀) hlen0 h.loglen (by omega) (by omega) (by omega)
    cp_wt_empty_inner
  have e5 : 10 ^ 5 * (NT + M₀ + 1) * (D + 1) * (k + L.q + 1) ^ 6 =
    10 ^ 5 * ((NT + M₀ + 1) * (D + 1) * (k + L.q + 1) ^ 6) := by ring
  generalize hYd : (NT + M₀ + 1) * (D + 1) * (k + L.q + 1) ^ 6 = Y at hBwY hY6 hYM hkst e5
  have hres : σ.res.length ≤ NT := by omega
  have hTsl : σ.Ts.length ≤ NT := by omega
  have hc0 : σ.cache.length ≤ M₀ := by omega
  -- the program state and the argument
  set ks := σ.vals par (.list []) with hks
  have hsv : σ.val par (.list []) = .list ks := rfl
  have hksY : (Val.list ks).wt ≤ 2 * par.wt + 10 ^ 5 * Y := by
    have h1 : (Val.list ks).wt = (σ.val par (.list [])).wt := rfl
    rw [h1]
    rw [e5] at hkst
    exact hkst
  have hinl : incl.length ≤ k := cp_os_length_le e hnd
  set iV := encPts (incl.map (domPos e L.q)) with hiV
  have hiVw : iV.wt ≤ 10 * (k + L.q + 1) ^ 2 := cp_wt_pts (by rw [List.length_map]; exact hinl)
  have hwA : (Val.list [.list ks, iV]).wt ≤ Bw := by
    have := wt_list2_le (.list ks) iV
    omega
  have hwW : (Val.list [.list ks, iV]).wt ≤ W := by omega
  have hp0 : ks[0]? = some (.list [.list [.nat k, gv0, dv0, xv, yv, hv, rv, boolVal S.floor,
    .nat S.h, .nat S.N], .list [.nat k, .nat L.q], gpV gp, .nat (Fintype.card S.dom), .nat D,
    encPts osA, pSplitCtx k L.q, .nat (k + L.q)]) := rfl
  have hs0 : [Val.list [.nat k, gv0, dv0, xv, yv, hv, rv, boolVal S.floor, .nat S.h, .nat S.N],
    .list [.nat k, .nat L.q], gpV gp, .nat (Fintype.card S.dom), .nat D,
    encPts osA, pSplitCtx k L.q, .nat (k + L.q)][0]? = some (.list [.nat k, gv0, dv0, xv, yv, hv,
      rv, boolVal S.floor, .nat S.h, .nat S.N]) := rfl
  have h0 : ∀ rest : List Val, (Val.list [.list ks, iV] :: rest)[0]? =
      some (.list [.list ks, iV]) := fun _ => rfl
  have hksW : (Val.list ks).wt < W :=
    lt_of_lt_of_le (cp_wt_get (vs := [.list ks, iV]) (j := 0) rfl) hwW
  refine CpFB.intro hat.start ?_
  rw [hsv]
  unfold cpStartF
  -- the kernel in graph form
  have hA := grp_le (cpPhi S πd σ.T) (dstr S (cpZ S σ.s)) σ.t
  have hx0W : (natList (ptsKey (labPts k (tlist σ.T)))).wt < W :=
    ((cp_wt_get (vs := [indT σ.T, natList (ptsKey (labPts k (tlist σ.T)))]) (j := 1) rfl).trans
      (cp_wt_get (vs := ks) (j := 11) rfl)).trans hksW
  have hargS : (Val.list [.list [.nat k, .nat L.q], gpV σ.ps,
      natList (ptsKey (labPts k (tlist σ.T)))]).wt ≤ W := by
    have := cp_wt_gp hlp
    have := cp_wt_ts (k := k) (q := L.q) σ.T
    have := cp_wt_get (vs := [indT σ.T, natList (ptsKey (labPts k (tlist σ.T)))]) (j := 1)
      (v := natList (ptsKey (labPts k (tlist σ.T)))) rfl
    have := wt_nat_le k; have := wt_nat_le L.q
    have := wt_list2_le (.nat k) (.nat L.q)
    have := wt_list3_le (.list [.nat k, .nat L.q]) (gpV σ.ps)
      (natList (ptsKey (labPts k (tlist σ.T))))
    have : (k + L.q + 1) ^ 4 ≤ (k + L.q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
    unfold tsV at *
    omega
  have dS := Det.mk3 (cp_rdP (P := Pg) (h0 []) hwW hp0 (j := 1) (v := .list [.nat k, .nat L.q]) rfl
      (by omega)) (cp_rdK (P := Pg) (h0 []) hwW (j := 8) (v := gpV σ.ps) rfl (by omega))
    (Det.rd (a := 3) (j := 1) (cp_rdK (P := Pg) (h0 []) hwW (j := 11) (v := tsV k σ.T) rfl
      (by omega)) le_rfl rfl hx0W.le (by omega))
  have hbS := cp_bud_kstab hst hpre hm hat.stab hjp ctx.hπ hA h.ps hlp hW2
  refine (CpEB.letE (CpEB.call (CpEB.det dS le_rfl hargS (Q := fun v => v = .list [.list [.nat k,
      .nat L.q], gpV σ.ps, natList (ptsKey (labPts k (tlist σ.T)))]) rfl) fun v hv _ => hv ▸ hbS)
    (Cb := 15 * cpG hst hpre hm W + 6000 * (W + 20)) fun nv hnv hnW => ?_).mono
    (by omega) fun _ h => h
  obtain ⟨ns, rfl, hnl, hns⟩ := hnv
  -- the cache key
  have hkey := cp_key_eb hst hpre hm hat (env := [.list [.list ks, iV], gpV ns]) (h0 _) hwW hp0
    hs0 (k := k) (q := L.q) rfl rfl rfl rfl hlp hnl hW2
  refine (CpEB.letE hkey (Cb := 10 * cpG hst hpre hm W + 5500 * (W + 20))
    fun kv hkv hkW => ?_).mono (by omega) fun _ h => h
  subst hkv
  -- weights of the pieces
  have hcacheW : (Val.list (σ.cache.map ckEntV)).wt < (Val.list ks).wt :=
    cp_wt_get (vs := ks) (j := 4) rfl
  have hkeyB : (ckKeyV σ.ps ns).wt ≤ 1500 * (k + L.q + 1) ^ 6 := by
    have := cp_wt_encGroupPairs (k := k) (q := L.q) hlp
    have := cp_wt_encGroupPairs (k := k) (q := L.q) hnl
    have := wt_list2_le (encGroup (σ.ps.map encPair)) (encGroup (ns.map encPair))
    unfold ckKeyV; omega
  have hY1 : 1 ≤ Y := by
    have : 1 ≤ (k + L.q + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
    omega
  set env1 := [Val.list [.list ks, iV], gpV ns, ckKeyV σ.ps ns] with henv1
  have hargF : (Val.list [ckKeyV σ.ps ns, .list (σ.cache.map ckEntV)]).wt ≤ W := by
    have := wt_list2_le (ckKeyV σ.ps ns) (.list (σ.cache.map ckEntV))
    omega
  have dF := Det.mk2 (Det.rv (P := Pg) (env := env1) (i := 2) rfl hkW)
    (cp_rdK (P := Pg) (h0 _) hwW (j := 4) (v := .list (σ.cache.map ckEntV)) rfl (by omega))
  refine (CpEB.letE (CpEB.call (CpEB.det dF le_rfl hargF
      (Q := fun v => v = .list [ckKeyV σ.ps ns, .list (σ.cache.map ckEntV)]) rfl)
    fun v hv hvw => hv ▸ cp_bud_find hst hpre hm hat.find hjm σ.ps ns σ.cache (hv ▸ hvw))
    (Cb := 9 * cpG hst hpre hm W + 5400 * (W + 20)) fun iv hiv hiW => ?_).mono
    (by omega) fun _ h => h
  subst hiv
  -- the representatives and the new cache
  set i := σ.cache.findIdx (ckTest σ.ps ns) with hi
  have hil : i ≤ σ.cache.length := List.findIdx_le_length
  have hargR : (Val.list [σ.val par (.list []), ckKeyV σ.ps ns, .nat i]).wt ≤ 4 * Bw := by
    have := wt_list3_le (σ.val par (.list [])) (ckKeyV σ.ps ns) (.nat i)
    have := wt_nat_le i
    have h1 : (σ.val par (.list [])).wt = (Val.list ks).wt := rfl
    omega
  have hRs := cp_reps_spec hst hpre hm hat ctx hBw hW (σ := σ) (acc := acc) h hlen0 hns hnl hargR
  set env2 := env1 ++ [Val.nat i] with henv2
  have dR := Det.mk3 (cp_rdKs (P := Pg) (env := env2) (h0 _) hwW)
    (Det.rv (P := Pg) (env := env2) (i := 2) rfl hkW) (Det.rv (P := Pg) (env := env2) (i := 3) rfl hiW)
  have hargR' : (Val.list [Val.list ks, ckKeyV σ.ps ns, .nat i]).wt ≤ W := by
    have h2 : (Val.list [Val.list ks, ckKeyV σ.ps ns, .nat i]).wt ≤ 4 * Bw := hargR
    omega
  refine (CpEB.letE (CpEB.call (CpEB.det dR le_rfl hargR'
      (Q := fun v => v = .list [σ.val par (.list []), ckKeyV σ.ps ns, .nat i]) rfl)
    fun v hv _ => hv ▸ hRs)
    (Cb := 4 * cpG hst hpre hm W + 5000 * (W + 20)) fun rv hrv hrW => ?_).mono
    (by omega) fun _ h => h
  obtain ⟨as0, c', rec', rfl, hc', hsub, hcl, hmem, hG, hD, hent⟩ := hrv
  have hne0 : as0 ≠ [] := by
    intro h0'
    have := cp_reps_ne_nil (hc'.1.2.2 _ hmem)
    simp [h0'] at this
  obtain ⟨a, as, rfl⟩ := List.exists_cons_of_ne_nil hne0
  set aV : Val := .list ((a :: as).map encPerm) with haV
  set rV : Val := .list [aV, .list (c'.map ckEntV)] with hrV
  have haVW : aV.wt < W := lt_of_lt_of_le (cp_wt_get (vs := [aV, .list (c'.map ckEntV)]) (j := 0) rfl) hrW
  have haW : (encPerm a).wt < W :=
    lt_trans (cp_wt_get (vs := (a :: as).map encPerm) (j := 0) rfl) haVW
  set env3 := env2 ++ [rV] with henv3
  have hr4 : env3[4]? = some rV := rfl
  have h3 : ∀ rest : List Val, (env3 ++ rest)[0]? = some (.list [.list ks, iV]) := fun _ => rfl
  -- the window group
  have hnW' : (gpV ns).wt ≤ 50 * (k + L.q + 1) ^ 4 := cp_wt_gp hnl
  have w4 : (k + L.q + 1) ^ 4 ≤ (k + L.q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  have hkK := wt_nat_le k
  have hargK : (Val.list [.nat k, gpV ns]).wt ≤ W := by
    have := wt_list2_le (.nat k) (gpV ns); omega
  have dK := Det.mk2 (cp_rdS (P := Pg) (env := env3) (h0 _) hwW hp0 hs0 (j := 0) rfl (by omega))
    (Det.rv (P := Pg) (env := env3) (i := 1) rfl hnW)
  refine (CpEB.letE (CpEB.call (CpEB.det dK le_rfl hargK
      (Q := fun v => v = .list [.nat k, gpV ns]) rfl)
    fun v hv _ => hv ▸ cp_bud_kr hst hpre hm hat.kr hjp hnl hW2)
    (Cb := 3 * cpG hst hpre hm W + 4800 * (W + 20)) fun gv hgv hgW => ?_).mono
    (by omega) fun _ h => h
  obtain ⟨hs, rfl, hsg, hsl⟩ := hgv
  have hgvC := groupValC_of_kr (S.liftGroup_le _) hns hsg hsl
  -- the window indicator
  have hiVW' : iV.wt ≤ W := by omega
  have hargI : (Val.list [.nat k, iV]).wt ≤ W := by
    have := wt_list2_le (.nat k) iV; omega
  set env4 := env3 ++ [encGroup hs] with henv4
  have dI := Det.mk2 (cp_rdS (P := Pg) (env := env4) (h0 _) hwW hp0 hs0 (j := 0) rfl (by omega))
    (Det.rd (a := 1) (j := 1) (Det.rv (P := Pg) (env := env4) (i := 0) rfl hwW) le_rfl rfl hiVW'
      (by omega))
  refine (CpEB.letE (CpEB.call (CpEB.det dI le_rfl hargI
      (Q := fun v => v = .list [.nat k, iV]) rfl)
    fun v hv _ => hv ▸ cp_ind_spec hst hpre hm hat (q := L.q) (e := e) hnd hinl hW2)
    (Cb := 2 * cpG hst hpre hm W + 4500 * (W + 20)) fun dv hdv hdW => ?_).mono
    (by omega) fun _ h => h
  have hset : {v | v ∈ incl} = ((inc (cpPhi S πd σ.T) (dstr S (cpZ S σ.s)) σ.t : Finset S.dom) :
      Set S.dom) := by
    ext v; simp [hinc]
  rw [hset] at hdv
  -- the window colors of `a`
  have hz : ColorVal e c (if σ.s then yv else xv) (cpZ S σ.s) := by
    cases σ.s <;> simpa [cpStr]
  have hcode : ∀ v, c (cpZ S σ.s v) < 2 * k := by
    intro v; cases σ.s
    · exact (hcan.colors v).1
    · exact (hcan.colors v).2
  have hksW' : (Val.list ks).wt < W := hksW
  have hdv0W : dv0.wt < W := by
    have := cp_wt_get (vs := ks) (j := 0) hp0
    have := cp_wt_get hs0
    have := cp_wt_get (vs := [.nat k, gv0, dv0, xv, yv, hv, rv, boolVal S.floor, .nat S.h,
      .nat S.N]) (j := 2) rfl
    omega
  have hzW : (if σ.s then yv else xv).wt < W := by
    have := cp_wt_get (vs := ks) (j := 0) hp0
    have := cp_wt_get hs0
    have := cp_wt_get (vs := [.nat k, gv0, dv0, xv, yv, hv, rv, boolVal S.floor, .nat S.h,
      .nat S.N]) (j := 3) rfl
    have := cp_wt_get (vs := [.nat k, gv0, dv0, xv, yv, hv, rv, boolVal S.floor, .nat S.h,
      .nat S.N]) (j := 4) rfl
    split_ifs <;> omega
  have hAW : (Val.list [dv0, if σ.s then yv else xv, encPerm a]).wt ≤ W := by
    have := wt_list3_le dv0 (if σ.s then yv else xv) (encPerm a)
    have h1 : (Val.list ks).wt + 1 ≤ (Val.list [.list ks, iV]).wt := cp_wt_get (vs := [.list ks, iV]) (j := 0) rfl
    have := cp_wt_get (vs := ks) (j := 0) hp0
    have := cp_wt_get hs0
    have := cp_wt_get (vs := [.nat k, gv0, dv0, xv, yv, hv, rv, boolVal S.floor, .nat S.h,
      .nat S.N]) (j := 2) rfl
    have := cp_wt_get (vs := [.nat k, gv0, dv0, xv, yv, hv, rv, boolVal S.floor, .nat S.h,
      .nat S.N]) (j := 3) rfl
    have := cp_wt_get (vs := [.nat k, gv0, dv0, xv, yv, hv, rv, boolVal S.floor, .nat S.h,
      .nat S.N]) (j := 4) rfl
    have hsW : (if σ.s then yv else xv).wt < (Val.list [.nat k, gv0, dv0, xv, yv, hv, rv,
      boolVal S.floor, .nat S.h, .nat S.N]).wt := by split_ifs <;> omega
    have hsvP : (Val.list [.nat k, gv0, dv0, xv, yv, hv, rv, boolVal S.floor, .nat S.h,
        .nat S.N]).wt < par.wt := cp_wt_get (vs := [Val.list [.nat k, gv0, dv0, xv, yv, hv, rv,
          boolVal S.floor, .nat S.h, .nat S.N], .list [.nat k, .nat L.q], gpV gp,
          .nat (Fintype.card S.dom), .nat D, encPts osA, pSplitCtx k L.q, .nat (k + L.q)]) (j := 0)
          rfl
    have := wt_encPerm_le a
    have : (k + 1) ^ 2 ≤ (k + L.q + 1) ^ 12 :=
      (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  have hW2' : 10 ^ 10 * (k + 1) ^ 12 ≤ W := by
    have : (k + 1) ^ 12 ≤ (k + L.q + 1) ^ 12 := Nat.pow_le_pow_left (by omega) 12
    omega
  set env5 := env4 ++ [dv] with henv5
  have dA := Det.mk3 (cp_rdS (P := Pg) (env := env5) (h0 _) hwW hp0 hs0 (j := 2) (v := dv0) rfl
      (by omega))
    (cp_zv_det (P := Pg) (env := env5) (h0 _) hwW hp0 hs0 (s := σ.s) rfl rfl rfl)
    (Det.rd (a := 2) (j := 0) (Det.rd (a := 1) (j := 0) (Det.rv (P := Pg) (env := env5) (i := 4)
      rfl hrW) le_rfl rfl haVW.le (by omega)) (by omega) rfl haW.le (by omega))
  refine (CpEB.letE (CpEB.call (CpEB.det dA le_rfl hAW
      (Q := fun v => v = .list [dv0, if σ.s then yv else xv, encPerm a]) rfl)
    fun v hv _ => hv ▸ cp_bud_wp hst hpre hm hat hdv0 (cpZ S σ.s) hz hcode a hW2')
    (Cb := cpG hst hpre hm W + 4200 * (W + 20)) fun wv hwv hwvW => ?_).mono
    (by omega) fun _ h => h
  subst hwv
  -- the remaining representatives
  set env6 := env5 ++ [.list [natList (winCodesX e c S (cpZ S σ.s) a),
    natList (winCodesY e c S (cpZ S σ.s) a)]] with henv6
  have dT := Det.rd (a := 1) (j := 0) (Det.rv (P := Pg) (env := env6) (i := 4) rfl hrW) le_rfl
    rfl haVW.le (by omega)
  refine (CpEB.letE (CpEB.call (CpEB.det dT le_rfl haVW.le
      (Q := fun v => v = .list (encPerm a :: as.map encPerm)) rfl)
    fun v hv hvw => hv ▸ cp_bud_tail hst hpre hm hat.tail _ _ (hv ▸ hvw))
    (Cb := 3900 * (W + 20)) fun tv htv htW => ?_).mono (by omega) fun _ h => h
  subst htv
  -- the new program state
  set σ' : CpSt k L.q := { σ with cache := c' } with hσ'
  set inner' := cpInnerV as [] hs dv (incl.map (domPos e L.q)) a with hinner'
  have hfd : ∃ f : Fin k → ℕ, dv = encFun f ∧ ∀ i, f i ≤ 1 := by
    unfold DomVal at hdv
    exact ⟨_, hdv, fun i => by split_ifs <;> omega⟩
  obtain ⟨fd, hfd, hfd1⟩ := hfd
  have hDl : (a :: as).length ≤ D := hD
  have hin : CpInLen k L.q D inner' := by
    refine ⟨as, [], hs, fd, incl.map (domPos e L.q), a, by rw [hinner', hfd], ?_, hsl,
      hfd1, by rw [List.length_map]; exact hinl⟩
    simp only [List.length_nil, List.length_cons] at hDl ⊢
    have := Nat.mul_le_mul_right (k ^ 2 + 1) hDl
    omega
  have hlen' : CpLen D σ' := by
    unfold CpLen
    exact ⟨hlt, hlo, hl0, hlx, hlp, hlr, hent⟩
  have hm0 : 0 < m := by
    rw [hm']; simp only [cpMeas]; exact Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  have hc'M : σ'.cache.length ≤ M₀ := by
    show c'.length ≤ M₀
    omega
  have hIV := cp_wt_inner hin
  have hlog' : CpLogLen σ' := ⟨h.loglen.1, h.loglen.2, h.loglen.3, h.loglen.4⟩
  have hKS := cp_wt_state (par := par) hlen' hlog' hTsl hres hc'M hIV (u := .list [])
    (by simp only [wt_list_nil]; have : 1 ≤ (k + 1) ^ 6 := Nat.one_le_pow _ _ (by omega); omega)
  have hKV : (σ'.val par inner').wt < Bw :=
    lt_of_lt_of_le (cp_wt_get (vs := [σ'.val par inner', .list []]) (j := 0) rfl) (hKS.trans hBw)
  have hsvP : (Val.list [.nat k, gv0, dv0, xv, yv, hv, rv, boolVal S.floor, .nat S.h,
      .nat S.N]).wt < par.wt := cp_wt_get (vs := [Val.list [.nat k, gv0, dv0, xv, yv, hv, rv,
        boolVal S.floor, .nat S.h, .nat S.N], .list [.nat k, .nat L.q], gpV gp,
        .nat (Fintype.card S.dom), .nat D, encPts osA, pSplitCtx k L.q, .nat (k + L.q)]) (j := 0)
        rfl
  have hhvP := cp_wt_get (vs := [.nat k, gv0, dv0, xv, yv, hv, rv, boolVal S.floor, .nat S.h,
      .nat S.N]) (j := 5) (v := hv) rfl
  have hNP := cp_wt_get (vs := [.nat k, gv0, dv0, xv, yv, hv, rv, boolVal S.floor, .nat S.h,
      .nat S.N]) (j := 9) (v := .nat S.N) rfl
  have hhsI : (encGroup hs).wt < inner'.wt := cp_wt_get (vs := [.list (as.map encPerm),
      .list (([] : List (Perm (Fin k))).map encPerm), encGroup hs, dv,
      encPts (incl.map (domPos e L.q)), encPerm a]) (j := 2) rfl
  have hdvI : dv.wt < inner'.wt := cp_wt_get (vs := [.list (as.map encPerm),
      .list (([] : List (Perm (Fin k))).map encPerm), encGroup hs, dv,
      encPts (incl.map (domPos e L.q)), encPerm a]) (j := 3) rfl
  have hIVB : inner'.wt ≤ Bw := by
    have e1 : 10 ^ 4 * (D + 1) * (k + L.q + 1) ^ 6 ≤ 10 ^ 6 * (D + 1) * (k + L.q + 1) ^ 6 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))
    omega
  have hB6 : 10 ^ 6 ≤ Bw := by
    have : 1 ≤ (D + 1) * (k + L.q + 1) ^ 6 :=
      Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega)))
    have e1 : 10 ^ 6 * (D + 1) * (k + L.q + 1) ^ 6 = 10 ^ 6 * ((D + 1) * (k + L.q + 1) ^ 6) := by
      ring
    omega
  have hcx := cp_wt_codesX (e := e) (c := c) (S := S) (cpZ S σ.s) a
  have hcy := cp_wt_codesY (e := e) (c := c) (S := S) (cpZ S σ.s) a
  have hkk : k * (4 * k + 5) + 4 ≤ Bw := by
    have : k * (4 * k + 5) ≤ 5 * (k + L.q + 1) ^ 2 := by
      have e2 : (k + L.q + 1) * (5 * (k + L.q + 1)) = 5 * (k + L.q + 1) ^ 2 := by ring
      exact (Nat.mul_le_mul (show k ≤ k + L.q + 1 by omega)
        (show 4 * k + 5 ≤ 5 * (k + L.q + 1) by omega)).trans e2.le
    have : (k + L.q + 1) ^ 2 ≤ (k + L.q + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    have : (k + L.q + 1) ^ 6 ≤ (D + 1) * (k + L.q + 1) ^ 6 := Nat.le_mul_of_pos_left _ (by omega)
    have e1 : 10 ^ 6 * (D + 1) * (k + L.q + 1) ^ 6 = 10 ^ 6 * ((D + 1) * (k + L.q + 1) ^ 6) := by
      ring
    omega
  set WV := winVal' k (encGroup hs) dv (natList (winCodesX e c S (cpZ S σ.s) a))
    (natList (winCodesY e c S (cpZ S σ.s) a)) hv S.N with hWVd
  have hWV : WV.wt ≤ 21 * Bw + 14 := by
    rw [hWVd, winVal']
    refine (wt_list_le_of _ (c := Bw) ?_).trans (by simp only [List.length_cons, List.length_nil]; clear * -; omega)
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    have := wt_nat_le k; have := wt_nat_le 0; have := wt_nat_le 2
    have : (boolVal false).wt ≤ 2 := wt_nat_le 0
    have : k ≤ k * (4 * k + 5) := Nat.le_mul_of_pos_right _ (by omega)
    rcases hx with h | h | h | h | h | h | h | h | h | h <;> rw [h]
    all_goals first | omega | (simp; omega)
  have hWB : 10 ^ 4 * (Bw + 2) ≤ W := by
    have : Bw + 2 ≤ (Bw + 2) ^ 2 := Nat.le_self_pow (by omega) _
    omega
  have hl4 : 4 * (2 * (21 * Bw + 14) + 1) + 4 ≤ W := by omega
  have hTop : (Val.list [.nat 1, .nat (modeCode .cont), WV, σ'.val par inner']).wt ≤ W := by
    refine (wt_list_le_of _ (c := 21 * Bw + 14) ?_).trans ?_
    swap
    · simp only [List.length_cons, List.length_nil]
      omega
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    have := wt_nat_le 1; have := wt_nat_le (modeCode .cont)
    have : modeCode .cont = 1 := rfl
    rcases hx with rfl | rfl | rfl | rfl <;> omega
  set env := env6 ++ [.list (as.map encPerm)] with henv
  have h1 : ∀ rest : List Val, (env ++ rest)[0]? = some (.list [.list ks, iV]) := fun _ => rfl
  have h1' : env[0]? = some (.list [.list ks, iV]) := rfl
  have hasW : (Val.list (as.map encPerm)).wt ≤ W := htW
  have hgsW : (encGroup hs).wt ≤ W := hgW
  have dI := cp_mkList' (P := Pg) (env := env) (W := W) (c := 6 * (W + 20)) (v := inner')
    [(.var 8, .list (as.map encPerm)), (.nil, .list []), (.var 5, encGroup hs), (.var 6, dv),
      (GI.Lang.arg 1, iV), (.get (.get (.var 4) (.nat 0)) (.nat 0), encPerm a)] rfl (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (Det.rv (P := Pg) (env := env) (i := 8) rfl hasW).mono (by omega)
      · exact Det.nil.mono (by omega)
      · exact (Det.rv (P := Pg) (env := env) (i := 5) rfl hgsW).mono (by omega)
      · exact (Det.rv (P := Pg) (env := env) (i := 6) rfl hdW).mono (by omega)
      · exact (Det.rd (a := 1) (j := 1) (Det.rv (P := Pg) (env := env) (i := 0) rfl hwW) le_rfl
          rfl hiVW' (by omega)).mono (by omega)
      · exact (Det.rd (a := 2) (j := 0) (Det.rd (a := 1) (j := 0) (Det.rv (P := Pg) (env := env)
          (i := 4) rfl hrW) le_rfl rfl haVW.le (by omega)) (by omega) rfl haW.le (by omega)).mono
          (by omega)) (by omega)
  have hcV : (Val.list (c'.map ckEntV)).wt ≤ W :=
    (cp_wt_get (vs := [aV, .list (c'.map ckEntV)]) (j := 1) rfl).le.trans hrW
  have dKs := cp_mkList' (P := Pg) (env := env) (W := W) (c := 50 * (W + 20))
    (v := σ'.val par inner')
    [(cpKf 0, par), (cpKf 1, .list (σ.Ts.map (tsV k))), (cpKf 2, boolVal σ.s),
      (cpKf 3, .list (σ.res.map resV)), (.get (.var 4) (.nat 1), .list (c'.map ckEntV)),
      (cpKf 5, gpV σ.p0), (cpKf 6, gpV σ.px), (cpKf 7, .nat σ.t), (cpKf 8, gpV σ.ps),
      (cpKf 9, encPts σ.osP),
      (Expr.mkList [.var 8, .nil, .var 5, .var 6, GI.Lang.arg 1,
        .get (.get (.var 4) (.nat 0)) (.nat 0)], inner'),
      (cpKf 11, tsV k σ.T), (cpKf 12, .list (σ.lz.map cpSgV)), (cpKf 13, .list (σ.lx.map cpSgV)),
      (cpKf 14, .list (σ.logs.map cpLogV))] rfl (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl
      · exact (cp_rdK (P := Pg) h1' hwW (j := 0) rfl (by omega)).mono (by omega)
      · exact (cp_rdK (P := Pg) h1' hwW (j := 1) rfl (by omega)).mono (by omega)
      · exact (cp_rdK (P := Pg) h1' hwW (j := 2) rfl (by omega)).mono (by omega)
      · exact (cp_rdK (P := Pg) h1' hwW (j := 3) rfl (by omega)).mono (by omega)
      · exact (Det.rd (a := 1) (j := 1) (Det.rv (P := Pg) (env := env) (i := 4) rfl hrW) le_rfl
          rfl hcV (by omega)).mono (by omega)
      · exact (cp_rdK (P := Pg) h1' hwW (j := 5) rfl (by omega)).mono (by omega)
      · exact (cp_rdK (P := Pg) h1' hwW (j := 6) rfl (by omega)).mono (by omega)
      · exact (cp_rdK (P := Pg) h1' hwW (j := 7) rfl (by omega)).mono (by omega)
      · exact (cp_rdK (P := Pg) h1' hwW (j := 8) rfl (by omega)).mono (by omega)
      · exact (cp_rdK (P := Pg) h1' hwW (j := 9) rfl (by omega)).mono (by omega)
      · exact dI.mono (by simp only [List.length_cons, List.length_nil]; omega)
      · exact (cp_rdK (P := Pg) h1' hwW (j := 11) rfl (by omega)).mono (by omega)
      · exact (cp_rdK (P := Pg) h1' hwW (j := 12) rfl (by omega)).mono (by omega)
      · exact (cp_rdK (P := Pg) h1' hwW (j := 13) rfl (by omega)).mono (by omega)
      · exact (cp_rdK (P := Pg) h1' hwW (j := 14) rfl (by omega)).mono (by omega))
      (by omega)
  have hwpW : (Val.list [natList (winCodesX e c S (cpZ S σ.s) a),
      natList (winCodesY e c S (cpZ S σ.s) a)]).wt ≤ W := hwvW
  have dWv := cp_mkList' (P := Pg) (env := env) (W := W) (c := 6 * (W + 20)) (v := WV)
    [(cpSf 0, .nat k), (.var 5, encGroup hs), (.var 6, dv),
      (.get (.var 7) (.nat 0), natList (winCodesX e c S (cpZ S σ.s) a)),
      (.get (.var 7) (.nat 1), natList (winCodesY e c S (cpZ S σ.s) a)), (cpSf 5, hv),
      (.nil, .list []), (.nat 0, .nat 0), (.nat 2, .nat 2), (cpSf 9, .nat S.N)] rfl (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (cp_rdS (P := Pg) h1' hwW hp0 hs0 (j := 0) rfl (by omega)).mono (by omega)
      · exact (Det.rv (P := Pg) (env := env) (i := 5) rfl hgsW).mono (by omega)
      · exact (Det.rv (P := Pg) (env := env) (i := 6) rfl hdW).mono (by omega)
      · exact (Det.rd (a := 1) (j := 0) (Det.rv (P := Pg) (env := env) (i := 7) rfl hwpW) le_rfl
          rfl (by omega) (by omega)).mono (by omega)
      · exact (Det.rd (a := 1) (j := 1) (Det.rv (P := Pg) (env := env) (i := 7) rfl hwpW) le_rfl
          rfl (by omega) (by omega)).mono (by omega)
      · exact (cp_rdS (P := Pg) h1' hwW hp0 hs0 (j := 5) rfl (by omega)).mono (by omega)
      · exact Det.nil.mono (by omega)
      · exact (Det.nat 0).mono (by omega)
      · exact (Det.nat 2).mono (by omega)
      · exact (cp_rdS (P := Pg) h1' hwW hp0 hs0 (j := 9) rfl (by omega)).mono (by omega))
      (by omega)
  have hmc : modeCode .cont = 1 := rfl
  have dTop := cp_mkList' (P := Pg) (env := env) (W := W) (c := 900 * (W + 20))
    (v := .list [.nat 1, .nat (modeCode .cont), WV, σ'.val par inner'])
    [(.nat 1, .nat 1), (.nat (modeCode .cont), .nat (modeCode .cont)),
      (cpWinE (.var 5) (.var 6) (.var 7), WV),
      (Expr.mkList [cpKf 0, cpKf 1, cpKf 2, cpKf 3, .get (.var 4) (.nat 1), cpKf 5, cpKf 6, cpKf 7,
        cpKf 8, cpKf 9,
        Expr.mkList [.var 8, .nil, .var 5, .var 6, GI.Lang.arg 1,
          .get (.get (.var 4) (.nat 0)) (.nat 0)],
        cpKf 11, cpKf 12, cpKf 13, cpKf 14], σ'.val par inner')] rfl (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact (Det.nat 1).mono (by omega)
      · exact (Det.nat _).mono (by rw [hmc]; omega)
      · exact dWv.mono (by simp only [List.length_cons, List.length_nil]; omega)
      · exact dKs.mono (by simp only [List.length_cons, List.length_nil]; omega)) hTop
  have hne : inc (cpPhi S πd σ.T) (dstr S (cpZ S σ.s)) σ.t ≠ ∅ := by
    intro he
    obtain ⟨v, hv'⟩ := List.exists_mem_of_ne_nil incl hne
    have := (hinc v).1 hv'
    rw [he] at this
    simp at this
  have hwt : ∀ u', AnsC e u' (cpCall πd σ.T σ.s σ.t (domOfPos e S a)).answer →
      (Val.list [CpSt.val par σ' inner', u']).wt ≤ Bw := fun u' hu' =>
    (cp_wt_state hlen' hlog' hTsl hres hc'M hIV (cp_wt_ans hu')).trans hBw
  refine CpEB.det dTop ?_ hTop
    (Or.inl (cp_round_start ctx.inj hcan hhv ctx.good ctx.tr h ht hne hm' hmf hM hNT hc' hsub hcl
      hmem hG (by simp only [List.length_cons] at hDl; omega) hgvC hdv hnd hinc rfl hlen' hin hwt))
  simp only [List.length_cons, List.length_nil]
  omega

end Start

end GI.Impl
