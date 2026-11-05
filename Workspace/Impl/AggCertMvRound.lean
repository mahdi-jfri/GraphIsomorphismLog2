module

public import Workspace.Impl.AggCertMvEnd

@[expose] public section

/-!
# The move program: the start of a round

The function `cpRoundF` (at `b + 1`) runs when no window call is under way. At `t = n` it hands
over to the end of the string (`cp_end_spec`). Otherwise it computes the increment `V_t` with
the increment program (`inc_spec`). If `V_t` is empty, the round is skipped
(`cp_round_empty_rep`); if not, the first window call of the round is made by `cpStartF`, whose
specification is a hypothesis here (it is proved in `AggCertMvStart.lean`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens PointwiseStab Preimage Membership)
open GI.Machine (BinOp)

/-- `incList` keeps a part of the list of outside points, in order. -/
theorem incList_sublist {V Q : Type} [Group Q] {P : Subgroup (Perm V)} (phi : P →* Q)
    (A : Subgroup (Perm V)) (W : Set V) (os : List V) (a : ℕ) :
    (incList phi A W os a).Sublist os := by
  unfold incList
  split_ifs <;> first | exact List.nil_sublist _ | exact List.filter_sublist

section Round

variable {k : ℕ} {Ω C : Type} [Finite Ω] [DecidableEq Ω] {e : Ω ≃ Fin k} {c : C → ℕ}
  {S : State Ω C} [Fintype S.dom] {L : GiantLabels S}
  {πd : S.domGroup →* alternatingGroup (Fin L.q)}
  (hst : PointwiseStab) (hpre : Preimage) (hm : Membership)

omit [Finite Ω] [DecidableEq Ω] [Fintype S.dom] in
/-- **The increment program, within the budget.** -/
theorem cp_bud_inc {Pg : Program} {b jp : ℕ} (hb : Pg.HasAt b (incFuns b jp))
    (hj : Pg.prims[jp]? = some (pointwiseStabPrim hst))
    (hπ : ∀ g : S.G, πd ⟨S.domHom g, g, rfl⟩ = L.π g)
    {T : Finset (Fin L.q)} {A : Subgroup (Perm S.dom)} (hA : A ≤ Pgrp S.domGroup πd T)
    {ps : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L (S.liftGroup A) ps)
    (hpl : ps.length ≤ (k + L.q) ^ 2) (Wn : Set S.dom) {os : List S.dom}
    (hos : ∀ v, v ∈ os ↔ v ∉ Wn) (hosl : os.length ≤ k) {D W : ℕ}
    (hD : Nat.card (alternatingGroup T) = D) (hDW : 10 * D + 10 ≤ W)
    (hW : 10 ^ 10 * (k + L.q + 1) ^ 12 ≤ W) :
    CpFB Pg b (.list [.list [.nat k, .nat L.q], .list (ps.map pairV),
        natList (ptsKey (labPts k (tlist T))), .nat D, .nat D, encPts (os.map (domPos e L.q))])
      W (cpG hst hpre hm W)
      (fun w => w = encPts ((incList (phiT S.domGroup πd T) A Wn os D).map (domPos e L.q))) := by
  have h := inc_spec πd hst hb hj hπ hA hps Wn hos (B := D) hD.le
  rw [hD] at h
  have hsub := incList_sublist (phiT S.domGroup πd T) A Wn os D
  have hl : ((incList (phiT S.domGroup πd T) A Wn os D).map (domPos e L.q)).length ≤ k := by
    rw [List.length_map]; exact hsub.length_le.trans hosl
  have hwt := cp_wt_pts (q := L.q) hl
  obtain ⟨f1, f2, -, -, -, -, -, -, -, -⟩ := cp_pow_facts k L.q
  have w2 : (k + L.q + 1) ^ 2 ≤ (k + L.q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  refine CpFB.det h ?_ (by omega) rfl
  have hT : T.card ≤ L.q := by simpa using Finset.card_le_univ T
  have hM : incM k L.q ps D T.card os.length ≤ W := by
    unfold incM
    have : k + L.q + 1 ≤ (k + L.q + 1) ^ 12 := Nat.le_self_pow (by omega) _
    have : (k + L.q + 1) ^ 2 ≤ (k + L.q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
    have : (k + L.q) ^ 2 ≤ (k + L.q + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hkW : k + L.q + 1 ≤ W := by
    have : k + L.q + 1 ≤ (k + L.q + 1) ^ 12 := Nat.le_self_pow (by omega) _
    omega
  have a1 : (2 * os.length + 2) * cardCost hst (2 * incM k L.q ps D T.card os.length) ≤
      (2 * W + 2) * cardCost hst (2 * W) :=
    Nat.mul_le_mul (by omega) (cardCost_mono hst (by omega))
  have a2 : incK * incM k L.q ps D T.card os.length ^ 12 ≤ incK * (W + 1) ^ 12 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 12)
  have a3 := cp_poly_le (W := W) (K := incK) (d := 12) (by simp [incK]) (by norm_num) (by omega)
  have := cpG_poly hst hpre hm (W := W)
  have := cpG_card hst hpre hm (W := W)
  unfold cpG at *
  omega

set_option maxHeartbeats 4000000 in
/-- **The start of a round.** The hypothesis `hstart` is the specification of the first window
call (`cpStartF`). -/
theorem cp_round_spec {Pg : Program} {b jp jpre jm : ℕ} (hat : CpMvAt Pg b jp jpre jm)
    (hjp : Pg.prims[jp]? = some (pointwiseStabPrim hst))
    (hjpre : Pg.prims[jpre]? = some (preimagePrim hpre))
    {sv : Val} {gp : GPairs k L.q} {osA : List (Fin (k + L.q))} {D : ℕ}
    (ctx : CpCtx e c S L πd sv gp osA D) {NT M₀ Bw W Cs : ℕ}
    (hBw : cpBw k L.q (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA)).wt NT M₀ D
      ≤ Bw) (hW : 10 ^ 4 * (Bw + 2) ^ 2 ≤ W)
    {m f : ℕ} {σ : CpSt k L.q} {acc : List (StagePair S)} {T : Finset (Fin L.q)}
    {rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))}
    (h : CpRoundInv e πd σ acc T rec) (hT : T = σ.T)
    (hm' : m = cpMeas (Fintype.card S.dom) D (.round acc T σ.Ts σ.s σ.t)) (hmf : m ≤ f)
    (hM : σ.cache.length + m ≤ M₀) (hNT : σ.res.length + σ.Ts.length + 1 ≤ NT)
    (hlen : CpLen D σ) {u : Val}
    (hst' : (Val.list [σ.val (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA))
      (.list []), u]).wt ≤ Bw)
    (hstart : ∀ incl : List S.dom, incl.Nodup →
      (∀ v, v ∈ incl ↔ v ∈ inc (cpPhi S πd T) (dstr S (cpZ S σ.s)) σ.t) → incl ≠ [] →
      σ.t < Fintype.card S.dom →
      CpFB Pg (b + 3) (.list [σ.val (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp)
          (encPts osA)) (.list []), encPts (incl.map (domPos e L.q))]) W Cs
        (CpMvPost e S L πd (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA)) D Bw
          M₀ NT m ((fun R => cpAt S πd (dstr S S.x) (dstr S S.y) R
            (.round acc T σ.Ts σ.s σ.t)) '' Cands rec) f)) :
    CpFB Pg (b + 1) (.list [σ.val (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA))
        (.list []), u]) W (Cs + 3 * cpG hst hpre hm W + 2000 * (W + 20))
      (CpMvPost e S L πd (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA)) D Bw M₀
        NT m ((fun R => cpAt S πd (dstr S S.x) (dstr S S.y) R (.round acc T σ.Ts σ.s σ.t)) ''
          Cands rec) f) := by
  set par := cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA) with hpar
  subst hT
  obtain ⟨hW1, hW2, hW3, hW4, hW5⟩ := cp_W_facts hBw hW
  have hkW : k + L.q + 1 ≤ W := by
    have : k + L.q + 1 ≤ (k + L.q + 1) ^ 12 := Nat.le_self_pow (by omega) _
    omega
  have hwW0 : (Val.list [σ.val par (.list []), u]).wt ≤ W := by omega
  set ks := σ.vals par (.list []) with hks
  have hsv : σ.val par (.list []) = .list ks := rfl
  have hwW : (Val.list [.list ks, u]).wt ≤ W := by rw [← hsv]; omega
  have hksW : (Val.list ks).wt < W :=
    lt_of_lt_of_le (cp_wt_get (vs := [.list ks, u]) (j := 0) rfl) hwW
  have hp0 : ks[0]? = some (.list [sv, .list [.nat k, .nat L.q], gpV gp,
    .nat (Fintype.card S.dom), .nat D, encPts osA, pSplitCtx k L.q, .nat (k + L.q)]) := rfl
  have hlen0 := hlen
  obtain ⟨hlt, hlo, hl0, hlx, hlp, hlr, hlc⟩ := hlen
  have h0 : ∀ rest : List Val, (Val.list [.list ks, u] :: rest)[0]? = some (.list [.list ks, u]) :=
    fun _ => rfl
  refine CpFB.intro hat.round ?_
  unfold cpRoundF
  have dc := Det.arith' (op := .eq) (cp_rdK (P := Pg) (h0 []) hwW (j := 7) (v := .nat σ.t) rfl
    (by omega)) (cp_rdP (P := Pg) (h0 []) hwW hp0 (j := 3) (v := .nat (Fintype.card S.dom)) rfl
    (by omega)) rfl
  have hz : BinOp.eq.eval σ.t (Fintype.card S.dom) ≤ 1 := by
    simp only [BinOp.eval]; split_ifs <;> omega
  refine (CpEB.ite dc (Ct := 2 * cpG hst hpre hm W + 1150 * (W + 20))
    (Ce := Cs + cpG hst hpre hm W + 600 * (W + 20)) ?_ ?_).mono (by omega) fun _ h => h
  · -- `t = n`: the end of the string
    intro hne
    have ht : σ.t = Fintype.card S.dom := by
      by_contra hc; simp only [BinOp.eval, hc, if_false, ne_eq, not_true_eq_false] at hne
    refine (CpEB.call (CpEB.det (Det.rv (P := Pg) (env := [.list [.list ks, u]]) (i := 0) rfl hwW)
      le_rfl hwW (Q := fun v => v = .list [.list ks, u]) rfl)
      (Cb := 2 * cpG hst hpre hm W + 1100 * (W + 20)) fun v hv _ => ?_).mono
      (by omega) fun _ h => h
    subst hv
    rw [← hsv]
    exact cp_end_spec hst hpre hm hat hjpre ctx hBw hW h rfl hm' hmf hM hNT hlen0 ht hst'
  · -- `t < n`: the increment
    intro heq
    have ht : σ.t < Fintype.card S.dom := by
      have := h.t_le
      have : σ.t ≠ Fintype.card S.dom := by
        intro hc; simp only [BinOp.eval, hc, if_true, one_ne_zero] at heq
      omega
    obtain ⟨os, hnd, hos, hosP⟩ := h.os
    have hosl : os.length ≤ k := cp_os_length_le e hnd
    have hA := (grp_le (cpPhi S πd σ.T) (dstr S (cpZ S σ.s)) σ.t)
    have hDT : Nat.card (alternatingGroup σ.T) = D := ctx.hD σ.T h.card
    have hDB : 10 ^ 6 * (D + 1) ≤ Bw := by
      have : (D + 1) ≤ (D + 1) * (k + L.q + 1) ^ 6 :=
        Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by omega))
      have e1 : 10 ^ 6 * (D + 1) * (k + L.q + 1) ^ 6 = 10 ^ 6 * ((D + 1) * (k + L.q + 1) ^ 6) := by
        ring
      omega
    have hDW : 10 * D + 10 ≤ W := by omega
    set incl := incList (phiT S.domGroup πd σ.T) (grp (cpPhi S πd σ.T) (dstr S (cpZ S σ.s)) σ.t)
      (win (cpPhi S πd σ.T) (dstr S (cpZ S σ.s)) σ.t : Set S.dom) os D with hincl
    have hinc : ∀ v, v ∈ incl ↔ v ∈ inc (cpPhi S πd σ.T) (dstr S (cpZ S σ.s)) σ.t := by
      intro v
      have := incList_toFinset (phiT S.domGroup πd σ.T)
        (grp (cpPhi S πd σ.T) (dstr S (cpZ S σ.s)) σ.t)
        (win (cpPhi S πd σ.T) (dstr S (cpZ S σ.s)) σ.t) hos
      rw [hDT] at this
      rw [← List.mem_toFinset, this]
    have hnd' : incl.Nodup := (incList_sublist _ _ _ _ _).nodup hnd
    -- the argument of the increment program
    have hTsl : (Val.list [indT σ.T, natList (ptsKey (labPts k (tlist σ.T)))]).wt < W :=
      (cp_wt_get (vs := ks) (j := 11) rfl).trans hksW
    have hpsW : (gpV σ.ps).wt < W := (cp_wt_get (vs := ks) (j := 8) rfl).trans hksW
    have hosW : (encPts σ.osP).wt < W := (cp_wt_get (vs := ks) (j := 9) rfl).trans hksW
    have hx0W : (natList (ptsKey (labPts k (tlist σ.T)))).wt < W :=
      (cp_wt_get (vs := [indT σ.T, natList (ptsKey (labPts k (tlist σ.T)))]) (j := 1) rfl).trans
        hTsl
    have hargW : (Val.list [.list [.nat k, .nat L.q], gpV σ.ps,
        natList (ptsKey (labPts k (tlist σ.T))), .nat D, .nat D, encPts σ.osP]).wt ≤ W := by
      obtain ⟨f1, f2, -, f24, -, -, -, -, f9, -⟩ := cp_pow_facts k L.q
      have w4 : (k + L.q + 1) ^ 4 ≤ (k + L.q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
      have := cp_wt_gp hlp
      have hts : (Val.list [indT σ.T, natList (ptsKey (labPts k (tlist σ.T)))]).wt ≤
          50 * (k + L.q + 1) ^ 2 := cp_wt_ts (k := k) (q := L.q) σ.T
      have := cp_wt_pts (q := L.q) hlo
      have := cp_wt_get (vs := [indT σ.T, natList (ptsKey (labPts k (tlist σ.T)))]) (j := 1)
        (v := natList (ptsKey (labPts k (tlist σ.T)))) rfl
      have := wt_nat_le k; have := wt_nat_le L.q; have := wt_nat_le D
      have := wt_list2_le (.nat k) (.nat L.q)
      have := cp_wt_list (vs := [.list [.nat k, .nat L.q], gpV σ.ps,
        natList (ptsKey (labPts k (tlist σ.T))), .nat D, .nat D, encPts σ.osP]) (n := 6)
        (c := 50 * (k + L.q + 1) ^ 4 + 50 * (k + L.q + 1) ^ 2 + D + 100) (by simp) (by
          intro x hx
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
      omega
    have dA := cp_mkList' (P := Pg) (env := [.list [.list ks, u]]) (W := W) (c := 5 * (W + 20))
      (v := .list [.list [.nat k, .nat L.q], gpV σ.ps, natList (ptsKey (labPts k (tlist σ.T))),
        .nat D, .nat D, encPts σ.osP])
      [(cpPf 1, .list [.nat k, .nat L.q]), (cpKf 8, gpV σ.ps),
        (.get (cpKf 11) (.nat 1), natList (ptsKey (labPts k (tlist σ.T)))), (cpPf 4, .nat D),
        (cpPf 4, .nat D), (cpKf 9, encPts σ.osP)] rfl (by
        intro p hp
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
        · exact (cp_rdP (P := Pg) (h0 _) hwW hp0 (j := 1) rfl (by omega)).mono (by omega)
        · exact (cp_rdK (P := Pg) (h0 _) hwW (j := 8) rfl (by omega)).mono (by omega)
        · exact Det.rd (a := 4) ((cp_rdK (P := Pg) (h0 _) hwW (j := 11) rfl (by omega)).mono
            (by omega)) le_rfl rfl hx0W.le (by omega)
        · exact (cp_rdP (P := Pg) (h0 _) hwW hp0 (j := 4) rfl (by omega)).mono (by omega)
        · exact (cp_rdP (P := Pg) (h0 _) hwW hp0 (j := 4) rfl (by omega)).mono (by omega)
        · exact (cp_rdK (P := Pg) (h0 _) hwW (j := 9) rfl (by omega)).mono (by omega)) hargW
    have hosP' : encPts σ.osP = encPts (os.map (domPos e L.q)) := by rw [hosP]
    have hbud := cp_bud_inc hst hpre hm hat.inc hjp ctx.hπ (hA.trans le_rfl) h.ps hlp
      (win (cpPhi S πd σ.T) (dstr S (cpZ S σ.s)) σ.t : Set S.dom) (os := os) (by simpa using hos)
      hosl hDT hDW hW2
    rw [← hosP'] at hbud
    refine (CpEB.letE (CpEB.call (CpEB.det dA le_rfl hargW
        (Q := fun v => v = .list [.list [.nat k, .nat L.q], gpV σ.ps,
          natList (ptsKey (labPts k (tlist σ.T))), .nat D, .nat D, encPts σ.osP]) rfl)
      fun v hv _ => hv ▸ hbud) (Cb := Cs + 500 * (W + 20)) fun iv hiv hiW => ?_).mono
      (by simp only [List.length_cons, List.length_nil]; omega) fun _ h => h
    subst hiv
    rw [encPts_map_posOf] at hiW ⊢
    replace hiW : (Val.list (incl.map fun v => Val.nat (domPos e L.q v : ℕ))).wt ≤ W := hiW
    have h1 : ∀ rest : List Val, (Val.list [.list ks, u] :: rest)[0]? =
        some (.list [.list ks, u]) := fun _ => rfl
    have dl := Det.length (Det.rv (P := Pg) (env := [.list [.list ks, u],
      .list (incl.map fun v => Val.nat (domPos e L.q v : ℕ))]) (i := 1) rfl hiW)
    have hll := length_lt_wt_list (incl.map fun v => Val.nat (domPos e L.q v : ℕ))
    refine (CpEB.ite dl (Ct := Cs + 6 * (W + 20)) (Ce := 450 * (W + 20)) ?_ ?_).mono
      (by omega) fun _ h => h
    · -- a nonempty increment: the first window call
      intro hne
      have hne' : incl ≠ [] := by intro hc; simp [hc] at hne
      have dA2 := Det.mk2 (cp_rdKs (P := Pg) (h1 _) hwW) (Det.rv (P := Pg)
        (env := [.list [.list ks, u], .list (incl.map fun v => Val.nat (domPos e L.q v : ℕ))])
        (i := 1) rfl hiW)
      have hA2W : (Val.list [.list ks, .list (incl.map fun v => Val.nat (domPos e L.q v : ℕ))]).wt
          ≤ W := by
        have := wt_list2_le (.list ks) (.list (incl.map fun v => Val.nat (domPos e L.q v : ℕ)))
        have hl : (incl.map (domPos e L.q)).length ≤ k := by
          rw [List.length_map]; exact (incList_sublist _ _ _ _ _).length_le.trans hosl
        have := cp_wt_pts (q := L.q) hl
        rw [encPts_map_posOf] at this
        have : (k + L.q + 1) ^ 2 ≤ (k + L.q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
        have hk : (Val.list ks).wt < Bw :=
          lt_of_lt_of_le (cp_wt_get (vs := [.list ks, u]) (j := 0) rfl) (by rw [← hsv]; exact hst')
        omega
      refine (CpEB.call (CpEB.det dA2 le_rfl hA2W (Q := fun v => v = .list [.list ks,
        .list (incl.map fun v => Val.nat (domPos e L.q v : ℕ))]) rfl) (Cb := Cs)
        fun v hv _ => ?_).mono
        (by have := wt_list2_le (.list ks)
              (.list (incl.map fun v => Val.nat (domPos e L.q v : ℕ)))
            omega) fun _ h => h
      subst hv
      have := hstart incl hnd' hinc hne' ht
      rw [encPts_map_posOf] at this
      exact this
    · -- an empty increment: the next round, without a call
      intro he
      have he' : incl = [] := by simpa using he
      have hempty : inc (cpPhi S πd σ.T) (dstr S (cpZ S σ.s)) σ.t = ∅ := by
        ext v
        simp only [Finset.notMem_empty, iff_false]
        intro hv
        have := (hinc v).mpr hv
        rw [he'] at this
        simp at this
      have hcard := cp_card_dom_le (S := S) e
      have hlen' : CpLen D σ.succ := ⟨by simp only [CpSt.succ]; omega, hlo, hl0, hlx, hlp, hlr, hlc⟩
      have hres : σ.res.length ≤ NT := by omega
      have htW : σ.t + 1 ≤ W := by omega
      have hTsl : σ.Ts.length ≤ NT := by omega
      have hc : σ.cache.length ≤ M₀ := by omega
      have hR' := h.succ_empty ht hempty hlp
      have hnew := cp_wt_new (par := par) hlen' hR'.loglen hTsl hres hc hBw
      have hsW : (σ.succ.val par (.list [])).wt ≤ W := by
        have := cp_wt_get (vs := [σ.succ.val par (.list []), .nat 0]) (j := 0) rfl
        omega
      obtain ⟨m', Ss', hlt', hsub, hrep⟩ :=
        cp_round_empty_rep h hm' hmf hM hNT ht hempty rfl hlen' hnew
      set env := [Val.list [.list ks, u], .list (incl.map fun v => Val.nat (domPos e L.q v : ℕ))]
      have d12 : Det Pg env (.snoc (cpKf 12) (mk2 (cpKf 8) (.var 1)))
          (.list ((σ.lz ++ [(σ.ps, [])]).map cpSgV)) (25 * (W + 20)) := by
        have := Det.snoc (cp_rdK (P := Pg) (h1 _) hwW (j := 12) rfl (by omega))
          (Det.mk2 (cp_rdK (P := Pg) (h1 _) hwW (j := 8) rfl (by omega))
            (Det.rv (P := Pg) (env := env) (i := 1) rfl hiW))
        have hv : Val.list (σ.lz.map cpSgV ++ [.list [gpV σ.ps,
            .list (incl.map fun v => Val.nat (domPos e L.q v : ℕ))]]) =
            .list ((σ.lz ++ [(σ.ps, [])]).map cpSgV) := by
          rw [he']; simp [cpSgV, encPts]
        rw [hv] at this
        refine this.mono ?_
        have := wt_list2_le (gpV σ.ps) (.list (incl.map fun v => Val.nat (domPos e L.q v : ℕ)))
        have := cp_wt_get (vs := ks) (j := 8) (v := gpV σ.ps) rfl
        have h1 := cp_wt_get (vs := σ.succ.vals par (.list [])) (j := 12)
          (v := .list ((σ.lz ++ [(σ.ps, [])]).map cpSgV)) rfl
        have h2 : (Val.list (σ.succ.vals par (.list []))).wt ≤ W := hsW
        omega
      have dK := cp_mkList' (P := Pg) (env := env) (W := W) (c := 25 * (W + 20))
        (v := σ.succ.val par (.list []))
        [(cpKf 0, par), (cpKf 1, .list (σ.Ts.map (tsV k))), (cpKf 2, boolVal σ.s),
          (cpKf 3, .list (σ.res.map resV)), (cpKf 4, .list (σ.cache.map ckEntV)),
          (cpKf 5, gpV σ.p0), (cpKf 6, gpV σ.px),
          (.arith .add (cpKf 7) (.nat 1), .nat (σ.t + 1)), (cpKf 8, gpV σ.ps),
          (cpKf 9, encPts σ.osP), (cpKf 10, .list []), (cpKf 11, tsV k σ.T),
          (.snoc (cpKf 12) (mk2 (cpKf 8) (.var 1)), .list ((σ.lz ++ [(σ.ps, [])]).map cpSgV)),
          (cpKf 13, .list (σ.lx.map cpSgV)), (cpKf 14, .list (σ.logs.map cpLogV))] rfl (by
          intro p hp
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl
          · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 0) rfl (by omega)).mono (by omega)
          · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 1) rfl (by omega)).mono (by omega)
          · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 2) rfl (by omega)).mono (by omega)
          · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 3) rfl (by omega)).mono (by omega)
          · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 4) rfl (by omega)).mono (by omega)
          · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 5) rfl (by omega)).mono (by omega)
          · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 6) rfl (by omega)).mono (by omega)
          · exact (Det.arith' (cp_rdK (P := Pg) (h1 _) hwW (j := 7) rfl (by omega)) (Det.nat 1)
              (z := σ.t + 1) rfl).mono (by omega)
          · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 8) rfl (by omega)).mono (by omega)
          · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 9) rfl (by omega)).mono (by omega)
          · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 10) rfl (by omega)).mono (by omega)
          · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 11) rfl (by omega)).mono (by omega)
          · exact d12
          · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 13) rfl (by omega)).mono (by omega)
          · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 14) rfl (by omega)).mono (by omega))
        hsW
      have := wt_list2_le (σ.succ.val par (.list [])) (.nat 0)
      have := wt_list2_le (.nat 2) (.list [σ.succ.val par (.list []), .nat 0])
      have : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
      have : (Val.nat 2).wt ≤ 4 := wt_nat_le 2
      refine CpEB.det (Det.mk2 (Det.nat 2) (Det.mk2 dK (Det.nat 0))) ?_ (by omega)
        (Or.inr ⟨m', _, Ss', hlt', hsub, hrep, rfl⟩)
      simp only [List.length_cons, List.length_nil]
      omega

end Round

end GI.Impl
