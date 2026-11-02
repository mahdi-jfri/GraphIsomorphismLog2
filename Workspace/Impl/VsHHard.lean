import Workspace.Impl.VsHSplitOK
import Workspace.Impl.VsHPowIt
import Workspace.Impl.VsHFront
import Workspace.Impl.VsQTSplit

/-!
# The hard case

On `[vsQLCV s, vsPGIn s as Lb ccs tcs ys r]` (the hand-off of step 4), the program `vsHHardE`
runs the front (`vsHFront_spec`). With no isotropic element (`|K| = 0`) it runs the `Q₈`
program (`vsHQ8_spec`) and returns `[2, us, ⟨ks⟩]`; otherwise it computes the pieces
(`vsHPs_spec`), `B = (|Ps| + 1)^278`, and the spine's split by the tuple of pieces
(`vsQTSplit_spec`), which is a correct split, case 2 with `E = 278` (`VsHHyp.splitOK`).
-/

open Matrix Module

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst} {s : VsQSt I}

/-- The hard case, on `[vsQLCV s, vsPGIn …]`. -/
def vsHHardE (front q8 ps itq wr : ℕ) : Expr :=
  .letE (.call front (arg 1))
  (.ite (.length (.get (.var 1) (.nat 2)))
    (.letE (.call ps (mk2 (arg 1) (.get (.var 1) (.nat 2))))
    (.letE (.call itq (mk3 (.arith .add (.length (.var 2)) (.nat 1)) (.nat 278) (.nat 1)))
      (.call wr (mk3 (arg 0) (.var 2) (.var 3)))))
    (.call q8 (mk2 (arg 1) (.get (.var 1) (.nat 1)))))

/-- The indices of the spine's split program and its parts. -/
structure VsHWX where
  (f kmp kI cat appd tl so fa smp sI lmp lI rng jp jm key' cat' appd' tk cat'' lift bas
    itm loc phi tl₁ chk mp fI tl' chk' ker img key cat₂ appd₂ : ℕ)

/-- The layout of the spine's split program. -/
structure VsHWLay (P : Program) (x : VsHWX) (hps : PointwiseStab) (hm : Membership) : Prop where
  H : VsQTSplitAt P x.f x.kmp x.kI x.cat x.appd x.tl x.so x.fa x.smp x.sI x.lmp x.lI x.rng x.jp x.jm
  HK : VsQTKeyItemAt P x.kI x.key' x.cat' x.appd'
  HL : VsQTLowAt P x.lI x.tk x.cat'' x.lift x.bas
  HA : VsQTActAt P x.fa x.itm x.loc x.phi x.tl₁ x.chk x.mp x.fI x.tl' x.chk' x.ker x.img x.key x.cat₂ x.appd₂
  hjp : P.prims[x.jp]? = some (pointwiseStabPrim hps)
  hjm : P.prims[x.jm]? = some (membershipPrim hm)

/-- The indices of the hard case. -/
structure VsHHX where
  (hard fr : ℕ) (f : VsHFX) (q : VsHQX) (pp : VsHPX) (w : VsHWX)

/-- The layout of the hard case. -/
structure VsHHLay (P : Program) (x : VsHHX) (hps : PointwiseStab) (hm : Membership) : Prop where
  hh : P.funs[x.hard]? = some (vsHHardE x.fr x.q.q8 x.pp.ps x.f.itq x.w.f)
  hf : P.funs[x.fr]? = some (vsHFrontE x.f.ctx x.f.c2 x.f.bas x.f.i.m.e.en x.f.iso)
  F : VsHFLay P x.f
  Q : VsHQLay P x.q hps hm
  Pp : VsHPLay P x.pp
  W : VsHWLay P x.w hps hm

/-- What the hard case returns. -/
def VsHHardOut [Fact I.p.Prime] {s : VsQSt I} (hs : VsQStOK s) (Lb : List (List (List ℕ)))
    (ccs ys : List (Perm (Fin I.n))) (r Tm : ℕ) (w : Val) : Prop :=
  (∃ (Lo : List (List (Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)) × Perm (Fin I.n)))
      (ks : List (Perm (Fin I.n))),
      w = .list [.nat 2, .list (Lo.map fun q => encPerm q.2), encGroup ks] ∧
      VsQOrbL (vsHAlT s) (1 :: ccs) ((vsHB s Lb r ys).map (vsHT s)) Lo ∧
      (∀ h, h ∈ gens ks ↔ h ∈ gens ccs ∧
        vsHAlT s h ((vsHB s Lb r ys).map (vsHT s)) = (vsHB s Lb r ys).map (vsHT s)) ∧
      ks.length ≤ I.n ^ 2 ∧ Lo.length ≤ 24 ∧
      (vsHK s Lb r ys).length = 0) ∨
  (∃ ts cs lows, w = vsQSplitV ts cs lows ∧ VsQSplitOK s 278 Tm ts cs lows)

/-- The cost of the spine's split program. -/
noncomputable def vsHWCost (hps : PointwiseStab) (hm : Membership) (n S Cφ Bv : ℕ) : ℕ :=
  vsQSotCost hps hm n (vsQTS S Bv) (Cφ + 10 ^ 15 * (S ^ 3 + 1) ^ 7) + 10 ^ 20 * (S ^ 3 + 1) ^ 12 +
    10 ^ 8 * vsQTS S Bv ^ 4 + 10 ^ 30 * (S ^ 3 + 1) ^ 13

/-- The cost of the hard case. -/
noncomputable def vsHHardCost (hps : PointwiseStab) (hm : Membership) (Cφ N N2 W n Ss S Bv : ℕ) : ℕ :=
  16 * (vsHFrontCost Cφ N W + vsHQ8Cost hps hm Cφ N n Ss + vsHPsCost Cφ N2 +
    10 ^ 7 * (300 * (S + 1) + 900) + vsHWCost hps hm n S Cφ Bv) + 10 ^ 3 * (N + N2 + S + W + Ss + Bv)

set_option maxHeartbeats 16000000 in
/-- **The hard case.** -/
theorem vsHHard_spec [Fact I.p.Prime] {P : Program} {x : VsHHX} {hps : PointwiseStab}
    {hm : Membership} (L : VsHHLay P x hps hm) {Cφ N N2 W Ss S Tm : ℕ}
    (hphi1 : ∀ g ∈ gens I.gs, FunDet P x.f.i.m.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hphi2 : ∀ g ∈ gens I.gs, FunDet P x.q.t.c.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hphi3 : ∀ g ∈ gens I.gs, FunDet P x.pp.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hphi4 : ∀ g ∈ gens I.gs, FunDet P x.w.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {hs : VsQStOK s} {as : List (Perm (Fin I.n))} {Lb : List (List (List ℕ))}
    {ccs tcs ys : List (Perm (Fin I.n))} {r : ℕ} (h : VsHHyp hs as Lb ys r)
    (hcc : gens ccs ≤ gens s.hs) (hccl : ccs.length ≤ I.n ^ 2)
    (hccC : vsPBar hs (gens ccs) ≤ Subgroup.centralizer (vsPBar hs (gens as) : Set _))
    (hnab : ¬ s.Ab)
    (H : VsPCtxOK I N W s.ws' (vsQCs s) (vsPRows I.p Lb) s.hs)
    (hA : (vsPGIn s as Lb ccs tcs ys r).wt ≤ W) (hAN : (vsPGIn s as Lb ccs tcs ys r).wt ≤ N2)
    (hlc : (vsQLCV s).wt ≤ N2) (hD : vsQD s ^ 2 + 1 ≤ N) (hyl : ys.length + 1 ≤ N) (hr : r ≤ N) (hLbl : Lb.length ≤ N)
    (hsz2 : VsQSz I.p I.d (vsQExp I) N2) (hΓ2 : (vsQGam I).wt ≤ N2) (hn2 : I.n ≤ N2)
    (hfr2 : VsWFrOK I.p N2 I.d s.ws' (vsQCs s))
    (hNbig : 1 + vsQD s * vsQD s * (as.length + 1 + vsQD s ^ 2) ≤ N2)
    (hasl : as.length + 1 + vsQD s ^ 2 ≤ N2)
    (hac : (vsHAcV s).wt ≤ 1000 * (N + 1) ^ 3)
    (hSn : I.n ^ 2 + 2 ≤ Ss) (hSac : 1000 * (N + 1) ^ 3 ≤ Ss) (hSk : 20 * (N + 1) ^ 4 ≤ Ss)
    (hSW : (vsPGIn s as Lb ccs tcs ys r).wt + 100 * (N + 1) ^ 3 ≤ Ss)
    (hS : VsQDSz I S Tm) (hTm : (I.d + 1) ^ 278 ≤ Tm) :
    FunAll P x.hard (.list [vsQLCV s, vsPGIn s as Lb ccs tcs ys r]) (fun w c =>
      VsHHardOut hs Lb ccs ys r Tm w ∧
      c ≤ vsHHardCost hps hm Cφ N N2 W I.n Ss S
        (((vsHPs s ((1 :: as) ++ vsHK s Lb r ys)).length + 1) ^ 278)) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  set A := vsPGIn s as Lb ccs tcs ys r
  set lc := vsQLCV s
  set B := vsHB s Lb r ys
  set K := vsHK s Lb r ys
  set C2 := vsHGc (vsPCtx I s.ws' (vsQCs s) (vsPRows I.p Lb) s.hs) r
    (I.p ^ (vsPRows I.p Lb).length - 1) (decide (r ∣ I.p ^ (vsPRows I.p Lb).length - 1))
  set FV := Val.list [C2, .list (B.map encPerm), .list (K.map encPerm)]
  have a1 := Det.arg' (P := P) (vs := [lc, A]) (rest := []) (j := 1) rfl
  have hFr : FunDet P x.fr A FV (vsHFrontCost Cφ N W) :=
    vsHFront_spec L.hf L.F hphi1 h H hA hD hyl hr hLbl
  have dF := Det.call a1 hFr
  have wF : FV.wt < vsHFrontCost Cφ N W := FunDet.wt_lt' hFr
  set E1 := [Val.list [lc, A], FV]
  have dK : Det P E1 (.get (.var 1) (.nat 2)) (.list (K.map encPerm)) _ :=
    Det.get' (Det.var' (P := P) (env := E1) (i := 1) rfl) (Det.nat 2) rfl
  have dKl := Det.length dK
  rw [List.length_map] at dKl
  refine FunAll.intro L.hh (EvalAll.letE dF fun v1 c1 hv1 => ?_)
  obtain ⟨rfl, hc1⟩ := hv1
  refine EvalAll.ite dKl (fun vc cc hvc => ⟨_, hvc.1⟩) fun xk ck hck => ?_
  obtain ⟨hxk, hck⟩ := hck
  have hxk' : xk = K.length := by injection hxk
  subst hxk'
  by_cases hK0 : K.length = 0
  · -- the `Q₈` branch
    rw [if_pos hK0]
    have hB : ∀ b ∈ B, b ∈ gens s.hs := fun b hb => h.hys b (h.bas.1 b hb)
    have hBl : B.length ≤ N := by
      have := (vsHGreedy_sublist (vsHBT I s.ws' (vsQCs s) (vsPRows I.p Lb) r) ys).length_le
      have e : B = vsHGreedy (vsHBT I s.ws' (vsQCs s) (vsPRows I.p Lb) r) ys := rfl
      rw [e]; omega
    have hBY : ∀ b ∈ B, vsPRho hs b ∈ vsHY hs as ys := fun b hb => (h.inY b (h.bas.1 b hb)).2
    obtain ⟨-, hidx⟩ := h.q8 hK0 hccC
    have hDD1 : vsQD s * vsQD s + 1 ≤ N := by rw [← sq]; exact hD
    have hQ := vsHQ8_spec L.Q hphi2 H hDD1 hac hB hBl hcc hccl hBY hidx hSn hSac hSk hSW
    have b1 := Det.arg' (P := P) (vs := [lc, A]) (rest := [FV]) (j := 1) rfl
    have dBv : Det P E1 (.get (.var 1) (.nat 1)) (.list (B.map encPerm)) _ :=
      Det.get' (Det.var' (P := P) (env := E1) (i := 1) rfl) (Det.nat 1) rfl
    refine EvalAll.call_funAll (Det.mk2 b1 dBv) fun v ca hv => ?_
    obtain ⟨rfl, hca⟩ := hv
    refine (hQ.wt_lt).mono fun w c hw => ?_
    obtain ⟨⟨Lo, ks, hw1, hLo, hks, hksl, hc⟩, hwc⟩ := hw
    refine ⟨Or.inl ⟨Lo, ks, hw1, hLo, hks, hksl, ⟨?_, hK0⟩⟩, ?_⟩
    · have hK : genGroup (1 :: ccs) ≤ gens s.hs := by rw [vsH_genGroup_one]; exact hcc
      have hCb : ∀ g ∈ genGroup (1 :: ccs), vsPRho hs g ∈ vsPBar hs (gens ccs) := by
        intro g hg
        rw [vsH_genGroup_one] at hg
        exact vsPRho_mem_vsPBar hs hg (hcc hg)
      rw [hLo.length_eq]
      exact (vsH_q8_orbit hs hB hK hCb hBY).trans hidx
    · have l1 := wt_list2_le lc A
      have hBw : (Val.list (B.map encPerm)).wt < FV.wt := wt_le_wt_list (by simp [FV])
      have hKw : (Val.list (K.map encPerm)).wt < FV.wt := wt_le_wt_list (by simp [FV])
      have l2 := wt_list2_le A (Val.list (B.map encPerm))
      have eF : (Val.list [C2, Val.list (List.map encPerm B), Val.list (List.map encPerm K)]).wt = FV.wt := rfl
      have := wt_nat_le 1; have := wt_nat_le 2
      have wF' : FV.wt < vsHFrontCost Cφ N W := wF
      have hv : lc.wt ≤ N2 := hlc
      have hu : A.wt ≤ N2 := hAN
      unfold vsHHardCost
      omega
  · rw [if_neg hK0]
    have hk : 1 ≤ K.length := Nat.one_le_iff_ne_zero.2 hK0
    set Ps := vsHPs s ((1 :: as) ++ K)
    obtain ⟨hPf, -, h2le, hind, hdim, htop, horb⟩ := h.pieces hk
    have hKs : ∀ g ∈ K, g ∈ gens s.hs := (h.split).1
    have hKl : K.length ≤ vsQD s ^ 2 := by
      have h1 := (vsHGreedy_sublist (vsHT2 s Lb r) (vsHE s Lb r ys)).length_le
      have h2 := h.E_length
      have e : K = vsHGreedy (vsHT2 s Lb r) (vsHE s Lb r ys) := rfl
      rw [e]; omega
    have hN' : 1 + vsQD s * vsQD s * ((1 :: as) ++ K).length ≤ N2 := by
      have : ((1 :: as) ++ K).length ≤ as.length + 1 + vsQD s ^ 2 := by simp; omega
      have := Nat.mul_le_mul_left (vsQD s * vsQD s) this
      omega
    have hLl : ((1 :: as) ++ K).length ≤ N2 := by simp; omega
    have hPsS := vsHPs_spec L.Pp hphi3 hs hsz2 hΓ2 hn2 hfr2 h.has hKs hN' hLl hAN
    have wPs := FunDet.wt_lt' hPsS
    have b1 := Det.arg' (P := P) (vs := [lc, A]) (rest := [FV]) (j := 1) rfl
    have dPs := Det.call (Det.mk2 b1 dK) hPsS
    -- the bound `B`
    have hcnt := vsFEigL_count I.prime (vsHFx s ((1 :: as) ++ K)) (vsHFx_sq _)
    have hPsl : Ps.length ≤ vsQD s := hcnt.1
    have hDd := vsQD_le hs
    have hSd := hS.d
    set PV := vsFMatsVal Ps
    set E2 := [Val.list [lc, A], FV, PV]
    have dl := Det.length (Det.var' (P := P) (env := E2) (i := 2) rfl (v := Val.list (Ps.map vsWVs)))
    rw [List.length_map] at dl
    have dc := Det.arith (op := .add) dl (Det.nat (P := P) (env := E2) 1)
    have ec : GI.Machine.BinOp.eval .add Ps.length 1 = Ps.length + 1 := rfl
    rw [ec] at dc
    set M := 280 * (S + 1) + 20
    have hM : ∀ i ≤ 278, GI.Machine.len ((Ps.length + 1) ^ i) + GI.Machine.len (Ps.length + 1) +
        GI.Machine.len 278 ≤ M := by
      intro i hi
      have h1 := GI.Machine.len_pow_le (Ps.length + 1) i
      have h2 := GI.Machine.len_le_self (Ps.length + 1)
      have h3 : GI.Machine.len 278 ≤ 9 := by decide
      have h4 : i * GI.Machine.len (Ps.length + 1) ≤ 278 * (S + 1) :=
        Nat.mul_le_mul hi (by omega)
      omega
    have hPw := vsHPowIt_spec L.F.hitq L.F.hstq hM
    have dB := Det.call (Det.mk3 dc (Det.nat (P := P) (env := E2) 278) (Det.nat (P := P) (env := E2) 1)) hPw
    set Bv := (Ps.length + 1) ^ 278
    -- the split
    have hsum : (Ps.map List.length).sum ≤ S := by
      have := (vsFEigL_cnt I.prime (vsHFx s ((1 :: as) ++ K)) (vsHFx_sq _)).2
      exact this.trans (by omega)
    have hbS : Ps.length ≤ S := by omega
    have hW := vsQTSplit_spec hps hm L.W.H L.W.HK L.W.HL L.W.HA L.W.hjp L.W.hjm hphi4 hS hs hPf
      hbS hsum horb
    set E3 := [Val.list [lc, A], FV, PV, Val.nat Bv]
    have c0 := Det.arg' (P := P) (vs := [lc, A]) (rest := [FV, PV, Val.nat Bv]) (j := 0) rfl
    refine EvalAll.letE dPs fun v2 c2 hv2 => ?_
    obtain ⟨rfl, hc2⟩ := hv2
    refine EvalAll.letE dB fun v3 c3 hv3 => ?_
    obtain ⟨rfl, hc3⟩ := hv3
    refine EvalAll.call_funAll (Det.mk3 c0 (Det.var' (P := P) (env := E3) (i := 2) rfl)
      (Det.var' (P := P) (env := E3) (i := 3) rfl)) fun v ca hv => ?_
    obtain ⟨rfl, hca⟩ := hv
    refine (hW.wt_lt).mono fun w c hw => ?_
    obtain ⟨⟨⟨Lo, ks, hw1, hLo, hks, hksl⟩, hc⟩, hwc⟩ := hw
    refine ⟨Or.inr ⟨_, ks, _, hw1, h.splitOK hk hLo hks hksl ?_ hnab⟩, ?_⟩
    · rw [hLo.length_eq]
      refine horb.trans ((Nat.pow_le_pow_left (show Ps.length + 1 ≤ I.d + 1 by omega) 278).trans hTm)
    · have l1 := wt_list2_le lc A
      have hKw : (Val.list (K.map encPerm)).wt < FV.wt := wt_le_wt_list (by simp [FV])
      have eF : (Val.list [C2, Val.list (List.map encPerm B), Val.list (List.map encPerm K)]).wt = FV.wt := rfl
      have wF' : FV.wt < vsHFrontCost Cφ N W := wF
      have wPs' : PV.wt < vsHPsCost Cφ N2 := wPs
      have hv : lc.wt ≤ N2 := hlc
      have hu : A.wt ≤ N2 := hAN
      have l2 := wt_list2_le A (Val.list (K.map encPerm))
      have l3 := wt_list3_le lc PV (Val.nat Bv)
      have l4 := wt_list3_le (Val.nat (Ps.length + 1)) (Val.nat 278) (Val.nat 1)
      have hB278 := hM 278 le_rfl
      have wBv : (Val.nat Bv).wt ≤ M + 2 := by
        rw [wt_nat']
        show GI.Machine.len ((Ps.length + 1) ^ 278) + 2 ≤ M + 2
        omega
      have wc1 : (Val.nat (Ps.length + 1)).wt ≤ M + 2 := by rw [wt_nat']; omega
      have w278 : (Val.nat 278).wt ≤ 300 := by rw [wt_nat']; decide
      have n1 := wt_nat_le 1; have n2 := wt_nat_le 2; have n0 := wt_nat_le 0
      have hPV : (Val.list (Ps.map vsWVs)).wt = PV.wt := rfl
      have hlP := length_lt_wt_list (Ps.map vsWVs)
      rw [List.length_map] at hlP
      have hpw : 10 ^ 4 * (278 + 1) * (M + 278 + 10) ≤ 10 ^ 7 * (300 * (S + 1) + 900) := by
        simp only [M]; omega
      have hpos : 0 ≤ (N + 1) ^ 3 := Nat.zero_le _
      have hM' : M = 280 * (S + 1) + 20 := rfl
      have eWC : vsHWCost hps hm I.n S Cφ Bv = vsQSotCost hps hm I.n (vsQTS S Bv) (Cφ + 10 ^ 15 * (S ^ 3 + 1) ^ 7) +
          10 ^ 20 * (S ^ 3 + 1) ^ 12 + 10 ^ 8 * vsQTS S Bv ^ 4 + 10 ^ 30 * (S ^ 3 + 1) ^ 13 := rfl
      have hcW : c ≤ vsHWCost hps hm I.n S Cφ Bv := by rw [eWC]; exact hc
      have hc1' : c1 ≤ 2 * vsHFrontCost Cφ N W + 8 * N2 + 40 := by
        linarith only [hc1, hv, hu, l1, l2, l3, l4, wF, wF', eF, hKw, wPs, wPs', wBv, wc1, w278, hPV, hlP, hpw, n0, n1, n2]
      have hKlw := length_lt_wt_list (K.map encPerm)
      rw [List.length_map] at hKlw
      have hck' : ck ≤ 3 * vsHFrontCost Cφ N W + 20 := by
        linarith only [hck, hKlw, hv, hu, l1, l2, l3, l4, wF, wF', eF, hKw, wPs, wPs', wBv, wc1, w278, hPV, hlP, hpw, n0, n1, n2]
      have hc2' : c2 ≤ 2 * vsHPsCost Cφ N2 + 20 * N2 + 10 * vsHFrontCost Cφ N W + 100 := by
        linarith only [hc2, hv, hu, l1, l2, l3, l4, wF, wF', eF, hKw, wPs, wPs', wBv, wc1, w278, hPV, hlP, hpw, n0, n1, n2]
      have hc3' : c3 ≤ 3 * vsHPsCost Cφ N2 + 10 ^ 7 * (300 * (S + 1) + 900) + 10 * M + 2000 := by
        linarith only [hc3, hv, hu, l1, l2, l3, l4, wF, wF', eF, hKw, wPs, wPs', wBv, wc1, w278, hPV, hlP, hpw, n0, n1, n2]
      have hca' : ca ≤ 20 * N2 + 10 * vsHPsCost Cφ N2 + 10 * M + 200 := by
        linarith only [hca, hv, hu, l1, l2, l3, l4, wF, wF', eF, hKw, wPs, wPs', wBv, wc1, w278, hPV, hlP, hpw, n0, n1, n2]
      have hMS : M ≤ 300 * (S + 1) + 900 := by omega
      unfold vsHHardCost
      clear_value M
      linarith only [hwc, hcW, hc1', hck', hc2', hc3', hca', hMS]

end GI.Impl
