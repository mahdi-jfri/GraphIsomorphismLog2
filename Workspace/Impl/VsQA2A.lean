import Workspace.Impl.VsQA2S

/-!
# The front

On `[lc, encGroup as]` the program `vsQA2AE` computes the basis `Lb` of `L = 𝔽_p[Λ(as)]`, the
kernel of the nilpotent part of `L` and the pieces of `L`.

* If the kernel is not everything, it returns the chain split by it (case 1).
* If there is one piece, `L` is a field and it returns `[2, Lb]`.
* Otherwise it runs the case of two or more pieces (`vsQA2S_spec`).

Result: `vsQA2A_spec`.
-/

open Matrix Module

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

variable {I : VecStabInst}

/-- The front of step 2, on `[lc, encGroup as]`. -/
def vsQA2AE (bm bas ann nil eig fix spl s2s : ℕ) : Expr :=
  .letE (.call bm (mk2 (arg 0) (arg 1)))
  (.letE (.call bas (mk2 vsQLp (.call ann (mk3 vsQLp vsQLd (.call nil (mk3 vsQLp vsQLd (.var 1)))))))
  (.ite (.arith .lt (.length (.var 2)) vsQLd)
    (.call spl (mk2 (arg 0) (.var 2)))
    (.letE (.call eig (mk3 vsQLp vsQLd (.call fix (mk3 vsQLp vsQLd (.var 1)))))
      (.ite (.arith .lt (.length (.var 3)) (.nat 2))
        (mk2 (.nat 2) (.var 1))
        (.call s2s (mk2 (arg 0) (.var 3)))))))

/-- The indices of the front. -/
structure VsQA2AX where
  (f bm mpb itb locb phib idpb algb bas ann nil eig fix spl : ℕ) (s : VsQA2SX)

/-- The layout of the front. -/
structure VsQA2AAt (P : Program) (x : VsQA2AX) (hps : PointwiseStab) (hm : Membership)
    (hmb : MinimalBlocks) : Prop where
  hf : P.funs[x.f]? = some (vsQA2AE x.bm x.bas x.ann x.nil x.eig x.fix x.spl x.s.f)
  Bm : VsQABmAt P x.bm x.mpb x.itb x.locb x.phib x.idpb x.algb
  hbas : P.HasAt x.bas (vsWBasFuns x.bas)
  hann : P.HasAt x.ann (vsFAnnFuns x.ann)
  hnil : P.HasAt x.nil (vsFNilFuns x.nil)
  heig : P.HasAt x.eig (vsFEigFuns x.eig)
  hfix : P.HasAt x.fix (vsFFixFuns x.fix)
  hspl : P.HasAt x.spl (vsQSplFuns x.spl)
  S : VsQA2SAt P x.s hps hm hmb

/-- What step 2 returns: a correct split, or the tag `2` with the basis of `L` when `L` is a
field. -/
def VsQA2Out [Fact I.p.Prime] {s : VsQSt I} (hs : VsQStOK s) (as : List (Perm (Fin I.n))) (Tm : ℕ)
    (w : Val) : Prop :=
  (∃ ts cs lows, w = vsQSplitV ts cs lows ∧ VsQSplitOK s 278 Tm ts cs lows) ∨
    (w = .list [.nat 2, vsFMatsVal (vsHBm s (1 :: as))] ∧ vsTDom (vsTAlg (vsPBar hs (gens as))))

theorem VsQDSz.szN {S Tm N : ℕ} (hS : VsQDSz I S Tm) (hN : S ≤ N) : VsQSz I.p I.d (vsQExp I) N := by
  refine ⟨by have := hS.p; omega, by have := hS.d; omega, ?_, I.prime.pos⟩
  have h1 := hS.g
  have h2 : (Val.nat (vsQExp I)).wt < (vsQE I.p I.d (vsQExp I) 1).wt :=
    wt_le_wt_list (show Val.nat (vsQExp I) ∈ [Val.nat I.p, natList (List.replicate I.d 0),
      .nat (vsQExp I), .list ((vsQL (1 : Matrix (Fin I.d) (Fin I.d) (ZMod I.p))ᵀ).map natList)]
      by simp)
  have h3 : (vsQE I.p I.d (vsQExp I) 1).wt < (vsQGam I).wt :=
    wt_le_wt_list (show vsQE I.p I.d (vsQExp I) 1 ∈ [encGroup I.gs, vsQTable I,
      vsQE I.p I.d (vsQExp I) 1] by simp)
  omega

theorem vsQ_frOKN {S Tm N : ℕ} (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s) (hN : 4 * S ≤ N) :
    VsWFrOK I.p N I.d s.ws' (vsQCs s) := by
  have H := vsQ_frOK hS hs
  exact ⟨H.hp, H.hpN.trans hN, H.hdN.trans hN, H.h', H.hc, H.hl.trans hN⟩

/-- The size bound for the basis program. -/
def vsQNB (S : ℕ) : ℕ := 10 ^ 7 * S ^ 6

/-- The cost of the front of step 2. -/
noncomputable def vsQA2ACost (hps : PointwiseStab) (hm : Membership) (hmb : MinimalBlocks) (Cφ S : ℕ) : ℕ :=
  vsQABmCost Cφ (vsQNB S) + 128 * vsQA2TCost (I := I) hps hm hmb Cφ S

set_option maxHeartbeats 16000000 in
/-- **The front of step 2.** -/
theorem vsQA2A_spec [Fact I.p.Prime] {P : Program} {x : VsQA2AX} {hps : PointwiseStab}
    {hm : Membership} {hmb : MinimalBlocks} (L : VsQA2AAt P x hps hm hmb) {Cφ S Tm : ℕ}
    (hphiB : ∀ g ∈ gens I.gs, FunDet P x.phib (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hphi : ∀ g ∈ gens I.gs, FunDet P x.s.t.w.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hS : VsQDSz I S Tm) (hTm : (I.d + 1) ^ 278 ≤ Tm) {s : VsQSt I} (hs : VsQStOK s)
    (hD2 : 2 ≤ vsQD s) (hnab : ¬ s.Ab) {as : List (Perm (Fin I.n))} (has : gens as ≤ gens s.hs)
    (hasn : VsPNormd (gens s.hs) (gens as)) (hal : as.length ≤ I.n ^ 2)
    (habl : vsPBar hs (gens as) ≤ Subgroup.centralizer (vsPBar hs (gens as) : Set _)) :
    FunAll P x.f (.list [vsQLCV s, encGroup as]) (fun w c =>
      VsQA2Out hs as Tm w ∧ c ≤ 8 * vsQA2ACost (I := I) hps hm hmb Cφ S + 10 ^ 33 * S ^ 32) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have h := VsQAHyp.of_bm hs has hasn hal habl
  have hS1 := hS.one_le
  have hDd := vsQD_le hs
  have hSd := hS.d
  have hSp := hS.p
  have hSn := hS.n
  have hp1 := I.prime.one_lt
  set D := vsQD s with hD
  set Lb := vsHBm s (1 :: as)
  set N := 2 * S ^ 4 with hN
  set NB := vsQNB S with hNB
  have hS4 : S ≤ S ^ 4 := by have := hS.pow_le (show 1 ≤ 4 by omega); simpa using this
  have hS6 : S ^ 4 ≤ S ^ 6 := hS.pow_le (by omega)
  have hDS : D ≤ S := by omega
  have hDD : D * D ≤ S ^ 2 := by rw [sq]; exact Nat.mul_le_mul hDS hDS
  have hS24 : S ^ 2 ≤ S ^ 4 := hS.pow_le (by omega)
  have hpN : I.p ≤ N := by omega
  have hDN : D ≤ N := by omega
  have hDDN : D * D ≤ N := by omega
  have hLbl : Lb.length ≤ D * D := h.hLbl
  have hLbN : Lb.length ≤ N := by omega
  -- the values
  set lc := vsQLCV s
  set EG := encGroup as
  set A := Val.list [lc, EG]
  set frV := vsWFrVal I.p I.d s.ws' (vsQCs s)
  set MsV := vsFMatsVal (vsQMs s)
  have elc : lc = .list [vsQStV I s, frV, .nat D, MsV] := rfl
  have a0 : ∀ rest, Det P (A :: rest) (arg 0) lc (2 * A.wt + 0 + 5) := fun rest =>
    Det.arg' (P := P) (vs := [lc, EG]) (rest := rest) (j := 0) rfl
  have a1 : ∀ rest, Det P (A :: rest) (arg 1) EG (2 * A.wt + 1 + 5) := fun rest =>
    Det.arg' (P := P) (vs := [lc, EG]) (rest := rest) (j := 1) rfl
  have dp : ∀ rest, Det P (A :: rest) vsQLp (.nat I.p) _ := fun rest =>
    Det.get' (Det.get' (Det.get' (a0 rest) (Det.nat 1) rfl) (Det.nat 0) rfl) (Det.nat 0) rfl
  have dD : ∀ rest, Det P (A :: rest) vsQLd (.nat D) _ := fun rest =>
    Det.get' (a0 rest) (Det.nat 2) rfl
  -- 1. the basis of `L`
  have wLC : lc.wt ≤ 10 ^ 6 * S ^ 6 := vsQ_wt_LC hS hs
  have hNB1 : S ≤ NB := by
    have : S ≤ S ^ 6 := hS.pow_le (show 1 ≤ 6 by omega) |>.trans' (by simp)
    simp only [NB, vsQNB]; omega
  have hBm := vsQABm_spec L.Bm hphiB hs (as := as) (hS.szN hNB1) (hS.g.trans hNB1) (by omega)
    (vsQ_frOKN hS hs (by simp only [NB, vsQNB]; have : S ≤ S ^ 6 := hS.pow_le (show 1 ≤ 6 by omega) |>.trans' (by simp); omega))
    has (by
      have h1 : (1 :: as).length ≤ S ^ 2 := by
        have := hS.n
        have h2 : (I.n + 1) ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left hS.n 2
        have h3 : (I.n + 1) ^ 2 = I.n ^ 2 + 2 * I.n + 1 := by ring
        simp only [List.length_cons]; omega
      have h2 : D * D * (1 :: as).length ≤ S ^ 2 * S ^ 2 := Nat.mul_le_mul hDD h1
      have e : S ^ 2 * S ^ 2 = S ^ 4 := by ring
      have q16 : 1 ≤ S ^ 6 := Nat.one_le_pow _ _ hS1
      show 1 + D * D * (1 :: as).length ≤ 10 ^ 7 * S ^ 6
      omega)
    (by
      have h2 : (I.n + 1) ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left hS.n 2
      have h3 : (I.n + 1) ^ 2 = I.n ^ 2 + 2 * I.n + 1 := by ring
      have : S ^ 2 ≤ S ^ 6 := hS.pow_le (by omega)
      show as.length + 1 ≤ 10 ^ 7 * S ^ 6
      omega)
    (by show lc.wt ≤ 10 ^ 7 * S ^ 6; omega)
  have dBm := Det.call (Det.mk2 (a0 []) (a1 [])) hBm
  refine FunAll.intro L.hf (EvalAll.letE dBm fun v1 c1 hv1 => ?_)
  obtain ⟨rfl, hc1⟩ := hv1
  set LbV := vsFMatsVal Lb
  set E1 := [A, LbV]
  -- 2. the kernel of the nilpotent part
  have hLsq : ∀ M ∈ Lb, VsWSq I.p D M := h.sq
  have dvL : Det P E1 (.var 1) LbV (LbV.wt + 1) := Det.var' rfl
  have hNilL := vsFNilL_length hp1 hpN hDDN hLsq hLbN
  have dnil := Det.call (Det.mk3 (dp [LbV]) (dD [LbV]) dvL) (vsFNil_spec L.hnil hp1 hpN hDDN hLsq hLbN)
  have dann := Det.call (Det.mk3 (dp [LbV]) (dD [LbV]) dnil)
    (vsFAnn_spec L.hann hp1 hpN hDN (vsFNilL_sq I.prime.pos _) (by omega))
  set AnnL := vsFAnnL I.p D (vsFNilL I.p D Lb)
  have hAfit : VsWFit I.p D AnnL := vsFAnnL_fit hp1 _ _ (vsWId_fit hp1 _)
  have hAl : AnnL.length ≤ D := by
    have := vsFAnnL_length hp1 hpN hDN (vsFNilL I.p D Lb) (vsWId D)
      (vsFNilL_sq I.prime.pos _) (vsWId_fit hp1 D) (by simp [vsWId]; omega)
    simpa [AnnL, vsFAnnL, vsWId] using this
  have dbas := Det.call (Det.mk2 (dp [LbV]) dann) (vsWBas_spec L.hbas I.prime.pos hpN hDN hAfit (by omega))
  refine EvalAll.letE dbas fun v2 c2 hv2 => ?_
  obtain ⟨rfl, hc2⟩ := hv2
  set U := vsWBas I.p AnnL
  set E2 := [A, LbV, vsWVs U]
  have hUf : VsWFit I.p D U := vsWBas_fit I.prime.pos hAfit
  have hUsp : vsWSp I.p D U = vsWSp I.p D AnnL := vsWBas_span I.prime hAfit
  have hUl : U.length ≤ D := by
    rw [vsWBas_length I.prime hAfit]
    exact (Submodule.finrank_le _).trans (by rw [Module.finrank_fin_fun])
  have dlen := Det.length (Det.var' (P := P) (env := E2) (i := 2) rfl)
  rw [List.length_map] at dlen
  have dlt := Det.arith' (op := .lt) dlen (dD [LbV, vsWVs U]) rfl
  obtain ⟨hAbot, hAinv⟩ := vsQA_ann h (by omega)
  have hd2 : 2 ≤ I.d := by omega
  -- weights
  have wEG : EG.wt ≤ 320 * S ^ 6 := hS.wt_group hal
  have wA2 := wt_list2_le lc EG
  have eA : A.wt = (Val.list [lc, EG]).wt := rfl
  have q6 : S ^ 6 ≤ S ^ 32 := hS.pow_le (by omega)
  have q0 : 1 ≤ S ^ 32 := Nat.one_le_pow _ _ hS1
  have qS : S ≤ S ^ 32 := Nat.le_self_pow (by norm_num) _
  have hA' : A.wt ≤ 10 ^ 7 * S ^ 32 := by omega
  have hlcA : lc.wt < A.wt := wt_le_wt_list (by simp [A])
  have hfr : frV.wt < lc.wt := wt_le_wt_list (by simp [frV, MsV, D, lc, vsQLCV])
  have hDv : (Val.nat D).wt < lc.wt := wt_le_wt_list (by simp [frV, MsV, D, lc, vsQLCV])
  have hF0 : (Val.list [Val.nat I.p, Val.nat I.d, natList (vsWZ I.d), natList (vsWZ (vsQCs s).length)]).wt <
      frV.wt := wt_le_wt_list (by simp [frV, vsWFrVal])
  have hpv : (Val.nat I.p).wt < (Val.list [Val.nat I.p, Val.nat I.d, natList (vsWZ I.d),
      natList (vsWZ (vsQCs s).length)]).wt := wt_le_wt_list (by simp)
  have efr : frV.wt = (Val.list [Val.list [Val.nat I.p, Val.nat I.d, natList (vsWZ I.d),
      natList (vsWZ (vsQCs s).length)], vsWVs s.ws', vsWVs (vsQCs s),
      Val.list (List.map VsRow.val (vsWFrRows I.p s.ws' (vsQCs s)))]).wt := rfl
  have pw : ∀ k ≤ 8, (N + 1) ^ k ≤ 6561 * S ^ 32 := fun k hk => vsQ_powN hS1 hk
  have wLb : LbV.wt ≤ 40 * (N + 1) ^ 4 :=
    wt_vsFMatsVal_le hpN hDN (fun M hM => vsFSq_of_wSq (hLsq M hM)) (by omega)
  have wBmc : LbV.wt < vsQABmCost Cφ NB := FunDet.wt_lt' hBm
  have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 2; have := wt_nat_le 3
  have wc1 : c1 ≤ 2 * vsQABmCost Cφ NB + 10 ^ 9 * S ^ 32 := by
    have w2 := wt_list2_le lc EG
    clear_value lc EG A frV MsV LbV
    omega
  have wc2 : c2 ≤ 10 ^ 22 * S ^ 32 := by
    have := pw 7 (by omega); have := pw 6 (by omega); have := pw 5 (by omega); have := pw 4 (by omega)
    have wNil : (vsFMatsVal (vsFNilL I.p D Lb)).wt < 10 ^ 14 * (N + 1) ^ 7 :=
      FunDet.wt_lt' (vsFNil_spec L.hnil hp1 hpN hDDN hLsq hLbN)
    have wAnn : (vsWVs AnnL).wt < 10 ^ 9 * (N + 1) ^ 6 :=
      FunDet.wt_lt' (vsFAnn_spec L.hann hp1 hpN hDN (vsFNilL_sq I.prime.pos _) (by omega))
    have wU : (vsWVs U).wt < 5 * 10 ^ 7 * (N + 1) ^ 5 :=
      FunDet.wt_lt' (vsWBas_spec L.hbas I.prime.pos hpN hDN hAfit (by omega))
    have l1 := wt_list3_le (.nat I.p) (.nat D) LbV
    have l2 := wt_list3_le (.nat I.p) (.nat D) (vsFMatsVal (vsFNilL I.p D Lb))
    have l3 := wt_list2_le (.nat I.p) (vsWVs AnnL)
    clear_value lc EG A frV MsV LbV AnnL U
    omega
  have hTm1 : 1 ≤ Tm := le_trans (Nat.one_le_pow _ _ (by omega)) hTm
  set T2 := 128 * vsQA2TCost (I := I) hps hm hmb Cφ S + 10 ^ 30 * S ^ 32
  by_cases hlt : U.length < D
  · -- the chain split by the kernel
    have ev : GI.Machine.BinOp.lt.eval U.length D = 1 := by simp [GI.Machine.BinOp.eval, hlt]
    rw [ev] at dlt
    have dT := Det.call'' (Det.mk2c (a0 [LbV, vsWVs U]) (Det.var' (P := P) (env := E2) (i := 2) rfl))
      (vsQSpl_spec L.hspl hS hs hUf (by omega))
    refine Det.post (Det.ite_pos dlt one_ne_zero dT) fun c hc => ⟨Or.inl ⟨[1], s.hs, vsQSplLows s U, rfl,
      vsQ_split1 hs hTm1 (by rw [hUsp]; exact hAbot)
        (by rw [hUsp]; exact vsWSp_ne_top_of_bas I.prime hAfit hlt) (by rw [hUsp]; exact hAinv)⟩, ?_⟩
    have wO := vsQSpl_wt hS hs hd2 U
    have wU : (vsWVs U).wt ≤ 100 * S ^ 3 := vsQ_wt_loc hS hs hUf (by omega)
    have q3 : S ^ 3 ≤ S ^ 32 := hS.pow_le (by omega)
    have wDn := wt_nat_le D; have := wt_nat_le U.length
    have eW : (Val.list (List.map natList U)).wt = (vsWVs U).wt := rfl
    have w2 := wt_list2_le lc (vsWVs U)
    have tc : c ≤ 10 ^ 21 * S ^ 32 := by
      clear_value lc EG A frV MsV LbV AnnL U T2
      omega
    unfold vsQA2ACost
    rw [← hNB]
    clear_value lc EG A frV MsV LbV AnnL U T2
    omega
  · have ev : GI.Machine.BinOp.lt.eval U.length D = 0 := by simp [GI.Machine.BinOp.eval, hlt]
    rw [ev] at dlt
    have hAtop : vsWSp I.p D AnnL = ⊤ := vsWSp_top_of_bas I.prime hAfit (by show D ≤ U.length; omega)
    refine (EvalAll.vsQ_ite_zero' (R := fun w c => VsQA2Out hs as Tm w ∧ c ≤ 10 ^ 24 * S ^ 32 + 4 * T2 ∧
      w.wt ≤ 10 ^ 9 * S ^ 32 + T2) dlt ?_).mono fun w c hw => ?_
    swap
    · obtain ⟨ce, ⟨hout, hce, hw⟩, hc⟩ := hw
      refine ⟨hout, ?_⟩
      have wDn := wt_nat_le D; have := wt_nat_le U.length
      have eW : (Val.list (List.map natList U)).wt = (vsWVs U).wt := rfl
      have wU : (vsWVs U).wt ≤ 100 * S ^ 3 := vsQ_wt_loc hS hs hUf (by omega)
      have q3 : S ^ 3 ≤ S ^ 32 := hS.pow_le (by omega)
      unfold vsQA2ACost
      rw [← hNB]
      have eT : T2 = 128 * vsQA2TCost (I := I) hps hm hmb Cφ S + 10 ^ 30 * S ^ 32 := rfl
      clear_value lc EG A frV MsV LbV AnnL U T2
      omega
    -- 3. the pieces
    have hFl := vsFFixL_length hp1 hpN hDDN hLsq hLbN
    have dvL3 : Det P E2 (.var 1) LbV (LbV.wt + 1) := Det.var' rfl
    have dfix := Det.call (Det.mk3 (dp [LbV, vsWVs U]) (dD [LbV, vsWVs U]) dvL3)
      (vsFFix_spec L.hfix hp1 hpN hDDN hLsq hLbN)
    have deig := Det.call (Det.mk3 (dp [LbV, vsWVs U]) (dD [LbV, vsWVs U]) dfix)
      (vsFEig_spec L.heig I.prime hpN hDN (vsQAFix_sq (s := s) Lb) (by omega))
    refine EvalAll.letE deig fun v3 c3 hv3 => ?_
    obtain ⟨rfl, hc3⟩ := hv3
    set PcV := vsFMatsVal (vsFEigL I.p D (vsFFixL I.p D Lb))
    set E3 := [A, LbV, vsWVs U, PcV]
    have dlen3 := Det.length (Det.var' (P := P) (env := E3) (i := 3) rfl)
    rw [List.length_map] at dlen3
    have dlt2 := Det.arith' (op := .lt) dlen3 (Det.nat (P := P) (env := E3) 2) rfl
    have wc3 : c3 ≤ 10 ^ 22 * S ^ 32 := by
      have := pw 8 (by omega); have := pw 7 (by omega); have := pw 4 (by omega)
      have wFx : (vsFMatsVal (vsFFixL I.p D Lb)).wt < 10 ^ 14 * (N + 1) ^ 7 :=
        FunDet.wt_lt' (vsFFix_spec L.hfix hp1 hpN hDDN hLsq hLbN)
      have wPc : PcV.wt < 10 ^ 17 * (N + 1) ^ 8 :=
        FunDet.wt_lt' (vsFEig_spec L.heig I.prime hpN hDN (vsQAFix_sq (s := s) Lb) (by omega))
      have l1 := wt_list3_le (.nat I.p) (.nat D) LbV
      have l2 := wt_list3_le (.nat I.p) (.nat D) (vsFMatsVal (vsFFixL I.p D Lb))
      clear_value lc EG A frV MsV LbV AnnL U T2 PcV
      omega
    have ePc : PcV = vsFMatsVal (vsQAPcs s Lb) := rfl
    by_cases hm2 : (vsQAPcs s Lb).length < 2
    · -- one piece: `L` is a field
      have ev : GI.Machine.BinOp.lt.eval (vsFEigL I.p D (vsFFixL I.p D Lb)).length 2 = 1 := by
        simp only [GI.Machine.BinOp.eval]; exact if_pos hm2
      rw [ev] at dlt2
      have dout := Det.mk2 (Det.nat (P := P) (env := E3) 2) (Det.var' (P := P) (env := E3) (i := 1) rfl)
      refine Det.post (Det.ite_pos dlt2 one_ne_zero dout) fun c hc => ⟨Or.inr ⟨rfl, ?_⟩, ?_, ?_⟩
      · -- exactly one piece, and it is everything
        haveI : Nontrivial (Fin D → ZMod I.p) := by
          haveI : Nonempty (Fin D) := ⟨⟨0, by omega⟩⟩
          infer_instance
        have htopU := vsQAU_top h
        have h1 : 0 < (vsQAPcs s Lb).length := by
          by_contra h0
          have he : (vsQAPcs s Lb).length = 0 := by omega
          have : (⨆ k, vsQAU s Lb k) = ⊥ := by
            haveI : IsEmpty (Fin (vsQAPcs s Lb).length) := by rw [he]; infer_instance
            exact iSup_of_empty _
          rw [this] at htopU
          exact bot_ne_top htopU
        have hone : (vsQAPcs s Lb).length = 1 := by omega
        have hQ : (vsQAPcs s Lb)[0] ∈ vsQAPcs s Lb := List.getElem_mem h1
        have htopQ : vsWSp I.p D (vsQAPcs s Lb)[0] = ⊤ := by
          rw [← htopU]
          apply le_antisymm
          · exact le_iSup (vsQAU s Lb) ⟨0, h1⟩
          · refine iSup_le fun k => ?_
            have : k = ⟨0, h1⟩ := Fin.ext (by have := k.2; omega)
            rw [this]; rfl
        exact vsQA_field h hAtop hQ htopQ
      · have w2 := wt_list2_le (.nat 2) LbV
        have := pw 4 (by omega); have := pw 8 (by omega)
        have wPc : PcV.wt < 10 ^ 17 * (N + 1) ^ 8 :=
          FunDet.wt_lt' (vsFEig_spec L.heig I.prime hpN hDN (vsQAFix_sq (s := s) Lb) (by omega))
        have ePl : (Val.list (List.map (fun M => Val.list (List.map natList M))
          (vsFEigL I.p D (vsFFixL I.p D Lb)))).wt = PcV.wt := rfl
        have hl := length_lt_wt_list (List.map (fun M => Val.list (List.map natList M))
          (vsFEigL I.p D (vsFFixL I.p D Lb)))
        rw [List.length_map] at hl
        clear_value lc EG A frV MsV LbV AnnL U T2 PcV
        omega
      · have w2 := wt_list2_le (.nat 2) LbV
        have := pw 4 (by omega)
        clear_value lc EG A frV MsV LbV AnnL U T2 PcV
        omega
    · -- two or more pieces
      have ev : GI.Machine.BinOp.lt.eval (vsFEigL I.p D (vsFFixL I.p D Lb)).length 2 = 0 := by
        simp only [GI.Machine.BinOp.eval]; exact if_neg hm2
      rw [ev] at dlt2
      have hPcw : PcV.wt < 10 ^ 17 * (N + 1) ^ 8 :=
        FunDet.wt_lt' (vsFEig_spec L.heig I.prime hpN hDN (vsQAFix_sq (s := s) Lb) (by omega))
      have := pw 8 (by omega)
      refine (EvalAll.vsQ_ite_zero' dlt2 (R := fun w c => (∃ ts cs lows, w = vsQSplitV ts cs lows ∧
          VsQSplitOK s 278 Tm ts cs lows) ∧ c ≤ 10 ^ 22 * S ^ 32 + 2 * T2 + 1 ∧ w.wt ≤ T2)
        (EvalAll.call_funAll (Det.mk2 (a0 [LbV, vsWVs U, PcV])
        (Det.var' (P := P) (env := E3) (i := 3) rfl)) fun v ca hv => ?_)).mono fun w c hw => ?_
      · obtain ⟨rfl, hca⟩ := hv
        rw [ePc]
        refine (vsQA2S_spec L.S hphi hS hTm hs h (by omega) hD2 hnab).wt_lt.mono fun w cb hw => ?_
        obtain ⟨⟨hout, hcb⟩, hwc⟩ := hw
        refine ⟨hout, ?_, by omega⟩
        have w2 := wt_list2_le lc PcV
        have eT : T2 = 128 * vsQA2TCost (I := I) hps hm hmb Cφ S + 10 ^ 30 * S ^ 32 := rfl
        clear_value lc EG A frV MsV LbV AnnL U T2 PcV
        omega
      · obtain ⟨ce, ⟨hout, hce, hwT⟩, hc⟩ := hw
        refine ⟨Or.inl hout, ?_, by omega⟩
        have := pw 4 (by omega)
        have ePl : (Val.list (List.map (fun M => Val.list (List.map natList M))
          (vsFEigL I.p D (vsFFixL I.p D Lb)))).wt = PcV.wt := rfl
        have hl := length_lt_wt_list (List.map (fun M => Val.list (List.map natList M))
          (vsFEigL I.p D (vsFFixL I.p D Lb)))
        rw [List.length_map] at hl
        clear_value lc EG A frV MsV LbV AnnL U T2 PcV

        omega

end GI.Impl