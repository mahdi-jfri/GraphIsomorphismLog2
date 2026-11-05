module

public import Workspace.Impl.VsHCAb

@[expose] public section

open Matrix Module

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

/-- On `[lc,G,G']`, split using the product of the first elements of the two bases. -/
def vsHCProdE (head comp ps wr : ℕ) : Expr :=
  .letE (.call head (arg 1))
  (.letE (.call head (arg 2))
  (.letE (.call comp (mk2 (.var 1) (.var 2)))
  (.letE (.call ps (mk2 (arg 1) (mk1 (.var 3))))
    (.call wr (mk3 (arg 0) (.var 4) (.nat 72))))))

noncomputable def vsHCProdCost (hps : PointwiseStab) (hm : Membership) (n Cφ S : ℕ) : ℕ :=
  10 ^ 6 * (vsHCHeadCost Cφ S + vsHPsCost Cφ (10 ^ 9 * S ^ 8) +
    vsHWCost hps hm n S Cφ 72 + 10 ^ 20 * (S + 1) ^ 20)

set_option maxHeartbeats 4000000 in
/-- Two commuting `Q₈` hand-offs lead directly to a split, with no further step-4 call. -/
theorem vsHCProd_spec {I : VecStabInst} [Fact I.p.Prime] {P : Program}
    {x : VsHHX} {phi f head comp : ℕ} {hps : PointwiseStab} {hm : Membership}
    (L : VsHHardLink P x phi hps hm)
    (hf : P.funs[f]? = some (vsHCProdE head comp x.pp.ps x.w.f))
    (hhead : P.funs[head]? = some (vsHCHeadE x.fr)) (hcomp : P.HasAt comp (composeFuns comp))
    {Cφ S Tm : ℕ}
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hS : VsQDSz I S Tm) (hTm : (I.d + 1) ^ 278 ≤ Tm)
    {s : VsQSt I} (hs : VsQStOK s) (hnab : ¬ s.Ab)
    {as : List (Perm (Fin I.n))} {Lb : List (List (List ℕ))}
    {ccs tcs ys ks ts ys' : List (Perm (Fin I.n))} {r r' : ℕ}
    (h : VsHHardHand hs as Lb ccs tcs ys r)
    (h' : VsHHardHand hs as Lb ks ts ys' r')
    (hks : ∀ g, g ∈ gens ks ↔ g ∈ gens ccs ∧
      vsHAlT s g ((vsHB s Lb r ys).map (vsHT s)) = (vsHB s Lb r ys).map (vsHT s))
    (hy' : ∀ y ∈ ys', y ∈ gens ks)
    (h0 : (vsHK s Lb r ys).length = 0) (h0' : (vsHK s Lb r' ys').length = 0) :
    FunAll P f (.list [vsQLCV s, vsPGIn s as Lb ccs tcs ys r, vsPGIn s as Lb ks ts ys' r'])
      (fun w c => VsQSplOK (s := s) Tm w ∧ c ≤ vsHCProdCost hps hm I.n Cφ S) := by
  have H : VsHHyp hs as Lb ys r := ⟨h.hyp.has, h.hyp.hLb, h.hyp.hspan, h.hys, h.hard⟩
  have H' : VsHHyp hs as Lb ys' r' := ⟨h'.hyp.has, h'.hyp.hLb, h'.hyp.hspan, h'.hys, h'.hard⟩
  have hr : r = 2 := (H.q8 h0 h.hyp.hccC).1
  have hr' : r' = 2 := (H'.q8 h0' h'.hyp.hccC).1
  subst r
  subst r'
  set y := vsHCHead s Lb 2 ys
  set z := vsHCHead s Lb 2 ys'
  obtain ⟨hy, hyY, hyS⟩ := vsHC_head H
  obtain ⟨hz, hzY, hzS⟩ := vsHC_head H'
  have hYY := vsHC_next_cent h.hyp H hks hy'
  have hi := vsHC_empty_iso H h0
  have hi' := vsHC_empty_iso H' h0'
  set Ps := vsHPs s ((1 :: as) ++ [y * z])
  obtain ⟨hfit, hlen, hind, hdim, htop, horb⟩ :=
    vsH_q8two_pieces hs h.hyp.has h.hard hi h'.hard hi' hYY hy hz hyY hyS hzY hzS
  have hD2 := vsHC_dim_two H
  have hD := vsQD_le hs
  have hSd := hS.d
  have hcnt := vsFEigL_cnt I.prime (vsHFx s ((1 :: as) ++ [y * z])) (vsHFx_sq _)
  have hsum : (Ps.map List.length).sum ≤ S := hcnt.2.trans (by omega)
  have hb : Ps.length ≤ S := by change Ps.length = 2 at hlen; omega
  have hW := vsQTSplit_spec hps hm L.toVsHHLay.W.H L.toVsHHLay.W.HK L.toVsHHLay.W.HL
    L.toVsHHLay.W.HA L.toVsHHLay.W.hjp L.toVsHHLay.W.hjm (L.p4 ▸ hphi) hS hs hfit hb hsum horb
  have hY := vsHCHead_spec L hhead hphi hS hs h
  have hZ := vsHCHead_spec L hhead hphi hS hs h'
  have hP := vsHC_ps_spec L hphi hS hs h (K := [y * z])
    (by intro g hg; simp only [List.mem_singleton] at hg; subst g; exact mul_mem hy hz)
    (by simp; nlinarith only [hD2])
  set G := vsPGIn s as Lb ccs tcs ys 2
  set G' := vsPGIn s as Lb ks ts ys' 2
  set lc := vsQLCV s
  set A := Val.list [lc, G, G']
  set PV := vsFMatsVal Ps
  set M := 10 ^ 20 * (S + 1) ^ 20
  set R := vsHCHeadCost Cφ S + vsHPsCost Cφ (10 ^ 9 * S ^ 8) +
    vsHWCost hps hm I.n S Cφ 72 + M
  have hM1 : 1 ≤ M := by have := Nat.one_le_pow 20 (S + 1) (by omega); dsimp [M]; omega
  have hR1 : 1 ≤ R := by dsimp [R]; omega
  have whY : (encPerm y).wt < vsHCHeadCost Cφ S := FunDet.wt_lt' hY
  have whZ : (encPerm z).wt < vsHCHeadCost Cφ S := FunDet.wt_lt' hZ
  have wp : PV.wt < vsHPsCost Cφ (10 ^ 9 * S ^ 8) := FunDet.wt_lt' hP
  have h8 : S ^ 8 ≤ (S + 1) ^ 20 := (Nat.pow_le_pow_left (Nat.le_succ S) 8).trans
    (Nat.pow_le_pow_right (by omega) (by omega))
  have h6 : S ^ 6 ≤ (S + 1) ^ 20 := (Nat.pow_le_pow_left (Nat.le_succ S) 6).trans
    (Nat.pow_le_pow_right (by omega) (by omega))
  have h3 : (I.n + 1) ^ 3 ≤ (S + 1) ^ 20 :=
    (Nat.pow_le_pow_left (hS.n.trans (Nat.le_succ S)) 3).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  have h2 : S ^ 2 ≤ (S + 1) ^ 20 := (Nat.pow_le_pow_left (Nat.le_succ S) 2).trans
    (Nat.pow_le_pow_right (by omega) (by omega))
  have wG : G.wt ≤ M := by have := vsHC_wt_hand hS hs h; dsimp [G, M]; omega
  have wG' : G'.wt ≤ M := by have := vsHC_wt_hand hS hs h'; dsimp [G', M]; omega
  have wlc : lc.wt ≤ M := by have := vsQ_wt_LC hS hs; dsimp [lc, M]; omega
  have we : (encPerm (y * z)).wt ≤ M := by have := hS.wt_perm (y * z); dsimp [M]; omega
  have wc : permK * (I.n + 1) ^ 3 ≤ M := by dsimp [M, permK]; omega
  have wA := wt_list3_le lc G G'
  have wYZ := wt_list2_le (encPerm y) (encPerm z)
  have wK := wt_list1_le (encPerm (y * z))
  have wPK := wt_list2_le G (.list [encPerm (y * z)])
  have w72 := wt_nat_le 72
  have wW := wt_list3_le lc PV (.nat 72)
  have a1 := Det.arg' (P := P) (vs := [lc, G, G']) (rest := []) (j := 1) rfl
  have dy := Det.call a1 hY
  refine FunAll.intro hf (EvalAll.letE dy fun v1 c1 hv1 => ?_)
  obtain ⟨rfl, hc1⟩ := hv1
  have a2 := Det.arg' (P := P) (vs := [lc, G, G']) (rest := [encPerm y]) (j := 2) rfl
  have dz := Det.call a2 hZ
  refine EvalAll.letE dz fun v2 c2 hv2 => ?_
  obtain ⟨rfl, hc2⟩ := hv2
  set E2 := [A, encPerm y, encPerm z]
  have de := Det.call (Det.mk2 (Det.var' (P := P) (env := E2) (i := 1) rfl)
    (Det.var' (P := P) (env := E2) (i := 2) rfl)) (compose_spec hcomp y z)
  refine EvalAll.letE de fun v3 c3 hv3 => ?_
  obtain ⟨rfl, hc3⟩ := hv3
  set E3 := [A, encPerm y, encPerm z, encPerm (y * z)]
  have dK := Det.mk1 (Det.var' (P := P) (env := E3) (i := 3) rfl)
  have aG := Det.arg' (P := P) (vs := [lc, G, G']) (rest := [encPerm y, encPerm z, encPerm (y * z)]) (j := 1) rfl
  have dp := Det.call (Det.mk2 aG dK) hP
  refine EvalAll.letE dp fun v4 c4 hv4 => ?_
  obtain ⟨rfl, hc4⟩ := hv4
  set E4 := [A, encPerm y, encPerm z, encPerm (y * z), PV]
  have al := Det.arg' (P := P) (vs := [lc, G, G'])
    (rest := [encPerm y, encPerm z, encPerm (y * z), PV]) (j := 0) rfl
  refine EvalAll.call_funAll (Det.mk3 al (Det.var' (P := P) (env := E4) (i := 4) rfl) (Det.nat 72))
    fun v ca hv => ?_
  obtain ⟨rfl, hca⟩ := hv
  refine hW.wt_lt.mono fun w c hw => ?_
  obtain ⟨⟨⟨Lo, cs, rfl, hLo, hcs, hcsl⟩, hc⟩, hwt⟩ := hw
  have h72 : 72 ≤ Tm := by
    calc 72 ≤ 3 ^ 4 := by norm_num
      _ ≤ (I.d + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
      _ ≤ (I.d + 1) ^ 278 := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ Tm := hTm
  have hLoTm : Lo.length ≤ Tm := (hLo.length_eq ▸ horb).trans h72
  have hout := (vsH_q8two_splitOK hs h.hyp.has h.hard hi h'.hard hi' hYY hy hz hyY hyS hzY hzS
    hLo hcs hcsl hLoTm hnab).1
  refine ⟨⟨_, cs, _, rfl, hout⟩, ?_⟩
  have hcW : c ≤ vsHWCost hps hm I.n S Cφ 72 := hc
  have ey : (encPerm (vsHCHead s Lb 2 ys)).wt = (encPerm y).wt := rfl
  have ez : (encPerm (vsHCHead s Lb 2 ys')).wt = (encPerm z).wt := rfl
  have eA : (Val.list [lc, G, G']).wt = A.wt := rfl
  have ePV : (vsFMatsVal (vsHPs s ((1 :: as) ++ [y * z]))).wt = PV.wt := rfl
  have hM : M ≤ R := by dsimp [R]; omega
  have hHC : vsHCHeadCost Cφ S ≤ R := by dsimp [R]; omega
  have hPC : vsHPsCost Cφ (10 ^ 9 * S ^ 8) ≤ R := by dsimp [R]; omega
  have hWC : vsHWCost hps hm I.n S Cφ 72 ≤ R := by dsimp [R]; omega
  change _ ≤ 10 ^ 6 * R
  omega

end GI.Impl
