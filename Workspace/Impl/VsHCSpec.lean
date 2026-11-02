import Workspace.Impl.VsHCProg

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

set_option maxHeartbeats 8000000 in
/-- The continuation has one step-4 call and satisfies the spine's `Q₈` hypothesis. -/
theorem vsHC_spec {I : VecStabInst} [Fact I.p.Prime] {P : Program} {x : VsHContX} {phi : ℕ}
    {hps : PointwiseStab} {hm : Membership} {hn : NormalClosure} {hd : DerivedSubgroup}
    (L : VsHContLay P x phi hps hm hn hd) {Cφ S Tm : ℕ}
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hS : VsQDSz I S Tm) (hTm : (I.d + 1) ^ 278 ≤ Tm)
    {s : VsQSt I} (hs : VsQStOK s) :
    VsQ8CHyp P x.q8c (vsHCQ hps hm hn hd Cφ I S) Tm hs := by
  intro as Lb ccs tcs ys r Lo ks hHand hnab hLo hks hksl hLol h0
  have hH := hHand.hyp
  have HH : VsHHardHand hs as Lb ccs tcs ys r :=
    ⟨hH, hHand.tmem, hHand.cov, by have := hHand.tl; omega,
      hHand.hys, hHand.ysl, hHand.rp, hHand.rn, hHand.hard⟩
  have H : VsHHyp hs as Lb ys r := ⟨hH.has, hH.hLb, hH.hspan, hHand.hys, hHand.hard⟩
  have hK : gens ks ≤ gens s.hs := fun g hg => hH.hcc ((hks g).1 hg).1
  obtain ⟨humem, hucov⟩ := vsHQ8_cover hs hH.hcc hLo hks
  set U := Lo.map Prod.snd
  set T := vsHCTrans tcs U
  obtain ⟨htmem, htcov⟩ := vsHCTrans_cover hHand.tmem
    (fun u hu => hH.hcc (humem u hu)) hHand.cov hucov
  have hTl : T.length ≤ 24 * vsQD s := by
    change (vsHCTrans tcs U).length ≤ _
    rw [vsHCTrans_length]
    have hu : U.length ≤ 24 := by simp only [U, List.length_map]; exact hLol
    have hh := Nat.mul_le_mul hHand.tl hu
    omega
  have hD2 := vsHC_dim_two H
  have hD := vsQD_le hs
  have hSd := hS.d
  have hSn := hS.n
  have hS1 := hS.one_le
  have hS2 : S ≤ S ^ 2 := Nat.le_self_pow (by omega) _
  have hTtm : T.length ≤ Tm := by
    calc T.length ≤ 24 * vsQD s := hTl
      _ ≤ (I.d + 1) ^ 3 * (I.d + 1) := Nat.mul_le_mul (by
        calc 24 ≤ 3 ^ 3 := by norm_num
          _ ≤ (I.d + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3) (by omega)
      _ = (I.d + 1) ^ 4 := by ring
      _ ≤ (I.d + 1) ^ 278 := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ Tm := hTm
  set N := 1000 * S ^ 2
  have hnN : I.n ≤ N := by dsimp [N]; omega
  have htN : tcs.length ≤ N := by have := hHand.tl; dsimp [N]; omega
  have huN : U.length ≤ N := by
    have : U.length ≤ 24 := by simp only [U, List.length_map]; exact hLol
    dsimp [N]; omega
  have htuN : tcs.length * U.length ≤ N := by
    have hu : U.length ≤ 24 := by simp only [U, List.length_map]; exact hLol
    have ht : tcs.length ≤ S := hHand.tl.trans (by omega)
    have hh := Nat.mul_le_mul ht hu
    dsimp [N]; omega
  have hTr := vsHCTrans_spec L.T hnN tcs U htN huN htuN
  have hAb := vsHCAb_spec L.H L.S L.hab L.pStep hphi hS hs HH hK hksl
  set G := vsPGIn s as Lb ccs tcs ys r
  set lc := vsQLCV s
  set TV := Val.list (T.map encPerm)
  set V8 := Val.list [.nat 2, .list (U.map encPerm), encGroup ks]
  set A := Val.list [lc, G, V8]
  set M := 10 ^ 30 * (S + 1) ^ 30
  set CT := 10 ^ 12 * (N + 1) ^ 7
  set ST := vsPStep4Cost (I := I) Cφ hn hd S + 10 ^ 7 * (vsPN S + 1) * (10 ^ 9 * S ^ 8)
  set CH := vsHHardCH hps hm Cφ I S
  set CP := vsHCProdCost hps hm I.n Cφ S
  set R := CH + ST + vsHCAbCost Cφ S + CT + CP + M
  have eCQ : vsHCQ hps hm hn hd Cφ I S = 10 ^ 8 * R := by dsimp [vsHCQ, R, CH, ST, CT, CP, M, N]; ring
  have hM : M ≤ R := by dsimp [R]; omega
  have hCT : CT ≤ R := by dsimp [R]; omega
  have hST : ST ≤ R := by dsimp [R]; omega
  have hCH : CH ≤ R := by dsimp [R]; omega
  have hCP : CP ≤ R := by dsimp [R]; omega
  have hCA : vsHCAbCost Cφ S ≤ R := by dsimp [R]; omega
  have hM1 : 10 ^ 30 ≤ M := by have := Nat.one_le_pow 30 (S + 1) (by omega); dsimp [M]; omega
  have hR1 : 1000 ≤ R := by omega
  have p6 : S ^ 6 ≤ (S + 1) ^ 30 := (Nat.pow_le_pow_left (Nat.le_succ S) 6).trans
    (Nat.pow_le_pow_right (by omega) (by omega))
  have p8 : S ^ 8 ≤ (S + 1) ^ 30 := (Nat.pow_le_pow_left (Nat.le_succ S) 8).trans
    (Nat.pow_le_pow_right (by omega) (by omega))
  have hWM : 10 ^ 9 * S ^ 8 ≤ M := by dsimp [M]; omega
  have hLM : 10 ^ 6 * S ^ 6 ≤ M := by dsimp [M]; omega
  have hKM : 320 * S ^ 6 ≤ M := by dsimp [M]; omega
  have wG : G.wt ≤ R := (vsHC_wt_hand hS hs HH).trans (hWM.trans hM)
  have wlc : lc.wt ≤ R := (vsQ_wt_LC hS hs).trans (hLM.trans hM)
  have wks : (encGroup ks).wt ≤ R := (hS.wt_group hksl).trans (hKM.trans hM)
  have wU : (Val.list (U.map encPerm)).wt ≤ R := by
    have hh := vsP_wt_perms hnN U (by omega)
    have pp : (N + 1) ^ 3 ≤ (N + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
    have hhCT : 10 ^ 12 * (N + 1) ^ 7 ≤ R := hCT
    omega
  have wT : TV.wt ≤ R := (FunDet.wt_lt' hTr).le.trans hCT
  have wV8 := wt_list3_le (.nat 2) (.list (U.map encPerm)) (encGroup ks)
  have wA := wt_list3_le lc G V8
  have w2 := wt_nat_le 2
  have wV8' : V8.wt ≤ 10 * R := by change V8.wt ≤ _ at wV8; omega
  have wA' : A.wt ≤ 100 * R := by change A.wt ≤ _ at wA; omega
  have wb : (boolVal (decide (∀ g ∈ 1 :: ks, ∀ h ∈ 1 :: ks,
      vsPLocL I s.ws' (vsQCs s) (g * h) = vsPLocL I s.ws' (vsQCs s) (h * g)))).wt ≤ R :=
    (FunDet.wt_lt' hAb).le.trans hCA
  have eV8 : Val.list [.nat 2, .list (Lo.map fun q => encPerm q.2), encGroup ks] = V8 := by
    simp [V8, U, List.map_map, Function.comp_def]
  rw [eV8]
  have a0 : ∀ rest, Det P (A :: rest) (arg 0) lc (2 * A.wt + 0 + 5) := fun rest =>
    Det.arg' (P := P) (vs := [lc, G, V8]) (rest := rest) (j := 0) rfl
  have a1 : ∀ rest, Det P (A :: rest) (arg 1) G (2 * A.wt + 1 + 5) := fun rest =>
    Det.arg' (P := P) (vs := [lc, G, V8]) (rest := rest) (j := 1) rfl
  have a2 : ∀ rest, Det P (A :: rest) (arg 2) V8 (2 * A.wt + 2 + 5) := fun rest =>
    Det.arg' (P := P) (vs := [lc, G, V8]) (rest := rest) (j := 2) rfl
  have dtcs := Det.get' (a1 []) (Det.nat 7) (show [vsQGam I, encGroup s.hs, vsWVs s.ws',
    vsWVs s.ws, vsWFrVal I.p I.d s.ws' (vsQCs s), encGroup as, encGroup ccs,
    Val.list (tcs.map encPerm), Val.list (ys.map encPerm), .nat r, vsFMatsVal Lb][7]? =
      some (.list (tcs.map encPerm)) from rfl)
  have du := Det.get' (a2 []) (Det.nat 1)
    (show [Val.nat 2, Val.list (U.map encPerm), encGroup ks][1]? = some (.list (U.map encPerm)) from rfl)
  have dtr := Det.call (Det.mk2 dtcs du) hTr
  have wts : (Val.list (tcs.map encPerm)).wt < G.wt := wt_le_wt_list (by simp [G, vsPGIn])
  have eTV : (Val.list ((vsHCTrans tcs U).map encPerm)).wt = TV.wt := rfl
  have eA : (Val.list [lc, G, V8]).wt = A.wt := rfl
  have wtarg := wt_list2_le (.list (tcs.map encPerm)) (.list (U.map encPerm))
  refine FunAll.intro L.hq (EvalAll.letE dtr fun v1 c1 hv1 => ?_)
  obtain ⟨rfl, hc1⟩ := hv1
  have hc1R : c1 ≤ 10000 * R := by omega
  have dk := Det.get' (a2 [TV]) (Det.nat 2)
    (show [Val.nat 2, Val.list (U.map encPerm), encGroup ks][2]? = some (encGroup ks) from rfl)
  have da := Det.call (Det.mk2 (a1 [TV]) dk) hAb
  have wabarg := wt_list2_le G (encGroup ks)
  refine EvalAll.letE da fun v2 c2 hv2 => ?_
  obtain ⟨rfl, hc2⟩ := hv2
  have hc2R : c2 ≤ 10000 * R := by omega
  set b := boolVal (decide (∀ g ∈ 1 :: ks, ∀ h ∈ 1 :: ks,
    vsPLocL I s.ws' (vsQCs s) (g * h) = vsPLocL I s.ws' (vsQCs s) (h * g)))
  have wbR : b.wt ≤ R := wb
  set E2 := [A, TV, b]
  have db := Det.var' (P := P) (env := E2) (i := 2) (v := b) rfl
  refine EvalAll.ite db (fun vc cc hvc => ⟨_, hvc.1⟩) fun xb cb hxb => ?_
  obtain ⟨hxb, hcb⟩ := hxb
  by_cases ht : ∀ g ∈ 1 :: ks, ∀ h ∈ 1 :: ks,
      vsPLocL I s.ws' (vsQCs s) (g * h) = vsPLocL I s.ws' (vsQCs s) (h * g)
  · have hx : xb = 1 := by
      have he : Val.nat xb = .nat 1 := by simpa only [b, decide_eq_true ht] using hxb
      exact Val.nat.inj he
    subst xb
    rw [if_neg one_ne_zero]
    have dks := Det.get' (a2 [TV, b]) (Det.nat 2)
      (show [Val.nat 2, Val.list (U.map encPerm), encGroup ks][2]? = some (encGroup ks) from rfl)
    have dws := Det.get' (a1 [TV, b]) (Det.nat 2)
      (show [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws,
        vsWFrVal I.p I.d s.ws' (vsQCs s), encGroup as, encGroup ccs,
        Val.list (tcs.map encPerm), Val.list (ys.map encPerm), Val.nat r, vsFMatsVal Lb][2]? =
          some (vsWVs s.ws') from rfl)
    have ds := Det.mk4 (Det.nat (P := P) (env := E2) 1)
      (Det.var' (P := P) (env := E2) (i := 1) (v := TV) rfl) dks (Det.mk1 dws)
    have hok := vsHC_splitOK hs (E := 278) hksl hK htmem htcov hTtm
      (vsQAb_of_comm hs hK (vsQ_comm_of_test hs hK ht)) hnab hD2 hTl
    refine ds.post fun c hc => ⟨Or.inl ⟨T, ks, [s.ws'], rfl, hok⟩, ?_⟩
    have wws : (vsWVs s.ws').wt < G.wt := wt_le_wt_list (by simp [G, vsPGIn])
    have wl := wt_list1_le (vsWVs s.ws')
    have wo := wt_list4_le (.nat 1) TV (encGroup ks) (.list [vsWVs s.ws'])
    have w1 := wt_nat_le 1
    have eOut : (vsQSplitV T ks [s.ws']).wt =
        (Val.list [.nat 1, TV, encGroup ks, .list [vsWVs s.ws']]).wt := rfl
    rw [eCQ]
    omega
  · have hx : xb = 0 := by
      have he : Val.nat xb = .nat 0 := by simpa only [b, decide_eq_false ht] using hxb
      exact Val.nat.inj he
    subst xb
    rw [if_pos rfl]
    have hNext := H.q8_next hH hks hksl (vsQ_nab_of_test hs hK ht)
    set In := vsPIn s as Lb ks T
    have wIn : In.wt ≤ 10 ^ 9 * S ^ 8 := vsHC_wt_in hS hs hH.hal
      (fun M hM => ⟨fun a ha => (hH.hLb M hM).rows a ha, (hH.hLb M hM).len⟩) hH.hLbl hksl hTl
    have hSt := vsPStep4_spec L.hst4 L.S (L.pStep ▸ hphi) hS hs hNext (tcs := T)
    have stBound : vsPStep4Cost (I := I) Cφ hn hd S +
        10 ^ 7 * (vsPN S + 1) * In.wt ≤ ST := by
      exact Nat.add_le_add_left (Nat.mul_le_mul_left (10 ^ 7 * (vsPN S + 1)) wIn) _
    have dAs := Det.get' (a1 [TV, b]) (Det.nat 5) (show [vsQGam I, encGroup s.hs,
      vsWVs s.ws', vsWVs s.ws, vsWFrVal I.p I.d s.ws' (vsQCs s), encGroup as, encGroup ccs,
      Val.list (tcs.map encPerm), Val.list (ys.map encPerm), Val.nat r, vsFMatsVal Lb][5]? = some (encGroup as) from rfl)
    have dLb := Det.get' (a1 [TV, b]) (Det.nat 10) (show [vsQGam I, encGroup s.hs,
      vsWVs s.ws', vsWVs s.ws, vsWFrVal I.p I.d s.ws' (vsQCs s), encGroup as, encGroup ccs,
      Val.list (tcs.map encPerm), Val.list (ys.map encPerm), Val.nat r, vsFMatsVal Lb][10]? = some (vsFMatsVal Lb) from rfl)
    have dks := Det.get' (a2 [TV, b]) (Det.nat 2)
      (show [Val.nat 2, Val.list (U.map encPerm), encGroup ks][2]? = some (encGroup ks) from rfl)
    have dIn := Det.vsPMk5 (a0 [TV, b]) dAs dLb dks
      (Det.var' (P := P) (env := E2) (i := 1) (v := TV) rfl)
    have was : (encGroup as).wt < G.wt := wt_le_wt_list (by simp [G, vsPGIn])
    have wLb : (vsFMatsVal Lb).wt < G.wt := wt_le_wt_list (by simp [G, vsPGIn])
    have wInR : In.wt ≤ R := wIn.trans (hWM.trans hM)
    have eIn : (Val.list [lc, encGroup as, vsFMatsVal Lb, encGroup ks, TV]).wt = In.wt := rfl
    refine EvalAll.letE (Ra := fun w c => VsPOut hs as Lb ks T w ∧ c ≤ 10000 * R ∧ w.wt ≤ R)
      (EvalAll.call_funAll dIn fun v ca hv => ?_) fun v3 c3 hv3 => ?_
    · obtain ⟨rfl, hca⟩ := hv
      refine hSt.wt_lt.mono fun w c hw => ?_
      obtain ⟨⟨hout, hc⟩, hwt⟩ := hw
      have hcST : c ≤ ST := hc.trans stBound
      refine ⟨hout, ?_, (hwt.le.trans hcST).trans hST⟩
      omega
    obtain ⟨hout3, hc3, w3⟩ := hv3
    rcases hout3 with ⟨as', rfl, hgr⟩ | ⟨ys', r', rfl, hysH, hysK, hysl, hrp, hrn, hhard⟩
    · set V3 := Val.list [.nat 0, encGroup as']
      have eV3 : (Val.list [.nat 0, encGroup as']).wt = V3.wt := rfl
      have wV3R : V3.wt ≤ R := w3
      set E3 := [A, TV, b, V3]
      have dz := Det.get' (Det.var' (P := P) (env := E3) (i := 3) rfl) (Det.nat 0)
        (show [Val.nat 0, encGroup as'][0]? = some (.nat 0) from rfl)
      refine (Det.ite_zero dz (Det.var' (P := P) (env := E3) (i := 3) rfl)).post fun c hc =>
        ⟨Or.inr ⟨as', rfl, hgr⟩, ?_⟩
      have wz := wt_nat_le 0
      rw [eCQ]
      omega
    · set G' := vsPGIn s as Lb ks T ys' r'
      set V3 := Val.list [.nat 1, G']
      have eV3 : (Val.list [.nat 1, G']).wt = V3.wt := rfl
      have wV3R : V3.wt ≤ R := w3
      set E3 := [A, TV, b, V3]
      have HH' : VsHHardHand hs as Lb ks T ys' r' :=
        ⟨hNext, htmem, htcov, hTl, hysH, hysl, hrp, hrn, hhard⟩
      have hHard := vsHHard_run L.H hphi hS hTm hs as Lb ks T ys' r' HH' hnab
      have dtag := Det.get' (Det.var' (P := P) (env := E3) (i := 3) rfl) (Det.nat 0)
        (show [Val.nat 1, G'][0]? = some (.nat 1) from rfl)
      have dG' := Det.get' (Det.var' (P := P) (env := E3) (i := 3) rfl) (Det.nat 1)
        (show [Val.nat 1, G'][1]? = some G' from rfl)
      have wG' : G'.wt < V3.wt := wt_le_wt_list (by simp [V3])
      have w1 := wt_nat_le 1
      refine EvalAll.ite dtag (fun vc cc hvc => ⟨_, hvc.1⟩) fun xt ct hxt => ?_
      obtain ⟨hxt, hct⟩ := hxt
      have hx : xt = 1 := by simpa using hxt
      subst xt
      rw [if_neg one_ne_zero]
      have wHarg := wt_list2_le lc G'
      refine EvalAll.letE (Ra := fun w c => VsQHardOut hs Lb ks ys' r' Tm w ∧
          c ≤ 10000 * R ∧ w.wt ≤ R)
        (EvalAll.call_funAll (Det.mk2 (a0 [TV, b, V3]) dG') fun v ca hv => ?_) fun v4 c4 hv4 => ?_
      · obtain ⟨rfl, hca⟩ := hv
        refine hHard.wt_lt.mono fun w c hw => ?_
        obtain ⟨⟨hout, hc⟩, hwt⟩ := hw
        have hcR : c ≤ R := hc.trans hCH
        exact ⟨hout, by omega, hwt.le.trans hcR⟩
      obtain ⟨hout4, hc4, w4⟩ := hv4
      rcases hout4 with ⟨Lo', ks', rfl, hLo', hks', hksl', hLol', h0'⟩ | ⟨ts', cs', lows', rfl, hok⟩
      · set V4 := Val.list [.nat 2, .list (Lo'.map fun q => encPerm q.2), encGroup ks']
        have eV4 : (Val.list [.nat 2, .list (Lo'.map fun q => encPerm q.2), encGroup ks']).wt = V4.wt := rfl
        have wV4R : V4.wt ≤ R := w4
        set E4 := [A, TV, b, V3, V4]
        have de := Det.arith' (op := .eq) (Det.get' (Det.var' (P := P) (env := E4) (i := 4) rfl)
          (Det.nat 0) (show [Val.nat 2, .list (Lo'.map fun q => encPerm q.2), encGroup ks'][0]? =
            some (.nat 2) from rfl)) (Det.nat (P := P) (env := E4) 2) rfl
        have hP := vsHCProd_spec L.H L.hprod L.hhead L.T.hc hphi hS hTm hs hnab HH HH' hks hysK h0 h0'
        have dG'' := Det.get' (Det.var' (P := P) (env := E4) (i := 3) rfl) (Det.nat 1)
          (show [Val.nat 1, G'][1]? = some G' from rfl)
        have wpArg := wt_list3_le lc G G'
        refine EvalAll.ite de (fun vc cc hvc => ⟨_, hvc.1⟩) fun xe ce hxe => ?_
        obtain ⟨hxe, hce⟩ := hxe
        have hx : xe = 1 := by simpa using hxe
        subst xe
        rw [if_neg one_ne_zero]
        refine EvalAll.call_funAll (Det.mk3 (a0 [TV, b, V3, V4]) (a1 [TV, b, V3, V4]) dG'')
          fun v ca hv => ?_
        obtain ⟨rfl, hca⟩ := hv
        refine hP.wt_lt.mono fun w c hw => ?_
        obtain ⟨⟨hout, hc⟩, hwt⟩ := hw
        have hcR : c ≤ R := hc.trans hCP
        refine ⟨Or.inl hout, ?_⟩
        have wtag : (Val.nat 2).wt < V4.wt := wt_le_wt_list (by simp [V4])
        have ev : GI.Machine.BinOp.eval .eq 2 2 = 1 := rfl
        have wev := wt_nat_le (GI.Machine.BinOp.eval .eq 2 2)
        rw [eCQ]
        omega
      · set V4 := vsQSplitV ts' cs' lows'
        have eV4 : (Val.list [.nat 1, .list (ts'.map encPerm), encGroup cs', vsQLowsV lows']).wt = V4.wt := rfl
        have wV4R : V4.wt ≤ R := w4
        set E4 := [A, TV, b, V3, V4]
        have de := Det.arith' (op := .eq) (Det.get' (Det.var' (P := P) (env := E4) (i := 4) rfl)
          (Det.nat 0) (show [Val.nat 1, .list (ts'.map encPerm), encGroup cs', vsQLowsV lows'][0]? =
            some (.nat 1) from rfl)) (Det.nat (P := P) (env := E4) 2) rfl
        have ev : GI.Machine.BinOp.eval .eq 1 2 = 0 := rfl
        rw [ev] at de
        refine (Det.ite_zero de (Det.var' (P := P) (env := E4) (i := 4) rfl)).post fun c hc =>
          ⟨Or.inl ⟨ts', cs', lows', rfl, hok⟩, ?_⟩
        have wtag : (Val.nat 1).wt < V4.wt := wt_le_wt_list (by simp [V4, vsQSplitV])
        have wz := wt_nat_le 0
        rw [eCQ]
        omega

end GI.Impl
