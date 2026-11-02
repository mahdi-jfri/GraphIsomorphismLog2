import Workspace.Impl.VsQA2TM

/-!
# The transitive case

On `[lc, pieces]`, when `H` moves the pieces transitively, the program `vsQA2TE` computes the
tables of the generators, a minimal block system (`MinimalBlocks`), the block sums, and the split
by the tuple of block sums (`vsQTSplit_spec`). The result is a correct split, case 2
(`vsQA2T_spec`).
-/

open Matrix Module

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

variable {I : VecStabInst}

/-- `p`, `D` and the local matrices, read from the local context in argument 0. -/
def vsQLp : Expr := .get (.get (.get (arg 0) (.nat 1)) (.nat 0)) (.nat 0)
def vsQLd : Expr := .get (arg 0) (.nat 2)
def vsQLm : Expr := .get (arg 0) (.nat 3)

/-- The transitive case, on `[lc, pieces]`. -/
def vsQA2TE (tbl jmb blks itq tsp : ℕ) : Expr :=
  .letE (.call tbl (mk3 (mk2 vsQLp vsQLd) (arg 1) vsQLm))
  (.letE (.prim jmb (.var 1))
  (.letE (.call blks (mk2 (arg 1) (.var 2)))
  (.letE (.call itq (mk3 (.arith .add (.length (.var 3)) (.nat 1)) (.nat 278) (.nat 1)))
    (.call tsp (mk3 (arg 0) (.var 3) (.var 4))))))

/-- The indices of the table program. -/
structure VsQTblX where
  (f mpk ki key cat appd mpo fo mpi fi it tl chk ker img key' cat' appd' fnd eq : ℕ)

/-- The indices of the block program. -/
structure VsQBlkX where
  (f rng mpo fo mpi fi cat flt fn : ℕ)

/-- The indices of the tuple split program. -/
structure VsQTSX where
  (f kmp kI cat appd tl so fa smp sI lmp lI rng jp jm key' cat' appd' tk cat'' lift bas
    itm loc phi tl₁ chk mp fI tl' chk' ker img key cat₂ appd₂ : ℕ)

/-- The indices of the transitive case. -/
structure VsQA2TX where
  (f jmb itq st : ℕ) (t : VsQTblX) (b : VsQBlkX) (w : VsQTSX)

/-- The layout of the transitive case. -/
structure VsQA2TAt (P : Program) (x : VsQA2TX) (hps : PointwiseStab) (hm : Membership)
    (hmb : MinimalBlocks) : Prop where
  hf : P.funs[x.f]? = some (vsQA2TE x.t.f x.jmb x.b.f x.itq x.w.f)
  T : VsQATblAt P x.t.f x.t.mpk x.t.ki x.t.key x.t.cat x.t.appd x.t.mpo x.t.fo x.t.mpi x.t.fi x.t.it
    x.t.tl x.t.chk x.t.ker x.t.img x.t.key' x.t.cat' x.t.appd' x.t.fnd x.t.eq
  hjmb : P.prims[x.jmb]? = some (minimalBlocksPrim hmb)
  B : VsQABlksAt P x.b.f x.b.rng x.b.mpo x.b.fo x.b.mpi x.b.fi x.b.cat x.b.flt x.b.fn
  hitq : P.HasAt x.itq (iterFuns x.itq x.st)
  hst : P.funs[x.st]? = some vsHMulE
  W : VsQTSplitAt P x.w.f x.w.kmp x.w.kI x.w.cat x.w.appd x.w.tl x.w.so x.w.fa x.w.smp x.w.sI x.w.lmp
    x.w.lI x.w.rng x.w.jp x.w.jm
  HK : VsQTKeyItemAt P x.w.kI x.w.key' x.w.cat' x.w.appd'
  HL : VsQTLowAt P x.w.lI x.w.tk x.w.cat'' x.w.lift x.w.bas
  HA : VsQTActAt P x.w.fa x.w.itm x.w.loc x.w.phi x.w.tl₁ x.w.chk x.w.mp x.w.fI x.w.tl' x.w.chk' x.w.ker
    x.w.img x.w.key x.w.cat₂ x.w.appd₂
  hjp : P.prims[x.w.jp]? = some (pointwiseStabPrim hps)
  hjm : P.prims[x.w.jm]? = some (membershipPrim hm)

theorem vsQSotCost_monoS (hps : PointwiseStab) (hm : Membership) (n : ℕ) {S S' : ℕ} (h : S ≤ S') (A : ℕ) :
    vsQSotCost hps hm n S A ≤ vsQSotCost hps hm n S' A := by
  unfold vsQSotCost vsQPsB
  have h2 : S ^ 2 ≤ S' ^ 2 := Nat.pow_le_pow_left h 2
  have h4 : S ^ 4 ≤ S' ^ 4 := Nat.pow_le_pow_left h 4
  have h6 : S ^ 6 ≤ S' ^ 6 := Nat.pow_le_pow_left h 6
  have h9 : S ^ 9 ≤ S' ^ 9 := Nat.pow_le_pow_left h 9
  have hA := Nat.mul_le_mul_right A h2
  have hP : (pointwiseStabPrim hps).c * (3000 * S ^ 4 + 2) ^ (pointwiseStabPrim hps).k ≤
      (pointwiseStabPrim hps).c * (3000 * S' ^ 4 + 2) ^ (pointwiseStabPrim hps).k :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hR := reduceCost_mono hm n (show 4 * S ^ 2 ≤ 4 * S' ^ 2 by omega)
  have h6' := Nat.mul_le_mul_left orbTK h6
  omega

/-- The cost of the tuple split for block sums. -/
noncomputable def vsQA2WCost (hps : PointwiseStab) (hm : Membership) (Cφ S : ℕ) : ℕ :=
  vsQSotCost hps hm I.n (vsQTS (S ^ 2) ((S + 1) ^ 278)) (Cφ + 10 ^ 15 * ((S ^ 2) ^ 3 + 1) ^ 7) +
    10 ^ 20 * ((S ^ 2) ^ 3 + 1) ^ 12 + 10 ^ 8 * vsQTS (S ^ 2) ((S + 1) ^ 278) ^ 4 +
    10 ^ 30 * ((S ^ 2) ^ 3 + 1) ^ 13

/-- The cost of the transitive case. -/
noncomputable def vsQA2TCost (hps : PointwiseStab) (hm : Membership) (hmb : MinimalBlocks) (Cφ S : ℕ) : ℕ :=
  vsQATblCost (4 * S ^ 2) + (minimalBlocksPrim hmb).c * (vsQATblCost (4 * S ^ 2) + 2) ^ (minimalBlocksPrim hmb).k +
    vsQABlksCost (4 * S ^ 2) + 10 ^ 7 * (300 * (S + 1) + 900) + vsQA2WCost (I := I) hps hm Cφ S

set_option maxHeartbeats 16000000 in
/-- **The transitive case.** -/
theorem vsQA2T_spec [Fact I.p.Prime] {P : Program} {x : VsQA2TX} {hps : PointwiseStab}
    {hm : Membership} {hmb : MinimalBlocks} (L : VsQA2TAt P x hps hm hmb) {Cφ S Tm : ℕ}
    (hphi : ∀ g ∈ gens I.gs, FunDet P x.w.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hS : VsQDSz I S Tm) (hTm : (I.d + 1) ^ 278 ≤ Tm) {s : VsQSt I} (hs : VsQStOK s)
    {as : List (Perm (Fin I.n))} {Lb : List (List (List ℕ))} (h : VsQAHyp hs as Lb)
    (h2 : 2 ≤ (vsQAPcs s Lb).length) (htop : vsQAW s Lb = ⊤) (hnab : ¬ s.Ab) :
    FunAll P x.f (.list [vsQLCV s, vsFMatsVal (vsQAPcs s Lb)]) (fun w c =>
      (∃ ts cs lows, w = vsQSplitV ts cs lows ∧ VsQSplitOK s 278 Tm ts cs lows) ∧
      c ≤ 16 * vsQA2TCost (I := I) hps hm hmb Cφ S + 10 ^ 11 * S ^ 12) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hS1 := hS.one_le
  have hDd := vsQD_le hs
  have hSd := hS.d
  have hSp := hS.p
  set N := 4 * S ^ 2 with hN
  set D := vsQD s with hD
  set lc := vsQLCV s
  set PV := vsFMatsVal (vsQAPcs s Lb)
  set A := Val.list [lc, PV]
  set frV := vsWFrVal I.p I.d s.ws' (vsQCs s)
  set MsV := vsFMatsVal (vsQMs s)
  have elc : lc = .list [vsQStV I s, frV, .nat D, MsV] := rfl
  -- sizes
  have hSS : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
  have hpN : I.p ≤ N := by omega
  have hDS : D + 1 ≤ S := by omega
  have hDD : D * D + 1 ≤ N := by
    have : D * D ≤ S * S := Nat.mul_le_mul (by omega) (by omega)
    have e : S * S = S ^ 2 := (sq S).symm
    omega
  have hcnt := vsFEigL_cnt I.prime _ (vsQAFix_sq (s := s) Lb)
  have hPsum : ((vsQAPcs s Lb).map List.length).sum ≤ D := hcnt.2
  have hPfit : ∀ Q ∈ vsQAPcs s Lb, VsWFit I.p D Q := fun Q hQ => (hcnt.1 Q hQ).2.1
  have hPl1 : ∀ Q ∈ vsQAPcs s Lb, Q.length ≤ D := fun Q hQ =>
    (List.le_sum_of_mem (List.mem_map_of_mem (f := List.length) hQ)).trans hPsum
  have hPne : ∀ Q ∈ vsQAPcs s Lb, Q ≠ [] := fun Q hQ => (hcnt.1 Q hQ).1
  have hml : (vsQAPcs s Lb).length ≤ D := by
    have h1 := List.sum_le_sum (l := vsQAPcs s Lb) (f := fun _ => 1) (g := List.length) (fun Q hQ => by
      have := hPne Q hQ; exact List.length_pos_iff.mpr this)
    simp only [List.map_const', List.sum_replicate, smul_eq_mul, mul_one] at h1
    omega
  have hMl : (vsQMs s).length ≤ N := by
    have := vsQ_hsl hS hs; simp only [vsQMs, List.length_map]; omega
  -- readers
  have a0 : ∀ rest, Det P (A :: rest) (arg 0) lc (2 * A.wt + 0 + 5) := fun rest =>
    Det.arg' (P := P) (vs := [lc, PV]) (rest := rest) (j := 0) rfl
  have a1 : ∀ rest, Det P (A :: rest) (arg 1) PV (2 * A.wt + 1 + 5) := fun rest =>
    Det.arg' (P := P) (vs := [lc, PV]) (rest := rest) (j := 1) rfl
  have dp : ∀ rest, Det P (A :: rest) vsQLp (.nat I.p) _ := fun rest =>
    Det.get' (Det.get' (Det.get' (a0 rest) (Det.nat 1) rfl) (Det.nat 0) rfl) (Det.nat 0) rfl
  have dD : ∀ rest, Det P (A :: rest) vsQLd (.nat D) _ := fun rest =>
    Det.get' (a0 rest) (Det.nat 2) rfl
  have dM : ∀ rest, Det P (A :: rest) vsQLm MsV _ := fun rest =>
    Det.get' (a0 rest) (Det.nat 3) rfl
  -- 1. the tables
  have hT := vsQATbl_spec' L.T hpN hDD Lb (fun Q hQ => ⟨hPfit Q hQ, by have := hPl1 Q hQ; omega⟩)
    (by omega) (vsQMs_sq s) hMl
  rw [vsQA_tblGroup h] at hT
  have dT := Det.call (Det.mk3 (Det.mk2 (dp []) (dD [])) (a1 []) (dM [])) hT
  refine FunAll.intro L.hf (EvalAll.letE dT fun v1 c1 hv1 => ?_)
  obtain ⟨rfl, hc1⟩ := hv1
  -- 2. the minimal blocks
  set TV := encGroup (s.hs.map (vsQAPiG h))
  set E1 := [A, TV]
  have htr : ∀ i j : Fin (vsQAPcs s Lb).length, ∃ g ∈ gens (s.hs.map (vsQAPiG h)), g i = j := by
    intro i j
    obtain ⟨σ, hσ, he⟩ := vsQAPi_trans h (by omega) htop i j
    rw [vsQAPi_range h] at hσ
    exact ⟨σ, hσ, he⟩
  have hmbc := minimalBlocks_call hmb L.hjmb (Det.var' (P := P) (env := E1) (i := 1) rfl) ⟨_, rfl, rfl⟩ h2 htr
  refine EvalAll.letE hmbc fun v2 c2 hv2 => ?_
  obtain ⟨⟨lab, rfl, hlt, hmin⟩, hc2⟩ := hv2
  -- 3. the block sums
  set labL := (List.finRange (vsQAPcs s Lb).length).map lab
  have hlabE : encFun lab = natList labL := by simp [encFun, natList, labL, List.map_map, Function.comp_def]
  set E2 := [A, TV, encFun lab]
  have HB : VsQABlkSz (vsQAPcs s Lb) labL N := by
    refine ⟨fun Q hQ => VsWFit.bnd (hPfit Q hQ) hpN (by omega), by omega, by omega, by simp [labL], ?_⟩
    intro y hy
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
    have := hlt i
    omega
  have dPs := Det.call (Det.mk2 (a1 [TV, encFun lab])
    (Det.var' (P := P) (env := E2) (i := 2) (show E2[2]? = some (natList labL) by simp [E2, hlabE])))
    (vsQABlks_spec L.B HB)
  refine EvalAll.letE dPs fun v3 c3 hv3 => ?_
  obtain ⟨rfl, hc3⟩ := hv3
  have F := vsQA_blkFacts h h2 htop hlt hmin
  set Ps := vsQABlks (vsQAPcs s Lb) labL
  -- 4. the bound `(b + 1)^278`
  set E3 := [A, TV, encFun lab, vsFMatsVal Ps]
  have dl := Det.length (Det.var' (P := P) (env := E3) (i := 3) rfl (v := Val.list (Ps.map vsWVs)))
  rw [List.length_map] at dl
  have dc := Det.arith (op := .add) dl (Det.nat (P := P) (env := E3) 1)
  have ec : GI.Machine.BinOp.eval .add Ps.length 1 = Ps.length + 1 := rfl
  rw [ec] at dc
  have hPsl : Ps.length ≤ D := (vsQABlks_length_le _ _).trans hml
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
  have hPw := vsHPowIt_spec L.hitq L.hst hM
  have dB := Det.call (Det.mk3 dc (Det.nat (P := P) (env := E3) 278) (Det.nat (P := P) (env := E3) 1)) hPw
  refine EvalAll.letE dB fun v4 c4 hv4 => ?_
  obtain ⟨rfl, hc4⟩ := hv4
  set Bv := (Ps.length + 1) ^ 278
  -- 5. the split
  have hsum : (Ps.map List.length).sum ≤ S ^ 2 := by
    have h1 : (Ps.map List.length).sum ≤ (vsQAPcs s Lb).length * D := vsQABlks_sum_le hPsum
    have : (vsQAPcs s Lb).length * D ≤ S * S := Nat.mul_le_mul (by omega) (by omega)
    have e : S * S = S ^ 2 := (sq S).symm
    omega
  have hbS : Ps.length ≤ S ^ 2 := by omega
  have hW := vsQTSplit_spec hps hm L.W L.HK L.HL L.HA L.hjp L.hjm hphi hS.sq hs F.fit hbS hsum F.orb
  set E4 := [A, TV, encFun lab, vsFMatsVal Ps, Val.nat Bv]
  refine EvalAll.call_funAll (Det.mk3 (a0 [TV, encFun lab, vsFMatsVal Ps, Val.nat Bv])
    (Det.var' (P := P) (env := E4) (i := 3) rfl) (Det.var' (P := P) (env := E4) (i := 4) rfl)) fun v ca hv => ?_
  obtain ⟨rfl, hca⟩ := hv
  refine (hW.wt_lt).mono fun w c hw => ?_
  obtain ⟨⟨⟨Lo, ks, hw1, hLo, hks, hksl⟩, hc⟩, hwc⟩ := hw
  refine ⟨⟨_, ks, _, hw1, F.splitOK hs hLo hks hksl ?_ hnab⟩, ?_⟩
  · rw [hLo.length_eq]
    exact F.orb.trans ((Nat.pow_le_pow_left (show Ps.length + 1 ≤ I.d + 1 by omega) 278).trans hTm)
  · -- the cost
    have wLC : lc.wt ≤ 10 ^ 6 * S ^ 6 := vsQ_wt_LC hS hs
    have hfr : frV.wt < lc.wt := wt_le_wt_list (by simp [frV, MsV, D])
    have hMs : MsV.wt < lc.wt := wt_le_wt_list (by simp [frV, MsV, D])
    have hDv : (Val.nat D).wt < lc.wt := wt_le_wt_list (by simp [frV, MsV, D])
    have hF0 : (Val.list [Val.nat I.p, Val.nat I.d, natList (vsWZ I.d), natList (vsWZ (vsQCs s).length)]).wt <
        frV.wt := wt_le_wt_list (by simp [frV, vsWFrVal])
    have efr : frV.wt = (Val.list [Val.list [Val.nat I.p, Val.nat I.d, natList (vsWZ I.d),
        natList (vsWZ (vsQCs s).length)], vsWVs s.ws', vsWVs (vsQCs s),
        Val.list (List.map VsRow.val (vsWFrRows I.p s.ws' (vsQCs s)))]).wt := rfl
    have hpv : (Val.nat I.p).wt < (Val.list [Val.nat I.p, Val.nat I.d, natList (vsWZ I.d),
        natList (vsWZ (vsQCs s).length)]).wt := wt_le_wt_list (by simp)
    have hN1 : N + 1 ≤ 5 * S ^ 2 := by have := Nat.one_le_pow 2 S hS1; omega
    have hN4 : (N + 1) ^ 4 ≤ 625 * S ^ 8 := by
      calc (N + 1) ^ 4 ≤ (5 * S ^ 2) ^ 4 := Nat.pow_le_pow_left hN1 4
        _ = 625 * S ^ 8 := by ring
    have hN2 : (N + 1) ^ 2 ≤ 25 * S ^ 4 := by
      calc (N + 1) ^ 2 ≤ (5 * S ^ 2) ^ 2 := Nat.pow_le_pow_left hN1 2
        _ = 25 * S ^ 4 := by ring
    have wPV : PV.wt ≤ 40 * (N + 1) ^ 4 :=
      vsQ_wt_mats_le (fun Q hQ => ⟨VsWFit.bnd (hPfit Q hQ) hpN (by omega), by have := hPl1 Q hQ; omega⟩)
        (by omega)
    have wA := wt_list2_le lc PV
    have wTV : TV.wt < vsQATblCost N := FunDet.wt_lt' hT
    have wPs : (vsFMatsVal Ps).wt < vsQABlksCost N := FunDet.wt_lt' (vsQABlks_spec L.B HB)
    have ePs : (Val.list (List.map vsWVs Ps)).wt = (vsFMatsVal Ps).wt := rfl
    have wL : (natList labL).wt ≤ 5 * (N + 1) ^ 2 := HB.wL
    have hmbb : (minimalBlocksPrim hmb).bound TV ≤
        (minimalBlocksPrim hmb).c * (vsQATblCost N + 2) ^ (minimalBlocksPrim hmb).k :=
      mb_bound_le _ wTV.le
    have hB278 := hM 278 le_rfl
    have wBv : (Val.nat Bv).wt ≤ M + 2 := by
      rw [wt_nat']
      show GI.Machine.len ((Ps.length + 1) ^ 278) + 2 ≤ M + 2
      omega
    have wc1 : (Val.nat (Ps.length + 1)).wt ≤ M + 2 := by rw [wt_nat']; omega
    have w278 : (Val.nat 278).wt ≤ 300 := by rw [wt_nat']; decide
    have := wt_nat_le 1; have := wt_nat_le 2; have := wt_nat_le 0; have := wt_nat_le I.p
    have := wt_nat_le D
    have l1 := wt_list2_le (.nat I.p) (.nat D)
    have l2 := wt_list3_le (.list [.nat I.p, .nat D]) PV MsV
    have l3 := wt_list2_le PV (natList labL)
    have l4 := wt_list3_le (.nat (Ps.length + 1)) (.nat 278) (.nat 1)
    have l5 := wt_list3_le lc (vsFMatsVal Ps) (.nat Bv)
    have hpw : 10 ^ 4 * (278 + 1) * (M + 278 + 10) ≤ 10 ^ 7 * (300 * (S + 1) + 900) := by
      simp only [M]; omega
    -- the split cost
    have hB : (Ps.length + 1) ^ 278 ≤ (S + 1) ^ 278 := Nat.pow_le_pow_left (by omega) 278
    have hTS : vsQTS (S ^ 2) ((Ps.length + 1) ^ 278) ≤ vsQTS (S ^ 2) ((S + 1) ^ 278) := by
      unfold vsQTS; omega
    have hc' : c ≤ vsQA2WCost (I := I) hps hm Cφ S := by
      unfold vsQA2WCost
      have h1 := vsQSotCost_monoS hps hm I.n hTS (Cφ + 10 ^ 15 * ((S ^ 2) ^ 3 + 1) ^ 7)
      have h2 := Nat.pow_le_pow_left hTS 4
      omega
    have hm2 : 7 * ((vsQAPcs s Lb).length + 1) ^ 2 ≤ 7 * S ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
    have q4 : S ^ 2 ≤ S ^ 12 := hS.pow_le (by omega)
    have q6 : S ^ 6 ≤ S ^ 12 := hS.pow_le (by omega)
    have q8 : S ^ 8 ≤ S ^ 12 := hS.pow_le (by omega)
    have q44 : S ^ 4 ≤ S ^ 12 := hS.pow_le (by omega)
    unfold vsQA2TCost
    rw [show 4 * S ^ 2 = N from hN.symm]
    have eA : A.wt = (Val.list [lc, PV]).wt := rfl
    have hlcA : lc.wt < A.wt := wt_le_wt_list (by simp [A])
    have hPVA : PV.wt < A.wt := wt_le_wt_list (by simp [A])
    have hMS : M ≤ 10 ^ 7 * (300 * (S + 1) + 900) := by simp only [M]; omega
    have hMS' : 300 ≤ M := by simp only [M]; omega
    have hMS2 : M ≤ 600 * S := by simp only [M]; omega
    have q112 : S ≤ S ^ 12 := Nat.le_self_pow (by norm_num) _
    have q68 : S ^ 6 ≤ S ^ 8 := hS.pow_le (by omega)
    have q1 : 1 ≤ S ^ 8 := Nat.one_le_pow _ _ hS1
    have hPsS : Ps.length ≤ S := by omega
    clear_value lc PV A frV MsV TV labL Ps M Bv
    have hA' : A.wt ≤ 10 ^ 8 * S ^ 8 := by omega
    have t1 : c1 ≤ 2 * vsQATblCost N + 100 * A.wt + 1000 := by omega
    have t2 : c2 ≤ vsQATblCost N + (minimalBlocksPrim hmb).c * (vsQATblCost N + 2) ^ (minimalBlocksPrim hmb).k +
      7 * S ^ 2 + 2 := by omega
    have t3 : c3 ≤ 2 * vsQABlksCost N + 100 * A.wt + 1000 * S ^ 4 + 1000 := by omega
    have t4 : c4 ≤ 10 ^ 7 * (300 * (S + 1) + 900) + 2 * vsQABlksCost N + 20 * M + 10 * S + 10000 := by omega
    have t5 : ca ≤ 10 * A.wt + 8 * vsQABlksCost N + 20 * M + 10000 := by omega
    have q0 : 1 ≤ S ^ 12 := Nat.one_le_pow _ _ hS1
    clear * - t1 t2 t3 t4 t5 hA' hc' hwc hMS2 q112 q8 hS1 q4 q44 q0
    omega

end GI.Impl
