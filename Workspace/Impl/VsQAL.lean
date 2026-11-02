import Workspace.Impl.VsQA4

/-!
# The A-loop

On `[lc, encGroup as]` (with `Ā` an abelian normal subgroup of `H̄`) the program `vsQALE` runs
step 2 (`vsQA2A_spec`), then step 3 (`vsQA3_spec`), then step 4 with the hand-off (`vsQA4_spec`).
A split is returned. A grow of `A` makes the loop call itself on the larger `as'`. The algebra
`𝔽_p[Ā]` grows strictly each time, so there are at most `D²` rounds (`vsQAL_spec`).
-/

open Matrix Module

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- The A-loop, on `[lc, encGroup as]`. -/
def vsQALE (s2a s3 s4 al : ℕ) : Expr :=
  .letE (.call s2a (.var 0))
  (.ite (.arith .eq (.get (.var 1) (.nat 0)) (.nat 2))
    (.letE (.call s3 (mk3 (arg 0) (arg 1) (.get (.var 1) (.nat 1))))
      (.ite (.arith .eq (.get (.var 2) (.nat 0)) (.nat 3))
        (.letE (.call s4 (mk2 (arg 0) (.get (.var 2) (.nat 1))))
          (.ite (.get (.var 3) (.nat 0))
            (.var 3)
            (.call al (mk2 (arg 0) (.get (.var 3) (.nat 1))))))
        (.var 2)))
    (.var 1))

/-- The measure of the loop: the codimension of `𝔽_p[Ā]` in the algebra of all maps. -/
noncomputable def vsQAM [Fact I.p.Prime] {s : VsQSt I} (hs : VsQStOK s) (as : List (Perm (Fin I.n))) : ℕ :=
  finrank (ZMod I.p) (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p)) -
    finrank (ZMod I.p) (Subalgebra.toSubmodule (vsTAlg (vsPBar hs (gens as))))

theorem vsQAM_lt [Fact I.p.Prime] {s : VsQSt I} {hs : VsQStOK s} {as as' : List (Perm (Fin I.n))}
    (h : VsPGrowOut hs as as') : vsQAM hs as' < vsQAM hs as := by
  have h1 := Submodule.finrank_lt_finrank_of_lt (Subalgebra.toSubmodule.lt_iff_lt.2 h.lt)
  have h2 := Submodule.finrank_le (Subalgebra.toSubmodule (vsTAlg (vsPBar hs (gens as'))))
  unfold vsQAM
  omega

theorem vsQAM_le [Fact I.p.Prime] {s : VsQSt I} (hs : VsQStOK s) (as : List (Perm (Fin I.n))) :
    vsQAM hs as ≤ vsQD s * vsQD s := by
  unfold vsQAM
  have : finrank (ZMod I.p) (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p)) = vsQD s * vsQD s := by
    rw [Module.finrank_linearMap, Module.finrank_fin_fun]
  omega

/-- The cost of one round of the loop. -/
noncomputable def vsQALCost (hps : PointwiseStab) (hm : Membership) (hmb : MinimalBlocks)
    (hn : NormalClosure) (hd : DerivedSubgroup) (Cφ S CH CQ : ℕ) : ℕ :=
  4 * (8 * vsQA2ACost (I := I) hps hm hmb Cφ S + 10 ^ 33 * S ^ 32) + 4 * (64 * vsQA3Cost (I := I) hps hm Cφ S) +
    4 * (64 * (vsPStep4Cost (I := I) Cφ hn hd S + 10 ^ 7 * (vsPN S + 1) * (10 ^ 9 * S ^ 8) + CH + CQ) +
      100 * (10 ^ 6 * S ^ 6 + 10 ^ 9 * S ^ 8) + 10000) + 10 ^ 12 * S ^ 8

theorem vsQ_wt_In [Fact I.p.Prime] {S Tm : ℕ} (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s)
    {as : List (Perm (Fin I.n))} {Lb : List (List (List ℕ))} {ks us : List (Perm (Fin I.n))}
    (hal : as.length ≤ I.n ^ 2) (hLb : ∀ M ∈ Lb, VsWSq I.p (vsQD s) M) (hLbl : Lb.length ≤ vsQD s * vsQD s)
    (hksl : ks.length ≤ I.n ^ 2) (hus : us.length ≤ vsQD s) :
    (vsPIn s as Lb ks us).wt ≤ 10 ^ 9 * S ^ 8 := by
  have hS1 := hS.one_le
  have hD := vsQD_le hs
  have hSd := hS.d
  have hSp := hS.p
  have hS2 : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
  have wlc := vsQ_wt_LC hS hs
  have wEG := hS.wt_group hal
  have wks := hS.wt_group hksl
  have hDD : vsQD s * vsQD s ≤ S * S := Nat.mul_le_mul (by omega) (by omega)
  have hSS : S * S = S ^ 2 := (sq S).symm
  have wLb : (vsFMatsVal Lb).wt ≤ 40 * (4 * S ^ 2 + 1) ^ 4 :=
    wt_vsFMatsVal_le (by omega) (by omega) (fun M hM => vsFSq_of_wSq (hLb M hM)) (by omega)
  have hN4 : (4 * S ^ 2 + 1) ^ 4 ≤ 625 * S ^ 8 := by
    have h1 : 4 * S ^ 2 + 1 ≤ 5 * S ^ 2 := by have := Nat.one_le_pow 2 S hS1; omega
    calc (4 * S ^ 2 + 1) ^ 4 ≤ (5 * S ^ 2) ^ 4 := Nat.pow_le_pow_left h1 4
      _ = 625 * S ^ 8 := by ring
  have wus : (Val.list (us.map encPerm)).wt ≤ 20 * S ^ 3 := by
    have h1 := vs_wt_list_le_of (us.map encPerm) (c := 4 * S ^ 2) (by
      intro v hv
      obtain ⟨u, -, rfl⟩ := List.mem_map.1 hv
      exact hS.wt_perm u)
    rw [List.length_map] at h1
    have h2 : us.length * (2 * (4 * S ^ 2) + 1) ≤ S * (9 * S ^ 2) := Nat.mul_le_mul (by omega)
      (by have := Nat.one_le_pow 2 S hS1; omega)
    have e : S * (9 * S ^ 2) = 9 * S ^ 3 := by ring
    have := Nat.one_le_pow 3 S hS1
    omega
  have l := wt_list_le [vsQLCV s, encGroup as, vsFMatsVal Lb, encGroup ks, .list (us.map encPerm)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at l
  have e : (vsPIn s as Lb ks us).wt = (Val.list [vsQLCV s, encGroup as, vsFMatsVal Lb, encGroup ks,
    .list (us.map encPerm)]).wt := rfl
  have q68 : S ^ 6 ≤ S ^ 8 := hS.pow_le (by omega)
  have q38 : S ^ 3 ≤ S ^ 8 := hS.pow_le (by omega)
  have q08 : 1 ≤ S ^ 8 := Nat.one_le_pow _ _ hS1
  omega

set_option maxHeartbeats 16000000 in
/-- **The A-loop.** -/
theorem vsQAL_spec [Fact I.p.Prime] {P : Program} {f s4 st4 hard q8c CH CQ : ℕ} {x2 : VsQA2AX}
    {x3 : VsQA3X} {x4 : VsPStep4X} {hps : PointwiseStab} {hm : Membership} {hmb : MinimalBlocks}
    {hn : NormalClosure} {hd : DerivedSubgroup}
    (hf : P.funs[f]? = some (vsQALE x2.f x3.f s4 f))
    (L2 : VsQA2AAt P x2 hps hm hmb) (L3 : VsQA3At P x3 hps hm)
    (h4 : P.funs[s4]? = some (vsQA4E st4 hard q8c))
    (hst4 : P.funs[st4]? = some (vsPStep4E x4.ctxP x4.der x4.x2.x3.x4.ab x4.x2.x3.x4.grow x4.x2.x3.tl x4.s2))
    (L4 : VsPStep4Lay P hn hd x4) {Cφ : ℕ}
    (hphi1 : ∀ g ∈ gens I.gs, FunDet P x2.phib (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hphi2 : ∀ g ∈ gens I.gs, FunDet P x2.s.t.w.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hphi3 : ∀ g ∈ gens I.gs, FunDet P x3.c.t.c.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hphi4 : ∀ g ∈ gens I.gs, FunDet P x3.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hphi5 : ∀ g ∈ gens I.gs, FunDet P x4.x2.x3.x4.d.o.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {S Tm : ℕ} (hS : VsQDSz I S Tm) (hTm : (I.d + 1) ^ 278 ≤ Tm) {s : VsQSt I} (hs : VsQStOK s)
    (hD2 : 2 ≤ vsQD s) (hnab : ¬ s.Ab)
    (hHard : VsQHardHyp P hard CH Tm hs) (hQ8 : VsQ8CHyp P q8c CQ Tm hs) :
    ∀ (m : ℕ) (as : List (Perm (Fin I.n))), vsQAM hs as ≤ m → gens as ≤ gens s.hs →
      VsPNormd (gens s.hs) (gens as) → as.length ≤ I.n ^ 2 →
      vsPBar hs (gens as) ≤ Subgroup.centralizer (vsPBar hs (gens as) : Set _) →
      FunAll P f (.list [vsQLCV s, encGroup as]) (fun w c => VsQSplOK (s := s) Tm w ∧
        c ≤ (m + 1) * vsQALCost (I := I) hps hm hmb hn hd Cφ S CH CQ) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro as hmeas has hasn hal habl
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hS1 := hS.one_le
  set lc := vsQLCV s
  set EG := encGroup as
  set A := Val.list [lc, EG]
  set K := vsQALCost (I := I) hps hm hmb hn hd Cφ S CH CQ
  set X2 := 8 * vsQA2ACost (I := I) hps hm hmb Cφ S + 10 ^ 33 * S ^ 32
  set X3 := 64 * vsQA3Cost (I := I) hps hm Cφ S
  set X4 := 64 * (vsPStep4Cost (I := I) Cφ hn hd S + 10 ^ 7 * (vsPN S + 1) * (10 ^ 9 * S ^ 8) + CH + CQ) +
      100 * (10 ^ 6 * S ^ 6 + 10 ^ 9 * S ^ 8) + 10000
  have eK : K = 4 * X2 + 4 * X3 + 4 * X4 + 10 ^ 12 * S ^ 8 := rfl
  have eX2 : X2 = 8 * vsQA2ACost (I := I) hps hm hmb Cφ S + 10 ^ 33 * S ^ 32 := rfl
  have eX3 : X3 = 64 * vsQA3Cost (I := I) hps hm Cφ S := rfl
  have eX4 : X4 = 64 * (vsPStep4Cost (I := I) Cφ hn hd S + 10 ^ 7 * (vsPN S + 1) * (10 ^ 9 * S ^ 8) + CH + CQ) +
      100 * (10 ^ 6 * S ^ 6 + 10 ^ 9 * S ^ 8) + 10000 := rfl
  have wlc : lc.wt ≤ 10 ^ 6 * S ^ 6 := vsQ_wt_LC hS hs
  have wEG : EG.wt ≤ 320 * S ^ 6 := hS.wt_group hal
  have wA2 := wt_list2_le lc EG
  have eA : A.wt = (Val.list [lc, EG]).wt := rfl
  have q68 : S ^ 6 ≤ S ^ 8 := hS.pow_le (by omega)
  have q08 : 1 ≤ S ^ 8 := Nat.one_le_pow _ _ hS1
  have hA : A.wt ≤ 10 ^ 7 * S ^ 8 := by omega
  have a0 : ∀ rest, Det P (A :: rest) (arg 0) lc (2 * A.wt + 0 + 5) := fun rest =>
    Det.arg' (P := P) (vs := [lc, EG]) (rest := rest) (j := 0) rfl
  have a1 : ∀ rest, Det P (A :: rest) (arg 1) EG (2 * A.wt + 1 + 5) := fun rest =>
    Det.arg' (P := P) (vs := [lc, EG]) (rest := rest) (j := 1) rfl
  have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 2; have := wt_nat_le 3
  -- step 2
  refine FunAll.intro hf (EvalAll.letE (Ra := fun w c => VsQA2Out hs as Tm w ∧ c ≤ A.wt + 2 + 2 * X2 ∧ w.wt ≤ X2)
    (EvalAll.call_funAll (Det.var' (P := P) (env := [A]) (i := 0) rfl) fun v ca hv => ?_) fun v1 c1 hv1 => ?_)
  · obtain ⟨rfl, hca⟩ := hv
    refine (vsQA2A_spec L2 hphi1 hphi2 hS hTm hs hD2 hnab has hasn hal habl).wt_lt.mono fun w c hw => ?_
    obtain ⟨⟨hout, hc⟩, hwc⟩ := hw
    exact ⟨hout, by omega, by omega⟩
  obtain ⟨hout2, hc1, hw1⟩ := hv1
  rcases hout2 with ⟨ts, cs, lows, rfl, hok⟩ | ⟨rfl, hdom⟩
  · -- a split from step 2
    have wsp := hS.wt_split hok
    have de := Det.arith' (op := .eq) (Det.get' (Det.var' (P := P) (env := [A, vsQSplitV ts cs lows]) (i := 1) rfl)
      (Det.nat 0) (show [Val.nat 1, .list (ts.map encPerm), encGroup cs, vsQLowsV lows][0]? = some (.nat 1) from rfl))
      (Det.nat (P := P) (env := [A, vsQSplitV ts cs lows]) 2) rfl
    have hev : GI.Machine.BinOp.eval .eq 1 2 = 0 := rfl
    rw [hev] at de
    refine Det.post (Det.ite_zero de (Det.var' (P := P) (env := [A, vsQSplitV ts cs lows]) (i := 1) rfl))
      fun c hc => ⟨⟨ts, cs, lows, rfl, hok⟩, ?_⟩
    have eS : (Val.list [Val.nat 1, Val.list (List.map encPerm ts), encGroup cs, vsQLowsV lows]).wt =
      (vsQSplitV ts cs lows).wt := rfl
    have hK1 : K ≤ (m + 1) * K := Nat.le_mul_of_pos_left _ (by omega)
    clear_value lc EG A K X2 X3 X4
    omega
  · -- step 3
    set Lb := vsHBm s (1 :: as)
    have h := VsQAHyp.of_bm hs has hasn hal habl
    set V1 := Val.list [.nat 2, vsFMatsVal Lb]
    have de := Det.arith' (op := .eq) (Det.get' (Det.var' (P := P) (env := [A, V1]) (i := 1) rfl)
      (Det.nat 0) (show [Val.nat 2, vsFMatsVal Lb][0]? = some (.nat 2) from rfl))
      (Det.nat (P := P) (env := [A, V1]) 2) rfl
    have hev : GI.Machine.BinOp.eval .eq 2 2 = 1 := rfl
    rw [hev] at de
    have dLb := Det.get' (Det.var' (P := P) (env := [A, V1]) (i := 1) rfl)
      (Det.nat 1) (show [Val.nat 2, vsFMatsVal Lb][1]? = some (vsFMatsVal Lb) from rfl)
    have hLbw : (vsFMatsVal Lb).wt < V1.wt := wt_le_wt_list (by simp [V1])
    have hLsq := h.sq
    have hLbl : Lb.length ≤ vsQD s * vsQD s := h.hLbl
    have hDS : vsQD s ≤ S := by have := vsQD_le hs; have := hS.d; omega
    have hDDS : vsQD s * vsQD s ≤ S * S := Nat.mul_le_mul hDS hDS
    have hSS : S * S = S ^ 2 := (sq S).symm
    have hS2 : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
    have wLb : (vsFMatsVal Lb).wt ≤ 40 * (4 * S ^ 2 + 1) ^ 4 :=
      wt_vsFMatsVal_le (by have := hS.p; omega) (by omega) (fun M hM => vsFSq_of_wSq (hLsq M hM)) (by omega)
    have hN4 : (4 * S ^ 2 + 1) ^ 4 ≤ 625 * S ^ 8 := by
      have h1 : 4 * S ^ 2 + 1 ≤ 5 * S ^ 2 := by have := Nat.one_le_pow 2 S hS1; omega
      calc (4 * S ^ 2 + 1) ^ 4 ≤ (5 * S ^ 2) ^ 4 := Nat.pow_le_pow_left h1 4
        _ = 625 * S ^ 8 := by ring
    have eV1 : (Val.list [Val.nat 2, vsFMatsVal Lb]).wt = V1.wt := rfl
    have wV1 : V1.wt ≤ 10 ^ 5 * S ^ 8 := by
      have := wt_list2_le (.nat 2) (vsFMatsVal Lb); omega
    refine (EvalAll.vsQ_ite_pos' (R := fun w c => VsQSplOK (s := s) Tm w ∧
      c ≤ m * K + 2 * X3 + 2 * X4 + 10 ^ 11 * S ^ 8 ∧ w.wt ≤ 2000 * S ^ 6) de one_ne_zero ?_).mono
      fun w c hw => ?_
    swap
    · obtain ⟨ct, ⟨hout, hct, hwB⟩, hc⟩ := hw
      refine ⟨hout, ?_⟩
      have q32 : S ^ 8 ≤ S ^ 32 := hS.pow_le (by omega)
      rw [Nat.add_mul, one_mul]
      clear_value lc EG A K X2 X3 X4 Lb V1
      omega
    refine EvalAll.letE (Ra := fun w c => VsQA3Out hs as Lb Tm w ∧ c ≤ 10 ^ 9 * S ^ 8 + 2 * X3)
      (EvalAll.call_funAll (Det.mk3 (a0 [V1]) (a1 [V1]) dLb) fun v ca hv => ?_) fun v2 c2 hv2 => ?_
    · obtain ⟨rfl, hca⟩ := hv
      refine (vsQA3_spec L3 hphi3 hphi4 hS hTm hs hD2 hnab h hdom).wt_lt.mono fun w c hw => ?_
      obtain ⟨⟨hout, hc⟩, hwc⟩ := hw
      refine ⟨hout, ?_⟩
      have w3 := wt_list3_le lc EG (vsFMatsVal Lb)
      clear_value lc EG A K X2 X3 X4 Lb V1
      omega
    obtain ⟨hout3, hc2⟩ := hv2
    rcases hout3 with ⟨ts, cs, lows, rfl, hok⟩ | ⟨ks, us, rfl, hH, htmem, hcov, hus⟩
    · -- a split from step 3
      have wsp := hS.wt_split hok
      set E2 := [A, V1, vsQSplitV ts cs lows]
      have de3 := Det.arith' (op := .eq) (Det.get' (Det.var' (P := P) (env := E2) (i := 2) rfl)
        (Det.nat 0) (show [Val.nat 1, .list (ts.map encPerm), encGroup cs, vsQLowsV lows][0]? = some (.nat 1) from rfl))
        (Det.nat (P := P) (env := E2) 3) rfl
      have hev3 : GI.Machine.BinOp.eval .eq 1 3 = 0 := rfl
      rw [hev3] at de3
      refine Det.post (Det.ite_zero de3 (Det.var' (P := P) (env := E2) (i := 2) rfl))
        fun c hc => ⟨⟨ts, cs, lows, rfl, hok⟩, ?_, by omega⟩
      have eS : (Val.list [Val.nat 1, Val.list (List.map encPerm ts), encGroup cs, vsQLowsV lows]).wt =
        (vsQSplitV ts cs lows).wt := rfl
      have := Nat.zero_le (m * K)
      clear_value lc EG A K X2 X3 X4 Lb V1
      omega
    · -- step 4
      set In := vsPIn s as Lb ks us
      set V3 := Val.list [.nat 3, In]
      set E2 := [A, V1, V3]
      have wIn : In.wt ≤ 10 ^ 9 * S ^ 8 := vsQ_wt_In hS hs hal hLsq hLbl hH.hccl hus
      have eV3 : (Val.list [Val.nat 3, In]).wt = V3.wt := rfl
      have wV3 : V3.wt ≤ 3 * 10 ^ 9 * S ^ 8 := by
        have := wt_list2_le (.nat 3) In; omega
      have de3 := Det.arith' (op := .eq) (Det.get' (Det.var' (P := P) (env := E2) (i := 2) rfl)
        (Det.nat 0) (show [Val.nat 3, In][0]? = some (.nat 3) from rfl))
        (Det.nat (P := P) (env := E2) 3) rfl
      have hev3 : GI.Machine.BinOp.eval .eq 3 3 = 1 := rfl
      rw [hev3] at de3
      have dIn := Det.get' (Det.var' (P := P) (env := E2) (i := 2) rfl)
        (Det.nat 1) (show [Val.nat 3, In][1]? = some In from rfl)
      refine (EvalAll.vsQ_ite_pos' (R := fun w c => VsQSplOK (s := s) Tm w ∧
        c ≤ m * K + 2 * X4 + 2 * 10 ^ 10 * S ^ 8 + 10 ^ 4 * S ^ 6 ∧ w.wt ≤ 2000 * S ^ 6) de3 one_ne_zero ?_).mono
        fun w c hw => ?_
      swap
      · obtain ⟨ct, ⟨hout, hct, hwB⟩, hc⟩ := hw
        refine ⟨hout, ?_, hwB⟩
        clear_value lc EG A K X2 X3 X4 Lb V1 In V3
        omega
      have hcost4 : 64 * (vsPStep4Cost (I := I) Cφ hn hd S + 10 ^ 7 * (vsPN S + 1) * In.wt + CH + CQ) +
          100 * ((vsQLCV s).wt + In.wt) + 10000 ≤ X4 := by
        have := Nat.mul_le_mul_left (10 ^ 7 * (vsPN S + 1)) wIn
        rw [eX4]
        have e : (vsQLCV s).wt = lc.wt := rfl
        omega
      refine EvalAll.letE (Ra := fun w c => VsQ4Out hs as Tm w ∧ c ≤ 10 ^ 10 * S ^ 8 + 2 * X4)
        (EvalAll.call_funAll (Det.mk2 (a0 [V1, V3]) dIn) fun v ca hv => ?_) fun v4 c4 hv4 => ?_
      · obtain ⟨rfl, hca⟩ := hv
        refine (vsQA4_spec h4 hst4 L4 hphi5 hS hs hnab hHard hQ8 hH htmem hcov hus).wt_lt.mono
          fun w c hw => ?_
        obtain ⟨⟨hout, hc⟩, hwc⟩ := hw
        refine ⟨hout, ?_⟩
        have w2 := wt_list2_le lc In
        have e : (vsPIn s as Lb ks us).wt = In.wt := rfl
        rw [e] at hc
        have elc : (vsQLCV s).wt = lc.wt := rfl
        clear_value lc EG A K X2 X3 X4 Lb V1 In V3
        omega
      obtain ⟨hout4, hc4⟩ := hv4
      rcases hout4 with ⟨ts, cs, lows, rfl, hok⟩ | ⟨as', rfl, hgr⟩
      · -- a split from step 4
        have wsp := hS.wt_split hok
        set E3 := [A, V1, V3, vsQSplitV ts cs lows]
        have d0 := Det.get' (Det.var' (P := P) (env := E3) (i := 3) rfl)
          (Det.nat 0) (show [Val.nat 1, .list (ts.map encPerm), encGroup cs, vsQLowsV lows][0]? = some (.nat 1) from rfl)
        refine Det.post (Det.ite_pos d0 one_ne_zero (Det.var' (P := P) (env := E3) (i := 3) rfl))
          fun c hc => ⟨⟨ts, cs, lows, rfl, hok⟩, ?_, by omega⟩
        have eS : (Val.list [Val.nat 1, Val.list (List.map encPerm ts), encGroup cs, vsQLowsV lows]).wt =
          (vsQSplitV ts cs lows).wt := rfl
        have := Nat.zero_le (m * K)
        have q06 : 1 ≤ S ^ 6 := Nat.one_le_pow _ _ hS1
        clear_value lc EG A K X2 X3 X4 Lb V1 In V3
        omega
      · -- a grow: the loop again
        set V4 := Val.list [.nat 0, encGroup as']
        set E3 := [A, V1, V3, V4]
        have wEG' : (encGroup as').wt ≤ 320 * S ^ 6 := hS.wt_group hgr.len
        have eV4 : (Val.list [Val.nat 0, encGroup as']).wt = V4.wt := rfl
        have wV4 : V4.wt ≤ 700 * S ^ 6 := by have := wt_list2_le (.nat 0) (encGroup as'); have := Nat.one_le_pow 6 S hS1; omega
        have d0 := Det.get' (Det.var' (P := P) (env := E3) (i := 3) rfl)
          (Det.nat 0) (show [Val.nat 0, encGroup as'][0]? = some (.nat 0) from rfl)
        have d1 := Det.get' (Det.var' (P := P) (env := E3) (i := 3) rfl)
          (Det.nat 1) (show [Val.nat 0, encGroup as'][1]? = some (encGroup as') from rfl)
        have hlt := vsQAM_lt hgr
        have hm' : vsQAM hs as' < m := lt_of_lt_of_le hlt hmeas
        have ihs := ih (vsQAM hs as') hm' as' le_rfl hgr.le' hgr.normd hgr.len hgr.abel
        refine (EvalAll.vsQ_ite_zero' (R := fun w c => VsQSplOK (s := s) Tm w ∧
            c ≤ m * K + 10 ^ 8 * S ^ 8 ∧ w.wt ≤ 2000 * S ^ 6) d0 (EvalAll.call_funAll
          (Det.mk2 (a0 [V1, V3, V4]) d1) fun v ca hv => ?_)).mono fun w c hw => ?_
        · obtain ⟨rfl, hca⟩ := hv
          exact ihs.wt_lt.mono fun w c hw => (show (fun w c => VsQSplOK (s := s) Tm w ∧
            c ≤ m * K + 10 ^ 8 * S ^ 8 ∧ w.wt ≤ 2000 * S ^ 6) w (ca + c + w.wt + 1) from by
            obtain ⟨⟨hout, hc⟩, hwc⟩ := hw
            obtain ⟨ts, cs, lows, rfl, hok⟩ := hout
            have wsp := hS.wt_split hok
            refine ⟨⟨ts, cs, lows, rfl, hok⟩, ?_, wsp⟩
            have hmK : (vsQAM hs as' + 1) * K ≤ m * K := Nat.mul_le_mul_right _ hm'
            have w2 := wt_list2_le lc (encGroup as')
            clear_value lc EG A K X2 X3 X4 Lb V1 In V3 V4
            omega)
        · obtain ⟨ce, ⟨hout, hce, hwB⟩, hc⟩ := hw
          refine ⟨hout, ?_, hwB⟩
          clear_value lc EG A K X2 X3 X4 Lb V1 In V3 V4

          omega

end GI.Impl