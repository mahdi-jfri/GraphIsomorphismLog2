import Workspace.Impl.VsQAL
import Workspace.Impl.VsBOne

/-!
# The analysis of a state

On a state `vsQStV I s` the program `vsQAnaE` computes the local context (`vsQLC_spec`) and then:

* `D = 0`: the leaf `(1, hs)` (`vsB_ans_D0`);
* `D = 1`: the orbit base (`vsBOrb_spec` with bound `p`);
* `D ≥ 2` and `H` abelian on `W/W'` (tested with `vsPAb_spec`): the abelian branch (`vsQAb_spec`);
* otherwise: the A-loop with `A = 1` (`vsQAL_spec`).

The four branches enter `vsQAna_spec` as hypotheses on the called functions.
-/

open Matrix Module

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- Entry `k` of the state, in variable `0`. -/
def vsQAx (k : ℕ) : Expr := .get (.var 0) (.nat k)

/-- `encGroup []`, from the state. -/
def vsQEG0 : Expr := mk2 (.get (vsQAx 1) (.nat 0)) (mk1 (.get (.get (vsQAx 1) (.nat 1)) (.nat 0)))

/-- The analysis, on a state. -/
def vsQAnaE (lcp orb ctxp abt abb al : ℕ) : Expr :=
  .letE (.call lcp (.var 0))
  (.ite (.arith .lt (.get (.var 1) (.nat 2)) (.nat 2))
    (.ite (.get (.var 1) (.nat 2))
      (.call orb (mk2 (.var 0) (.get (.get (.get (.var 1) (.nat 1)) (.nat 0)) (.nat 0))))
      (mk2 (.nat 0) (mk3 (.nat 1) (.get (.get (vsQAx 1) (.nat 1)) (.nat 0)) (vsQAx 1))))
    (.letE (.call ctxp (vsPMk5 (.var 1) vsQEG0 .nil vsQEG0 .nil))
      (.ite (.call abt (mk2 (.var 2) (vsQAx 1)))
        (.call abb (.var 1))
        (.call al (mk2 (.var 1) vsQEG0)))))

theorem vsQ_encGroup_nil : encGroup ([] : List (Perm (Fin I.n))) =
    .list [.nat I.n, .list [encPerm (1 : Perm (Fin I.n))]] := rfl

set_option maxHeartbeats 16000000 in
/-- **The analysis of a state.** -/
theorem vsQAna_spec [Fact I.p.Prime] {P : Program}
    {f lcp orb abb al ctx flm it fl rws rep abt fo no fi nc comp loc eq phi CL CO CB CAL Cφ S Tm : ℕ}
    (hf : P.funs[f]? = some (vsQAnaE lcp orb ctx abt abb al))
    (hctx : P.funs[ctx]? = some (vsPCtxE flm rws rep)) (hflm : P.HasAt flm (mapFuns flm it))
    (hit : P.funs[it]? = some (vsPFlItemE fl)) (hfl : P.HasAt fl (vsWFlatFuns fl))
    (hrws : P.HasAt rws (vsWRowsFuns rws)) (hrep : P.HasAt rep (replicateFuns rep))
    (habt : P.funs[abt]? = some (vsPAbE fo)) (hfo : P.HasAt fo (findFuns fo no))
    (hno : P.funs[no]? = some (vsPNoE fi)) (hfi : P.HasAt fi (findFuns fi nc))
    (hnc : P.funs[nc]? = some (vsPNcE comp loc eq)) (hcomp : P.HasAt comp (composeFuns comp))
    (hloc : P.funs[loc]? = some (vsPLocE phi (loc + 1))) (hwl : P.HasAt (loc + 1) (vsWLocFuns (loc + 1)))
    (heq : P.HasAt eq (vsPEqFuns eq))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s)
    (hLC : FunDet P lcp (vsQStV I s) (vsQLCV s) CL)
    (hOrb : vsQD s = 1 → FunAll P orb (.list [vsQStV I s, .nat I.p])
      (fun w c => (∃ a, w = vsQLeafV a ∧ VsQAnsOK hs.prob a) ∧ c ≤ CO))
    (hAbB : s.Ab → 2 ≤ vsQD s → FunAll P abb (vsQLCV s) (fun w c => VsQAnaOut hs 278 Tm w ∧ c ≤ CB))
    (hAL : ¬ s.Ab → 2 ≤ vsQD s → FunAll P al (.list [vsQLCV s, encGroup ([] : List (Perm (Fin I.n)))])
      (fun w c => VsQSplOK (s := s) Tm w ∧ c ≤ CAL)) :
    FunAll P f (vsQStV I s) (fun w c => VsQAnaOut hs 278 Tm w ∧
      c ≤ 8 * (CL + CO + CB + CAL + vsPCtxPCost (vsPN S) (10 ^ 9 * S ^ 8) +
        vsPAbCost Cφ (vsPN S) (10 ^ 8 * S ^ 6)) + 10 ^ 12 * S ^ 12) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hS1 := hS.one_le
  have hDd := vsQD_le hs
  have hSd := hS.d
  have hSp := hS.p
  set D := vsQD s with hD
  set stV := vsQStV I s
  set lc := vsQLCV s
  set frV := vsWFrVal I.p I.d s.ws' (vsQCs s)
  set MsV := vsFMatsVal (vsQMs s)
  have elc : lc = .list [stV, frV, .nat D, MsV] := rfl
  have est : stV = .list [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x, natList s.y] := rfl
  set T := 8 * (CL + CO + CB + CAL + vsPCtxPCost (vsPN S) (10 ^ 9 * S ^ 8) +
    vsPAbCost Cφ (vsPN S) (10 ^ 8 * S ^ 6)) + 10 ^ 12 * S ^ 12
  have eT : T = 8 * (CL + CO + CB + CAL + vsPCtxPCost (vsPN S) (10 ^ 9 * S ^ 8) +
    vsPAbCost Cφ (vsPN S) (10 ^ 8 * S ^ 6)) + 10 ^ 12 * S ^ 12 := rfl
  have wst : stV.wt ≤ 10 ^ 6 * S ^ 6 := by
    have h1 : lc.wt ≤ 10 ^ 6 * S ^ 6 := vsQ_wt_LC hS hs
    have : stV.wt < lc.wt := wt_le_wt_list (by simp [lc, vsQLCV, stV])
    omega
  have wlc : lc.wt ≤ 10 ^ 6 * S ^ 6 := vsQ_wt_LC hS hs
  have wLCc : lc.wt < CL := FunDet.wt_lt' hLC
  have q6 : S ^ 6 ≤ S ^ 12 := hS.pow_le (by omega)
  have q0 : 1 ≤ S ^ 12 := Nat.one_le_pow _ _ hS1
  have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 2; have := wt_nat_le 3
  have wDn := wt_nat_le D
  have eSt : (Val.list [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x, natList s.y]).wt =
    stV.wt := rfl
  have qS : S ≤ S ^ 12 := Nat.le_self_pow (by norm_num) _
  refine FunAll.intro hf (EvalAll.letE (Det.call (Det.var' (P := P) (env := [stV]) (i := 0) rfl) hLC)
    fun v1 c1 hv1 => ?_)
  obtain ⟨rfl, hc1⟩ := hv1
  set E1 := [stV, lc]
  have dlc : Det P E1 (.var 1) lc (lc.wt + 1) := Det.var' rfl
  have dD := Det.get' dlc (Det.nat 2) (show [stV, frV, Val.nat D, MsV][2]? = some (.nat D) from rfl)
  have dlt := Det.arith' (op := .lt) dD (Det.nat (P := P) (env := E1) 2) rfl
  have dEH : Det P E1 (vsQAx 1) (encGroup s.hs) _ :=
    Det.get' (Det.var' (P := P) (env := E1) (i := 0) rfl) (Det.nat 1) rfl
  have dEH' : Det P E1 (vsQAx 1) (.list [.nat I.n, .list ((1 :: s.hs).map encPerm)]) _ := dEH
  have d1 := Det.get' (Det.get' dEH' (Det.nat 1) (show [Val.nat I.n, .list ((1 :: s.hs).map encPerm)][1]? =
    some (.list ((1 :: s.hs).map encPerm)) from rfl)) (Det.nat 0)
    (show ((1 :: s.hs).map encPerm)[0]? = some (encPerm 1) from rfl)
  have dn := Det.get' dEH' (Det.nat 0) (show [Val.nat I.n, .list ((1 :: s.hs).map encPerm)][0]? =
    some (.nat I.n) from rfl)
  have wEH : (encGroup s.hs).wt ≤ 320 * S ^ 6 := hS.wt_group hs.hsl
  have hEHst : (encGroup s.hs).wt < stV.wt := wt_le_wt_list (by simp [stV, vsQStV])
  by_cases hlt : D < 2
  · have ev : GI.Machine.BinOp.eval .lt D 2 = 1 := by simp [GI.Machine.BinOp.eval, hlt]
    rw [ev] at dlt
    refine (EvalAll.vsQ_ite_pos' (R := fun w c => VsQAnaOut hs 278 Tm w ∧ c ≤ 2 * CO + 10 ^ 10 * S ^ 12)
      dlt one_ne_zero ?_).mono fun w c hw => ?_
    swap
    · obtain ⟨ct, ⟨hout, hct⟩, hc⟩ := hw
      refine ⟨hout, ?_⟩
      have := hout
      rcases hout with ⟨a, rfl, ha⟩ | ⟨ts, cs, lows, rfl, hok⟩
      · have := vsQLeaf_wt hS (VsQAnsOK.len ha)
        clear_value stV lc frV MsV T

        omega
      · have := hS.wt_split hok
        clear_value stV lc frV MsV T
        omega
    by_cases hD0 : D = 0
    · -- `D = 0`: the leaf `(1, hs)`
      have dD' := dD
      rw [hD0] at dD'
      have dout := Det.mk2 (Det.nat (P := P) (env := E1) 0) (Det.mk3 (Det.nat (P := P) (env := E1) 1) d1 dEH)
      have eo : Val.list [.nat 0, .list [.nat 1, encPerm (1 : Perm (Fin I.n)), encGroup s.hs]] =
        vsQLeafV (some (1, s.hs)) := rfl
      rw [eo] at dout
      have ha := vsB_ans_D0 hs hD0
      refine Det.post (Det.ite_zero dD' dout) fun c hc => ⟨Or.inl ⟨_, rfl, ha⟩, ?_⟩
      have := vsQLeaf_wt hS (VsQAnsOK.len ha)
      have hE1 : (encPerm (1 : Perm (Fin I.n))).wt ≤ 4 * S ^ 2 := hS.wt_perm 1
      have q2 : S ^ 2 ≤ S ^ 12 := hS.pow_le (by omega)
      have hlE : (Val.list ((1 :: s.hs).map encPerm)).wt < (encGroup s.hs).wt :=
        wt_le_wt_list (by simp [encGroup, encPerms])
      have l3 := wt_list3_le (.nat 1) (encPerm (1 : Perm (Fin I.n))) (encGroup s.hs)
      clear_value stV lc frV MsV T

      omega
    · -- `D = 1`: the orbit base
      have hD1 : D = 1 := by omega
      have dp := Det.get' (Det.get' (Det.get' dlc (Det.nat 1) (show [stV, frV, Val.nat D, MsV][1]? = some frV from rfl))
        (Det.nat 0) rfl) (Det.nat 0) rfl
      refine EvalAll.vsQ_ite_pos' (R := fun w c => VsQAnaOut hs 278 Tm w ∧ c ≤ 2 * CO + 10 ^ 9 * S ^ 12)
        dD hD0 ?_ |>.mono fun w c hw => ?_
      · refine EvalAll.call_funAll (Det.mk2 (Det.var' (P := P) (env := E1) (i := 0) rfl) dp) fun v ca hv => ?_
        obtain ⟨rfl, hca⟩ := hv
        refine (hOrb hD1).wt_lt.mono fun w c hw => ?_
        obtain ⟨⟨⟨a, rfl, ha⟩, hc⟩, hwc⟩ := hw
        refine ⟨Or.inl ⟨a, rfl, ha⟩, ?_⟩
        have := vsQLeaf_wt hS (VsQAnsOK.len ha)
        have hfr : frV.wt < lc.wt := wt_le_wt_list (by simp [lc, vsQLCV, frV])
        have hF0 : (Val.list [Val.nat I.p, Val.nat I.d, natList (vsWZ I.d), natList (vsWZ (vsQCs s).length)]).wt <
            frV.wt := wt_le_wt_list (by simp [frV, vsWFrVal])
        have hpv : (Val.nat I.p).wt < (Val.list [Val.nat I.p, Val.nat I.d, natList (vsWZ I.d),
            natList (vsWZ (vsQCs s).length)]).wt := wt_le_wt_list (by simp)
        have efr : frV.wt = (Val.list [Val.list [Val.nat I.p, Val.nat I.d, natList (vsWZ I.d),
            natList (vsWZ (vsQCs s).length)], vsWVs s.ws', vsWVs (vsQCs s),
            Val.list (List.map VsRow.val (vsWFrRows I.p s.ws' (vsQCs s)))]).wt := rfl
        have l2 := wt_list2_le stV (.nat I.p)
        clear_value stV lc frV MsV T
        omega
      · obtain ⟨ct, ⟨hout, hct⟩, hc⟩ := hw
        refine ⟨hout, ?_⟩
        rcases hout with ⟨a, rfl, ha⟩ | ⟨ts, cs, lows, rfl, hok⟩
        · have := vsQLeaf_wt hS (VsQAnsOK.len ha)
          clear_value stV lc frV MsV T
          omega
        · have := hS.wt_split hok
          clear_value stV lc frV MsV T
          omega
  · -- `D ≥ 2`
    have hD2 : 2 ≤ D := by omega
    have ev : GI.Machine.BinOp.eval .lt D 2 = 0 := by simp [GI.Machine.BinOp.eval, hlt]
    rw [ev] at dlt
    -- the context of step 4, with `as = Lb = ccs = tcs = []`
    have dEG0 : Det P E1 vsQEG0 (encGroup ([] : List (Perm (Fin I.n)))) _ := Det.mk2 dn (Det.mk1 d1)
    have dIn := Det.vsPMk5 dlc dEG0 (Det.nil (P := P) (env := E1)) dEG0 (Det.nil (P := P) (env := E1))
    have eIn : Val.list [lc, encGroup ([] : List (Perm (Fin I.n))), .list [], encGroup ([] : List (Perm (Fin I.n))),
        .list []] = vsPIn s [] [] [] [] := rfl
    rw [eIn] at dIn
    have hDDS : D * D ≤ S * S := Nat.mul_le_mul (by omega) (by omega)
    have hSS : S * S = S ^ 2 := (sq S).symm
    have hS2 : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
    have wIn0 : (vsPIn s [] [] [] []).wt ≤ 10 ^ 9 * S ^ 8 :=
      vsQ_wt_In hS hs (by simp) (by simp) (by simp) (by simp) (by simp)
    have hctxP := vsPCtxP_spec hctx hflm hit hfl hrws hrep hs (N := vsPN S) (W := 10 ^ 9 * S ^ 8)
      (by simp only [vsPN]; omega) (by show D * D ≤ vsPN S; simp only [vsPN]; omega)
      (as := []) (Lb := []) (ccs := []) (tcs := []) (by simp) (by simp) wIn0
    have htest : (∀ g ∈ 1 :: s.hs, ∀ h ∈ 1 :: s.hs,
        vsPLocL I s.ws' (vsQCs s) (g * h) = vsPLocL I s.ws' (vsQCs s) (h * g)) ↔ s.Ab := by
      constructor
      · intro ht
        exact vsQAb_of_comm hs le_rfl (vsQ_comm_of_test hs le_rfl ht)
      · intro hab g hg h hh
        have hg' : g ∈ gens s.hs := by
          rcases List.mem_cons.1 hg with rfl | hg
          · exact one_mem _
          · exact Subgroup.subset_closure hg
        have hh' : h ∈ gens s.hs := by
          rcases List.mem_cons.1 hh with rfl | hh
          · exact one_mem _
          · exact Subgroup.subset_closure hh
        rw [vsPLocL_eq_iff hs, vsQLam_mul hs hg' hh', vsQLam_mul hs hh' hg']
        exact (vsQAb_iff hs).1 hab g hg' h hh'
    have HC := vsPCtx_ok hS hs (Lb := []) (by simp) (by simp)
    set CV := vsPCtx I s.ws' (vsQCs s) (vsPRows I.p []) s.hs
    have hns : ∀ h ∈ s.hs, h ∈ gens I.gs := fun h hh => hs.prob.le (Subgroup.subset_closure hh)
    refine (EvalAll.vsQ_ite_zero' (R := fun w c => VsQAnaOut hs 278 Tm w ∧ c ≤ 2 * CB + 2 * CAL +
      8 * vsPCtxPCost (vsPN S) (10 ^ 9 * S ^ 8) + 2 * vsPAbCost Cφ (vsPN S) (10 ^ 8 * S ^ 6) + 10 ^ 11 * S ^ 12)
      dlt ?_).mono fun w c hw => ?_
    swap
    · obtain ⟨ct, ⟨hout, hct⟩, hc⟩ := hw
      refine ⟨hout, ?_⟩
      rcases hout with ⟨a, rfl, ha⟩ | ⟨ts, cs, lows, rfl, hok⟩
      · have := vsQLeaf_wt hS (VsQAnsOK.len ha)
        clear_value stV lc frV MsV T CV
        omega
      · have := hS.wt_split hok
        clear_value stV lc frV MsV T CV
        omega
    refine EvalAll.letE (Det.call dIn hctxP) fun v2 c2 hv2 => ?_
    obtain ⟨rfl, hc2⟩ := hv2
    set E2 := [stV, lc, CV]
    have dEH2 : Det P E2 (vsQAx 1) (encGroup s.hs) _ :=
      Det.get' (Det.var' (P := P) (env := E2) (i := 0) rfl) (Det.nat 1) rfl
    have dab := Det.call (Det.mk2 (Det.var' (P := P) (env := E2) (i := 2) rfl) dEH2)
      (vsPAb_spec habt hfo hno hfi hnc hcomp hloc hwl heq hphi HC hns hs.hsl)
    have wCV : CV.wt < vsPCtxPCost (vsPN S) (10 ^ 9 * S ^ 8) := FunDet.wt_lt' hctxP
    by_cases hab : s.Ab
    · have ev2 : boolVal (decide (∀ g ∈ 1 :: s.hs, ∀ h ∈ 1 :: s.hs,
          vsPLocL I s.ws' (vsQCs s) (g * h) = vsPLocL I s.ws' (vsQCs s) (h * g))) = .nat 1 := by
        rw [decide_eq_true (htest.2 hab)]; rfl
      rw [ev2] at dab
      refine (EvalAll.vsQ_ite_pos' (R := fun w c => VsQAnaOut hs 278 Tm w ∧ c ≤ 2 * CB + 10 ^ 7 * S ^ 6) dab
        one_ne_zero (EvalAll.call_funAll (Det.var' (P := P) (env := E2) (i := 1) rfl) fun v ca hv => ?_)).mono
        fun w c hw => ?_
      · obtain ⟨rfl, hca⟩ := hv
        refine (hAbB hab hD2).wt_lt.mono fun w c hw => ?_
        obtain ⟨⟨hout, hc⟩, hwc⟩ := hw
        refine ⟨hout, ?_⟩
        clear_value stV lc frV MsV T CV
        omega
      · obtain ⟨ct, ⟨hout, hct⟩, hc⟩ := hw
        refine ⟨hout, ?_⟩
        have l2 := wt_list2_le CV (encGroup s.hs)
        have eEG0 : (encGroup ([] : List (Perm (Fin I.n)))).wt ≤ 40 * S ^ 2 := by
          have := wt_list2_le (.nat I.n) (.list [encPerm (1 : Perm (Fin I.n))])
          have := wt_list1_le (encPerm (1 : Perm (Fin I.n)))
          have := hS.wt_perm 1; have := wt_nat_le I.n; have := hS.n
          have q12 : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
          have := Nat.one_le_pow 2 S hS1
          rw [vsQ_encGroup_nil]; omega
        have q2 : S ^ 2 ≤ S ^ 12 := hS.pow_le (by omega)
        have q8 : S ^ 8 ≤ S ^ 12 := hS.pow_le (by omega)
        have eG0 : (Val.list [Val.nat I.n, Val.list (List.map encPerm [(1 : Perm (Fin I.n))])]).wt =
          (encGroup ([] : List (Perm (Fin I.n)))).wt := rfl
        have eG1 : (Val.list (List.map encPerm [(1 : Perm (Fin I.n))])).wt = (Val.list [encPerm (1 : Perm (Fin I.n))]).wt := rfl
        have l5 := wt_list_le [lc, encGroup ([] : List (Perm (Fin I.n))), .list [],
          encGroup ([] : List (Perm (Fin I.n))), .list []]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
          List.length_nil] at l5
        have w0 : (Val.list []).wt ≤ 10 := (wt_list_le []).trans (by simp)
        have hlE : (Val.list ((1 :: s.hs).map encPerm)).wt < (encGroup s.hs).wt :=
          wt_le_wt_list (by simp [encGroup, encPerms])
        have hE1 : (encPerm (1 : Perm (Fin I.n))).wt ≤ 4 * S ^ 2 := hS.wt_perm 1
        have wn := wt_nat_le I.n
        have hSn := hS.n
        have hEG2 : (encGroup s.hs).wt ≤ 320 * S ^ 6 := wEH
        have q68 : S ^ 6 ≤ S ^ 8 := hS.pow_le (by omega)
        have q28 : S ^ 2 ≤ S ^ 8 := hS.pow_le (by omega)
        have q08 : 1 ≤ S ^ 8 := Nat.one_le_pow _ _ hS1
        have qS8 : S ≤ S ^ 8 := Nat.le_self_pow (by norm_num) _
        have l1e := wt_list1_le (encPerm (1 : Perm (Fin I.n)))
        have t2 : c2 ≤ vsPCtxPCost (vsPN S) (10 ^ 9 * S ^ 8) + CV.wt + 10 ^ 11 * S ^ 8 := by
          clear_value stV lc frV MsV T CV
          clear * - hc2 wlc eSt wst hEG2 wn hSn hlE hE1 l1e eG0 eEG0 wIn0 q68 q28 q08 qS8
          omega
        have tc : c ≤ 6 * CV.wt + vsPAbCost Cφ (vsPN S) (10 ^ 8 * S ^ 6) + ct + w.wt + 10 ^ 8 * S ^ 6 := by
          have w1 := wt_nat_le 1; have w0 := wt_nat_le 0
          have q60 : 1 ≤ S ^ 6 := Nat.one_le_pow _ _ hS1
          clear_value stV lc frV MsV T CV
          clear * - hc l2 hEG2 eSt wst hEHst w1 w0 q60
          omega
        rcases hout with ⟨a, rfl, ha⟩ | ⟨ts, cs, lows, rfl, hok⟩
        · have := vsQLeaf_wt hS (VsQAnsOK.len ha)
          clear_value stV lc frV MsV T CV
          omega
        · have := hS.wt_split hok
          clear_value stV lc frV MsV T CV
          omega
    · have ev2 : boolVal (decide (∀ g ∈ 1 :: s.hs, ∀ h ∈ 1 :: s.hs,
          vsPLocL I s.ws' (vsQCs s) (g * h) = vsPLocL I s.ws' (vsQCs s) (h * g))) = .nat 0 := by
        rw [decide_eq_false (fun ht => hab (htest.1 ht))]; rfl
      rw [ev2] at dab
      have dEH2' : Det P E2 (vsQAx 1) (.list [.nat I.n, .list ((1 :: s.hs).map encPerm)]) _ := dEH2
      have d1' := Det.get' (Det.get' dEH2' (Det.nat 1) (show [Val.nat I.n, .list ((1 :: s.hs).map encPerm)][1]? =
        some (.list ((1 :: s.hs).map encPerm)) from rfl)) (Det.nat 0)
        (show ((1 :: s.hs).map encPerm)[0]? = some (encPerm 1) from rfl)
      have dn' := Det.get' dEH2' (Det.nat 0) (show [Val.nat I.n, .list ((1 :: s.hs).map encPerm)][0]? =
        some (.nat I.n) from rfl)
      have dEG2 := Det.mk2 dn' (Det.mk1 d1')
      refine (EvalAll.vsQ_ite_zero' (R := fun w c => VsQAnaOut hs 278 Tm w ∧ c ≤ 2 * CAL + 10 ^ 7 * S ^ 6) dab
        (EvalAll.call_funAll (Det.mk2 (Det.var' (P := P) (env := E2) (i := 1) rfl) dEG2) fun v ca hv => ?_)).mono
        fun w c hw => ?_
      · obtain ⟨rfl, hca⟩ := hv
        refine (hAL hab hD2).wt_lt.mono fun w c hw => ?_
        obtain ⟨⟨hout, hc⟩, hwc⟩ := hw
        refine ⟨Or.inr hout, ?_⟩
        have l2 := wt_list2_le lc (encGroup ([] : List (Perm (Fin I.n))))
        have hlE : (Val.list ((1 :: s.hs).map encPerm)).wt < (encGroup s.hs).wt :=
          wt_le_wt_list (by simp [encGroup, encPerms])
        have hE1 : (encPerm (1 : Perm (Fin I.n))).wt ≤ 4 * S ^ 2 := hS.wt_perm 1
        have wn := wt_nat_le I.n
        have hSn := hS.n
        have l1 := wt_list1_le (encPerm (1 : Perm (Fin I.n)))
        have l2' := wt_list2_le (.nat I.n) (.list [encPerm (1 : Perm (Fin I.n))])
        have q12 : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
        have q26 : S ^ 2 ≤ S ^ 6 := hS.pow_le (by omega)
        rw [vsQ_encGroup_nil] at l2
        clear_value stV lc frV MsV T CV
        omega
      · obtain ⟨ct, ⟨hout, hct⟩, hc⟩ := hw
        refine ⟨hout, ?_⟩
        have l2 := wt_list2_le CV (encGroup s.hs)
        have eEG0 : (encGroup ([] : List (Perm (Fin I.n)))).wt ≤ 40 * S ^ 2 := by
          have := wt_list2_le (.nat I.n) (.list [encPerm (1 : Perm (Fin I.n))])
          have := wt_list1_le (encPerm (1 : Perm (Fin I.n)))
          have := hS.wt_perm 1; have := wt_nat_le I.n; have := hS.n
          have q12 : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
          have := Nat.one_le_pow 2 S hS1
          rw [vsQ_encGroup_nil]; omega
        have q2 : S ^ 2 ≤ S ^ 12 := hS.pow_le (by omega)
        have q8 : S ^ 8 ≤ S ^ 12 := hS.pow_le (by omega)
        have eG0 : (Val.list [Val.nat I.n, Val.list (List.map encPerm [(1 : Perm (Fin I.n))])]).wt =
          (encGroup ([] : List (Perm (Fin I.n)))).wt := rfl
        have eG1 : (Val.list (List.map encPerm [(1 : Perm (Fin I.n))])).wt = (Val.list [encPerm (1 : Perm (Fin I.n))]).wt := rfl
        have l5 := wt_list_le [lc, encGroup ([] : List (Perm (Fin I.n))), .list [],
          encGroup ([] : List (Perm (Fin I.n))), .list []]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
          List.length_nil] at l5
        have w0 : (Val.list []).wt ≤ 10 := (wt_list_le []).trans (by simp)
        have hlE : (Val.list ((1 :: s.hs).map encPerm)).wt < (encGroup s.hs).wt :=
          wt_le_wt_list (by simp [encGroup, encPerms])
        have hE1 : (encPerm (1 : Perm (Fin I.n))).wt ≤ 4 * S ^ 2 := hS.wt_perm 1
        have wn := wt_nat_le I.n
        have hSn := hS.n
        have hEG2 : (encGroup s.hs).wt ≤ 320 * S ^ 6 := wEH
        have q68 : S ^ 6 ≤ S ^ 8 := hS.pow_le (by omega)
        have q28 : S ^ 2 ≤ S ^ 8 := hS.pow_le (by omega)
        have q08 : 1 ≤ S ^ 8 := Nat.one_le_pow _ _ hS1
        have qS8 : S ≤ S ^ 8 := Nat.le_self_pow (by norm_num) _
        have l1e := wt_list1_le (encPerm (1 : Perm (Fin I.n)))
        have t2 : c2 ≤ vsPCtxPCost (vsPN S) (10 ^ 9 * S ^ 8) + CV.wt + 10 ^ 11 * S ^ 8 := by
          clear_value stV lc frV MsV T CV
          clear * - hc2 wlc eSt wst hEG2 wn hSn hlE hE1 l1e eG0 eEG0 wIn0 q68 q28 q08 qS8
          omega
        have tc : c ≤ 6 * CV.wt + vsPAbCost Cφ (vsPN S) (10 ^ 8 * S ^ 6) + ct + w.wt + 10 ^ 8 * S ^ 6 := by
          have w1 := wt_nat_le 1; have w0 := wt_nat_le 0
          have q60 : 1 ≤ S ^ 6 := Nat.one_le_pow _ _ hS1
          clear_value stV lc frV MsV T CV
          clear * - hc l2 hEG2 eSt wst hEHst w1 w0 q60
          omega
        rcases hout with ⟨a, rfl, ha⟩ | ⟨ts, cs, lows, rfl, hok⟩
        · have := vsQLeaf_wt hS (VsQAnsOK.len ha)
          clear_value stV lc frV MsV T CV
          omega
        · have := hS.wt_split hok
          clear_value stV lc frV MsV T CV
          omega

end GI.Impl