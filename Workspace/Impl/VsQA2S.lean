module

public import Workspace.Impl.VsQA2T

@[expose] public section

/-!
# Two or more pieces

On `[lc, pieces]` with at least two pieces, the program `vsQA2SE` computes the orbit sum `W` of
piece `0` (the span of `B_H P₀`). If `W` is not everything, it returns the chain split by `W`
(case 1). Otherwise `H` moves the pieces transitively and it runs the transitive case
(`vsQA2T_spec`). Result: `vsQA2S_spec`.
-/

open Matrix Module

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

variable {I : VecStabInst}

/-- The zero vector of length `D`, from the local context in argument 0. -/
def vsQLz : Expr := .get (.get (.get (arg 0) (.nat 1)) (.nat 0)) (.nat 3)

/-- Two or more pieces, on `[lc, pieces]`. -/
def vsQA2SE (idp alg spin spl s2t : ℕ) : Expr :=
  .letE (.get (.call alg (mk4 vsQLp vsQLm vsQLz (.call idp vsQLd))) (.nat 1))
  (.letE (.call spin (mk2 (mk3 vsQLp vsQLd (.get (arg 1) (.nat 0))) (.var 1)))
  (.ite (.arith .lt (.length (.var 2)) vsQLd)
    (.call spl (mk2 (arg 0) (.var 2)))
    (.call s2t (mk2 (arg 0) (arg 1)))))

/-- The indices of the spin program. -/
structure VsQSpX where
  (f mp it img cat bas : ℕ)

/-- The indices of the case of two or more pieces. -/
structure VsQA2SX where
  (f idp alg spl : ℕ) (sp : VsQSpX) (t : VsQA2TX)

/-- The layout of the case of two or more pieces. -/
structure VsQA2SAt (P : Program) (x : VsQA2SX) (hps : PointwiseStab) (hm : Membership)
    (hmb : MinimalBlocks) : Prop where
  hf : P.funs[x.f]? = some (vsQA2SE x.idp x.alg x.sp.f x.spl x.t.f)
  hidp : P.HasAt x.idp (vsWIdFuns x.idp)
  halg : P.HasAt x.alg (vsFAlgSpanFuns x.alg)
  Sp : VsQASpinAt P x.sp.f x.sp.mp x.sp.it x.sp.img x.sp.cat x.sp.bas
  hspl : P.HasAt x.spl (vsQSplFuns x.spl)
  T : VsQA2TAt P x.t hps hm hmb

set_option maxHeartbeats 16000000 in
/-- **Two or more pieces.** -/
theorem vsQA2S_spec [Fact I.p.Prime] {P : Program} {x : VsQA2SX} {hps : PointwiseStab}
    {hm : Membership} {hmb : MinimalBlocks} (L : VsQA2SAt P x hps hm hmb) {Cφ S Tm : ℕ}
    (hphi : ∀ g ∈ gens I.gs, FunDet P x.t.w.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hS : VsQDSz I S Tm) (hTm : (I.d + 1) ^ 278 ≤ Tm) {s : VsQSt I} (hs : VsQStOK s)
    {as : List (Perm (Fin I.n))} {Lb : List (List (List ℕ))} (h : VsQAHyp hs as Lb)
    (h2 : 2 ≤ (vsQAPcs s Lb).length) (hD2 : 2 ≤ vsQD s) (hnab : ¬ s.Ab) :
    FunAll P x.f (.list [vsQLCV s, vsFMatsVal (vsQAPcs s Lb)]) (fun w c =>
      (∃ ts cs lows, w = vsQSplitV ts cs lows ∧ VsQSplitOK s 278 Tm ts cs lows) ∧
      c ≤ 128 * vsQA2TCost (I := I) hps hm hmb Cφ S + 10 ^ 30 * S ^ 32) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hS1 := hS.one_le
  have hDd := vsQD_le hs
  have hSd := hS.d
  have hSp := hS.p
  have hp1 := I.prime.one_lt
  set D := vsQD s with hD
  set N := 2 * S ^ 4 with hN
  have hS4 : S ≤ S ^ 4 := by have := hS.pow_le (show 1 ≤ 4 by omega); simpa using this
  have hDS : D ≤ S := by omega
  have hDD : D * D ≤ S ^ 2 := by rw [sq]; exact Nat.mul_le_mul hDS hDS
  have hS22 : S ^ 2 * S ^ 2 = S ^ 4 := by ring
  have hMsl : (vsQMs s).length ≤ S ^ 2 := by
    simp only [vsQMs, List.length_map]; exact vsQ_hsl hS hs
  have hDDM : D * D * (vsQMs s).length ≤ S ^ 4 := by
    rw [← hS22]; exact Nat.mul_le_mul hDD hMsl
  have hS24 : S ^ 2 ≤ S ^ 4 := hS.pow_le (by omega)
  have hpN : I.p ≤ N := by omega
  have hDN : D ≤ N := by omega
  have hDDN : D * D ≤ N := by omega
  have hBl : (vsQBm s).length ≤ D * D := vsQBm_length s
  have hBsq := vsQBm_sq s
  -- the values
  set lc := vsQLCV s
  set PV := vsFMatsVal (vsQAPcs s Lb)
  set A := Val.list [lc, PV]
  set frV := vsWFrVal I.p I.d s.ws' (vsQCs s)
  set MsV := vsFMatsVal (vsQMs s)
  have elc : lc = .list [vsQStV I s, frV, .nat D, MsV] := rfl
  obtain ⟨P0, Pr, hPcs⟩ : ∃ P0 Pr, vsQAPcs s Lb = P0 :: Pr := by
    cases hc : vsQAPcs s Lb with
    | nil => rw [hc] at h2; simp at h2
    | cons a l => exact ⟨a, l, rfl⟩
  have hcnt := vsFEigL_cnt I.prime _ (vsQAFix_sq (s := s) Lb)
  have hP0 : P0 ∈ vsQAPcs s Lb := by rw [hPcs]; exact List.mem_cons_self
  have hP0fit : VsWFit I.p D P0 := (hcnt.1 P0 hP0).2.1
  have hP0l : P0.length ≤ D :=
    (List.le_sum_of_mem (List.mem_map_of_mem (f := List.length) hP0)).trans hcnt.2
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
  have dz : ∀ rest, Det P (A :: rest) vsQLz (natList (vsWZ D)) _ := fun rest =>
    Det.get' (Det.get' (Det.get' (a0 rest) (Det.nat 1) rfl) (Det.nat 0) rfl) (Det.nat 3) rfl
  -- 1. the algebra basis of `H`
  have didf := Det.call (dD []) (vsWId_spec L.hidp (N := N) hDN)
  have hzb : ∀ y ∈ vsWZ D, y < I.p := fun y hy => by simp [vsWZ] at hy; omega
  have dalg := Det.call (Det.mk4 (dp []) (dM []) (dz []) didf)
    (vsFAlgSpan_spec L.halg I.prime.pos hpN hDDN (gs := vsQMs s)
      (fun g hg => vsFSq_of_wSq (vsQMs_sq s g hg)) (by omega) (by omega) hzb (by simp [vsWZ])
      (vsWId_sq hp1 D))
  set stA := vsFAlgSpanL I.p (vsWZ D) (vsWId D) (vsQMs s) (D * D)
  have dBm := Det.get' dalg (Det.nat 1)
    (show [vsAccVal stA.1, vsFMatsVal stA.2][1]? = some (vsFMatsVal (vsQBm s)) from rfl)
  refine FunAll.intro L.hf (EvalAll.letE dBm fun v1 c1 hv1 => ?_)
  obtain ⟨rfl, hc1⟩ := hv1
  set BmV := vsFMatsVal (vsQBm s)
  set E1 := [A, BmV]
  -- 2. the orbit sum
  have dP0 := Det.get' (a1 [BmV]) (Det.nat 0)
    (show (List.map (fun M => Val.list (List.map natList M)) (vsQAPcs s Lb))[0]? = some (vsWVs P0) by
      rw [hPcs]; rfl)
  have hBP : (vsQBm s).length * P0.length ≤ N := by
    have : (vsQBm s).length * P0.length ≤ (D * D) * D := Nat.mul_le_mul hBl hP0l
    have : D * D * D ≤ S ^ 2 * S := Nat.mul_le_mul hDD hDS
    have e : S ^ 2 * S = S ^ 3 := by ring
    have : S ^ 3 ≤ S ^ 4 := hS.pow_le (by omega)
    omega
  have hsp := vsQASpinB_spec L.Sp I.prime.pos hpN hDN hBsq (by omega) hP0fit (by omega) hBP
  have dW := Det.call (Det.mk2 (Det.mk3 (dp [BmV]) (dD [BmV]) dP0)
    (Det.var' (P := P) (env := E1) (i := 1) rfl)) hsp
  have eSp : vsQSpinL I.p D (vsQBm s) P0 = vsQASpin s Lb := by
    simp only [vsQASpin, hPcs]; rfl
  rw [eSp] at dW
  refine EvalAll.letE dW fun v2 c2 hv2 => ?_
  obtain ⟨rfl, hc2⟩ := hv2
  set W := vsWBas I.p (vsQASpin s Lb)
  set E2 := [A, BmV, vsWVs W]
  have hSpf : VsWFit I.p D (vsQASpin s Lb) := by
    have := vsQSpinL_fit (p := I.p) (D := D) I.prime.pos hBsq P0
    rwa [eSp] at this
  have hWf : VsWFit I.p D W := vsWBas_fit I.prime.pos hSpf
  have hWsp : vsWSp I.p D W = vsQAW s Lb := by rw [vsWBas_span I.prime hSpf, vsQASpin_span]
  have hWl : W.length ≤ D := by
    rw [vsWBas_length I.prime hSpf]
    exact (Submodule.finrank_le _).trans (by rw [Module.finrank_fin_fun])
  have dlen := Det.length (Det.var' (P := P) (env := E2) (i := 2) rfl)
  rw [List.length_map] at dlen
  have dlt := Det.arith' (op := .lt) dlen (dD [BmV, vsWVs W]) rfl
  -- weights
  have hSS2 : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
  have wLC : lc.wt ≤ 10 ^ 6 * S ^ 6 := vsQ_wt_LC hS hs
  have hN4 : (4 * S ^ 2 + 1) ^ 4 ≤ 625 * S ^ 8 := by
    have h1 : 4 * S ^ 2 + 1 ≤ 5 * S ^ 2 := by have := Nat.one_le_pow 2 S hS1; omega
    calc (4 * S ^ 2 + 1) ^ 4 ≤ (5 * S ^ 2) ^ 4 := Nat.pow_le_pow_left h1 4
      _ = 625 * S ^ 8 := by ring
  have wPV : PV.wt ≤ 40 * (4 * S ^ 2 + 1) ^ 4 :=
    vsQ_wt_mats_le (fun Q hQ => ⟨VsWFit.bnd ((hcnt.1 Q hQ).2.1) (by omega) (by omega),
      by have := (List.le_sum_of_mem (List.mem_map_of_mem (f := List.length) hQ)).trans hcnt.2; omega⟩)
      (by
        have := List.sum_le_sum (l := vsQAPcs s Lb) (f := fun _ => 1) (g := List.length) (fun Q hQ => by
          have := (hcnt.1 Q hQ).1; exact List.length_pos_iff.mpr this)
        simp only [List.map_const', List.sum_replicate, smul_eq_mul, mul_one] at this
        have h3 : ((vsQAPcs s Lb).map List.length).sum ≤ D := hcnt.2
        omega)
  have wA := wt_list2_le lc PV
  have eA : A.wt = (Val.list [lc, PV]).wt := rfl
  have wBm : BmV.wt ≤ 1000 * S ^ 5 := vsQ_wt_mats hS hs hBsq (by omega)
  have wW : (vsWVs W).wt ≤ 100 * S ^ 3 := vsQ_wt_loc hS hs hWf (by omega)
  have q8 : S ^ 8 ≤ S ^ 32 := hS.pow_le (by omega)
  have q6 : S ^ 6 ≤ S ^ 32 := hS.pow_le (by omega)
  have q5 : S ^ 5 ≤ S ^ 32 := hS.pow_le (by omega)
  have q3 : S ^ 3 ≤ S ^ 32 := hS.pow_le (by omega)
  have q0 : 1 ≤ S ^ 32 := Nat.one_le_pow _ _ hS1
  have hA' : A.wt ≤ 10 ^ 7 * S ^ 32 := by omega
  have hlcA : lc.wt < A.wt := wt_le_wt_list (by simp [A])
  have hPVA : PV.wt < A.wt := wt_le_wt_list (by simp [A])
  have hfr : frV.wt < lc.wt := wt_le_wt_list (by simp [frV, MsV, D, lc, vsQLCV])
  have hMs : MsV.wt < lc.wt := wt_le_wt_list (by simp [frV, MsV, D, lc, vsQLCV])
  have hDv : (Val.nat D).wt < lc.wt := wt_le_wt_list (by simp [frV, MsV, D, lc, vsQLCV])
  have pw : ∀ k ≤ 8, (N + 1) ^ k ≤ 6561 * S ^ 32 := fun k hk => vsQ_powN hS1 hk
  have wc1 : c1 ≤ 10 ^ 20 * S ^ 32 := by
    have := pw 7 (by omega); have := pw 4 (by omega)
    have hF0 : (Val.list [Val.nat I.p, Val.nat I.d, natList (vsWZ I.d), natList (vsWZ (vsQCs s).length)]).wt <
        frV.wt := wt_le_wt_list (by simp [frV, vsWFrVal])
    have hpv : (Val.nat I.p).wt < (Val.list [Val.nat I.p, Val.nat I.d, natList (vsWZ I.d),
        natList (vsWZ (vsQCs s).length)]).wt := wt_le_wt_list (by simp)
    have hzv : (natList (vsWZ D)).wt < (Val.list [Val.nat I.p, Val.nat I.d, natList (vsWZ I.d),
        natList (vsWZ (vsQCs s).length)]).wt := wt_le_wt_list (by simp [D])
    have efr : frV.wt = (Val.list [Val.list [Val.nat I.p, Val.nat I.d, natList (vsWZ I.d),
        natList (vsWZ (vsQCs s).length)], vsWVs s.ws', vsWVs (vsQCs s),
        Val.list (List.map VsRow.val (vsWFrRows I.p s.ws' (vsQCs s)))]).wt := rfl
    have wId : (vsWVs (vsWId D)).wt < 2 * 10 ^ 8 * (N + 1) ^ 4 := FunDet.wt_lt' (vsWId_spec L.hidp (N := N) hDN)
    have wSt : (vsFAVal stA).wt < 10 ^ 9 * (N + 1) ^ 7 := FunDet.wt_lt' (vsFAlgSpan_spec L.halg I.prime.pos hpN
      hDDN (gs := vsQMs s) (fun g hg => vsFSq_of_wSq (vsQMs_sq s g hg)) (by omega) (by omega) hzb
      (by simp [vsWZ]) (vsWId_sq hp1 D))
    have eSt : (Val.list [vsAccVal stA.1, vsFMatsVal stA.2]).wt = (vsFAVal stA).wt := rfl
    have l4 := wt_list4_le (.nat I.p) MsV (natList (vsWZ D)) (vsWVs (vsWId D))
    have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 2; have := wt_nat_le 3
    have hBv : BmV.wt < (vsFAVal stA).wt := by
      rw [← eSt]
      exact wt_le_wt_list (show BmV ∈ [vsAccVal stA.1, vsFMatsVal stA.2] from
        List.mem_cons_of_mem _ (List.mem_singleton.2 rfl))
    clear_value lc PV A frV MsV BmV
    omega
  have wc2 : c2 ≤ 10 ^ 20 * S ^ 32 := by
    have := pw 7 (by omega)
    have hP0w : (vsWVs P0).wt < PV.wt := by
      have e : PV = .list (vsWVs P0 :: Pr.map vsWVs) := by simp only [PV, hPcs]; rfl
      rw [e]; exact wt_le_wt_list (by simp)
    have l3 := wt_list3_le (.nat I.p) (.nat D) (vsWVs P0)
    have l2 := wt_list2_le (.list [.nat I.p, .nat D, vsWVs P0]) BmV
    have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 2; have := wt_nat_le 3
    have hF0 : (Val.list [Val.nat I.p, Val.nat I.d, natList (vsWZ I.d), natList (vsWZ (vsQCs s).length)]).wt <
        frV.wt := wt_le_wt_list (by simp [frV, vsWFrVal])
    have hpv : (Val.nat I.p).wt < (Val.list [Val.nat I.p, Val.nat I.d, natList (vsWZ I.d),
        natList (vsWZ (vsQCs s).length)]).wt := wt_le_wt_list (by simp)
    have efr : frV.wt = (Val.list [Val.list [Val.nat I.p, Val.nat I.d, natList (vsWZ I.d),
        natList (vsWZ (vsQCs s).length)], vsWVs s.ws', vsWVs (vsQCs s),
        Val.list (List.map VsRow.val (vsWFrRows I.p s.ws' (vsQCs s)))]).wt := rfl
    unfold vsQASpinCost at hc2
    clear_value lc PV A frV MsV BmV W
    omega
  have hd2 : 2 ≤ I.d := by omega
  by_cases hlt : W.length < D
  · -- the chain split by the orbit sum
    have ev : GI.Machine.BinOp.lt.eval W.length D = 1 := by simp [GI.Machine.BinOp.eval, hlt]
    rw [ev] at dlt
    have dT := Det.call'' (Det.mk2c (a0 [BmV, vsWVs W]) (Det.var' (P := P) (env := E2) (i := 2) rfl))
      (vsQSpl_spec L.hspl hS hs hWf (by omega))
    refine Det.post (Det.ite_pos dlt one_ne_zero dT) fun c hc => ⟨⟨[1], s.hs, vsQSplLows s W, rfl, ?_⟩, ?_⟩
    · have hTm1 : 1 ≤ Tm := le_trans (Nat.one_le_pow _ _ (by omega)) hTm
      refine vsQ_split1 hs hTm1 ?_ ?_ ?_
      · rw [hWsp]
        intro hb
        have hle : vsWSp I.p D P0 ≤ ⊥ := by simpa [hPcs, hb] using vsQAW_ge (s := s) (Lb := Lb)
        exact ((vsFEigL_pieces I.prime _ (vsQAFix_sq (s := s) Lb)).1 P0 hP0).2.1 (le_bot_iff.1 hle)
      · rw [vsWBas_span I.prime hSpf]; exact vsWSp_ne_top_of_bas I.prime hSpf hlt
      · rw [hWsp]; exact vsQAW_inv
    · have wO := vsQSpl_wt hS hs hd2 W
      have := wt_nat_le 1; have := wt_nat_le D; have := wt_nat_le W.length
      have w2 := wt_list2_le lc (vsWVs W)
      have eW : (Val.list (List.map natList W)).wt = (vsWVs W).wt := rfl
      clear_value lc PV A frV MsV BmV W
      have wDn := wt_nat_le D
      have qS : S ≤ S ^ 32 := Nat.le_self_pow (by norm_num) _
      have tc : c ≤ 10 ^ 21 * S ^ 32 := by
        clear * - hc hA' wW hWl hDS q6 q0 eW wDn wO q3 qS
        omega
      clear * - tc wc1 wc2 wO q6 q0
      omega
  · -- the transitive case
    have ev : GI.Machine.BinOp.lt.eval W.length D = 0 := by simp [GI.Machine.BinOp.eval, hlt]
    rw [ev] at dlt
    have htop : vsQAW s Lb = ⊤ := by
      rw [← vsQASpin_span]; exact vsWSp_top_of_bas I.prime hSpf (by show D ≤ W.length; omega)
    set T := 16 * vsQA2TCost (I := I) hps hm hmb Cφ S + 10 ^ 11 * S ^ 12
    refine (EvalAll.vsQ_ite_zero' (R := fun w c => (∃ ts cs lows, w = vsQSplitV ts cs lows ∧
        VsQSplitOK s 278 Tm ts cs lows) ∧ c ≤ 10 ^ 9 * S ^ 32 + 2 * T ∧ w.wt ≤ T) dlt
      (EvalAll.call_funAll (Det.mk2 (a0 [BmV, vsWVs W]) (a1 [BmV, vsWVs W])) fun v ca hv => ?_)).mono
      fun w c hw => ?_
    · obtain ⟨rfl, hca⟩ := hv
      refine (vsQA2T_spec L.T hphi hS hTm hs h h2 htop hnab).wt_lt.mono fun w cb hw => ?_
      obtain ⟨⟨hout, hcb⟩, hwc⟩ := hw
      refine ⟨hout, ?_, by omega⟩
      have w2 := wt_list2_le lc PV
      have eT : T = 16 * vsQA2TCost (I := I) hps hm hmb Cφ S + 10 ^ 11 * S ^ 12 := rfl
      clear_value lc PV A frV MsV BmV W T
      omega
    · obtain ⟨ce, ⟨hout, hce, hwT⟩, hc⟩ := hw
      refine ⟨hout, ?_⟩
      have eW : (Val.list (List.map natList W)).wt = (vsWVs W).wt := rfl
      have wDn := wt_nat_le D
      have qS : S ≤ S ^ 32 := Nat.le_self_pow (by norm_num) _
      have eT : T = 16 * vsQA2TCost (I := I) hps hm hmb Cφ S + 10 ^ 11 * S ^ 12 := rfl
      have q12 : S ^ 12 ≤ S ^ 32 := hS.pow_le (by omega)
      clear_value lc PV A frV MsV BmV W T
      omega

end GI.Impl
