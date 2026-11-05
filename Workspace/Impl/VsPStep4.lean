module

public import Workspace.Impl.VsPS2P

@[expose] public section

/-!
# The assembled program

On the input `vsPIn s as Lb ccs tcs`: the context, the derived series of `C` down to `N₀`; if
`N̄₀` is abelian, grow with its generators, else go on with `vsPS2` (`vsPStep4_spec`).

The output satisfies `VsPOut`: either a grow output (`[0, ⟨as'⟩]`: `A` grows strictly, stays
abelian and normal, `≤ n²` generators), or the hand-off (`[1, gIn]` with `VsMHard H̄ Ā Ȳ r`).
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

variable {I : VecStabInst}

/-- **Step 4.** -/
def vsPStep4E (ctxP der ab grow tl s2 : ℕ) : Expr :=
  .letE (.call ctxP (.var 0))
  (.letE (.call der (mk2 (.var 1) (.get (.var 0) (.nat 3))))
    (.ite (.call ab (mk2 (.var 1) (.var 2)))
      (mk2 (.nat 0) (.call grow (mk3 (.var 1) (.get (.var 0) (.nat 1)) (.call tl (.get (.var 2) (.nat 1))))))
      (.call s2 (mk3 (.var 1) (.var 0) (.var 2)))))

/-- The function indices of step 4. -/
structure VsPStep4X where
  (x2 : VsPS2X) (s2 ctxP flm fit fl rws rep der dmkg bad fd derp : ℕ)

/-- The layout of step 4. -/
structure VsPStep4Lay (P : Program) (hn : NormalClosure) (hd : DerivedSubgroup) (x : VsPStep4X) :
    Prop where
  L2 : VsPS2Lay P hn x.x2
  hs2 : P.funs[x.s2]? = some (vsPS2E x.x2.fnd2 x.x2.ord x.x2.x3.x4.mkg x.x2.x3.x4.grow x.x2.x3.x4.ab
    x.x2.x3.tl x.x2.s3)
  hctx : P.funs[x.ctxP]? = some (vsPCtxE x.flm x.rws x.rep)
  hflm : P.HasAt x.flm (mapFuns x.flm x.fit)
  hfit : P.funs[x.fit]? = some (vsPFlItemE x.fl)
  hfl : P.HasAt x.fl (vsWFlatFuns x.fl)
  hrws : P.HasAt x.rws (vsWRowsFuns x.rws)
  hrep : P.HasAt x.rep (replicateFuns x.rep)
  hder : P.HasAt x.der (vsPDerFuns x.der x.x2.x3.x4.mkg x.bad x.derp)
  hbad : P.funs[x.bad]? = some (vsPBadE x.fd)
  hfd : P.HasAt x.fd (findFuns x.fd x.x2.x3.x4.d.nt)
  hderp : P.prims[x.derp]? = some (derivedSubgroupPrim hd)

/-- The cost of step 4. -/
noncomputable def vsPStep4Cost (Cφ : ℕ) (hn : NormalClosure) (hd : DerivedSubgroup) (S : ℕ) : ℕ :=
  vsPCtxPCost (vsPN S) (vsPW6 S) + vsPDerCost hd Cφ (vsPN S) (vsPW6 S) +
    vsPAbCost Cφ (vsPN S) (vsPW6 S) + vsPGrowCost hn (vsPN S) (vsPW6 S) + vsPS2Cost (I := I) Cφ hn S +
    10 ^ 4 * (vsPN S + 1) * (vsPW6 S + 100 * (vsPN S + 1) ^ 3)

/-- The local space is not zero when `C̄` is not abelian. -/
theorem _root_.GI.Proved.VsPHyp.nontrivial [Fact I.p.Prime] {s : VsQSt I} {hs : VsQStOK s}
    {as : List (Perm (Fin I.n))} {Lb : List (List (List ℕ))} {ccs : List (Perm (Fin I.n))}
    (hH : VsPHyp hs as Lb ccs) : Nontrivial (Fin (vsQD s) → ZMod I.p) := by
  by_contra hnt
  rw [not_nontrivial_iff_subsingleton] at hnt
  apply hH.hnab
  intro u _
  rw [Subgroup.mem_centralizer_iff]
  intro v _
  have : Subsingleton (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p)) :=
    ⟨fun f g => LinearMap.ext fun x => Subsingleton.elim _ _⟩
  exact Units.ext (Subsingleton.elim _ _)

/-- `C` is not inside `S`. -/
theorem _root_.GI.Proved.VsPHyp.not_le_Sp [Fact I.p.Prime] {s : VsQSt I} {hs : VsQStOK s}
    {as : List (Perm (Fin I.n))} {Lb : List (List (List ℕ))} {ccs : List (Perm (Fin I.n))}
    (hH : VsPHyp hs as Lb ccs) : ¬ gens ccs ≤ vsPSp hs as := by
  intro hle
  apply hH.hnab
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  obtain ⟨x, hxK, hx, rfl⟩ := (vsPBar_mem_iff hs).1 hu
  obtain ⟨y, hyK, hy, rfl⟩ := (vsPBar_mem_iff hs).1 hv
  have hxS := (vsPSp_iff hs as hx).1 (hle hxK)
  have hyS := (vsPSp_iff hs as hy).1 (hle hyK)
  set_option backward.isDefEq.respectTransparency false in
    exact vsM_scal_comm (fun a ha b hb => Subgroup.mem_centralizer_iff.1 (hH.habl hb) a ha) hyS hxS

set_option maxHeartbeats 16000000 in
/-- **Step 4 of the analysis.** On the input `vsPIn s as Lb ccs tcs`, under the hypotheses
`VsPHyp` of the A-loop, the program returns a `VsPOut`: a strict growth of `A` or the hand-off
to the hard case, at cost polynomial in the size `S`, the cost `Cφ` of `φ`, the primitives, and
the input weight. -/
theorem vsPStep4_spec [Fact I.p.Prime] {P : Program} {hn : NormalClosure} {hd : DerivedSubgroup}
    {f : ℕ} {x : VsPStep4X}
    (hf : P.funs[f]? = some (vsPStep4E x.ctxP x.der x.x2.x3.x4.ab x.x2.x3.x4.grow x.x2.x3.tl x.s2))
    (L : VsPStep4Lay P hn hd x) {Cφ : ℕ}
    (hphi : ∀ g ∈ gens I.gs, FunDet P x.x2.x3.x4.d.o.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {S Tm : ℕ} (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s)
    {as : List (Perm (Fin I.n))} {Lb : List (List (List ℕ))} {ccs tcs : List (Perm (Fin I.n))}
    (hH : VsPHyp hs as Lb ccs) :
    FunAll P f (vsPIn s as Lb ccs tcs) (fun w c => VsPOut hs as Lb ccs tcs w ∧
      c ≤ vsPStep4Cost (I := I) Cφ hn hd S + 10 ^ 7 * (vsPN S + 1) * (vsPIn s as Lb ccs tcs).wt) := by
  haveI := hH.nontrivial
  set N := vsPN S
  set W := vsPW6 S
  set rows := vsPRows I.p Lb
  set C := vsPCtx I s.ws' (vsQCs s) rows s.hs
  set A := vsPIn s as Lb ccs tcs
  set ib := vsPInLB I s.ws' (vsQCs s) rows
  have hS1 := hS.one_le
  have hD := vsQD_le hs
  have hLbW : ∀ M ∈ Lb, VsWSq I.p (vsQD s) M := fun M hM =>
    ⟨fun a ha => (hH.hLb M hM).rows a ha, (hH.hLb M hM).len⟩
  have hDDN : vsQD s * vsQD s + 1 ≤ N := by
    have : vsQD s * vsQD s ≤ S * S := Nat.mul_le_mul (by have := hS.d; omega) (by have := hS.d; omega)
    have hS2 : S * S = S ^ 2 := (sq S).symm
    have hS3 : 1 ≤ S ^ 2 := Nat.one_le_pow _ _ (by omega)
    show vsQD s * vsQD s + 1 ≤ 4 * S ^ 2
    omega
  have hLbN : Lb.length ≤ N := le_trans hH.hLbl (Nat.le_of_succ_le hDDN)
  have hC0 := vsPCtx_ok hS hs hLbW hLbN
  have H := hC0.mono_W (W' := W) (by simp only [W, vsPW6]; omega)
  have hnN : I.n * I.n + 1 ≤ N := by
    have : I.n * I.n ≤ S * S := Nat.mul_le_mul (by have := hS.n; omega) (by have := hS.n; omega)
    have hS2 : S * S = S ^ 2 := (sq S).symm
    have hS3 : 1 ≤ S ^ 2 := Nat.one_le_pow _ _ (by omega)
    show I.n * I.n + 1 ≤ 4 * S ^ 2
    omega
  have hpN : I.p ≤ N := by
    have := hS.p; have : S ≤ S ^ 2 := Nat.le_self_pow (by omega) _
    show I.p ≤ 4 * S ^ 2; omega
  have hSp : ∀ g ∈ gens ccs, ib g = true ↔ g ∈ vsPSp hs as := fun g hg =>
    (hH.ib g (hH.hcc hg)).trans (vsPSp_iff hs as (hH.hcc hg)).symm
  -- the context
  have dC := Det.call (Det.var' (P := P) (env := [A]) (i := 0) rfl)
    (vsPCtxP_spec L.hctx L.hflm L.hfit L.hfl L.hrws L.hrep hs hpN (Nat.le_of_succ_le hDDN) hLbW hLbN
      (W := A.wt) le_rfl)
  refine FunAll.intro hf (EvalAll.letE dC fun v1 c1 h1 => ?_)
  obtain ⟨rfl, hc1⟩ := h1
  -- the derived series
  have a3 := Det.get' (Det.var' (P := P) (env := [A, C]) (i := 0) (v := A) rfl) (Det.nat 3)
    (show [vsQLCV s, encGroup as, vsFMatsVal Lb, encGroup ccs, Val.list (tcs.map encPerm)][3]? =
      some (encGroup ccs) from rfl)
  obtain ⟨KA, hKA, dA⟩ : ∃ K, K = _ ∧ Det P [A, C] _ _ K :=
    ⟨_, rfl, Det.mk2 (Det.var' (P := P) (env := [A, C]) (i := 1) rfl) a3⟩
  refine EvalAll.letE (EvalAll.call_funAll dA (Q := fun w c => ∃ (ns : List (Perm (Fin I.n))) (j : ℕ),
      w = encGroup ns ∧ ns.length ≤ I.n ^ 2 ∧ gens ns = vsPDer (gens ccs) j ∧
      ¬ vsPDer (gens ccs) j ≤ vsPSp hs as ∧ vsPDer (gens ccs) (j + 1) ≤ vsPSp hs as ∧
      c ≤ KA + vsPDerCost hd Cφ N W + w.wt + 1) fun v ca hv => ?_) fun v2 c2 h2 => ?_
  · obtain ⟨rfl, hca⟩ := hv
    refine (vsPDer_spec hd L.hder L.L2.L3.L4.hmkg L.hbad L.hfd L.L2.L3.L4.d.hnt L.L2.L3.L4.d.hinl
      L.hderp hphi H hnN (hH.hcc.trans hs.prob.le) hH.hccl hSp hH.not_le_Sp).mono ?_
    rintro w cb ⟨ns, j, rfl, hl, hg, hn', hj, hcb⟩
    have hcb' : cb ≤ vsPDerCost hd Cφ N W := hcb
    exact ⟨ns, j, rfl, hl, hg, hn', hj, by omega⟩
  obtain ⟨ns0, j0, rfl, hl0, hgen, hout0, hj0, hc2⟩ := h2
  rw [← hgen] at hout0
  obtain ⟨hN0, hN0n, hN0C, -⟩ := hH.N0 hj0
  rw [← hgen] at hN0 hN0n hN0C
  have hns0I : ∀ h ∈ ns0, h ∈ gens I.gs := fun h hh => hs.prob.le (hN0 (Subgroup.subset_closure hh))
  set E2 := [A, C, encGroup ns0]
  have dT := Det.call (Det.mk2 (Det.var' (P := P) (env := E2) (i := 1) rfl)
    (Det.var' (P := P) (env := E2) (i := 2) rfl))
    (vsPAb_spec L.L2.L3.L4.hab L.L2.L3.L4.hfo L.L2.L3.L4.hno L.L2.L3.L4.hfi L.L2.L3.L4.hnc
      L.L2.L3.L4.d.L.hcomp L.L2.L3.L4.d.L.hloc L.L2.L3.L4.d.L.hwl L.L2.L3.L4.d.L.heq hphi H hns0I hl0)
  -- weights
  have wC : C.wt ≤ W := H.cw
  have hn6 : (I.n + 1) ^ 6 ≤ S ^ 6 := Nat.pow_le_pow_left hS.n 6
  have p6 : 1 ≤ S ^ 6 := Nat.one_le_pow _ _ (by omega)
  have wWS : W = 10 ^ 9 * S ^ 6 := rfl
  have wG0 : (encGroup ns0).wt ≤ 320 * (I.n + 1) ^ 6 := wt_encGroup_le_sq hl0
  have wCc : (encGroup ccs).wt < A.wt := wt_le_wt_list (by simp [A, vsPIn])
  have wAs : (encGroup as).wt < A.wt := wt_le_wt_list (by simp [A, vsPIn])
  have lA : (Val.list [vsQLCV s, encGroup as, vsFMatsVal Lb, encGroup ccs,
    Val.list (List.map encPerm tcs)]).wt = A.wt := rfl
  have wCG := wt_list2_le C (encGroup ccs)
  have wCG0 := wt_list2_le C (encGroup ns0)
  have wb := wt_boolVal_le (decide (∀ g ∈ 1 :: ns0, ∀ h ∈ 1 :: ns0,
    vsPLocL I s.ws' (vsQCs s) (g * h) = vsPLocL I s.ws' (vsQCs s) (h * g)))
  have hNS : N + 1 ≤ 5 * S ^ 6 := by
    have : S ^ 2 ≤ S ^ 6 := hS.pow_le (by omega)
    show 4 * S ^ 2 + 1 ≤ 5 * S ^ 6; omega
  set Y := (N + 1) * (W + 100 * (N + 1) ^ 3)
  have hY1 : W + 100 * (N + 1) ^ 3 ≤ Y := Nat.le_mul_of_pos_left _ (by omega)
  set Z := (N + 1) * A.wt
  have hZ1 : A.wt ≤ Z := Nat.le_mul_of_pos_left _ (by omega)
  have eCtx : vsPCtxPCost N A.wt = (N + 1) * (2 * 10 ^ 6 * (N + 1) ^ 4) + 4 * 10 ^ 7 * (N + 1) ^ 5 +
      10 ^ 4 * Z + 10 ^ 6 * ((N + 1) * (N + 1) ^ 3) := by
    simp only [vsPCtxPCost, Z]; ring
  have eCtxW : vsPCtxPCost N W = (N + 1) * (2 * 10 ^ 6 * (N + 1) ^ 4) + 4 * 10 ^ 7 * (N + 1) ^ 5 +
      10 ^ 4 * Y := by
    simp only [vsPCtxPCost, Y]; ring
  have hY2 : 100 * ((N + 1) * (N + 1) ^ 3) ≤ Y := by
    simp only [Y]
    calc 100 * ((N + 1) * (N + 1) ^ 3) = (N + 1) * (100 * (N + 1) ^ 3) := by ring
      _ ≤ (N + 1) * (W + 100 * (N + 1) ^ 3) := Nat.mul_le_mul_left _ (by omega)
  have eY : 10 ^ 4 * (N + 1) * (W + 100 * (N + 1) ^ 3) = 10 ^ 4 * Y := by rw [mul_assoc]
  have eZ : 10 ^ 7 * (N + 1) * A.wt = 10 ^ 7 * Z := by rw [mul_assoc]
  have lc : vsPCtxPCost (vsPN S) (vsPW6 S) = vsPCtxPCost N W := rfl
  have wC' : (vsPCtx I s.ws' (vsQCs s) (vsPRows I.p Lb) s.hs).wt ≤ W := wC
  have lAb' : vsPAbCost Cφ (vsPN S) W = vsPAbCost Cφ (vsPN S) (vsPW6 S) := rfl
  have lG0 : (Val.list [Val.nat I.n, Val.list (List.map encPerm (1 :: ns0))]).wt = (encGroup ns0).wt := rfl
  refine EvalAll.ite dT (fun vc cc h => ⟨_, h.1⟩) fun xb cc hcc => ?_
  obtain ⟨hxb', hcc⟩ := hcc
  by_cases hab : ∀ g ∈ 1 :: ns0, ∀ h ∈ 1 :: ns0,
      vsPLocL I s.ws' (vsQCs s) (g * h) = vsPLocL I s.ws' (vsQCs s) (h * g)
  · have hx : xb = 1 := by
      have e : boolVal (decide (∀ g ∈ 1 :: ns0, ∀ h ∈ 1 :: ns0,
        vsPLocL I s.ws' (vsQCs s) (g * h) = vsPLocL I s.ws' (vsQCs s) (h * g))) = .nat 1 := by
        rw [decide_eq_true hab]; rfl
      rw [e] at hxb'; injection hxb'
    subst hx
    rw [if_neg one_ne_zero]
    have gas := Det.get' (Det.var' (P := P) (env := E2) (i := 0) (v := A) rfl) (Det.nat 1)
      (show [vsQLCV s, encGroup as, vsFMatsVal Lb, encGroup ccs, Val.list (tcs.map encPerm)][1]? =
        some (encGroup as) from rfl)
    have g2 : Det P E2 (.get (.var 2) (.nat 1)) (.list (encPerm 1 :: ns0.map encPerm)) _ :=
      Det.get' (Det.var' (P := P) (env := E2) (i := 2) rfl) (Det.nat 1) rfl
    have gt := Det.call g2 (GI.Lang.tail_spec L.L2.L3.htl (encPerm (1 : Perm (Fin I.n))) (ns0.map encPerm))
    obtain ⟨KB, hKB, dB⟩ : ∃ K, K = _ ∧ Det P E2 _ _ K :=
      ⟨_, rfl, Det.mk3 (Det.var' (P := P) (env := E2) (i := 1) rfl) gas gt⟩
    refine (EvalAll.mk2_last (Det.nat (P := P) (env := E2) 0)
      (EvalAll.call_funAll dB (Q := fun w cb => ∃ as' : List (Perm (Fin I.n)),
        w = encGroup as' ∧ VsPGrowOut hs as as' ∧ cb ≤ KB + vsPGrowCost hn N W + w.wt + 1)
        fun v ca hv => ?_)).mono ?_
    · obtain ⟨rfl, hca⟩ := hv
      refine (vsPGrow_spec hn L.L2.L3.L4.hgrow L.L2.L3.L4.hap L.L2.L3.L4.hmkg L.L2.L3.L4.hncp H hs.hsl
        hH.hal hl0).mono ?_
      rintro w cb ⟨as', rfl, hl, he, hcb⟩
      have hcb' : cb ≤ vsPGrowCost hn N W := hcb
      exact ⟨as', rfl, hH.grow_abel hN0 hN0n hN0C hab hout0 hl he, by omega⟩
    · rintro w cw ⟨vb, cb, ⟨as', rfl, hout, hcb⟩, rfl, hcw⟩
      refine ⟨Or.inl ⟨as', rfl, hout⟩, ?_⟩
      have wa' : (encGroup as').wt ≤ 320 * (I.n + 1) ^ 6 := wt_encGroup_le_sq hout.len
      have w02 := wt_list2_le (Val.nat 0) (encGroup as')
      have w0 := wt_nat_le 0
      have wl0 : (Val.list (encPerm (1 : Perm (Fin I.n)) :: ns0.map encPerm)).wt < (encGroup ns0).wt :=
        wt_le_wt_list (by simp [encGroup, encPerms])
      have hTl : loopModK * ((ns0.map encPerm).length + 1) *
          (3 * (Val.list (encPerm (1 : Perm (Fin I.n)) :: ns0.map encPerm)).wt + 1) ≤ 1000 * (4 * Y) := by
        have hA : 3 * (Val.list (encPerm (1 : Perm (Fin I.n)) :: ns0.map encPerm)).wt + 1 ≤
            4 * (W + 100 * (N + 1) ^ 3) := by omega
        have e1 : (N + 1) * (4 * (W + 100 * (N + 1) ^ 3)) = 4 * Y := by simp only [Y]; ring
        have hl2N : (ns0.map encPerm).length ≤ N := by
          rw [List.length_map]
          have : I.n ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left (by have := hS.n; omega) 2
          show ns0.length ≤ 4 * S ^ 2; omega
        calc loopModK * ((ns0.map encPerm).length + 1) *
              (3 * (Val.list (encPerm (1 : Perm (Fin I.n)) :: ns0.map encPerm)).wt + 1)
            ≤ loopModK * (N + 1) * (4 * (W + 100 * (N + 1) ^ 3)) :=
              Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hA
          _ = 1000 * (4 * Y) := by rw [mul_assoc, e1]; rfl
      have wn0l : (Val.list (ns0.map encPerm)).wt ≤ 13 * (I.n + 1) ^ 6 := wt_list_encPerms_le_sq hl0
      have w3b := wt_list3_le C (encGroup as) (Val.list (ns0.map encPerm))
      have lG : vsPGrowCost hn N W = vsPGrowCost hn (vsPN S) (vsPW6 S) := rfl
      have lD : vsPDerCost hd Cφ N W = vsPDerCost hd Cφ (vsPN S) (vsPW6 S) := rfl
      have lAb : vsPAbCost Cφ N W = vsPAbCost Cφ (vsPN S) (vsPW6 S) := rfl
      have lAA : A.wt = (vsPIn s as Lb ccs tcs).wt := rfl
      unfold vsPStep4Cost
      rw [lc, eCtxW, eY]
      rw [eCtx] at hc1
      omega
  · have hx : xb = 0 := by
      have e : boolVal (decide (∀ g ∈ 1 :: ns0, ∀ h ∈ 1 :: ns0,
        vsPLocL I s.ws' (vsQCs s) (g * h) = vsPLocL I s.ws' (vsQCs s) (h * g))) = .nat 0 := by
        rw [decide_eq_false hab]; rfl
      rw [e] at hxb'; injection hxb'
    subst hx
    rw [if_pos rfl]
    refine EvalAll.call_funAll (Det.mk3 (Det.var' (P := P) (env := E2) (i := 1) rfl)
      (Det.var' (P := P) (env := E2) (i := 0) (v := A) rfl)
      (Det.var' (P := P) (env := E2) (i := 2) rfl)) fun v ca hv => ?_
    obtain ⟨rfl, hca⟩ := hv
    refine (vsPS2_spec L.hs2 L.L2 hphi hS hs hH hl0 hgen hj0 (hgen ▸ hout0) hab).wt_lt.mono ?_
    rintro w cw ⟨⟨hout, hcw⟩, -⟩
    refine ⟨hout, ?_⟩
    have hwt := VsPOut.wt_le hS hs hout
    have w3 := wt_list3_le C A (encGroup ns0)
    have lG : vsPGrowCost hn N W = vsPGrowCost hn (vsPN S) (vsPW6 S) := rfl
    have lD : vsPDerCost hd Cφ N W = vsPDerCost hd Cφ (vsPN S) (vsPW6 S) := rfl
    have lAb : vsPAbCost Cφ N W = vsPAbCost Cφ (vsPN S) (vsPW6 S) := rfl
    have lAA : A.wt = (vsPIn s as Lb ccs tcs).wt := rfl
    unfold vsPStep4Cost
    rw [lc, eCtxW, eY]
    rw [eCtx] at hc1
    omega

end GI.Impl
