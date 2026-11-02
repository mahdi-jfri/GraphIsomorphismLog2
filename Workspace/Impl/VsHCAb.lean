import Workspace.Impl.VsHHardHyp
import Workspace.Impl.VsHCData

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- A context bound shared by the continuation's tests. -/
theorem vsHC_ctx [Fact I.p.Prime] {S Tm : ℕ} (hS : VsQDSz I S Tm)
    {s : VsQSt I} (hs : VsQStOK s) {as : List (Perm (Fin I.n))}
    {Lb : List (List (List ℕ))} {ccs : List (Perm (Fin I.n))} (hH : VsPHyp hs as Lb ccs) :
    VsPCtxOK I (vsPN S) (10 ^ 9 * S ^ 8) s.ws' (vsQCs s) (vsPRows I.p Lb) s.hs := by
  have h1 := hS.one_le
  have hd := vsQD_le hs
  have hsD := hS.d
  have hS2 : S ≤ S ^ 2 := Nat.le_self_pow (by omega) _
  have hS68 : S ^ 6 ≤ S ^ 8 := Nat.pow_le_pow_right h1 (by omega)
  have hDD : vsQD s * vsQD s ≤ S * S := Nat.mul_le_mul (by omega) (by omega)
  have hLbW : ∀ M ∈ Lb, VsWSq I.p (vsQD s) M := fun M hM =>
    ⟨fun a ha => (hH.hLb M hM).rows a ha, (hH.hLb M hM).len⟩
  have hLbN : Lb.length ≤ vsPN S := by have := hH.hLbl; unfold vsPN; nlinarith only [hDD, this]
  exact (vsPCtx_ok hS hs hLbW hLbN).mono_W (by omega)

/-- The weight of an internal hard hand-off. -/
theorem vsHC_wt_hand [Fact I.p.Prime] {S Tm : ℕ} (hS : VsQDSz I S Tm)
    {s : VsQSt I} (hs : VsQStOK s) {as : List (Perm (Fin I.n))}
    {Lb : List (List (List ℕ))} {ccs tcs ys : List (Perm (Fin I.n))} {r : ℕ}
    (h : VsHHardHand hs as Lb ccs tcs ys r) :
    (vsPGIn s as Lb ccs tcs ys r).wt ≤ 10 ^ 9 * S ^ 8 :=
  vsH_wt_GIn hS hs h.hyp.hal
    (fun M hM => ⟨fun a ha => (h.hyp.hLb M hM).rows a ha, (h.hyp.hLb M hM).len⟩)
    h.hyp.hLbl h.hyp.hccl h.tl h.ysl h.rn

/-- Test whether the local image of the smaller centralizer is abelian. -/
def vsHCAbE (ctx ab : ℕ) : Expr :=
  .letE (.call ctx (arg 0)) (.call ab (mk2 (.var 1) (arg 1)))

/-- Extract the first nonscalar basis element. -/
def vsHCHeadE (front : ℕ) : Expr :=
  .letE (.call front (.var 0)) (.get (.get (.var 1) (.nat 1)) (.nat 0))

def vsHCAbCost (Cφ S : ℕ) : ℕ :=
  16 * (vsPCtxPCost (vsPN S) (10 ^ 9 * S ^ 8) +
    vsPAbCost Cφ (vsPN S) (10 ^ 9 * S ^ 8)) + 10 ^ 12 * (S + 1) ^ 12

def vsHCHeadCost (Cφ S : ℕ) : ℕ :=
  16 * vsHFrontCost Cφ (vsPN S) (10 ^ 9 * S ^ 8) + 10 ^ 12 * (S + 1) ^ 12

set_option maxHeartbeats 1000000 in
/-- The abelian test on the centralizer returned by the first `Q₈`. -/
theorem vsHCAb_spec [Fact I.p.Prime] {P : Program} {x : VsHHX} {phi f : ℕ}
    {hps : PointwiseStab} {hm : Membership} (L : VsHHardLink P x phi hps hm)
    {hn : NormalClosure} {hd : DerivedSubgroup} {st : VsPStep4X}
    (L4 : VsPStep4Lay P hn hd st)
    (hf : P.funs[f]? = some (vsHCAbE x.f.ctx st.x2.x3.x4.ab))
    (hp : st.x2.x3.x4.d.o.phi = phi) {Cφ S Tm : ℕ}
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s)
    {as : List (Perm (Fin I.n))} {Lb : List (List (List ℕ))}
    {ccs tcs ys ks : List (Perm (Fin I.n))} {r : ℕ}
    (h : VsHHardHand hs as Lb ccs tcs ys r) (hk : gens ks ≤ gens s.hs) (hkl : ks.length ≤ I.n ^ 2) :
    FunDet P f (.list [vsPGIn s as Lb ccs tcs ys r, encGroup ks])
      (boolVal (decide (∀ g ∈ 1 :: ks, ∀ h ∈ 1 :: ks,
        vsPLocL I s.ws' (vsQCs s) (g * h) = vsPLocL I s.ws' (vsQCs s) (h * g))))
      (vsHCAbCost Cφ S) := by
  have H := vsHC_ctx hS hs h.hyp
  have hLbW : ∀ M ∈ Lb, VsWSq I.p (vsQD s) M := fun M hM =>
    ⟨fun a ha => (h.hyp.hLb M hM).rows a ha, (h.hyp.hLb M hM).len⟩
  have hw := vsH_wt_GIn hS hs h.hyp.hal hLbW h.hyp.hLbl h.hyp.hccl h.tl h.ysl h.rn
  have hctx := vsHCtx_spec L.toVsHHLay.F.hctx L.toVsHHLay.F.hflm L.toVsHHLay.F.hfit
    L.toVsHHLay.F.hfl L.toVsHHLay.F.hrws L.toVsHHLay.F.hrep H.sz.pN H.dd hLbW
    (h.hyp.hLbl.trans H.dd) hw
  have J := L4.L2.L3.L4
  have hab := vsPAb_spec J.hab J.hfo J.hno J.hfi J.hnc J.d.L.hcomp J.d.L.hloc
    J.d.L.hwl J.d.L.heq (hp ▸ hphi) H
    (fun g hg => hs.prob.le (hk (Subgroup.subset_closure hg))) hkl
  set G := vsPGIn s as Lb ccs tcs ys r
  set C := vsPCtx I s.ws' (vsQCs s) (vsPRows I.p Lb) s.hs
  have a0 := Det.arg' (P := P) (vs := [G, encGroup ks]) (rest := []) (j := 0) rfl
  have dc := Det.call a0 hctx
  have a1 := Det.arg' (P := P) (vs := [G, encGroup ks]) (rest := [C]) (j := 1) rfl
  have da := Det.call (Det.mk2 (Det.var' (P := P) (env := [.list [G, encGroup ks], C]) (i := 1) rfl) a1) hab
  refine FunDet.intro hf ((Det.letE dc da).mono ?_)
  have wAb := FunDet.wt_lt' hab
  have wc := H.cw
  have wk := hS.wt_group hkl
  have wa := wt_list2_le G (encGroup ks)
  have wb := wt_list2_le C (encGroup ks)
  have hW : (10 ^ 9 * S ^ 8) ≤ 10 ^ 9 * (S + 1) ^ 12 :=
    Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (Nat.le_succ S) 8).trans
      (Nat.pow_le_pow_right (by omega) (by omega)))
  have h6 : S ^ 6 ≤ (S + 1) ^ 12 := (Nat.pow_le_pow_left (Nat.le_succ S) 6).trans
    (Nat.pow_le_pow_right (by omega) (by omega))
  have h1 : 1 ≤ (S + 1) ^ 12 := Nat.one_le_pow _ _ (by omega)
  unfold vsHCAbCost
  change G.wt ≤ _ at hw
  change C.wt ≤ _ at wc
  omega

set_option maxHeartbeats 1000000 in
/-- The basis extraction used in the final two-`Q₈` branch. -/
theorem vsHCHead_spec [Fact I.p.Prime] {P : Program} {x : VsHHX} {phi f : ℕ}
    {hps : PointwiseStab} {hm : Membership} (L : VsHHardLink P x phi hps hm)
    (hf : P.funs[f]? = some (vsHCHeadE x.fr)) {Cφ S Tm : ℕ}
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s)
    {as : List (Perm (Fin I.n))} {Lb : List (List (List ℕ))}
    {ccs tcs ys : List (Perm (Fin I.n))} {r : ℕ}
    (h : VsHHardHand hs as Lb ccs tcs ys r) :
    FunDet P f (vsPGIn s as Lb ccs tcs ys r) (encPerm (vsHCHead s Lb r ys)) (vsHCHeadCost Cφ S) := by
  have H := vsHC_ctx hS hs h.hyp
  have hM : VsHHyp hs as Lb ys r := ⟨h.hyp.has, h.hyp.hLb, h.hyp.hspan, h.hys, h.hard⟩
  have hLbW : ∀ M ∈ Lb, VsWSq I.p (vsQD s) M := fun M hM =>
    ⟨fun a ha => (h.hyp.hLb M hM).rows a ha, (h.hyp.hLb M hM).len⟩
  have hw := vsH_wt_GIn hS hs h.hyp.hal hLbW h.hyp.hLbl h.hyp.hccl h.tl h.ysl h.rn
  have hS1 := hS.one_le
  have hD := vsQD_le hs
  have hSd := hS.d
  have hSn := hS.n
  have hS2 : S ≤ S ^ 2 := Nat.le_self_pow (by omega) _
  have hDD : vsQD s * vsQD s ≤ S * S := Nat.mul_le_mul (by omega) (by omega)
  have hDDN : vsQD s ^ 2 + 1 ≤ vsPN S := by unfold vsPN; nlinarith only [hDD, hS1]
  have hLbl : Lb.length ≤ vsPN S := by have := h.hyp.hLbl; unfold vsPN; nlinarith only [hDD, this]
  have hF := vsHFront_spec L.toVsHHLay.hf L.toVsHHLay.F (L.p1 ▸ hphi) hM H hw hDDN
    (by have := h.ysl; omega) (by have := h.rn; unfold vsPN; omega) hLbl
  set G := vsPGIn s as Lb ccs tcs ys r
  set FV := Val.list [vsHGc (vsPCtx I s.ws' (vsQCs s) (vsPRows I.p Lb) s.hs) r
      (I.p ^ (vsPRows I.p Lb).length - 1) (decide (r ∣ I.p ^ (vsPRows I.p Lb).length - 1)),
    .list ((vsHB s Lb r ys).map encPerm), .list ((vsHK s Lb r ys).map encPerm)]
  have df := Det.call (Det.var' (P := P) (env := [G]) (i := 0) rfl) hF
  have db := Det.get' (Det.var' (P := P) (env := [G, FV]) (i := 1) rfl) (Det.nat 1)
    (show [vsHGc (vsPCtx I s.ws' (vsQCs s) (vsPRows I.p Lb) s.hs) r
      (I.p ^ (vsPRows I.p Lb).length - 1) (decide (r ∣ I.p ^ (vsPRows I.p Lb).length - 1)),
      Val.list ((vsHB s Lb r ys).map encPerm), Val.list ((vsHK s Lb r ys).map encPerm)][1]? =
      some (.list ((vsHB s Lb r ys).map encPerm)) from rfl)
  have hget : ((vsHB s Lb r ys).map encPerm)[0]? = some (encPerm (vsHCHead s Lb r ys)) := by
    cases he : vsHB s Lb r ys with
    | nil => exact False.elim (vsHC_basis_ne_nil hM he)
    | cons b bs => simp [vsHCHead, he]
  have dy := Det.get' db (Det.nat 0) hget
  refine FunDet.intro hf ((Det.letE df dy).mono ?_)
  have wf : FV.wt < vsHFrontCost Cφ (vsPN S) (10 ^ 9 * S ^ 8) := FunDet.wt_lt' hF
  have wb : (Val.list ((vsHB s Lb r ys).map encPerm)).wt < FV.wt := wt_le_wt_list (by simp [FV])
  have wHead : (encPerm (vsHCHead s Lb r ys)).wt <
      (Val.list ((vsHB s Lb r ys).map encPerm)).wt := by
    apply wt_le_wt_list
    cases he : vsHB s Lb r ys with
    | nil => exact False.elim (vsHC_basis_ne_nil hM he)
    | cons b bs => simp [vsHCHead, he]
  have wfFV : FV.wt < vsHFrontCost Cφ (vsPN S) (10 ^ 9 * S ^ 8) := wf
  dsimp only [FV] at wf wb
  have wG : G.wt ≤ 10 ^ 9 * (S + 1) ^ 12 := hw.trans (Nat.mul_le_mul_left _
    ((Nat.pow_le_pow_left (Nat.le_succ S) 8).trans (Nat.pow_le_pow_right (by omega) (by omega))))
  have h1 : 1 ≤ (S + 1) ^ 12 := Nat.one_le_pow _ _ (by omega)
  unfold vsHCHeadCost
  omega

/-- Pieces computation on a short list of elements of the current group. -/
theorem vsHC_ps_spec [Fact I.p.Prime] {P : Program} {x : VsHHX} {phi : ℕ}
    {hps : PointwiseStab} {hm : Membership} (L : VsHHardLink P x phi hps hm)
    {Cφ S Tm : ℕ}
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s)
    {as : List (Perm (Fin I.n))} {Lb : List (List (List ℕ))}
    {ccs tcs ys K : List (Perm (Fin I.n))} {r : ℕ}
    (h : VsHHardHand hs as Lb ccs tcs ys r)
    (hK : ∀ g ∈ K, g ∈ gens s.hs) (hKl : K.length ≤ vsQD s ^ 2) :
    FunDet P x.pp.ps (.list [vsPGIn s as Lb ccs tcs ys r, .list (K.map encPerm)])
      (vsFMatsVal (vsHPs s ((1 :: as) ++ K))) (vsHPsCost Cφ (10 ^ 9 * S ^ 8)) := by
  have H := vsHC_ctx hS hs h.hyp
  have hS1 := hS.one_le
  have hD := vsQD_le hs
  have hSd := hS.d
  have hSn := hS.n
  have hS2 : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
  have hS28 : S ^ 2 ≤ S ^ 8 := Nat.pow_le_pow_right hS1 (by norm_num)
  have hS48 : S ^ 4 ≤ S ^ 8 := Nat.pow_le_pow_right hS1 (by norm_num)
  have hS8 : 1 ≤ S ^ 8 := Nat.one_le_pow _ _ hS1
  have hDD : vsQD s * vsQD s ≤ S ^ 2 := by
    simpa [sq] using Nat.mul_le_mul (show vsQD s ≤ S by omega) (show vsQD s ≤ S by omega)
  have hnn : I.n ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left (by omega : I.n ≤ S) 2
  have hN2 : vsPN S ≤ 10 ^ 9 * S ^ 8 := by unfold vsPN; omega
  have hsz : VsQSz I.p I.d (vsQExp I) (10 ^ 9 * S ^ 8) :=
    ⟨H.sz.pN.trans hN2, H.sz.dN.trans hN2, H.sz.eN.trans hN2, H.sz.p0⟩
  have hfr : VsWFrOK I.p (10 ^ 9 * S ^ 8) I.d s.ws' (vsQCs s) :=
    ⟨H.fr.hp, H.fr.hpN.trans hN2, H.fr.hdN.trans hN2, H.fr.h', H.fr.hc, H.fr.hl.trans hN2⟩
  have ha : ((1 :: as) ++ K).length ≤ 3 * S ^ 2 := by
    have := h.hyp.hal
    simp only [List.length_append, List.length_cons]
    rw [← sq] at hDD
    omega
  have hbig : 1 + vsQD s * vsQD s * ((1 :: as) ++ K).length ≤ 10 ^ 9 * S ^ 8 := by
    have hb := Nat.mul_le_mul hDD ha
    have he : S ^ 2 * (3 * S ^ 2) = 3 * S ^ 4 := by ring
    rw [he] at hb
    omega
  have hLbW : ∀ M ∈ Lb, VsWSq I.p (vsQD s) M := fun M hM =>
    ⟨fun a ha => (h.hyp.hLb M hM).rows a ha, (h.hyp.hLb M hM).len⟩
  have hw := vsH_wt_GIn hS hs h.hyp.hal hLbW h.hyp.hLbl h.hyp.hccl h.tl h.ysl h.rn
  exact vsHPs_spec L.toVsHHLay.Pp (L.p3 ▸ hphi) hs hsz (H.gam.trans hN2)
    (H.n.trans hN2) hfr h.hyp.has hK hbig (by omega) hw

end GI.Impl
