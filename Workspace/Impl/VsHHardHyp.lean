module

public import Workspace.Impl.VsHHard
public import Workspace.Impl.VsQA4

@[expose] public section

/-!
# The hard case as the spine's hypothesis

`vsHHard_hardHyp`: under `VsQDSz I S Tm` and `(I.d + 1)^278 ≤ Tm`, the hard-case program
satisfies `VsQHardHyp P x.hard (vsHHardCH …) Tm hs`, with the closed cost `vsHHardCH`.
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

/-- The weight of the hand-off value. -/
theorem vsH_wt_GIn [Fact I.p.Prime] {S Tm : ℕ} (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s)
    {as : List (Perm (Fin I.n))} {Lb : List (List (List ℕ))} {ccs tcs ys : List (Perm (Fin I.n))}
    {r : ℕ} (hal : as.length ≤ I.n ^ 2) (hLb : ∀ M ∈ Lb, VsWSq I.p (vsQD s) M)
    (hLbl : Lb.length ≤ vsQD s * vsQD s) (hccl : ccs.length ≤ I.n ^ 2)
    (htl : tcs.length ≤ 24 * vsQD s) (hyl : ys.length ≤ vsQD s ^ 2) (hrn : r ≤ I.n) :
    (vsPGIn s as Lb ccs tcs ys r).wt ≤ 10 ^ 9 * S ^ 8 := by
  have hS1 := hS.one_le
  have hD := vsQD_le hs
  have hSd := hS.d
  have hSp := hS.p
  have hSn := hS.n
  have hS2 : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
  have hS23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS1 (by norm_num)
  have hS36 : S ^ 3 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
  have hS68 : S ^ 6 ≤ S ^ 8 := Nat.pow_le_pow_right hS1 (by norm_num)
  have wlc := vsQ_wt_LC hS hs
  set stl := [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x, natList s.y]
  have hst : (Val.list stl).wt < (vsQLCV s).wt := wt_le_wt_list (by simp [vsQStV, stl])
  have m0 : (vsQGam I).wt < (Val.list stl).wt := wt_le_wt_list (by simp [stl])
  have m1 : (encGroup s.hs).wt < (Val.list stl).wt := wt_le_wt_list (by simp [stl])
  have m2 : (vsWVs s.ws').wt < (Val.list stl).wt := wt_le_wt_list (by simp [stl])
  have m3 : (vsWVs s.ws).wt < (Val.list stl).wt := wt_le_wt_list (by simp [stl])
  have wfr := vsQ_wt_fr hS hs
  have was := hS.wt_group hal
  have wcc := hS.wt_group hccl
  have hp2 : ∀ g : Perm (Fin I.n), (encPerm g).wt ≤ 4 * S ^ 2 := fun g =>
    (wt_encPerm_le g).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hSn 2))
  have wt := vs_wt_list_le_of (tcs.map encPerm) (c := 4 * S ^ 2) (by
    intro v hv; obtain ⟨g, -, rfl⟩ := List.mem_map.1 hv; exact hp2 g)
  have wy := vs_wt_list_le_of (ys.map encPerm) (c := 4 * S ^ 2) (by
    intro v hv; obtain ⟨g, -, rfl⟩ := List.mem_map.1 hv; exact hp2 g)
  rw [List.length_map] at wt wy
  have ht1 : tcs.length * (2 * (4 * S ^ 2) + 1) ≤ (24 * S) * (9 * S ^ 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hDS2 : vsQD s ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hy1 : ys.length * (2 * (4 * S ^ 2) + 1) ≤ S ^ 2 * (9 * S ^ 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e1 : (24 * S) * (9 * S ^ 2) = 216 * S ^ 3 := by ring
  have e2 : S ^ 2 * (9 * S ^ 2) = 9 * S ^ 4 := by ring
  have hS46 : S ^ 4 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
  have hDD : vsQD s * vsQD s ≤ S * S := Nat.mul_le_mul (by omega) (by omega)
  have hSS : S * S = S ^ 2 := (sq S).symm
  have wLb : (vsFMatsVal Lb).wt ≤ 40 * (4 * S ^ 2 + 1) ^ 4 :=
    wt_vsFMatsVal_le (by omega) (by omega) (fun M hM => vsFSq_of_wSq (hLb M hM)) (by omega)
  have h41 : (4 * S ^ 2 + 1) ^ 4 ≤ 625 * S ^ 8 := by
    have : 4 * S ^ 2 + 1 ≤ 5 * S ^ 2 := by have := Nat.one_le_pow 2 S hS1; omega
    calc (4 * S ^ 2 + 1) ^ 4 ≤ (5 * S ^ 2) ^ 4 := Nat.pow_le_pow_left this 4
      _ = 625 * S ^ 8 := by ring
  have wr := wt_nat_le r
  have wl := wt_list_le [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws,
    vsWFrVal I.p I.d s.ws' (vsQCs s), encGroup as, encGroup ccs, Val.list (tcs.map encPerm),
    Val.list (ys.map encPerm), Val.nat r, vsFMatsVal Lb]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at wl
  show (Val.list [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws,
    vsWFrVal I.p I.d s.ws' (vsQCs s), encGroup as, encGroup ccs, Val.list (tcs.map encPerm),
    Val.list (ys.map encPerm), Val.nat r, vsFMatsVal Lb]).wt ≤ _
  omega

/-- The hard-case layout with a single matrix-program index. -/
structure VsHHardLink (P : Program) (x : VsHHX) (phi : ℕ)
    (hps : PointwiseStab) (hm : Membership) : Prop extends VsHHLay P x hps hm where
  p1 : x.f.i.m.phi = phi
  p2 : x.q.t.c.phi = phi
  p3 : x.pp.phi = phi
  p4 : x.w.phi = phi

/-- A uniform cost, retaining the costs of the cited primitives. -/
noncomputable def vsHHardCH (hps : PointwiseStab) (hm : Membership) (Cφ : ℕ)
    (I : VecStabInst) (S : ℕ) : ℕ :=
  vsHHardCost hps hm Cφ (vsPN S) (10 ^ 9 * S ^ 8) (10 ^ 9 * S ^ 8)
    I.n (10 ^ 20 * (S + 1) ^ 12) S ((S + 1) ^ 278)

/-- The conjugation context fits the size used by step 4. -/
theorem vsH_wt_ac [Fact I.p.Prime] {S Tm : ℕ} (hS : VsQDSz I S Tm)
    {s : VsQSt I} (hs : VsQStOK s) :
    (vsHAcV s).wt ≤ 1000 * (vsPN S + 1) ^ 3 := by
  have hS1 := hS.one_le
  have hD := vsQD_le hs
  have hSd := hS.d
  have hSp := hS.p
  have hS2 : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
  have hS23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS1 (by norm_num)
  have hS3 : 3 ≤ S := by
    have := hS.n
    have := I.p_le
    have := I.prime.two_le
    omega
  have hbase : 10 * S ≤ vsPN S + 1 := by unfold vsPN; nlinarith only [hS3]
  have h3 : 1000 * S ^ 3 ≤ (vsPN S + 1) ^ 3 := by
    have hh := Nat.pow_le_pow_left hbase 3
    have he : (10 * S) ^ 3 = 1000 * S ^ 3 := by ring
    rwa [he] at hh
  have wfr := vsQ_wt_fr hS hs
  have wg := hS.g
  have wp := wt_nat_le I.p
  have wd := wt_nat_le (vsQD s)
  have wz0 : (natList (vsWZ (vsQD s))).wt ≤ 5 * (S + 1) ^ 2 :=
    wt_natList_le_sq (B := S) (xs := vsWZ (vsQD s))
      (fun y hy => by simp [vsWZ] at hy; omega) (by simp [vsWZ]; omega)
  have hsq : (S + 1) ^ 2 ≤ 4 * S ^ 2 := by nlinarith only [hS1]
  have wz : (natList (vsWZ (vsQD s))).wt ≤ 20 * S ^ 2 := by omega
  have wl := wt_list_le [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s),
    Val.nat I.p, Val.nat (vsQD s), natList (vsWZ (vsQD s))]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.length_cons, List.length_nil] at wl
  change (Val.list _).wt ≤ _
  have h13 : 1 ≤ S ^ 3 := Nat.one_le_pow _ _ hS1
  omega

/-- Increasing the tuple orbit bound increases the hard-case cost. -/
theorem vsHHardCost_mono_B (hps : PointwiseStab) (hm : Membership)
    (Cφ N N2 W n Ss S : ℕ) {B B' : ℕ} (hb : B ≤ B') :
    vsHHardCost hps hm Cφ N N2 W n Ss S B ≤
      vsHHardCost hps hm Cφ N N2 W n Ss S B' := by
  unfold vsHHardCost vsHWCost vsQSotCost vsQPsB reduceCost vsQTS
  gcongr

/-- The internal hard hand-off permits the transversal enlarged by the first `Q₈`. -/
structure VsHHardHand [Fact I.p.Prime] {s : VsQSt I} (hs : VsQStOK s)
    (as : List (Perm (Fin I.n))) (Lb : List (List (List ℕ)))
    (ccs tcs ys : List (Perm (Fin I.n))) (r : ℕ) : Prop where
  hyp : VsPHyp hs as Lb ccs
  tmem : ∀ t ∈ tcs, t ∈ gens s.hs
  cov : ∀ h ∈ gens s.hs, ∃ t ∈ tcs, t⁻¹ * h ∈ gens ccs
  tl : tcs.length ≤ 24 * vsQD s
  hys : ∀ y ∈ ys, y ∈ gens s.hs
  ysl : ys.length ≤ vsQD s ^ 2
  rp : r.Prime
  rn : r ≤ I.n
  hard : VsMHard (vsPBar hs (gens s.hs)) (vsPBar hs (gens as))
    (vsPBar hs (gens ys) ⊔ vsMScal (vsPBar hs (gens as))) r

set_option maxHeartbeats 400000 in
/-- The hard program satisfies the spine's hard-case hypothesis for every state. -/
theorem vsHHard_run [Fact I.p.Prime] {P : Program} {x : VsHHX} {phi : ℕ}
    {hps : PointwiseStab} {hm : Membership} (L : VsHHardLink P x phi hps hm)
    {Cφ S Tm : ℕ}
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hS : VsQDSz I S Tm) (hTm : (I.d + 1) ^ 278 ≤ Tm)
    {s : VsQSt I} (hs : VsQStOK s) :
    ∀ (as : List (Perm (Fin I.n))) (Lb : List (List (List ℕ)))
      (ccs tcs ys : List (Perm (Fin I.n))) (r : ℕ),
      VsHHardHand hs as Lb ccs tcs ys r → ¬ s.Ab →
      FunAll P x.hard (.list [vsQLCV s, vsPGIn s as Lb ccs tcs ys r])
        (fun w c => VsQHardOut hs Lb ccs ys r Tm w ∧ c ≤ vsHHardCH hps hm Cφ I S) := by
  intro as Lb ccs tcs ys r hHand hnab
  have hH := hHand.hyp
  have h : VsHHyp hs as Lb ys r :=
    ⟨hH.has, hH.hLb, hH.hspan, hHand.hys, hHand.hard⟩
  have hS1 := hS.one_le
  have hD := vsQD_le hs
  have hSd := hS.d
  have hSn := hS.n
  have hSp := hS.p
  have hS2 : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
  have hS28 : S ^ 2 ≤ S ^ 8 := Nat.pow_le_pow_right hS1 (by norm_num)
  have hS48 : S ^ 4 ≤ S ^ 8 := Nat.pow_le_pow_right hS1 (by norm_num)
  have hS68 : S ^ 6 ≤ S ^ 8 := Nat.pow_le_pow_right hS1 (by norm_num)
  have hS8 : 1 ≤ S ^ 8 := Nat.one_le_pow _ _ hS1
  have hDD : vsQD s * vsQD s ≤ S ^ 2 := by
    simpa [sq] using Nat.mul_le_mul (show vsQD s ≤ S by omega) (show vsQD s ≤ S by omega)
  have hnn : I.n ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left (by omega : I.n ≤ S) 2
  have hDDN : vsQD s ^ 2 + 1 ≤ vsPN S := by unfold vsPN; rw [← sq] at hDD; omega
  have hLbW : ∀ M ∈ Lb, VsWSq I.p (vsQD s) M := fun M hM =>
    ⟨fun a ha => (hH.hLb M hM).rows a ha, (hH.hLb M hM).len⟩
  have hLbN : Lb.length ≤ vsPN S := by unfold vsPN; have := hH.hLbl; omega
  have H0 := vsPCtx_ok hS hs hLbW hLbN
  have H := H0.mono_W (W' := 10 ^ 9 * S ^ 8) (by omega)
  have ht24 : tcs.length ≤ 24 * vsQD s := by have := hHand.tl; omega
  have hw := vsH_wt_GIn hS hs hH.hal hLbW hH.hLbl hH.hccl ht24 hHand.ysl hHand.rn
  have hlc : (vsQLCV s).wt ≤ 10 ^ 9 * S ^ 8 := by
    have := vsQ_wt_LC hS hs
    omega
  have hN2 : vsPN S ≤ 10 ^ 9 * S ^ 8 := by unfold vsPN; omega
  have hsz : VsQSz I.p I.d (vsQExp I) (10 ^ 9 * S ^ 8) :=
    ⟨H.sz.pN.trans hN2, H.sz.dN.trans hN2, H.sz.eN.trans hN2, H.sz.p0⟩
  have hfr : VsWFrOK I.p (10 ^ 9 * S ^ 8) I.d s.ws' (vsQCs s) :=
    ⟨H.fr.hp, H.fr.hpN.trans hN2, H.fr.hdN.trans hN2, H.fr.h', H.fr.hc, H.fr.hl.trans hN2⟩
  have hbig : 1 + vsQD s * vsQD s * (as.length + 1 + vsQD s ^ 2) ≤ 10 ^ 9 * S ^ 8 := by
    have ha : as.length + 1 + vsQD s ^ 2 ≤ 3 * S ^ 2 := by have := hH.hal; rw [← sq] at hDD; omega
    have hb := Nat.mul_le_mul hDD ha
    have he : S ^ 2 * (3 * S ^ 2) = 3 * S ^ 4 := by ring
    rw [he] at hb
    omega
  have hasl : as.length + 1 + vsQD s ^ 2 ≤ 10 ^ 9 * S ^ 8 := by
    have := hH.hal
    rw [← sq] at hDD
    omega
  have hsac : 1000 * (vsPN S + 1) ^ 3 ≤ 10 ^ 20 * (S + 1) ^ 12 := by
    have hh := vsP_pow_N hS1 3
    have hp : S ^ 6 ≤ (S + 1) ^ 12 :=
      (Nat.pow_le_pow_left (Nat.le_succ S) 6).trans (Nat.pow_le_pow_right (by omega) (by norm_num))
    norm_num at hh
    omega
  have hsk : 20 * (vsPN S + 1) ^ 4 ≤ 10 ^ 20 * (S + 1) ^ 12 := by
    have hh := vsP_pow_N hS1 4
    have hp : S ^ 8 ≤ (S + 1) ^ 12 :=
      (Nat.pow_le_pow_left (Nat.le_succ S) 8).trans (Nat.pow_le_pow_right (by omega) (by norm_num))
    norm_num at hh
    omega
  have hsw : (vsPGIn s as Lb ccs tcs ys r).wt + 100 * (vsPN S + 1) ^ 3 ≤
      10 ^ 20 * (S + 1) ^ 12 := by
    have hh := vsP_pow_N hS1 3
    have hp : S ^ 8 ≤ (S + 1) ^ 12 :=
      (Nat.pow_le_pow_left (Nat.le_succ S) 8).trans (Nat.pow_le_pow_right (by omega) (by norm_num))
    norm_num at hh
    omega
  have hraw := vsHHard_spec L.toVsHHLay (L.p1 ▸ hphi) (L.p2 ▸ hphi)
    (L.p3 ▸ hphi) (L.p4 ▸ hphi) h hH.hcc hH.hccl hH.hccC hnab H hw hw hlc
    hDDN (by have := hHand.ysl; omega) (by have := hHand.rn; unfold vsPN; omega)
    hLbN hsz (H.gam.trans hN2) (H.n.trans hN2) hfr hbig hasl (vsH_wt_ac hS hs)
    (by have hp : S ^ 2 ≤ (S + 1) ^ 12 :=
          (Nat.pow_le_pow_left (Nat.le_succ S) 2).trans (Nat.pow_le_pow_right (by omega) (by norm_num))
        omega) hsac hsk hsw hS hTm
  refine hraw.mono fun w c hw' => ⟨hw'.1, hw'.2.trans ?_⟩
  have hcnt := vsFEigL_count I.prime (vsHFx s ((1 :: as) ++ vsHK s Lb r ys)) (vsHFx_sq _)
  have hcnt' : (vsHPs s ((1 :: as) ++ vsHK s Lb r ys)).length ≤ vsQD s := hcnt.1
  have hb : ((vsHPs s ((1 :: as) ++ vsHK s Lb r ys)).length + 1) ^ 278 ≤ (S + 1) ^ 278 :=
    Nat.pow_le_pow_left (by omega) 278
  exact vsHHardCost_mono_B hps hm Cφ _ _ _ _ _ _ hb

/-- The external hard-case hypothesis uses the sharper original transversal bound. -/
theorem vsHHard_hardHyp [Fact I.p.Prime] {P : Program} {x : VsHHX} {phi : ℕ}
    {hps : PointwiseStab} {hm : Membership} (L : VsHHardLink P x phi hps hm)
    {Cφ S Tm : ℕ}
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hS : VsQDSz I S Tm) (hTm : (I.d + 1) ^ 278 ≤ Tm)
    {s : VsQSt I} (hs : VsQStOK s) :
    VsQHardHyp P x.hard (vsHHardCH hps hm Cφ I S) Tm hs := by
  intro as Lb ccs tcs ys r h hnab
  exact vsHHard_run L hphi hS hTm hs as Lb ccs tcs ys r
    ⟨h.hyp, h.tmem, h.cov, by have := h.tl; omega, h.hys, h.ysl, h.rp, h.rn, h.hard⟩ hnab

end GI.Impl
