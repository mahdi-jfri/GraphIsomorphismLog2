module

public import Workspace.Impl.VsQRoots
public import Workspace.Impl.VsQSize
public import Workspace.Impl.VsQDrv

@[expose] public section

/-!
# The whole program on one instance

All layouts together (`VsQAllLay`), and the spec of the entry on the task input with an explicit
cost (`vsQAll_spec`). The hard case and the `Q₈` continuation enter as a hypothesis.
-/

open Matrix Module

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

set_option backward.isDefEq.respectTransparency false
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

/-- The indices of all parts. -/
structure VsQAllX where
  (top : VsQTopX) (drv : VsQDrvX) (ana : VsQAnaX) (al : VsQALX) (phi : VsQPhiX)

/-- All layouts, and the links between the parts. -/
structure VsQAllLay (P : Program) (x : VsQAllX) (hps : PointwiseStab) (hm : Membership)
    (hmb : MinimalBlocks) (hn : NormalClosure) (hd : DerivedSubgroup) (hcm : ConstructiveMembership) :
    Prop where
  T : VsQTopLay P x.top hm
  D : VsQDrvLay P x.drv hm
  A : VsQAnaLay P x.ana hps hm
  L : VsQALLay P x.al hps hm hmb hn hd
  F : VsQPhiLay P x.phi hcm
  e1 : x.top.drv = x.drv.drv
  e2 : x.drv.ana = x.ana.ana
  e3 : x.ana.al = x.al.al
  p1 : x.drv.phi = x.phi.phi
  p2 : x.ana.phi = x.phi.phi
  p3 : x.ana.fld.phi = x.phi.phi
  p4 : x.al.x2.phib = x.phi.phi
  p5 : x.al.x2.s.t.w.phi = x.phi.phi
  p6 : x.al.x3.c.t.c.phi = x.phi.phi
  p7 : x.al.x3.phi = x.phi.phi
  p8 : x.al.x4.x2.x3.x4.d.o.phi = x.phi.phi

/-- The bound `N` on the small sizes. -/
def vsQNf (X : ℕ) : ℕ := 2000 * (X + 1) ^ 7

/-- The size bound `S`. -/
def vsQSf (X : ℕ) : ℕ := 10 ^ 5 * (vsQNf X + 1) ^ 278

/-- The cost constant of the driver. -/
noncomputable def vsQCn (hps : PointwiseStab) (hm : Membership) (hmb : MinimalBlocks)
    (hn : NormalClosure) (hd : DerivedSubgroup) (CH CQ : ℕ → VecStabInst → ℕ → ℕ) (Cφ : ℕ)
    (I : VecStabInst) (N S : ℕ) : ℕ :=
  8 * (vsQLCCost Cφ S + vsBOrbCost hps hm I.n S Cφ N + (vsBFldCost hps hm I.n S Cφ + 10 ^ 25 * S ^ 32) +
    (S * S + 1) * vsQALCost (I := I) hps hm hmb hn hd Cφ S (CH Cφ I S) (CQ Cφ I S) +
    vsPCtxPCost (vsPN S) (10 ^ 9 * S ^ 8) + vsPAbCost Cφ (vsPN S) (10 ^ 8 * S ^ 6)) + 10 ^ 12 * S ^ 12 +
    vsQPasteCost hm I.n S + vsQAppCost Cφ N + 10 ^ 10 * S ^ 9

/-- The cost of the whole program on an input of weight `X`. -/
noncomputable def vsQTot (hps : PointwiseStab) (hm : Membership) (hmb : MinimalBlocks)
    (hn : NormalClosure) (hd : DerivedSubgroup) (hcm : ConstructiveMembership)
    (CH CQ : ℕ → VecStabInst → ℕ → ℕ) (I : VecStabInst) (X : ℕ) : ℕ :=
  vsQTopCost hm X (20 * vsQCn hps hm hmb hn hd CH CQ (vsQCphi hcm (vsQNf X)) I (vsQNf X) (vsQSf X)) 558

set_option maxHeartbeats 4000000 in
/-- **The whole program on one instance.** -/
theorem vsQAll_spec {P : Program} {x : VsQAllX} {hps : PointwiseStab} {hm : Membership}
    {hmb : MinimalBlocks} {hn : NormalClosure} {hd : DerivedSubgroup} {hcm : ConstructiveMembership}
    (L : VsQAllLay P x hps hm hmb hn hd hcm) {CH CQ : ℕ → VecStabInst → ℕ → ℕ}
    (HQ : ∀ (I : VecStabInst) [Fact I.p.Prime] (Cφ S Tm : ℕ),
      (∀ g ∈ gens I.gs, FunDet P x.phi.phi (.list [vsQGam I, encPerm g])
        (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ) →
      VsQDSz I S Tm → (I.d + 1) ^ 278 ≤ Tm → ∀ (s : VsQSt I) (hs : VsQStOK s),
      VsQHardHyp P x.al.hard (CH Cφ I S) Tm hs ∧ VsQ8CHyp P x.al.q8c (CQ Cφ I S) Tm hs)
    (I : VecStabInst) :
    FunAll P x.top.top (vsQTaskIn I) (fun w c => GensOf ((vecStab I).map (gens I.gs).subtype) w ∧
      c ≤ vsQTot hps hm hmb hn hd hcm CH CQ I (vsQTaskIn I).wt) := by
  haveI : Fact I.p.Prime := ⟨I.prime⟩
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  obtain ⟨hnX, hdX, hgX⟩ := vsQ_in_sizes I
  set X := (vsQTaskIn I).wt with hX
  set N := vsQNf X with hN
  set S := vsQSf X with hS
  set Tm := (I.d + 1) ^ 278 with hTm
  set Cφ := vsQCphi hcm N with hCφ
  have eN : N = 2000 * (X + 1) ^ 7 := rfl
  have eS : S = 10 ^ 5 * (N + 1) ^ 278 := rfl
  -- sizes
  have hpX : I.p ≤ X := I.p_le.trans hnX
  have hΓ : (vsQGam I).wt ≤ N := vsQ_wt_gam
  have hEw : (Val.nat (vsQExp I)).wt ≤ X ^ 2 + X + 3 := vsQ_wt_exp
  have hX1 : 1 ≤ (X + 1) ^ 7 := Nat.one_le_pow _ _ (by omega)
  have hX7 : X + 1 ≤ (X + 1) ^ 7 := Nat.le_self_pow (by norm_num) _
  have hX27 : (X + 1) ^ 2 ≤ (X + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hXN : X + 1 ≤ N := by omega
  have hEN : (Val.nat (vsQExp I)).wt ≤ N := by
    have : X ^ 2 + X + 3 ≤ 3 * (X + 1) ^ 2 := by nlinarith
    omega
  have hsz : VsQSz I.p I.d (vsQExp I) N := ⟨by omega, by omega, hEN, I.prime.pos⟩
  have hG : (encGroup I.gs).wt ≤ N := by
    have : (encGroup I.gs).wt < X := wt_le_wt_list (by simp [X, vsQTaskIn])
    omega
  have hN1 : 1 ≤ (N + 1) ^ 278 := Nat.one_le_pow _ _ (by omega)
  have hN4 : (N + 1) ^ 4 ≤ (N + 1) ^ 278 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hN2 : (N + 1) ^ 2 ≤ (N + 1) ^ 278 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hNS : N + 1 ≤ S := by
    have : N + 1 ≤ (N + 1) ^ 278 := Nat.le_self_pow (by norm_num) _
    omega
  have hTmS : Tm + 1 ≤ S := by
    have : (I.d + 1) ^ 278 ≤ (N + 1) ^ 278 := Nat.pow_le_pow_left (by omega) _
    omega
  have hDSz : VsQDSz I S Tm := ⟨by omega, by omega, by omega, by omega, hTmS⟩
  have hTm1 : 1 ≤ Tm := Nat.one_le_pow _ _ (by omega)
  have hn2S : I.n ^ 2 + 2 ≤ S := by
    have : I.n ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hN4S : 10 ^ 4 * (N + 1) ^ 4 ≤ S := by omega
  have hOSz : VsBOrbSz I N S I.p := ⟨hsz, by omega, hΓ, by omega, hn2S, hN4S, by omega⟩
  -- the layouts
  obtain ⟨LT, LD, LA, LL, LF, e1, e2, e3, p1, p2, p3, p4, p5, p6, p7, p8⟩ := L
  -- `φ`
  have hphi : ∀ g ∈ gens I.gs, FunDet P x.phi.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ :=
    vsQPhi_unif hcm LF.hphi LF.hj LF.hgl hsz hΓ (by omega) hG (by omega)
  -- the analysis
  have hana : ∀ (s : VsQSt I) (hs : VsQStOK s), FunAll P x.ana.ana (vsQStV I s)
      (fun w c => VsQAnaOut hs 278 Tm w ∧
        c ≤ 8 * (vsQLCCost Cφ S + vsBOrbCost hps hm I.n S Cφ N + (vsBFldCost hps hm I.n S Cφ + 10 ^ 25 * S ^ 32) +
          (S * S + 1) * vsQALCost (I := I) hps hm hmb hn hd Cφ S (CH Cφ I S) (CQ Cφ I S) +
          vsPCtxPCost (vsPN S) (10 ^ 9 * S ^ 8) + vsPAbCost Cφ (vsPN S) (10 ^ 8 * S ^ 6)) + 10 ^ 12 * S ^ 12) := by
    intro s hs
    rw [← p2] at hphi
    refine vsQAna_spec LA.hf LA.hctx LA.hflm LA.hit LA.hfl LA.hrws LA.hrep LA.habt LA.hfo LA.hno LA.hfi LA.hnc
      LA.hcomp LA.hloc LA.hwl LA.heq hphi hDSz hs (vsQLC_spec LA.hlcp hphi hDSz hs) ?_ ?_ ?_
    · intro hD1
      refine (vsBOrb_spec hps hm LA.horb LA.hojp LA.hojm hphi hOSz hs (vsB_orb_D1 hD1)).mono ?_
      rintro w c ⟨a, rfl, ha, hc⟩
      exact ⟨⟨a, rfl, ha⟩, hc⟩
    · intro hab hD2
      have hphi' := hphi
      rw [p2, ← p3] at hphi'
      exact vsQAb_spec LA.habb hDSz hTm1 hs hab hD2
        (vsBFld_spec hps hm LA.hfld hphi' hDSz hs hab (by omega))
    · intro hnab hD2
      have hq := HQ I Cφ S Tm (by rw [p2] at hphi; exact hphi) hDSz le_rfl s hs
      have hφ : ∀ i, i = x.phi.phi → ∀ g ∈ gens I.gs, FunDet P i (.list [vsQGam I, encPerm g])
          (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ := by
        rintro i rfl; rw [p2] at hphi; exact hphi
      have hD := vsQD_le hs
      have hm' : vsQAM hs [] ≤ S * S :=
        (vsQAM_le hs []).trans (Nat.mul_le_mul (by omega) (by omega))
      have := vsQAL_spec LL.hf LL.L2 LL.L3 LL.h4 LL.hst4 LL.L4
        (hφ _ p4) (hφ _ p5) (hφ _ p6) (hφ _ p7) (hφ _ p8) hDSz le_rfl hs hD2 hnab hq.1 hq.2 (S * S) []
        hm' (by simp [gens]) (by intro h _ y hy; simp [gens] at hy; simp [gens, hy]) (by simp)
        (by
          have : vsPBar hs (gens ([] : List (Perm (Fin I.n)))) = ⊥ := by
            simp only [vsPBar, gens, List.not_mem_nil, Set.setOf_false, Subgroup.closure_empty, Subgroup.subgroupOf]
            rw [eq_bot_iff]
            rintro _ ⟨y, hy, rfl⟩
            have : y = 1 := Subtype.ext hy
            subst this
            exact (Proved.vsQRho hs).map_one
          rw [this]; exact bot_le)
      rw [e3]
      exact this
  -- the driver
  have H : VsQDrvHyp P I x.drv.drv x.drv.ana x.drv.ai x.drv.cmp x.drv.paste 278 Tm S
      (8 * (vsQLCCost Cφ S + vsBOrbCost hps hm I.n S Cφ N + (vsBFldCost hps hm I.n S Cφ + 10 ^ 25 * S ^ 32) +
          (S * S + 1) * vsQALCost (I := I) hps hm hmb hn hd Cφ S (CH Cφ I S) (CQ Cφ I S) +
          vsPCtxPCost (vsPN S) (10 ^ 9 * S ^ 8) + vsPAbCost Cφ (vsPN S) (10 ^ 8 * S ^ 6)) + 10 ^ 12 * S ^ 12)
      (vsQAppCost Cφ N) (vsQPasteCost hm I.n S) (vsQCn hps hm hmb hn hd CH CQ Cφ I N S)
      (20 * vsQCn hps hm hmb hn hd CH CQ Cφ I N S) 558 := {
    funs := LD.hdrv
    hcmp := LD.hcmp
    hai := fun t ht y hy => vsQApp_spec LD.hai LD.hinv LD.hmm (by rw [p1]; exact hphi) hsz (by omega) hΓ ht hy
    hpaste := fun rs hl hks => vsQPaste_spec hm LD.hp LD.hfd LD.ht LD.hpinv LD.hmp LD.hmpE LD.hpc LD.happ
      LD.hmkg LD.hred LD.hjm rs (by omega) (by omega) hks
    hana := by rw [e2]; exact hana
    sz := hDSz
    hCn := le_rfl
    hc := le_rfl
    hK := by norm_num
    hK8 := by norm_num }
  refine (vsQTop_spec LT.hf LT.hrng LT.hfold LT.hst LT.hidp LT.hrep LT.htbm LT.hit LT.htr LT.hred LT.hjm LT.htl
    (K := 558) (by norm_num) (fun s hs => by rw [e1]; exact vsQDrv_spec H s hs)).mono ?_
  intro w c h
  exact h

end GI.Impl
