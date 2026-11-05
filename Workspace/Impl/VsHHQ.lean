module

public import Workspace.Impl.VsHCSpec
public import Workspace.Impl.VsHHardPoly

@[expose] public section

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved

/-- The continuation cost is linear in the cost of the matrix program. -/
theorem vsHCQ_linear (hps : PointwiseStab) (hm : GI.Cited.Membership)
    (hn : NormalClosure) (hd : DerivedSubgroup) (I : VecStabInst) (S Cφ : ℕ) :
    vsHCQ hps hm hn hd Cφ I S ≤ (Cφ + 1) * vsHCQ hps hm hn hd 1 I S := by
  apply (show VsHLinearCost (fun c => vsHCQ hps hm hn hd c I S) from ?_) Cφ
  simp only [vsHCQ, vsHHardCH, vsHHardCost, vsHFrontCost, vsPCtxPCost, vsHC2Cost, vsHBasCost,
    vsHBStepCost, vsHMemCost, vsPEnumCost, vsPEStepCost, vsPEMidCost, vsHMemItCost, vsPInLPCost,
    vsPLocCost, vsHIsoCost, vsHIStepCost, vsHGoodCost, vsPNoCost, vsPNcCost, vsHQ8Cost, vsHY0Cost,
    vsHPcCost, vsQSotCost, vsQPsB, reduceCost, memCost, vsHConjTCost, vsHConjCost, vsHPsCost,
    vsHWCost, vsQTS, vsPN, vsPStep4Cost, vsPW6, vsPDerCost, vsPDStepCost, vsPDerB, vsPBadCost,
    vsPAbCost, vsPGrowCost, vsPNcB, vsPS2Cost, vsPOrdCost, vsPWalkCost, vsPWStepCost, vsPS3Cost,
    vsPPairCost, vsPCommCost, vsPZpCost, vsPZItemCost, vsPRadCost, vsPKeyCost, vsPKeyItemCost,
    vsPRadPredCost, vsPWordCost, vsPS4Cost, vsPDescCost, vsPDsStepCost, vsPDimCost, vsPOrbCost,
    vsPOPassCost, vsPOInnerCost, vsPOInsCost, vsPBasisCost, vsPDPredCost, vsPFinCost, vsHCAbCost,
    vsHCProdCost, vsHCHeadCost]
  repeat' first
    | with_reducible exact vsHLinearCost_const _
    | with_reducible exact vsHLinearCost_id
    | with_reducible apply vsHLinearCost_add
    | with_reducible apply vsHLinearCost_mul_left

/-- For fixed primitive witnesses, the continuation cost is polynomial in the size. -/
theorem vsHCQ_poly (hps : PointwiseStab) (hm : GI.Cited.Membership)
    (hn : NormalClosure) (hd : DerivedSubgroup) :
    VsPoly (fun I : VecStabInst => I.n) (fun I S => vsHCQ hps hm hn hd 1 I S) := by
  simp only [vsHCQ, vsHHardCH, vsHHardCost, vsHFrontCost, vsPCtxPCost, vsHC2Cost, vsHBasCost,
    vsHBStepCost, vsHMemCost, vsPEnumCost, vsPEStepCost, vsPEMidCost, vsHMemItCost, vsPInLPCost,
    vsPLocCost, vsHIsoCost, vsHIStepCost, vsHGoodCost, vsPNoCost, vsPNcCost, vsHQ8Cost, vsHY0Cost,
    vsHPcCost, vsQSotCost, vsQPsB, reduceCost, memCost, vsHConjTCost, vsHConjCost, vsHPsCost,
    vsHWCost, vsQTS, vsPN, vsPStep4Cost, vsPW6, vsPDerCost, vsPDStepCost, vsPDerB, vsPBadCost,
    vsPAbCost, vsPGrowCost, vsPNcB, vsPS2Cost, vsPOrdCost, vsPWalkCost, vsPWStepCost, vsPS3Cost,
    vsPPairCost, vsPCommCost, vsPZpCost, vsPZItemCost, vsPRadCost, vsPKeyCost, vsPKeyItemCost,
    vsPRadPredCost, vsPWordCost, vsPS4Cost, vsPDescCost, vsPDsStepCost, vsPDimCost, vsPOrbCost,
    vsPOPassCost, vsPOInnerCost, vsPOInsCost, vsPBasisCost, vsPDPredCost, vsPFinCost, vsHCAbCost,
    vsHCProdCost, vsHCHeadCost]
  vs_poly

/-- The constants depend only on the fixed cited primitives. -/
theorem vsHCQ_bound (hps : PointwiseStab) (hm : GI.Cited.Membership)
    (hn : NormalClosure) (hd : DerivedSubgroup) :
    ∃ K D : ℕ, ∀ (I : VecStabInst) (S Cφ : ℕ), I.n ≤ S →
      vsHCQ hps hm hn hd Cφ I S ≤ K * (Cφ + 1) * (S + 1) ^ D := by
  obtain ⟨K, D, h⟩ := vsHCQ_poly hps hm hn hd
  refine ⟨K, D, fun I S Cφ hnS => ?_⟩
  calc
    vsHCQ hps hm hn hd Cφ I S ≤ (Cφ + 1) * vsHCQ hps hm hn hd 1 I S :=
      vsHCQ_linear hps hm hn hd I S Cφ
    _ ≤ (Cφ + 1) * (K * (S + 1) ^ D) := Nat.mul_le_mul_left _ (h I S hnS)
    _ = K * (Cφ + 1) * (S + 1) ^ D := by ring

/-- The exact hypothesis required by `vsQAll_spec`, for the two assembled programs. -/
theorem vsH_HQ {P : Program} {x : VsHContX} {phi : ℕ}
    {hps : PointwiseStab} {hm : GI.Cited.Membership} {hn : NormalClosure} {hd : DerivedSubgroup}
    (L : VsHContLay P x phi hps hm hn hd) :
    ∀ (I : VecStabInst) [Fact I.p.Prime] (Cφ S Tm : ℕ),
      (∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
        (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ) →
      VsQDSz I S Tm → (I.d + 1) ^ 278 ≤ Tm → ∀ (s : VsQSt I) (hs : VsQStOK s),
      VsQHardHyp P x.h.hard (vsHHardCH hps hm Cφ I S) Tm hs ∧
      VsQ8CHyp P x.q8c (vsHCQ hps hm hn hd Cφ I S) Tm hs := by
  intro I _ Cφ S Tm hphi hS hTm s hs
  exact ⟨vsHHard_hardHyp L.H hphi hS hTm hs, vsHC_spec L hphi hS hTm hs⟩

/-- Polynomial envelopes ready for the spine's `vsQTot_poly` theorem. -/
theorem vsH_HQ_poly {P : Program} {x : VsHContX} {phi : ℕ}
    {hps : PointwiseStab} {hm : GI.Cited.Membership} {hn : NormalClosure} {hd : DerivedSubgroup}
    (L : VsHContLay P x phi hps hm hn hd) :
    ∃ KH DH KQ DQ : ℕ,
    ∀ (I : VecStabInst) [Fact I.p.Prime] (Cφ S Tm : ℕ),
      (∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
        (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ) →
      VsQDSz I S Tm → (I.d + 1) ^ 278 ≤ Tm → ∀ (s : VsQSt I) (hs : VsQStOK s),
      VsQHardHyp P x.h.hard (KH * (Cφ + 1) * (S + 1) ^ DH) Tm hs ∧
      VsQ8CHyp P x.q8c (KQ * (Cφ + 1) * (S + 1) ^ DQ) Tm hs := by
  obtain ⟨KH, DH, hH⟩ := vsHHardCH_bound hps hm
  obtain ⟨KQ, DQ, hQ⟩ := vsHCQ_bound hps hm hn hd
  refine ⟨KH, DH, KQ, DQ, ?_⟩
  intro I _ Cφ S Tm hphi hS hTm s hs
  have hnS : I.n ≤ S := by have := hS.n; omega
  obtain ⟨hHard, hCont⟩ := vsH_HQ L I Cφ S Tm hphi hS hTm s hs
  constructor
  · intro as Lb ccs tcs ys r h hnab
    exact (hHard as Lb ccs tcs ys r h hnab).mono fun w c hw =>
      ⟨hw.1, hw.2.trans (hH I S Cφ hnS)⟩
  · intro as Lb ccs tcs ys r Lo ks h hnab hLo hks hksl hLol h0
    exact (hCont as Lb ccs tcs ys r Lo ks h hnab hLo hks hksl hLol h0).mono fun w c hw =>
      ⟨hw.1, hw.2.trans (hQ I S Cφ hnS)⟩

end GI.Impl
