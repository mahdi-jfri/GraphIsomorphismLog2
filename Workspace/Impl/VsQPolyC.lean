import Workspace.Impl.VsQFinal

/-!
# The costs are polynomial

Each cost function of the program, with polynomial arguments, is a polynomial (`VsPoly`). The
total cost `vsQTot` is then at most `K (X + 1)^D` in the input weight `X` (`vsQTot_poly`), when
the costs of the hard case and of the `Q₈` continuation are at most `K (Cφ + 1) (S + 1)^D`.
-/

namespace GI.Impl

open GI.Lang GI.Cited

set_option maxRecDepth 100000

section
variable {α : Type} {sz : α → ℕ} {a b c d : α → ℕ → ℕ}
  (ha : VsPoly sz a) (hb : VsPoly sz b) (hc : VsPoly sz c) (hd : VsPoly sz d)
include ha

theorem vsPoly_linTail : VsPoly sz fun x S => linTailCost (a x S) := by
  simp only [linTailCost]; vs_poly

theorem vsPoly_vsPN : VsPoly sz fun x S => vsPN (a x S) := by
  simp only [vsPN]; vs_poly

include hb

theorem vsPoly_reduce (hm : Membership) : VsPoly sz fun x S => reduceCost hm (a x S) (b x S) := by
  simp only [reduceCost, memCost]; vs_poly

theorem vsPoly_ctxP : VsPoly sz fun x S => vsPCtxPCost (a x S) (b x S) := by
  simp only [vsPCtxPCost]; vs_poly

theorem vsPoly_app : VsPoly sz fun x S => vsQAppCost (a x S) (b x S) := by
  simp only [vsQAppCost]; vs_poly

theorem vsPoly_lc : VsPoly sz fun x S => vsQLCCost (a x S) (b x S) := by
  simp only [vsQLCCost]; vs_poly

theorem vsPoly_paste (hm : Membership) : VsPoly sz fun x S => vsQPasteCost hm (a x S) (b x S) := by
  simp only [vsQPasteCost, reduceCost, memCost]; vs_poly

include hc

theorem vsPoly_ab : VsPoly sz fun x S => vsPAbCost (a x S) (b x S) (c x S) := by
  simp only [vsPAbCost, vsPNoCost, vsPNcCost, vsPLocCost]; vs_poly

theorem vsPoly_fld (hps : PointwiseStab) (hm : Membership) :
    VsPoly sz fun x S => vsBFldCost hps hm (a x S) (b x S) (c x S) := by
  simp only [vsBFldCost, vsBChCost, vsBMCost, vsB0TCost, vsBFldW, vsB0Cost, vsBDaCost, vsBDsCost, vsBS2, vsBWd,
    vsQSotCost, vsQPsB, reduceCost, memCost]; vs_poly

include hd

theorem vsPoly_orb (hps : PointwiseStab) (hm : Membership) :
    VsPoly sz fun x S => vsBOrbCost hps hm (a x S) (b x S) (c x S) (d x S) := by
  simp only [vsBOrbCost, vsQSotCost, vsQPsB, reduceCost, memCost]; vs_poly

end

theorem vsPoly_AL (hps : PointwiseStab) (hm : Membership) (hmb : MinimalBlocks) (hn : NormalClosure)
    (hd : DerivedSubgroup) {a b c d : VecStabInst → ℕ → ℕ} (ha : VsPoly VecStabInst.n a)
    (hb : VsPoly VecStabInst.n b) (hc : VsPoly VecStabInst.n c) (hd' : VsPoly VecStabInst.n d) :
    VsPoly VecStabInst.n fun I S => vsQALCost (I := I) hps hm hmb hn hd (a I S) (b I S) (c I S) (d I S) := by
  simp only [vsQALCost, vsQA2ACost, vsQA3Cost, vsPStep4Cost, vsQA2TCost, vsQA2WCost, vsQABmCost, vsQNB, vsQATblCost, vsQABlksCost, vsQTS, vsHQ8Cost, vsQSs, vsPN, vsPCtxPCost, vsPAbCost, vsPNoCost, vsPW6, vsPDerCost, vsPGrowCost, vsPS2Cost, vsQSotCost, vsQPsB, reduceCost, memCost, vsHConjTCost, vsHConjCost, vsHY0Cost, vsPDStepCost, vsPInLPCost, vsPLocCost, vsPNcB, vsPNcCost, vsPOrdCost, vsPS3Cost, vsHPcCost, vsPBadCost, vsPCommCost, vsPDerB, vsPPairCost, vsPRadCost, vsPS4Cost, vsPWalkCost, vsPZpCost, vsPDescCost, vsPFinCost, vsPKeyCost, vsPRadPredCost, vsPWStepCost, vsPWordCost, vsPZItemCost, vsPDimCost, vsPDsStepCost, vsPKeyItemCost, vsPBasisCost, vsPDPredCost, vsPEnumCost, vsPOrbCost, vsPEStepCost, vsPOPassCost, vsPEMidCost, vsPOInnerCost, vsPOInsCost]
  vs_poly

theorem vsPoly_Cphi {α : Type} {sz : α → ℕ} (hcm : ConstructiveMembership) :
    VsPoly sz fun _ X => vsQCphi hcm (vsQNf X) := by
  simp only [vsQCphi, vsQPhiCost, vsQMI, vsQLW, vsQNf, linGroupSlpCost, linGroupSlpLoopCost,
    linGroupSlpLoopStepCost, linGroupSlpStepCost, linGroupSlpArg, linVectorAccWt, vsQW]
  vs_poly

theorem vsPoly_Nf {α : Type} {sz : α → ℕ} : VsPoly sz fun _ X => vsQNf X := by
  simp only [vsQNf]; vs_poly

theorem vsPoly_Sf {α : Type} {sz : α → ℕ} : VsPoly sz fun _ X => vsQSf X := by
  simp only [vsQSf, vsQNf]; vs_poly

/-- **The total cost is polynomial in the input weight.** -/
theorem vsQTot_poly (hps : PointwiseStab) (hm : Membership) (hmb : MinimalBlocks) (hn : NormalClosure)
    (hd : DerivedSubgroup) (hcm : ConstructiveMembership) (KH DH KQ DQ : ℕ) :
    ∃ K D, ∀ (I : VecStabInst) (X : ℕ), I.n ≤ X →
      vsQTot hps hm hmb hn hd hcm (fun Cφ _ S => KH * (Cφ + 1) * (S + 1) ^ DH)
        (fun Cφ _ S => KQ * (Cφ + 1) * (S + 1) ^ DQ) I X ≤ K * (X + 1) ^ D := by
  have hC : VsPoly VecStabInst.n fun _ X => vsQCphi hcm (vsQNf X) := vsPoly_Cphi hcm
  have hN : VsPoly VecStabInst.n fun _ X => vsQNf X := vsPoly_Nf
  have hS : VsPoly VecStabInst.n fun _ X => vsQSf X := vsPoly_Sf
  have h : VsPoly VecStabInst.n fun I X => vsQTot hps hm hmb hn hd hcm
      (fun Cφ _ S => KH * (Cφ + 1) * (S + 1) ^ DH) (fun Cφ _ S => KQ * (Cφ + 1) * (S + 1) ^ DQ) I X := by
    simp only [vsQTot, vsQTopCost, vsQCn]
    repeat' (first
      | with_reducible apply vsPoly_linTail | with_reducible apply vsPoly_vsPN
      | with_reducible apply vsPoly_reduce | with_reducible apply vsPoly_ctxP
      | with_reducible apply vsPoly_app | with_reducible apply vsPoly_lc
      | with_reducible apply vsPoly_paste | with_reducible apply vsPoly_ab
      | with_reducible apply vsPoly_fld | with_reducible apply vsPoly_orb
      | with_reducible apply vsPoly_AL
      | with_reducible exact vsPoly_const _ | with_reducible apply vsPoly_add | with_reducible apply vsPoly_mul
      | with_reducible apply vsPoly_pow | with_reducible apply vsPoly_sub
      | with_reducible exact vsPoly_S | with_reducible exact vsPoly_n | with_reducible assumption)
  exact h

end GI.Impl
