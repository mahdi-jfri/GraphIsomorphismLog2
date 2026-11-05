module

public import Workspace.Impl.VsHHardHyp
public import Workspace.Impl.VsQPoly

@[expose] public section

namespace GI.Impl

open GI.Lang GI.Cited

/-- A cost whose dependence on the matrix program is at most linear. -/
def VsHLinearCost (f : ℕ → ℕ) : Prop := ∀ c, f c ≤ (c + 1) * f 1

theorem vsHLinearCost_const (n : ℕ) : VsHLinearCost (fun _ => n) := by
  intro c
  exact Nat.le_mul_of_pos_left n (by omega)

theorem vsHLinearCost_id : VsHLinearCost (fun c : ℕ => c) := by
  intro c
  simp

theorem vsHLinearCost_add {f g : ℕ → ℕ} (hf : VsHLinearCost f) (hg : VsHLinearCost g) :
    VsHLinearCost (fun c => f c + g c) := by
  intro c
  simpa [Nat.mul_add] using Nat.add_le_add (hf c) (hg c)

theorem vsHLinearCost_mul_left (n : ℕ) {f : ℕ → ℕ} (hf : VsHLinearCost f) :
    VsHLinearCost (fun c => n * f c) := by
  intro c
  simpa [Nat.mul_left_comm] using Nat.mul_le_mul_left n (hf c)

/-- The uniform hard-case cost is linear in the cost of the matrix program. -/
theorem vsHHardCH_linear (hps : PointwiseStab) (hm : GI.Cited.Membership)
    (I : VecStabInst) (S Cφ : ℕ) :
    vsHHardCH hps hm Cφ I S ≤ (Cφ + 1) * vsHHardCH hps hm 1 I S := by
  apply (show VsHLinearCost (fun c => vsHHardCH hps hm c I S) from ?_) Cφ
  simp only [vsHHardCH, vsHHardCost, vsHFrontCost, vsPCtxPCost, vsHC2Cost, vsHBasCost,
    vsHBStepCost, vsHMemCost, vsPEnumCost, vsPEStepCost, vsPEMidCost, vsHMemItCost, vsPInLPCost,
    vsPLocCost, vsHIsoCost, vsHIStepCost, vsHGoodCost, vsPNoCost, vsPNcCost, vsHQ8Cost, vsHY0Cost,
    vsHPcCost, vsQSotCost, vsQPsB, reduceCost, memCost, vsHConjTCost, vsHConjCost, vsHPsCost,
    vsHWCost, vsQTS, vsPN]
  repeat' first
    | with_reducible exact vsHLinearCost_const _
    | with_reducible exact vsHLinearCost_id
    | with_reducible apply vsHLinearCost_add
    | with_reducible apply vsHLinearCost_mul_left

/-- For fixed primitive witnesses, the remaining cost is polynomial in the size. -/
theorem vsHHardCH_poly (hps : PointwiseStab) (hm : GI.Cited.Membership) :
    VsPoly (fun I : VecStabInst => I.n) (fun I S => vsHHardCH hps hm 1 I S) := by
  simp only [vsHHardCH, vsHHardCost, vsHFrontCost, vsPCtxPCost, vsHC2Cost, vsHBasCost,
    vsHBStepCost, vsHMemCost, vsPEnumCost, vsPEStepCost, vsPEMidCost, vsHMemItCost, vsPInLPCost,
    vsPLocCost, vsHIsoCost, vsHIStepCost, vsHGoodCost, vsPNoCost, vsPNcCost, vsHQ8Cost, vsHY0Cost,
    vsHPcCost, vsQSotCost, vsQPsB, reduceCost, memCost, vsHConjTCost, vsHConjCost, vsHPsCost,
    vsHWCost, vsQTS, vsPN]
  vs_poly

/-- The polynomial constants depend on the chosen primitive witnesses, and not on `Cφ`. -/
theorem vsHHardCH_bound (hps : PointwiseStab) (hm : GI.Cited.Membership) :
    ∃ K D : ℕ, ∀ (I : VecStabInst) (S Cφ : ℕ), I.n ≤ S →
      vsHHardCH hps hm Cφ I S ≤ K * (Cφ + 1) * (S + 1) ^ D := by
  obtain ⟨K, D, h⟩ := vsHHardCH_poly hps hm
  refine ⟨K, D, fun I S Cφ hn => ?_⟩
  calc
    vsHHardCH hps hm Cφ I S ≤ (Cφ + 1) * vsHHardCH hps hm 1 I S :=
      vsHHardCH_linear hps hm I S Cφ
    _ ≤ (Cφ + 1) * (K * (S + 1) ^ D) := Nat.mul_le_mul_left _ (h I S hn)
    _ = K * (Cφ + 1) * (S + 1) ^ D := by ring

end GI.Impl
