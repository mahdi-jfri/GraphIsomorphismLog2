module

public import Workspace.Impl.LinObjectItemCompose
public import Workspace.Impl.LinPolyEnvelope

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

noncomputable def linObjectAffineRecord {G : Type*} [Group G] {d : ℕ} (m : Fin d → ℕ)
    (ρ : G →* (linFiniteVec m ≃+ linFiniteVec m)) (c : G → linFiniteVec m) (g : G) : Val :=
  .list [encIntMatrix (tmGLMat m (ρ g).toAddMonoidHom),linFiniteIntVecVal m (c g),
    encIntMatrix (tmGLMat m (ρ g⁻¹).toAddMonoidHom),linFiniteIntVecVal m (c g⁻¹)]

noncomputable def linObjectItemInvBudget (W : ℕ) : ℕ := invK * (W + 1) ^ 4
noncomputable def linObjectItemMatrixArg (W : ℕ) : ℕ :=
  100 * (W + linObjectItemInvBudget W + 1) ^ 2
noncomputable def linObjectItemMatrixBudget (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (hh : HermiteFullRank) (W : ℕ) : ℕ :=
  linPolyEnvelope (linObjectMatrixActualCost_poly hs hm hc hh) (linObjectItemMatrixArg W)
noncomputable def linObjectItemSource (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (hh : HermiteFullRank) (W : ℕ) : ℕ :=
  100 * (W + linObjectItemInvBudget W + linObjectItemMatrixBudget hs hm hc hh W + 1) ^ 2
noncomputable def linObjectItemActualCost (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (hh : HermiteFullRank) (W : ℕ) : ℕ :=
  100000000 * (linObjectItemSource hs hm hc hh W + 2) ^ 2

theorem linObjectItemActualCost_poly (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (hh : HermiteFullRank) :
    PBU (fun _ W _ => linObjectItemActualCost hs hm hc hh W) := by
  unfold linObjectItemActualCost linObjectItemSource linObjectItemMatrixBudget linObjectItemMatrixArg
    linObjectItemInvBudget linPolyEnvelope
  norm_poly

end GI.Impl
