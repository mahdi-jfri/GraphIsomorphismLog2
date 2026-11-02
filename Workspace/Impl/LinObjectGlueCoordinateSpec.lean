import Workspace.Impl.LinObjectGlueAction

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset
open scoped IsMulCommutative

set_option maxHeartbeats 400000 in
theorem linObjectGlueFrame_coordinate_spec {P : Program} {b jsci jder jmem jm n : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership} {hc : ConstructiveMembership}
    (h : linObjectSourceCoordinateAt P b jsci jder jmem jm hs hd hm hc)
    (as ns : List (Equiv.Perm (Fin n))) [((gens ns).subgroupOf (gens as)).Normal]
    [IsMulCommutative ((gens as) ⧸ (gens ns).subgroupOf (gens as))]
    (Y X : List (TmRiO n)) (F : linObjectGlueFrame as ns Y)
    (hok : TmRecObjOK (Y.length+X.length) (Y++X))
    (hsol : IsSolvable (gens as)) (hNA : gens ns ≤ gens as)
    (H : Subgroup (Equiv.Perm (Fin n))) (hAH : gens as ≤ H)
    (hA : GI.Multicoset.Normalizes H (gens as)) (hN : GI.Multicoset.Normalizes H (gens ns))
    (hcomm : ∀ a ∈ gens as,∀ b ∈ gens as,a*b*a⁻¹*b⁻¹ ∈ gens ns)
    (hal : as.length ≤ n^2) (hfY : Fixes (gens ns) (tmGlMs Y)) (hfX : Fixes (gens ns) (tmGlMs X))
    (g : Equiv.Perm (Fin n)) (hg : g ∈ H) (hy : Conf (gens as) (tmGlMs Y) (tmGlMs X ↼ g)) :
    let ctx := Val.list [encGroup as,encGroup ns,.list ((tmRiPcsO (gens as) Y).map tmGlObjsVal),
      encIntMatrix F.V,linVecVal (fun i => F.D i i)]
    let input := Val.list [ctx,.list ((tmRiPcsO (gens as) X).map tmGlObjsVal),encPerm g]
    FunDet P b input (linFiniteIntVecVal (tmGLQMod F.D) (F.point (tmGlMs X ↼ g)))
      (linObjectSourceCoordinateCost hs hm hc input.wt) := by
  let π := linObjectCanonicalProjection as ns
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker := linObjectCanonical_ker_local as ns Y hfY
  have hr := linObjectSourceCoordinate_spec h as ns π hπ Y X hok hsol hNA H hAH hA hN hcomm hal hfY hfX hker
    g hg hy F.q F.V F.D F.positive F.E F.frame_indexed
  rw [F.point_indexed hπ hker] at hr
  exact hr

end GI.Impl
