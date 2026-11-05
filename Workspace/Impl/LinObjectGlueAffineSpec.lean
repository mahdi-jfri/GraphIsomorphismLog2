module

public import Workspace.Impl.LinObjectGlueAction

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset
open scoped IsMulCommutative

set_option maxHeartbeats 400000 in
theorem linObjectGlueFrame_affine_spec (hh : HermiteFullRank)
    {P : Program} {b jsci jder jmem jm jh jv n : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership}
    {hc : ConstructiveMembership} {hv : VectorStabilizer}
    (h : linObjectAffineCallerAt P b jsci jder jmem jm jh jv hs hd hm hc hv)
    (hjh : P.prims[jh]? = some (linHermitePrim hh))
    (as ns : List (Equiv.Perm (Fin n))) [((gens ns).subgroupOf (gens as)).Normal]
    [IsMulCommutative ((gens as) ⧸ (gens ns).subgroupOf (gens as))]
    (Y : List (TmRiO n)) (F : linObjectGlueFrame as ns Y)
    (hok : TmRecObjOK Y.length Y) (hsol : TmRiListNorm (gens as) Y) (hNA : gens ns ≤ gens as)
    (gs : List (Equiv.Perm (Fin n))) (hAH : gens as ≤ gens gs)
    (hA : GI.Multicoset.Normalizes (gens gs) (gens as)) (hN : GI.Multicoset.Normalizes (gens gs) (gens ns))
    (hcomm : ∀ a ∈ gens as,∀ b ∈ gens as,a*b*a⁻¹*b⁻¹ ∈ gens ns)
    (hal : as.length ≤ n^2) (hf : Fixes (gens ns) (tmGlMs Y))
    (hy : ∀ g ∈ gens gs,Conf (gens as) (tmGlMs Y) (tmGlMs Y ↼ g))
    (hsolB : IsSolvable (F.rep (gens gs) hA hy (QuotientGroup.mk'_surjective _) (linObjectCanonical_ker_local as ns Y hf)).range)
    (v w : tmGLVec (tmGLQMod F.D)) :
    let π := linObjectCanonicalProjection as ns
    let hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
    let hker := linObjectCanonical_ker_local as ns Y hf
    let ρ := F.rep (gens gs) hA hy hπ hker
    let c := F.cocycle (gens gs) hA hy hπ hker
    let ctx := Val.list [encGroup as,encGroup ns,.list ((tmRiPcsO (gens as) Y).map tmGlObjsVal),
      encIntMatrix F.V,linVecVal (fun i => F.D i i)]
    let input := Val.list [ctx,encGroup gs,linFiniteIntVecVal (tmGLQMod F.D) v,linFiniteIntVecVal (tmGLQMod F.D) w]
    FunAll P b input (fun out cost => CosetC n out (tmGLAffTrans gs ρ c v w) ∧
      cost ≤ linObjectCallerCost hs hm hc hh hv input.wt) := by
  let π := linObjectCanonicalProjection as ns
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker := linObjectCanonical_ker_local as ns Y hf
  apply linObjectAffineCaller_object_spec hh h hjh as ns π hπ Y hok hsol hNA gs hAH hA hN hcomm hal hf hker hy
    F.q F.V F.D F.invertible F.positive F.E F.frame_indexed
    (F.rep (gens gs) hA hy hπ hker) (F.cocycle (gens gs) hA hy hπ hker)
  · intro k Z hZ
    rw [F.point_indexed hπ hker Z hZ,F.point_indexed hπ hker]
    exact F.rep_point (gens gs) hA hy hπ hker k Z hZ
  · exact hsolB
  · intro i p hp hd
    exact (linObjectCanonicalFrame_quotient_prime as ns Y (tmGLQMod F.D) F.E i p hp hd).trans (le_max_left _ _)
  · exact F.cocycle_law (gens gs) hA hy hπ hker

end GI.Impl
