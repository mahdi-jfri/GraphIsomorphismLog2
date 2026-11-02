import Workspace.Impl.LinObjectGlueSpec

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset

/-- The concrete object-glue entry satisfies the terminal recursion's
original interface, with a uniform polynomial input-bit cost. -/
theorem linObjectGlue_iface (ho : GroupOrder) (hh : HermiteFullRank) (hn : SmithNonsingular)
    {P : Program} {b jsci jder jmem jo jm jh js jv : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership}
    {hc : ConstructiveMembership} {hv : VectorStabilizer}
    (h : linObjectGlueAt P b jsci jder jmem jo jm jh js jv hs hd hm hc hv)
    (hjmem : P.prims[jmem]? = some (membershipPrim hm))
    (hjo : P.prims[jo]? = some (groupOrderPrim ho)) (hjm : P.prims[jm]? = some (linMembershipPrim hc))
    (hjh : P.prims[jh]? = some (linHermitePrim hh)) (hjs : P.prims[js]? = some (linSmithPrim hn)) :
    ∃ K D : ℕ,Iface.TermGlueObjSpec P K D b := by
  obtain ⟨K,D,hKD⟩ := linObjectGlue_uniform hs hm ho hc hh hn hv
  refine ⟨K,D,?_⟩
  intro n σH σN σA X Y σB τ hsol hNA hAH hN hA hcA hfX hfY hAB hBH hτ hP1 hP2 hP3 hP4 hP5
  let I : linObjectGlueRaw n := ⟨σH,σN,σA,X,Y,σB,τ,hsol,hNA,hAH,hN,hA,hcA,hfX,hfY,hAB,hBH,hτ,hP1,hP2,hP3,hP4,hP5⟩
  exact (linObjectGlue_spec I ho hh hn h hjmem hjo hjm hjh hjs).mono fun out cost hout =>
    ⟨hout.1,hout.2.trans (hKD I.value.wt)⟩

/-- Install the 2843-function list at any base. Only cited primitive
lookups remain as hypotheses. -/
theorem linObjectGlue_iface_of (hs : SolvableCosetIntersection) (hd : DerivedSubgroup) (hm : Membership)
    (ho : GroupOrder) (hc : ConstructiveMembership) (hh : HermiteFullRank)
    (hn : SmithNonsingular) (hv : VectorStabilizer)
    {P : Program} {b jsci jder jmem jo jm jh js jv : ℕ}
    (h : P.HasAt b (gObjF b jsci jder jmem jo jm jh js jv))
    (hjsci : P.prims[jsci]? = some (solvableCosetIntersectionPrim hs))
    (hjder : P.prims[jder]? = some (derivedSubgroupPrim hd))
    (hjmem : P.prims[jmem]? = some (membershipPrim hm))
    (hjo : P.prims[jo]? = some (groupOrderPrim ho))
    (hjm : P.prims[jm]? = some (linMembershipPrim hc))
    (hjh : P.prims[jh]? = some (linHermitePrim hh))
    (hjs : P.prims[js]? = some (linSmithPrim hn))
    (hjv : P.prims[jv]? = some (vectorStabilizerPrim hv)) :
    ∃ K D : ℕ,Iface.TermGlueObjSpec P K D b :=
  linObjectGlue_iface ho hh hn (linObjectGlueAt_of h hjsci hjder hjmem hjm hjv) hjmem hjo hjm hjh hjs

end GI.Impl
