module

public import Workspace.Impl.FinLayoutAgg
public import Workspace.Impl.LinPrims

@[expose] public section

/-!
# The primitive slot of the aggregation round

The items phase calls the cited joint refinement `KaryRefinement P₀.κ` at a primitive index
`jk` (`stRef_spec`, `it_col_spec`, `it_str_spec`). The primitive table reserves the
indices from `19` for the primitives of the round, after the A.20 block `linA20Extra` at
`14`–`18`. `aggExtra hk` is that block. It has one entry, `karyRefinementPrim hk`, so in the
final program with `ext = linA20Extra … ++ (aggExtra hk ++ ext'')` the refinement is primitive
`19` (`fcr_prim_kary`, by `rfl`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang
open GI.Cited (PointwiseStab Preimage NormalizedFactor Membership MinimalBlocks GroupOrder
  CameronRecognition DerivedSubgroup NormalizedIntersection
  NormalClosure SolvableCosetIntersection HermiteFullRank
  SmithNonsingular ConstructiveMembership VectorStabilizer KaryRefinement)

/-- **The primitives of the aggregation round**: the joint `κ`-ary refinement. In the final
program it sits at index `19`. -/
noncomputable def aggExtra (hk : KaryRefinement P₀.κ) : List Prim := [karyRefinementPrim hk]

theorem aggExtra_length (hk : KaryRefinement P₀.κ) : (aggExtra hk).length = 1 := rfl

/-- **KaryRefinement is primitive `19` of the final program** when the extra primitives are
`linA20Extra … ++ (aggExtra hk ++ ext'')`. -/
theorem fcr_prim_kary {hst : PointwiseStab} {hm : Membership} {hpre : Preimage}
    {hfac : NormalizedFactor} {hmb : MinimalBlocks} {hO : GroupOrder} {hC : CameronRecognition}
    {hder : DerivedSubgroup}
    {hni : NormalizedIntersection} {hnc : NormalClosure} {hs : SolvableCosetIntersection}
    {hh : HermiteFullRank} {hn : SmithNonsingular} {hcmb : ConstructiveMembership}
    {hv : VectorStabilizer} {hk : KaryRefinement P₀.κ} {ext'' : List Prim}
    {recF labF jF : List Expr} {crE cmE itE : Expr} {crF cmF itF : List Expr} :
    (fagProg hst hm hpre hfac hmb hO hC hder hni hnc
      (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ ext'')) recF labF jF crE cmE itE crF cmF
      itF).prims[19]? = some (karyRefinementPrim hk) := rfl

end GI.Impl
