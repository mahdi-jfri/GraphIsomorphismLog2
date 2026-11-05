module

public import Workspace.Impl.TermRecLayout
public import Workspace.Impl.FinLayoutCos
public import Workspace.Impl.LinPrims

@[expose] public section

/-!
# T5, the A.20 recursion in the final program

The final program (`flcProg`) keeps the list `recF` at `flcRecIdx`. With
`recF = tmRiRecF flcRecIdx 14 8 1 gObjF` and the extra primitives `ext = linA20Extra … ++ ext'`,
the cited SolvableCosetIntersection sits at primitive `14`, DerivedSubgroup at `8` and
Membership at `1` (all by `rfl`). So `tmRi_recSpecAt` gives `TermRecSpec` at `flcRecIdx` from
the glue spec at `flcRecIdx + tmRiGlueOff` (`tmRi_flcRecSpec`).
-/

namespace GI.Impl

open GI.Lang GI.Cited

/-- **`TermRecSpec` at `flcRecIdx` in the final program.** -/
theorem tmRi_flcRecSpec (hs : SolvableCosetIntersection) (hder : DerivedSubgroup)
    (hm : Membership) (Kg Dg : ℕ) :
    ∃ K D : ℕ, ∀ {hst : PointwiseStab} {hpre : Preimage} {hfac : NormalizedFactor}
      {hmb : MinimalBlocks} {hO : GroupOrder} {hC : CameronRecognition}
      {hni : NormalizedIntersection} {hnc : NormalClosure}
      {hh : HermiteFullRank} {hn : SmithNonsingular} {hcm : ConstructiveMembership}
      {hv : VectorStabilizer} {ext' : List Prim} {gen gObjF labF jF agg : List Expr},
      gen.length ≤ asmSlot → FlcFits (tmRiRecF flcRecIdx 14 8 1 gObjF) labF jF →
      Iface.TermGlueObjSpec (flcProg hst hm hpre hfac hmb hO hC hder hni hnc
        (linA20Extra hs hh hn hcm hv ++ ext') gen (tmRiRecF flcRecIdx 14 8 1 gObjF) labF jF agg)
        Kg Dg (flcRecIdx + tmRiGlueOff) →
      Iface.TermRecSpec (flcProg hst hm hpre hfac hmb hO hC hder hni hnc
        (linA20Extra hs hh hn hcm hv ++ ext') gen (tmRiRecF flcRecIdx 14 8 1 gObjF) labF jF agg)
        K D flcRecIdx := by
  obtain ⟨K, D, h⟩ := tmRi_recSpecAt hs hder hm Kg Dg
  exact ⟨K, D, fun hg hF hgl => h (flc_hasAt hg hF).2.1 rfl rfl rfl hgl⟩

/-- The room `FlcFits` needs for the list of the recursion: the glue program may have up to
`flcLabOff - flcRecOff - tmRiGlueOff = 298000` functions. -/
theorem tmRi_recF_fits {b jsci jder jmem : ℕ} {gObjF : List Expr}
    (h : gObjF.length ≤ flcLabOff - flcRecOff - tmRiGlueOff) :
    (tmRiRecF b jsci jder jmem gObjF).length ≤ flcLabOff - flcRecOff := by
  rw [length_tmRiRecF]; unfold flcLabOff flcRecOff tmRiGlueOff at *; omega

end GI.Impl
