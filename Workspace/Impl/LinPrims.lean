import Workspace.Impl.LinMembership
import Workspace.Impl.LinNormal
import Workspace.Lang.Prims.Other
import Workspace.Lang.Prims.PermGroups

/-! The fixed A.20 primitive block. Final assembly places it at index 14;
the specifications continue to accept an arbitrary base. -/
namespace GI.Impl
open GI.Cited GI.Lang

noncomputable def linA20Extra (hs : SolvableCosetIntersection) (hh : HermiteFullRank)
    (hn : SmithNonsingular) (hm : ConstructiveMembership) (hv : VectorStabilizer) : List Prim :=
  [solvableCosetIntersectionPrim hs, linHermitePrim hh, linSmithPrim hn,
    linMembershipPrim hm, vectorStabilizerPrim hv]

theorem linA20Extra_length (hs : SolvableCosetIntersection) (hh : HermiteFullRank)
    (hn : SmithNonsingular) (hm : ConstructiveMembership) (hv : VectorStabilizer) :
    (linA20Extra hs hh hn hm hv).length = 5 := rfl

structure linA20PrimsAt (P : Program) (b : ℕ) (hs : SolvableCosetIntersection)
    (hh : HermiteFullRank) (hn : SmithNonsingular) (hm : ConstructiveMembership)
    (hv : VectorStabilizer) : Prop where
  sci : P.prims[b]? = some (solvableCosetIntersectionPrim hs)
  hermite : P.prims[b + 1]? = some (linHermitePrim hh)
  smith : P.prims[b + 2]? = some (linSmithPrim hn)
  member : P.prims[b + 3]? = some (linMembershipPrim hm)
  vector : P.prims[b + 4]? = some (vectorStabilizerPrim hv)

theorem linA20PrimsAt_of {P : Program} {b : ℕ} {hs : SolvableCosetIntersection}
    {hh : HermiteFullRank} {hn : SmithNonsingular} {hm : ConstructiveMembership}
    {hv : VectorStabilizer} (h : P.PrimsAt b (linA20Extra hs hh hn hm hv)) :
    linA20PrimsAt P b hs hh hn hm hv where
  sci := by simpa [linA20Extra] using h 0 (by simp [linA20Extra])
  hermite := by simpa [linA20Extra] using h 1 (by simp [linA20Extra])
  smith := by simpa [linA20Extra] using h 2 (by simp [linA20Extra])
  member := by simpa [linA20Extra] using h 3 (by simp [linA20Extra])
  vector := by simpa [linA20Extra] using h 4 (by simp [linA20Extra])

end GI.Impl
