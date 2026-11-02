import Workspace.Impl.LinObjectShiftOffsetsSpec
import Workspace.Impl.LinObjectLiftSpec
import Workspace.Impl.LinObjectReindexPresentation
import Workspace.Impl.LinObjectFrameActions

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset

theorem linObjectCommonLift_exists {n : ℕ} {Q : Type*} [CommGroup Q]
    (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q) (hπ : Function.Surjective π)
    (Y : List (TmRiO n)) (Z : Multiset (CObj ℕ (Equiv.Perm (Fin n))))
    (hZ : Conf (gens as) (tmGlMs Y) Z)
    (hker : ∀ T ∈ pieces (gens as) (tmGlMs Y), π.ker ≤ (Aut (gens as) T).subgroupOf (gens as))
    (w : Fin (as.length * (tmRiPcsO (gens as) Y).length) → ℤ)
    (hw : linObjectOffsetsOut as π (tmRiPcsO (gens as) Y) Z (linVecVal w))
    (hz : (linObjectDiagonalModule (gens as) π (tmGlMs Y)).mkQ
      (linObjectConfigCoord (gens as) π (tmGlMs Y) Z) = 0) :
    ∃ a : Additive Q, ∀ i, linObjectLiftCoord as π (linObjectUnflatten _ _ w i) + a ∈
      linObjectLocalImages as π Y i := by
  obtain ⟨w',he,hcoord⟩ := linObjectOffsets_indexed as π hπ Y Z hZ hker hw
  have hew : w' = w := linVecVal_injective he.symm
  subst w'
  change linObjectProductMap (linObjectLocalImages as π Y) (linObjectLiftCoord as π)
    (linObjectUnflatten _ _ w) = linObjectIndexedConfigEquiv as π hπ Y hker ⟨Z,hZ⟩ at hcoord
  have hh : (linObjectDiagonalModule (gens as) π (tmGlMs Y)).mkQ
      (linObjectPieceReindex as π Y
        (linObjectProductMap (linObjectLocalImages as π Y) (linObjectLiftCoord as π)
          (linObjectUnflatten _ _ w))) = 0 := by
    rw [hcoord,linObjectPieceReindex_indexedConfig]
    exact hz
  rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero,linObjectPieceReindex_mem_diagonal] at hh
  have hh' : (LinearMap.range (linObjectDiagonal (linObjectLocalImages as π Y))).mkQ
      (linObjectProductMap (linObjectLocalImages as π Y) (linObjectLiftCoord as π)
        (linObjectUnflatten _ _ w)) = 0 := by
    rwa [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
  exact (linObjectCommonCorrection_coordinates (linObjectLocalImages as π Y) (linObjectLiftCoord as π)
    (linObjectUnflatten _ _ w)).mp hh'

theorem linObjectCommonLift_correct {n : ℕ} {Q : Type*} [CommGroup Q]
    (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q) (hπ : Function.Surjective π)
    (Y : List (TmRiO n)) (Z : Multiset (CObj ℕ (Equiv.Perm (Fin n))))
    (hZ : Conf (gens as) (tmGlMs Y) Z)
    (hker : ∀ T ∈ pieces (gens as) (tmGlMs Y), π.ker ≤ (Aut (gens as) T).subgroupOf (gens as))
    (w : Fin (as.length * (tmRiPcsO (gens as) Y).length) → ℤ)
    (hw : linObjectOffsetsOut as π (tmRiPcsO (gens as) Y) Z (linVecVal w))
    (a : Equiv.Perm (Fin n)) (ha : a ∈ gens as)
    (hrows : ∀ i, linObjectLiftCoord as π (linObjectUnflatten _ _ w i) + Additive.ofMul (π ⟨a,ha⟩) ∈
      linObjectLocalImages as π Y i) : Z ↼ a = tmGlMs Y := by
  obtain ⟨w',he,hcoord⟩ := linObjectOffsets_indexed as π hπ Y Z hZ hker hw
  have hew : w' = w := linVecVal_injective he.symm
  subst w'
  change linObjectProductMap (linObjectLocalImages as π Y) (linObjectLiftCoord as π)
    (linObjectUnflatten _ _ w) = linObjectIndexedConfigEquiv as π hπ Y hker ⟨Z,hZ⟩ at hcoord
  have hcancel : linObjectProductMap (linObjectLocalImages as π Y) (linObjectLiftCoord as π)
      (linObjectUnflatten _ _ w) + linObjectDiagonal (linObjectLocalImages as π Y) (Additive.ofMul (π ⟨a,ha⟩)) = 0 := by
    funext i
    change (linObjectLocalImages as π Y i).mkQ (linObjectLiftCoord as π (linObjectUnflatten _ _ w i)) +
      (linObjectLocalImages as π Y i).mkQ (Additive.ofMul (π ⟨a,ha⟩)) = 0
    rw [← map_add,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
    exact hrows i
  have hh : linObjectPieceReindex as π Y
      (linObjectProductMap (linObjectLocalImages as π Y) (linObjectLiftCoord as π) (linObjectUnflatten _ _ w)) +
      linObjectPieceReindex as π Y
        (linObjectDiagonal (linObjectLocalImages as π Y) (Additive.ofMul (π ⟨a,ha⟩))) = 0 := by
    calc
      _ = linObjectPieceReindex as π Y
          (linObjectProductMap (linObjectLocalImages as π Y) (linObjectLiftCoord as π) (linObjectUnflatten _ _ w) +
            linObjectDiagonal (linObjectLocalImages as π Y) (Additive.ofMul (π ⟨a,ha⟩))) :=
        ((linObjectPieceReindex as π Y).map_add _ _).symm
      _ = linObjectPieceReindex as π Y 0 := congrArg (linObjectPieceReindex as π Y) hcancel
      _ = 0 := (linObjectPieceReindex as π Y).map_zero
  have hDiag : linObjectPieceReindex as π Y
      (linObjectDiagonal (linObjectLocalImages as π Y) (Additive.ofMul (π ⟨a,ha⟩))) =
      linObjectDiagonal (fun T : ↥(pieces (gens as) (tmGlMs Y)) =>
        linObjectGroupImage (gens as) π (Aut (gens as) T.val)) (Additive.ofMul (π ⟨a,ha⟩)) :=
    linObjectPieceReindex_diagonal as π Y _
  rw [hDiag,hcoord,linObjectPieceReindex_indexedConfig] at hh
  apply dcond_witness hZ
  intro T hT
  have hTcoord := congrFun hh ⟨T,hT⟩
  change (linObjectGroupImage (gens as) π (Aut (gens as) T)).mkQ
      (Additive.ofMul (π (linIntoSubgroup (gens as) (coord (gens as) Z T)))) +
    (linObjectGroupImage (gens as) π (Aut (gens as) T)).mkQ (Additive.ofMul (π ⟨a,ha⟩)) = 0 at hTcoord
  rw [← map_add,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero] at hTcoord
  have hm := (linObject_groupImage_add_iff (gens as) π (Aut (gens as) T) (hker T hT)
    (linIntoSubgroup (gens as) (coord (gens as) Z T)) ⟨a,ha⟩).mp hTcoord
  have hv := linIntoSubgroup_val (gens as) _ (coord_spec hZ hT).1
  change (linIntoSubgroup (gens as) (coord (gens as) Z T)).val = coord (gens as) Z T at hv
  rwa [hv] at hm

end GI.Impl
