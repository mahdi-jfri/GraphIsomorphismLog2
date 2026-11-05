module

public import Workspace.Impl.LinObjectReindexDiagonal
public import Workspace.Impl.LinObjectBlockPresentation

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GI.Impl
open GI.Cited GI.Multicoset

variable {n : ℕ} {Q : Type*} [CommGroup Q]

abbrev linObjectOriginalProduct (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q) (Y : List (TmRiO n)) :=
  ∀ T : ↥(pieces (gens as) (tmGlMs Y)), Additive Q ⧸ linObjectGroupImage (gens as) π (Aut (gens as) T.val)

abbrev linObjectOriginalQuotient (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q) (Y : List (TmRiO n)) :=
  linObjectOriginalProduct as π Y ⧸ linObjectDiagonalModule (gens as) π (tmGlMs Y)

noncomputable def linObjectLocalImages (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (Y : List (TmRiO n)) (i : Fin (tmRiPcsO (gens as) Y).length) : Submodule ℤ (Additive Q) :=
  linObjectGroupImage (gens as) π (Aut (gens as) (tmGlMs ((tmRiPcsO (gens as) Y).get i)))

noncomputable def linObjectOriginalMap (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (Y : List (TmRiO n)) :
    (Fin (as.length * (tmRiPcsO (gens as) Y).length) → ℤ) →ₗ[ℤ] linObjectOriginalProduct as π Y :=
  (linObjectPieceReindex as π Y).toLinearMap.comp
    ((linObjectProductMap (linObjectLocalImages as π Y) (linObjectLiftCoord as π)).comp
      (linObjectUnflatten _ _).toLinearMap)

noncomputable def linObjectOriginalQuotientMap (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (Y : List (TmRiO n)) :
    (Fin (as.length * (tmRiPcsO (gens as) Y).length) → ℤ) →ₗ[ℤ] linObjectOriginalQuotient as π Y :=
  (linObjectDiagonalModule (gens as) π (tmGlMs Y)).mkQ.comp (linObjectOriginalMap as π Y)

theorem linObjectOriginalMap_surjective (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (Y : List (TmRiO n)) (hf : Function.Surjective (linObjectLiftCoord as π)) :
    Function.Surjective (linObjectOriginalMap as π Y) :=
  (linObjectPieceReindex as π Y).surjective.comp
    ((linObjectProductMap_surjective (linObjectLocalImages as π Y) (linObjectLiftCoord as π) hf).comp
      (linObjectUnflatten _ _).surjective)

theorem linObjectOriginalQuotientMap_surjective (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (Y : List (TmRiO n)) (hf : Function.Surjective (linObjectLiftCoord as π)) :
    Function.Surjective (linObjectOriginalQuotientMap as π Y) :=
  (Submodule.mkQ_surjective _).comp (linObjectOriginalMap_surjective as π Y hf)

theorem linObjectOriginalMap_kernel {r : ℕ} (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (Y : List (TmRiO n))
    (L : Fin (tmRiPcsO (gens as) Y).length → Matrix (Fin r) (Fin as.length) ℤ)
    (hL : ∀ i, LinearMap.ker ((linObjectLocalImages as π Y i).mkQ.comp (linObjectLiftCoord as π)) =
      linRelations (L i)) :
    LinearMap.ker (linObjectOriginalMap as π Y) = linRelations (linObjectBlockMatrix L) := by
  have hk := linObjectBlockPresentation_ker (linObjectLocalImages as π Y) (linObjectLiftCoord as π) L hL
  ext z
  change linObjectPieceReindex as π Y
    (linObjectProductMap (linObjectLocalImages as π Y) (linObjectLiftCoord as π)
      (linObjectUnflatten _ _ z)) = 0 ↔ z ∈ linRelations (linObjectBlockMatrix L)
  rw [← map_zero (linObjectPieceReindex as π Y),(linObjectPieceReindex as π Y).injective.eq_iff]
  change z ∈ LinearMap.ker ((linObjectProductMap (linObjectLocalImages as π Y) (linObjectLiftCoord as π)).comp
    (linObjectUnflatten _ _).toLinearMap) ↔ _
  rw [hk]

theorem linObjectOriginalQuotientMap_kernel {r : ℕ} (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (Y : List (TmRiO n)) (hf : Function.Surjective (linObjectLiftCoord as π))
    (L : Fin (tmRiPcsO (gens as) Y).length → Matrix (Fin r) (Fin as.length) ℤ)
    (hL : ∀ i, LinearMap.ker ((linObjectLocalImages as π Y i).mkQ.comp (linObjectLiftCoord as π)) =
      linRelations (L i)) :
    LinearMap.ker (linObjectOriginalQuotientMap as π Y) = linRelations (linObjectQuotientMatrix L) := by
  have hk := linObjectQuotientMatrix_ker (linObjectLocalImages as π Y) (linObjectLiftCoord as π) hf L hL
  ext z
  change (linObjectDiagonalModule (gens as) π (tmGlMs Y)).mkQ
    (linObjectPieceReindex as π Y
      (linObjectProductMap (linObjectLocalImages as π Y) (linObjectLiftCoord as π)
        (linObjectUnflatten _ _ z))) = 0 ↔ z ∈ linRelations (linObjectQuotientMatrix L)
  rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero,linObjectPieceReindex_mem_diagonal]
  rw [← hk]
  simp only [LinearMap.mem_ker,LinearMap.comp_apply,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
  rfl

end GI.Impl
