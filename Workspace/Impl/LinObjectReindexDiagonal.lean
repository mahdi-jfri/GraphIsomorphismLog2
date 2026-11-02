import Workspace.Impl.LinObjectIndexed
import Workspace.Impl.LinObjectDiagonalCriterion

namespace GI.Impl
open GI.Cited GI.Multicoset

variable {n : ℕ} {Q : Type*} [CommGroup Q]

/-- Reordering the reference pieces preserves the common-translation subspace. -/
theorem linObjectPieceReindex_diagonal (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (Y : List (TmRiO n)) (a : Additive Q) :
    linObjectPieceReindex as π Y
      (linObjectDiagonal (fun i => linObjectGroupImage (gens as) π
        (Aut (gens as) (tmGlMs ((tmRiPcsO (gens as) Y).get i)))) a) =
    linObjectDiagonal (fun T : ↥(pieces (gens as) (tmGlMs Y)) =>
      linObjectGroupImage (gens as) π (Aut (gens as) T.val)) a := by
  apply (linObjectPieceReindex as π Y).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem linObjectPieceReindex_mem_diagonal (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (Y : List (TmRiO n)) (w : linObjectIndexedProduct as π Y) :
    linObjectPieceReindex as π Y w ∈ linObjectDiagonalModule (gens as) π (tmGlMs Y) ↔
    w ∈ LinearMap.range (linObjectDiagonal (fun i => linObjectGroupImage (gens as) π
      (Aut (gens as) (tmGlMs ((tmRiPcsO (gens as) Y).get i))))) := by
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨a,(linObjectPieceReindex as π Y).injective ?_⟩
    rw [linObjectPieceReindex_diagonal]
    exact ha
  · rintro ⟨a,rfl⟩
    exact ⟨a,(linObjectPieceReindex_diagonal as π Y a).symm⟩

end GI.Impl
