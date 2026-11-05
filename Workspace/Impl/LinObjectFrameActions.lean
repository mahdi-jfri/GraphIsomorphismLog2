module

public import Workspace.Impl.LinObjectFrameRep
public import Workspace.Impl.LinObjectReindexPresentation

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Multicoset

variable {n : ℕ} {Q : Type*} [CommGroup Q]

theorem linObjectPieceReindex_indexedConfig (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (hπ : Function.Surjective π) (Y : List (TmRiO n))
    (hker : ∀ T ∈ pieces (gens as) (tmGlMs Y), π.ker ≤ (Aut (gens as) T).subgroupOf (gens as))
    (Z : {Z // Conf (gens as) (tmGlMs Y) Z}) :
    linObjectPieceReindex as π Y (linObjectIndexedConfigEquiv as π hπ Y hker Z) =
      linObjectConfigCoord (gens as) π (tmGlMs Y) Z.val := by
  change linObjectPieceReindex as π Y
    ((linObjectPieceReindex as π Y).symm (linObjectConfigCoord (gens as) π (tmGlMs Y) Z.val)) = _
  exact (linObjectPieceReindex as π Y).apply_symm_apply _

theorem linObjectFrameProduct_eval {d : ℕ} (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (hπ : Function.Surjective π) (Y : List (TmRiO n))
    (hker : ∀ T ∈ pieces (gens as) (tmGlMs Y), π.ker ≤ (Aut (gens as) T).subgroupOf (gens as))
    (H : Subgroup (Equiv.Perm (Fin n))) (hA : Normalizes H (gens as))
    (hy : ∀ g ∈ H, Conf (gens as) (tmGlMs Y) (tmGlMs Y ↼ g))
    (m : Fin d → ℕ) (E : linObjectOriginalProduct as π Y ≃+ linFiniteVec m)
    (g : H) (Z : Multiset (CObj ℕ (Equiv.Perm (Fin n)))) (hZ : Conf (gens as) (tmGlMs Y) Z) :
    linObjectFrameRep E (linObjectAffineLinear H (gens as) hA (tmGlMs Y) hy π hπ hker) g
        (E (linObjectConfigCoord (gens as) π (tmGlMs Y) Z)) +
      E (linObjectFiniteConfigAction H (gens as) hA (tmGlMs Y) hy π hπ hker g 0) =
      E (linObjectConfigCoord (gens as) π (tmGlMs Y) (Z ↼ g.val⁻¹)) := by
  rw [linObjectFrameRep_image,← map_add]
  apply congrArg E
  exact (linActionLinearEquiv_eval _ _ g _).trans
    (linObjectFiniteConfigAction_eval H (gens as) hA (tmGlMs Y) hy π hπ hker g Z hZ)

theorem linObjectFrameQuotient_eval {d : ℕ} (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (hπ : Function.Surjective π) (Y : List (TmRiO n))
    (hker : ∀ T ∈ pieces (gens as) (tmGlMs Y), π.ker ≤ (Aut (gens as) T).subgroupOf (gens as))
    (H : Subgroup (Equiv.Perm (Fin n))) (hA : Normalizes H (gens as))
    (hy : ∀ g ∈ H, Conf (gens as) (tmGlMs Y) (tmGlMs Y ↼ g))
    (m : Fin d → ℕ) (E : linObjectOriginalQuotient as π Y ≃+ linFiniteVec m)
    (g : H) (Z : Multiset (CObj ℕ (Equiv.Perm (Fin n)))) (hZ : Conf (gens as) (tmGlMs Y) Z) :
    linObjectFrameRep E (linObjectAffineQuotientLinear H (gens as) hA (tmGlMs Y) hy π hπ hker) g
        (E ((linObjectDiagonalModule (gens as) π (tmGlMs Y)).mkQ
          (linObjectConfigCoord (gens as) π (tmGlMs Y) Z))) +
      E ((linObjectDiagonalModule (gens as) π (tmGlMs Y)).mkQ
        (linObjectFiniteConfigAction H (gens as) hA (tmGlMs Y) hy π hπ hker g 0)) =
      E ((linObjectDiagonalModule (gens as) π (tmGlMs Y)).mkQ
        (linObjectConfigCoord (gens as) π (tmGlMs Y) (Z ↼ g.val⁻¹))) := by
  rw [linObjectFrameRep_image,← map_add]
  exact congrArg E (linObjectAffineQuotient_eval H (gens as) hA (tmGlMs Y) hy π hπ hker g Z hZ)

end GI.Impl
