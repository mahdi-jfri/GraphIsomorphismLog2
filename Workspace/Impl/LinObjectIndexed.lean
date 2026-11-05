module

public import Workspace.Impl.LinObjectPieceIndex
public import Workspace.Impl.LinObjectProductMath

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Multicoset GI.Lang

abbrev linObjectIndexedProduct {n : ℕ} {Q : Type*} [CommGroup Q]
    (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q) (Y : List (TmRiO n)) :=
  ∀ i : Fin (tmRiPcsO (gens as) Y).length,
    Additive Q ⧸ linObjectGroupImage (gens as) π (Aut (gens as) (tmGlMs ((tmRiPcsO (gens as) Y).get i)))

noncomputable def linObjectPieceReindex {n : ℕ} {Q : Type*} [CommGroup Q]
    (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q) (Y : List (TmRiO n)) :
    (∀ i : Fin (tmRiPcsO (gens as) Y).length,
      Additive Q ⧸ linObjectGroupImage (gens as) π (Aut (gens as) (tmGlMs ((tmRiPcsO (gens as) Y).get i)))) ≃ₗ[ℤ]
    (∀ T : ↥(pieces (gens as) (tmGlMs Y)),
      Additive Q ⧸ linObjectGroupImage (gens as) π (Aut (gens as) T.val)) :=
  LinearEquiv.piCongrLeft ℤ
    (fun T : ↥(pieces (gens as) (tmGlMs Y)) =>
      Additive Q ⧸ linObjectGroupImage (gens as) π (Aut (gens as) T.val))
    (linObjectPieceIndex as Y)

@[simp] theorem linObjectPieceReindex_symm_apply {n : ℕ} {Q : Type*} [CommGroup Q]
    (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q) (Y : List (TmRiO n))
    (w : ∀ T : ↥(pieces (gens as) (tmGlMs Y)),
      Additive Q ⧸ linObjectGroupImage (gens as) π (Aut (gens as) T.val))
    (i : Fin (tmRiPcsO (gens as) Y).length) :
    (linObjectPieceReindex as π Y).symm w i = w (linObjectPieceIndex as Y i) := rfl

noncomputable def linObjectIndexedConfigEquiv {n : ℕ} {Q : Type*} [CommGroup Q]
    (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q) (hπ : Function.Surjective π)
    (Y : List (TmRiO n))
    (hker : ∀ T ∈ pieces (gens as) (tmGlMs Y), π.ker ≤ (Aut (gens as) T).subgroupOf (gens as)) :
    {Z // Conf (gens as) (tmGlMs Y) Z} ≃
    (∀ i : Fin (tmRiPcsO (gens as) Y).length,
      Additive Q ⧸ linObjectGroupImage (gens as) π (Aut (gens as) (tmGlMs ((tmRiPcsO (gens as) Y).get i)))) :=
  (linObjectConfigEquiv (gens as) π hπ (tmGlMs Y) hker).trans
    (linObjectPieceReindex as π Y).symm.toEquiv

theorem linObjectIndexedConfigEquiv_apply {n : ℕ} {Q : Type*} [CommGroup Q]
    (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q) (hπ : Function.Surjective π)
    (Y : List (TmRiO n))
    (hker : ∀ T ∈ pieces (gens as) (tmGlMs Y), π.ker ≤ (Aut (gens as) T).subgroupOf (gens as))
    (Z : {Z // Conf (gens as) (tmGlMs Y) Z}) (i : Fin (tmRiPcsO (gens as) Y).length) :
    linObjectIndexedConfigEquiv as π hπ Y hker Z i =
      linObjectConfigCoord (gens as) π (tmGlMs Y) Z.val (linObjectPieceIndex as Y i) := rfl

/-- The offset collector gives the coordinates in the runtime piece order. -/
theorem linObjectOffsets_indexed {n : ℕ} {Q : Type*} [CommGroup Q]
    (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q) (hπ : Function.Surjective π)
    (Y : List (TmRiO n)) (Z : Multiset (CObj ℕ (Equiv.Perm (Fin n))))
    (hZ : Conf (gens as) (tmGlMs Y) Z)
    (hker : ∀ T ∈ pieces (gens as) (tmGlMs Y), π.ker ≤ (Aut (gens as) T).subgroupOf (gens as))
    {out : Val} (hout : linObjectOffsetsOut as π (tmRiPcsO (gens as) Y) Z out) :
    ∃ w : Fin (as.length * (tmRiPcsO (gens as) Y).length) → ℤ, out = linVecVal w ∧
      linObjectProductMap
        (fun i => linObjectGroupImage (gens as) π (Aut (gens as) (tmGlMs ((tmRiPcsO (gens as) Y).get i))))
        (linObjectLiftCoord as π) (linObjectUnflatten _ _ w) =
      linObjectIndexedConfigEquiv as π hπ Y hker ⟨Z,hZ⟩ := by
  have hRef : ∀ S ∈ tmRiPcsO (gens as) Y, tmGlMs S ∈ pieces (gens as) (tmGlMs Y) := by
    intro S hS
    have hh : tmGlMs S ∈ (((tmRiPcsO (gens as) Y).map tmGlMs : List _) : Multiset _) := by
      simp only [Multiset.mem_coe, List.mem_map]
      exact ⟨S,hS,rfl⟩
    rw [tmRiPcsO_ms] at hh
    exact hh
  obtain ⟨w,he,hw⟩ := linObjectOffsets_coordinate as π _ (tmGlMs Y) Z hZ hRef hker hout
  refine ⟨w,he,?_⟩
  funext i
  exact hw i

end GI.Impl
