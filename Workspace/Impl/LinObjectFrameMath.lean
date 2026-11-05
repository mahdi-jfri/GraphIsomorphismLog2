module

public import Workspace.Impl.LinObjectMovedMath

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset Matrix

/-- Integer lifting through a unimodular Smith multiplier is an exact right inverse. -/
theorem linObjectFrame_roundtrip {d : ℕ} (V : Matrix (Fin d) (Fin d) ℤ)
    (hV : IsUnit V.det) (x : Fin d → ℤ) : Matrix.vecMul (Matrix.vecMul x V⁻¹) V = x := by
  rw [Matrix.vecMul_vecMul,V.nonsing_inv_mul hV,Matrix.vecMul_one]

theorem linObjectFrame_basis {n : ℕ} {Q R : Type*} [CommGroup Q] [AddCommGroup R]
    (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q) (hπ : Function.Surjective π)
    (Y : List (TmRiO n))
    (hker : ∀ T ∈ pieces (gens as) (tmGlMs Y), π.ker ≤ (Aut (gens as) T).subgroupOf (gens as))
    (q : linObjectIndexedProduct as π Y →+ R)
    (V D : Matrix (Fin (as.length * (tmRiPcsO (gens as) Y).length))
      (Fin (as.length * (tmRiPcsO (gens as) Y).length)) ℤ)
    (hV : IsUnit V.det) (E : R ≃+ tmGLVec (tmGLQMod D))
    (hE : ∀ z, E (q (linObjectProductMap
      (fun i => linObjectGroupImage (gens as) π (Aut (gens as) (tmGlMs ((tmRiPcsO (gens as) Y).get i))))
      (linObjectLiftCoord as π) (linObjectUnflatten _ _ z))) = tmGLQMap V D z)
    (x : Fin (as.length * (tmRiPcsO (gens as) Y).length) → ℤ) :
    E (q (linObjectIndexedConfigEquiv as π hπ Y hker
      ⟨tmGlMs (linObjectWordPieces as Y (Matrix.vecMul x V⁻¹)).flatten,
        linObjectWordPieces_conf as Y (Matrix.vecMul x V⁻¹)⟩)) =
      (fun i => (x i : ZMod (tmGLQMod D i))) := by
  rw [linObjectWordPieces_coord,hE]
  change (fun i => ((Matrix.vecMul (Matrix.vecMul x V⁻¹) V) i : ZMod (tmGLQMod D i))) = _
  rw [linObjectFrame_roundtrip V hV]

/-- Any valid local-coordinate choices give the same finite Smith point. -/
theorem linObjectFrame_offsets {n : ℕ} {Q R : Type*} [CommGroup Q] [AddCommGroup R]
    (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q) (hπ : Function.Surjective π)
    (Y : List (TmRiO n))
    (hker : ∀ T ∈ pieces (gens as) (tmGlMs Y), π.ker ≤ (Aut (gens as) T).subgroupOf (gens as))
    (q : linObjectIndexedProduct as π Y →+ R)
    (V D : Matrix (Fin (as.length * (tmRiPcsO (gens as) Y).length))
      (Fin (as.length * (tmRiPcsO (gens as) Y).length)) ℤ)
    (E : R ≃+ tmGLVec (tmGLQMod D))
    (hE : ∀ z, E (q (linObjectProductMap
      (fun i => linObjectGroupImage (gens as) π (Aut (gens as) (tmGlMs ((tmRiPcsO (gens as) Y).get i))))
      (linObjectLiftCoord as π) (linObjectUnflatten _ _ z))) = tmGLQMap V D z)
    (Z : Multiset (CObj ℕ (Equiv.Perm (Fin n)))) (hZ : Conf (gens as) (tmGlMs Y) Z)
    {out : Val} (hout : linObjectOffsetsOut as π (tmRiPcsO (gens as) Y) Z out) :
    ∃ w, out = linVecVal w ∧ tmGLQMap V D w =
      E (q (linObjectIndexedConfigEquiv as π hπ Y hker ⟨Z,hZ⟩)) := by
  obtain ⟨w,he,hw⟩ := linObjectOffsets_indexed as π hπ Y Z hZ hker hout
  refine ⟨w,he,?_⟩
  rw [← hE,hw]

/-- Read a configuration action through either finite Smith frame. This
turns the concrete evaluator postcondition into an affine-map evaluation. -/
theorem linObjectFrame_actionPoint {n : ℕ} {Q R : Type*} [CommGroup Q] [AddCommGroup R]
    (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q) (hπ : Function.Surjective π)
    (Y : List (TmRiO n))
    (hker : ∀ T ∈ pieces (gens as) (tmGlMs Y), π.ker ≤ (Aut (gens as) T).subgroupOf (gens as))
    (q : linObjectIndexedProduct as π Y →+ R)
    (V D : Matrix (Fin (as.length * (tmRiPcsO (gens as) Y).length))
      (Fin (as.length * (tmRiPcsO (gens as) Y).length)) ℤ)
    (hV : IsUnit V.det) (E : R ≃+ tmGLVec (tmGLQMod D))
    (hE : ∀ z, E (q (linObjectProductMap
      (fun i => linObjectGroupImage (gens as) π (Aut (gens as) (tmGlMs ((tmRiPcsO (gens as) Y).get i))))
      (linObjectLiftCoord as π) (linObjectUnflatten _ _ z))) = tmGLQMap V D z)
    (H : Subgroup (Equiv.Perm (Fin n))) (hA : GI.Multicoset.Normalizes H (gens as))
    (g : Equiv.Perm (Fin n)) (hg : g ∈ H)
    (hy : Conf (gens as) (tmGlMs Y) (tmGlMs Y ↼ g⁻¹))
    (F : tmGLVec (tmGLQMod D) → tmGLVec (tmGLQMod D))
    (hF : ∀ Z (hZ : Conf (gens as) (tmGlMs Y) Z),
      F (E (q (linObjectIndexedConfigEquiv as π hπ Y hker ⟨Z,hZ⟩))) =
        E (q (linObjectIndexedConfigEquiv as π hπ Y hker
          ⟨Z ↼ g⁻¹,(affine_law hA (H.inv_mem hg) hy hZ).2.2⟩)))
    (x : Fin (as.length * (tmRiPcsO (gens as) Y).length) → ℤ) :
    E (q (linObjectIndexedConfigEquiv as π hπ Y hker
      ⟨tmGlMs (linObjectMovedPieces as Y (Matrix.vecMul x V⁻¹) g⁻¹).flatten,
        linObjectMovedPieces_conf as Y _ H hA g⁻¹ (H.inv_mem hg) hy⟩)) =
      F (fun i => (x i : ZMod (tmGLQMod D i))) := by
  have he := hF _ (linObjectWordPieces_conf as Y (Matrix.vecMul x V⁻¹))
  rw [linObjectFrame_basis as π hπ Y hker q V D hV E hE x] at he
  symm
  exact he.trans (by
    congr 2
    apply congrArg (linObjectIndexedConfigEquiv as π hπ Y hker)
    apply Subtype.ext
    exact (linObjectMs_shiftPieces _ g⁻¹).symm)

end GI.Impl
