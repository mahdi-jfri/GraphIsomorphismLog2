import Workspace.CleanRowSemidirect

/-! The final row quotients transported to the actual supplied group G. -/
namespace GI
theorem clean_equiv_map_kernel {P Q R : Type*} [Group P] [Group Q] [Group R]
    (e : P ≃* Q) (f : P →* R) :
    f.ker.map e.toMonoidHom = (f.comp e.symm.toMonoidHom).ker := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    change f (e.symm (e p)) = 1
    rw [e.symm_apply_apply]
    exact hp
  · intro hq
    exact ⟨e.symm q, hq, e.apply_symm_apply q⟩

namespace PureComplement
variable {I V : Type*} [Fintype I] [DecidableEq I]
variable {G : Subgroup (Equiv.Perm V)} {A : CleanBlockAction G I} (c : PureComplement A)
variable (h5 : 5 ≤ Fintype.card I) (i0 : I)

abbrev normalRows := c.commonRows (Nat.le_trans (by decide : 4 ≤ 5) h5) i0

theorem normalRows_invariant : RowAltInvariant (c.normalRows h5 i0) :=
  c.commonRows_invariant (Nat.le_trans (by decide) h5) i0

theorem normalRows_subdirect : RowSubdirect (c.normalRows h5 i0) :=
  c.commonRows_subdirect (Nat.le_trans (by decide) h5) i0

noncomputable def normalRowsEquiv :
    (c.normalRows h5 i0) ⋊[rowAltAction (c.normalRows h5 i0) (c.normalRows_invariant h5 i0)]
      alternatingGroup I ≃* G :=
  c.commonSemidirectEquiv (Nat.le_trans (by decide) h5) i0

noncomputable def actualRowMR (i j : I) : Subgroup G :=
  (rowMR (c.normalRows h5 i0) (c.normalRows_invariant h5 i0) i j).map
    (c.normalRowsEquiv h5 i0).toMonoidHom

noncomputable def actualRowM (i j : I) : Subgroup G :=
  (rowEmbeddedM (c.normalRows h5 i0) (c.normalRows_invariant h5 i0) i j).map
    (c.normalRowsEquiv h5 i0).toMonoidHom

theorem actualRowMR_normal {i j : I} (hij : i ≠ j) : (c.actualRowMR h5 i0 i j).Normal := by
  haveI : (rowMR (c.normalRows h5 i0) (c.normalRows_invariant h5 i0) i j).Normal :=
    rowMR_normal _ _ (c.normalRows_subdirect h5 i0) h5 hij
  exact (inferInstance : (rowMR (c.normalRows h5 i0) (c.normalRows_invariant h5 i0) i j).Normal).map
    (c.normalRowsEquiv h5 i0).toMonoidHom (c.normalRowsEquiv h5 i0).surjective

theorem actualRowM_normal {i j : I} (hij : i ≠ j) : (c.actualRowM h5 i0 i j).Normal := by
  haveI : (rowEmbeddedM (c.normalRows h5 i0) (c.normalRows_invariant h5 i0) i j).Normal :=
    rowEmbeddedM_normal _ _ (c.normalRows_subdirect h5 i0) h5 hij
  exact (inferInstance : (rowEmbeddedM (c.normalRows h5 i0) (c.normalRows_invariant h5 i0) i j).Normal).map
    (c.normalRowsEquiv h5 i0).toMonoidHom (c.normalRowsEquiv h5 i0).surjective

noncomputable def actualDiagonalHom {i j : I} (hij : i ≠ j) :
    letI : (rowKernelImage (c.normalRows h5 i0) i j).Normal :=
      row_kernel_normal _ (c.normalRows_subdirect h5 i0) i j
    G →* c.localGroup i0 ⧸ rowKernelImage (c.normalRows h5 i0) i j := by
  letI : (rowKernelImage (c.normalRows h5 i0) i j).Normal :=
    row_kernel_normal _ (c.normalRows_subdirect h5 i0) i j
  exact (rowSemidirectHom _ (c.normalRows_invariant h5 i0) (c.normalRows_subdirect h5 i0) h5 hij).comp
    (c.normalRowsEquiv h5 i0).symm.toMonoidHom

noncomputable def actualPairHom {i j : I} (hij : i ≠ j) :
    letI : (rowKernelImage (c.normalRows h5 i0) i j).Normal :=
      row_kernel_normal _ (c.normalRows_subdirect h5 i0) i j
    G →* (c.localGroup i0 ⧸ rowKernelImage (c.normalRows h5 i0) i j) × alternatingGroup I := by
  letI : (rowKernelImage (c.normalRows h5 i0) i j).Normal :=
    row_kernel_normal _ (c.normalRows_subdirect h5 i0) i j
  exact (rowPairHom _ (c.normalRows_invariant h5 i0) (c.normalRows_subdirect h5 i0) h5 hij).comp
    (c.normalRowsEquiv h5 i0).symm.toMonoidHom

theorem actualRowMR_eq_kernel {i j : I} (hij : i ≠ j) :
    letI : (rowKernelImage (c.normalRows h5 i0) i j).Normal :=
      row_kernel_normal _ (c.normalRows_subdirect h5 i0) i j
    c.actualRowMR h5 i0 i j = (c.actualDiagonalHom h5 i0 hij).ker := by
  letI : (rowKernelImage (c.normalRows h5 i0) i j).Normal :=
    row_kernel_normal _ (c.normalRows_subdirect h5 i0) i j
  rw [actualRowMR, rowMR_eq_ker _ _ (c.normalRows_subdirect h5 i0) h5 hij]
  exact clean_equiv_map_kernel _ _

theorem actualRowM_eq_kernel {i j : I} (hij : i ≠ j) :
    letI : (rowKernelImage (c.normalRows h5 i0) i j).Normal :=
      row_kernel_normal _ (c.normalRows_subdirect h5 i0) i j
    c.actualRowM h5 i0 i j = (c.actualPairHom h5 i0 hij).ker := by
  letI : (rowKernelImage (c.normalRows h5 i0) i j).Normal :=
    row_kernel_normal _ (c.normalRows_subdirect h5 i0) i j
  rw [actualRowM, rowEmbeddedM_eq_ker _ _ (c.normalRows_subdirect h5 i0) h5 hij]
  exact clean_equiv_map_kernel _ _

noncomputable def actualRowMRQuotientEquiv {i j : I} (hij : i ≠ j) :
    letI : (rowKernelImage (c.normalRows h5 i0) i j).Normal :=
      row_kernel_normal _ (c.normalRows_subdirect h5 i0) i j
    letI : (c.actualRowMR h5 i0 i j).Normal := c.actualRowMR_normal h5 i0 hij
    G ⧸ c.actualRowMR h5 i0 i j ≃* c.localGroup i0 ⧸ rowKernelImage (c.normalRows h5 i0) i j := by
  letI : (rowKernelImage (c.normalRows h5 i0) i j).Normal :=
    row_kernel_normal _ (c.normalRows_subdirect h5 i0) i j
  letI : (c.actualRowMR h5 i0 i j).Normal := c.actualRowMR_normal h5 i0 hij
  exact (QuotientGroup.quotientMulEquivOfEq (c.actualRowMR_eq_kernel h5 i0 hij)).trans
    (QuotientGroup.quotientKerEquivOfSurjective (c.actualDiagonalHom h5 i0 hij)
      ((rowSemidirectHom_surjective _ _ (c.normalRows_subdirect h5 i0) h5 hij).comp
        (c.normalRowsEquiv h5 i0).symm.surjective))

noncomputable def actualRowMQuotientEquiv {i j : I} (hij : i ≠ j) :
    letI : (rowKernelImage (c.normalRows h5 i0) i j).Normal :=
      row_kernel_normal _ (c.normalRows_subdirect h5 i0) i j
    letI : (c.actualRowM h5 i0 i j).Normal := c.actualRowM_normal h5 i0 hij
    G ⧸ c.actualRowM h5 i0 i j ≃*
      (c.localGroup i0 ⧸ rowKernelImage (c.normalRows h5 i0) i j) × alternatingGroup I := by
  letI : (rowKernelImage (c.normalRows h5 i0) i j).Normal :=
    row_kernel_normal _ (c.normalRows_subdirect h5 i0) i j
  letI : (c.actualRowM h5 i0 i j).Normal := c.actualRowM_normal h5 i0 hij
  exact (QuotientGroup.quotientMulEquivOfEq (c.actualRowM_eq_kernel h5 i0 hij)).trans
    (QuotientGroup.quotientKerEquivOfSurjective (c.actualPairHom h5 i0 hij)
      ((rowPairHom_surjective _ _ (c.normalRows_subdirect h5 i0) h5 hij).comp
        (c.normalRowsEquiv h5 i0).symm.surjective))

end PureComplement
end GI
