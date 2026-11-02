import Workspace.RowQuotients
import Mathlib.GroupTheory.SemidirectProduct

/-! The group with a pure alternating row action and its diagonal quotient. -/
namespace GI
variable {I H : Type*} [Fintype I] [DecidableEq I] [Group H]

/-- Inverse precomposition gives the genuine left action of pure row permutations. -/
def rowAltAction (K : Subgroup (I → H)) (hinv : RowAltInvariant K) :
    alternatingGroup I →* MulAut K where
  toFun s := {
    toFun := fun x => ⟨rowPermute (s.val)⁻¹ x.val,
      hinv _ ((alternatingGroup I).inv_mem s.property) x.val x.property⟩
    invFun := fun x => ⟨rowPermute s.val x.val, hinv _ s.property x.val x.property⟩
    left_inv := by
      intro x
      apply Subtype.ext
      funext r
      simp [rowPermute]
    right_inv := by
      intro x
      apply Subtype.ext
      funext r
      simp [rowPermute]
    map_mul' := fun _ _ => rfl }
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    funext r
    rfl
  map_mul' s t := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    funext r
    change x.val (((s.val * t.val)⁻¹) r) = x.val (t.val⁻¹ (s.val⁻¹ r))
    rw [mul_inv_rev, Equiv.Perm.mul_apply]

/-- The concrete subgroup MR in the pure-row semidirect product. -/
def rowMR (K : Subgroup (I → H)) (hinv : RowAltInvariant K) (i j : I) :
    Subgroup (K ⋊[rowAltAction K hinv] alternatingGroup I) :=
  ((rowM K i j).subgroupOf K).map SemidirectProduct.inl ⊔
    (SemidirectProduct.inr : alternatingGroup I →*
      K ⋊[rowAltAction K hinv] alternatingGroup I).range

/-- Evaluation in H/N extends over the pure alternating complement. -/
def rowSemidirectHom (K : Subgroup (I → H)) (hinv : RowAltInvariant K)
    (hs : RowSubdirect K) (hcard : 5 ≤ Fintype.card I) {i j : I} (hij : i ≠ j) :
    letI : (rowKernelImage K i j).Normal := row_kernel_normal K hs i j
    (K ⋊[rowAltAction K hinv] alternatingGroup I) →* H ⧸ rowKernelImage K i j := by
  letI : (rowKernelImage K i j).Normal := row_kernel_normal K hs i j
  exact {
    toFun := fun x => QuotientGroup.mk (x.left.val j)
    map_one' := rfl
    map_mul' := by
      intro x y
      change (QuotientGroup.mk (x.left.val j * y.left.val (x.right.val⁻¹ j)) :
        H ⧸ rowKernelImage K i j) = QuotientGroup.mk (x.left.val j) * QuotientGroup.mk (y.left.val j)
      rw [QuotientGroup.mk_mul,
        row_diagonal_quotient K hinv hcard hij y.left.val y.left.property (x.right.val⁻¹ j) j] }

theorem rowSemidirectHom_surjective (K : Subgroup (I → H)) (hinv : RowAltInvariant K)
    (hs : RowSubdirect K) (hcard : 5 ≤ Fintype.card I) {i j : I} (hij : i ≠ j) :
    letI : (rowKernelImage K i j).Normal := row_kernel_normal K hs i j
    Function.Surjective (rowSemidirectHom K hinv hs hcard hij) := by
  letI : (rowKernelImage K i j).Normal := row_kernel_normal K hs i j
  intro q
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨x, hx, hxj⟩ := hs j n
  refine ⟨⟨⟨x, hx⟩, 1⟩, ?_⟩
  change QuotientGroup.mk (x j) = QuotientGroup.mk n
  rw [hxj]

theorem rowMR_eq_ker (K : Subgroup (I → H)) (hinv : RowAltInvariant K)
    (hs : RowSubdirect K) (hcard : 5 ≤ Fintype.card I) {i j : I} (hij : i ≠ j) :
    letI : (rowKernelImage K i j).Normal := row_kernel_normal K hs i j
    rowMR K hinv i j = (rowSemidirectHom K hinv hs hcard hij).ker := by
  letI : (rowKernelImage K i j).Normal := row_kernel_normal K hs i j
  apply le_antisymm
  · apply sup_le
    · rintro x ⟨m, hm, rfl⟩
      change (QuotientGroup.mk (m.val j) : H ⧸ rowKernelImage K i j) = 1
      exact (QuotientGroup.eq_one_iff _).2 (hm.2 j)
    · rintro x ⟨s, rfl⟩
      rfl
  · intro x hx
    have hxj : x.left.val j ∈ rowKernelImage K i j := (QuotientGroup.eq_one_iff _).1 hx
    have hxM := (row_coordinate_in_kernel_iff K hinv hcard hij x.left).1 hxj
    rw [← SemidirectProduct.inl_left_mul_inr_right x]
    apply Subgroup.mul_mem
    · have hleft : ((rowM K i j).subgroupOf K).map SemidirectProduct.inl ≤
          rowMR K hinv i j := le_sup_left
      exact hleft ⟨x.left, hxM, rfl⟩
    · have hright : (SemidirectProduct.inr : alternatingGroup I →*
          K ⋊[rowAltAction K hinv] alternatingGroup I).range ≤ rowMR K hinv i j := le_sup_right
      exact hright ⟨x.right, rfl⟩

theorem rowMR_normal (K : Subgroup (I → H)) (hinv : RowAltInvariant K)
    (hs : RowSubdirect K) (hcard : 5 ≤ Fintype.card I) {i j : I} (hij : i ≠ j) :
    (rowMR K hinv i j).Normal := by
  letI : (rowKernelImage K i j).Normal := row_kernel_normal K hs i j
  rw [rowMR_eq_ker K hinv hs hcard hij]
  infer_instance

/-- The final pure-row group quotient G/(MR) is H/N. -/
noncomputable def rowSemidirectQuotientEquiv (K : Subgroup (I → H)) (hinv : RowAltInvariant K)
    (hs : RowSubdirect K) (hcard : 5 ≤ Fintype.card I) {i j : I} (hij : i ≠ j) :
    letI : (rowKernelImage K i j).Normal := row_kernel_normal K hs i j
    letI : (rowMR K hinv i j).Normal := rowMR_normal K hinv hs hcard hij
    (K ⋊[rowAltAction K hinv] alternatingGroup I) ⧸ rowMR K hinv i j ≃*
      H ⧸ rowKernelImage K i j := by
  letI : (rowKernelImage K i j).Normal := row_kernel_normal K hs i j
  letI : (rowMR K hinv i j).Normal := rowMR_normal K hinv hs hcard hij
  exact (QuotientGroup.quotientMulEquivOfEq (rowMR_eq_ker K hinv hs hcard hij)).trans
    (QuotientGroup.quotientKerEquivOfSurjective (rowSemidirectHom K hinv hs hcard hij)
      (rowSemidirectHom_surjective K hinv hs hcard hij))

/-- M regarded as the actual subgroup of the semidirect product. -/
def rowEmbeddedM (K : Subgroup (I → H)) (hinv : RowAltInvariant K) (i j : I) :
    Subgroup (K ⋊[rowAltAction K hinv] alternatingGroup I) :=
  ((rowM K i j).subgroupOf K).map SemidirectProduct.inl

def rowPairHom (K : Subgroup (I → H)) (hinv : RowAltInvariant K)
    (hs : RowSubdirect K) (hcard : 5 ≤ Fintype.card I) {i j : I} (hij : i ≠ j) :
    letI : (rowKernelImage K i j).Normal := row_kernel_normal K hs i j
    (K ⋊[rowAltAction K hinv] alternatingGroup I) →*
      (H ⧸ rowKernelImage K i j) × alternatingGroup I := by
  letI : (rowKernelImage K i j).Normal := row_kernel_normal K hs i j
  exact (rowSemidirectHom K hinv hs hcard hij).prod SemidirectProduct.rightHom

theorem rowEmbeddedM_eq_ker (K : Subgroup (I → H)) (hinv : RowAltInvariant K)
    (hs : RowSubdirect K) (hcard : 5 ≤ Fintype.card I) {i j : I} (hij : i ≠ j) :
    letI : (rowKernelImage K i j).Normal := row_kernel_normal K hs i j
    rowEmbeddedM K hinv i j = (rowPairHom K hinv hs hcard hij).ker := by
  letI : (rowKernelImage K i j).Normal := row_kernel_normal K hs i j
  apply le_antisymm
  · rintro x ⟨m, hm, rfl⟩
    change ((QuotientGroup.mk (m.val j) : H ⧸ rowKernelImage K i j), 1) = (1, 1)
    exact Prod.ext ((QuotientGroup.eq_one_iff _).2 (hm.2 j)) rfl
  · intro x hx
    change ((QuotientGroup.mk (x.left.val j) : H ⧸ rowKernelImage K i j), x.right) = (1, 1) at hx
    have hxj : x.left.val j ∈ rowKernelImage K i j :=
      (QuotientGroup.eq_one_iff _).1 (congrArg Prod.fst hx)
    have hxM := (row_coordinate_in_kernel_iff K hinv hcard hij x.left).1 hxj
    refine ⟨x.left, hxM, ?_⟩
    apply SemidirectProduct.ext
    · rfl
    · exact (congrArg Prod.snd hx).symm

theorem rowEmbeddedM_normal (K : Subgroup (I → H)) (hinv : RowAltInvariant K)
    (hs : RowSubdirect K) (hcard : 5 ≤ Fintype.card I) {i j : I} (hij : i ≠ j) :
    (rowEmbeddedM K hinv i j).Normal := by
  letI : (rowKernelImage K i j).Normal := row_kernel_normal K hs i j
  rw [rowEmbeddedM_eq_ker K hinv hs hcard hij]
  infer_instance

theorem rowPairHom_surjective (K : Subgroup (I → H)) (hinv : RowAltInvariant K)
    (hs : RowSubdirect K) (hcard : 5 ≤ Fintype.card I) {i j : I} (hij : i ≠ j) :
    letI : (rowKernelImage K i j).Normal := row_kernel_normal K hs i j
    Function.Surjective (rowPairHom K hinv hs hcard hij) := by
  letI : (rowKernelImage K i j).Normal := row_kernel_normal K hs i j
  rintro ⟨q, s⟩
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨x, hx, hxj⟩ := hs j n
  refine ⟨⟨⟨x, hx⟩, s⟩, ?_⟩
  change (QuotientGroup.mk (x j), s) = (QuotientGroup.mk n, s)
  rw [hxj]

/-- The complement acts trivially on K/M, giving the actual direct-product quotient. -/
noncomputable def rowSemidirectModuloMEquiv (K : Subgroup (I → H)) (hinv : RowAltInvariant K)
    (hs : RowSubdirect K) (hcard : 5 ≤ Fintype.card I) {i j : I} (hij : i ≠ j) :
    letI : (rowKernelImage K i j).Normal := row_kernel_normal K hs i j
    letI : (rowEmbeddedM K hinv i j).Normal := rowEmbeddedM_normal K hinv hs hcard hij
    (K ⋊[rowAltAction K hinv] alternatingGroup I) ⧸ rowEmbeddedM K hinv i j ≃*
      (H ⧸ rowKernelImage K i j) × alternatingGroup I := by
  letI : (rowKernelImage K i j).Normal := row_kernel_normal K hs i j
  letI : (rowEmbeddedM K hinv i j).Normal := rowEmbeddedM_normal K hinv hs hcard hij
  exact (QuotientGroup.quotientMulEquivOfEq (rowEmbeddedM_eq_ker K hinv hs hcard hij)).trans
    (QuotientGroup.quotientKerEquivOfSurjective (rowPairHom K hinv hs hcard hij)
      (rowPairHom_surjective K hinv hs hcard hij))

end GI
