module

public import Workspace.RowZeroSum
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-! Group-level quotients induced by the concrete row-coordinate subgroups. -/
namespace GI
open scoped BigOperators
variable {I H : Type*} [DecidableEq I] [Group H]

def rowPower (S : Subgroup H) : Subgroup (I → H) where
  carrier := {x | ∀ r, x r ∈ S}
  one_mem' := fun _ => S.one_mem
  mul_mem' hx hy := fun r => S.mul_mem (hx r) (hy r)
  inv_mem' hx := fun r => S.inv_mem (hx r)

def rowM (K : Subgroup (I → H)) (i j : I) : Subgroup (I → H) :=
  K ⊓ rowPower (rowKernelImage K i j)

def rowMstar (K : Subgroup (I → H)) (j : I) : Subgroup (I → H) :=
  rowPower (rowSingleKernel K j)

omit [DecidableEq I] in
theorem rowM_normal_in_K (K : Subgroup (I → H)) (hs : RowSubdirect K) (i j : I) :
    ((rowM K i j).subgroupOf K).Normal := by
  constructor
  intro n hn g
  change ((g : I → H) * (n : I → H) * (g : I → H)⁻¹) ∈ rowM K i j
  refine ⟨K.mul_mem (K.mul_mem g.property n.property) (K.inv_mem g.property), ?_⟩
  intro r
  exact (row_kernel_normal K hs i j).conj_mem (n.val r) (hn.2 r) (g.val r)

theorem rowMstar_normal_in_M (K : Subgroup (I → H)) (hs : RowSubdirect K) (i j : I) :
    ((rowMstar K j).subgroupOf (rowM K i j)).Normal := by
  constructor
  intro n hn g r
  exact (row_single_normal K hs j).conj_mem (n.val r) (hn r) (g.val r)

variable [Fintype I]

theorem rowMstar_le_M (K : Subgroup (I → H)) (hinv : RowAltInvariant K)
    (hcard : 5 ≤ Fintype.card I) {i j : I} (hij : i ≠ j) :
    rowMstar K j ≤ rowM K i j := by
  intro x hx
  exact ⟨row_single_power_le K hinv (by omega) hij x hx,
    fun r => row_single_le_kernel K hij (hx r)⟩

theorem row_coordinate_in_kernel_iff (K : Subgroup (I → H)) (hinv : RowAltInvariant K)
    (hcard : 5 ≤ Fintype.card I) {i j : I} (hij : i ≠ j)
    (x : K) : x.val j ∈ rowKernelImage K i j ↔ x.val ∈ rowM K i j := by
  constructor
  · intro hj
    refine ⟨x.property, ?_⟩
    intro r
    have hd := row_coordinate_difference_mem K hinv hcard hij x.val x.property j r
    have hm := (rowKernelImage K i j).mul_mem hj hd
    simpa using hm
  · exact fun hx => hx.2 j

/-- The actual onto coordinate map induces K/M ≃ H/N. -/
noncomputable def rowDiagonalEquiv (K : Subgroup (I → H)) (hinv : RowAltInvariant K)
    (hs : RowSubdirect K) (hcard : 5 ≤ Fintype.card I) {i j : I} (hij : i ≠ j) :
    letI : (rowKernelImage K i j).Normal := row_kernel_normal K hs i j
    letI : ((rowM K i j).subgroupOf K).Normal := rowM_normal_in_K K hs i j
    K ⧸ (rowM K i j).subgroupOf K ≃* H ⧸ rowKernelImage K i j := by
  letI : (rowKernelImage K i j).Normal := row_kernel_normal K hs i j
  letI : ((rowM K i j).subgroupOf K).Normal := rowM_normal_in_K K hs i j
  let f := (QuotientGroup.mk' (rowKernelImage K i j)).comp ((rowEval j).comp K.subtype)
  have hker : f.ker = (rowM K i j).subgroupOf K := by
    ext x
    change (QuotientGroup.mk (x.val j) : H ⧸ rowKernelImage K i j) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    exact row_coordinate_in_kernel_iff K hinv hcard hij x
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x, hx, hxj⟩ := hs j n
    refine ⟨⟨x, hx⟩, ?_⟩
    change QuotientGroup.mk (x j) = QuotientGroup.mk n
    rw [hxj]
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj)

/-- The proven abelianness supplies the group structure needed for a total-product map. -/
@[reducible] noncomputable def rowQuotientCommGroup (K : Subgroup (I → H)) (hinv : RowAltInvariant K)
    (hs : RowSubdirect K) (hcard : 5 ≤ Fintype.card I) {i j : I} (hij : i ≠ j) :
    letI : (rowSingleKernel K j).Normal := row_single_normal K hs j
    CommGroup ((rowKernelImage K i j) ⧸
      (rowSingleKernel K j).subgroupOf (rowKernelImage K i j)) := by
  letI : (rowSingleKernel K j).Normal := row_single_normal K hs j
  exact { (inferInstance : Group ((rowKernelImage K i j) ⧸
      (rowSingleKernel K j).subgroupOf (rowKernelImage K i j))) with
    mul_comm := row_N_quotient_mul_comm K hinv hs hcard hij }

/-- The actual coordinate quotient map on M. -/
def rowMQuotientHom (K : Subgroup (I → H)) (hs : RowSubdirect K) (i j : I) :
    letI : (rowSingleKernel K j).Normal := row_single_normal K hs j
    rowM K i j →* (I → (rowKernelImage K i j) ⧸
      (rowSingleKernel K j).subgroupOf (rowKernelImage K i j)) := by
  letI : (rowSingleKernel K j).Normal := row_single_normal K hs j
  exact {
    toFun := fun x r => QuotientGroup.mk ⟨x.val r, x.property.2 r⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }

omit [Fintype I] in
theorem rowMQuotientHom_ker (K : Subgroup (I → H)) (hs : RowSubdirect K) (i j : I) :
    letI : (rowSingleKernel K j).Normal := row_single_normal K hs j
    (rowMQuotientHom K hs i j).ker = (rowMstar K j).subgroupOf (rowM K i j) := by
  letI : (rowSingleKernel K j).Normal := row_single_normal K hs j
  ext x
  constructor
  · intro hx r
    have hr := congrFun hx r
    exact (QuotientGroup.eq_one_iff
      (N := (rowSingleKernel K j).subgroupOf (rowKernelImage K i j))
      (⟨x.val r, x.property.2 r⟩ : rowKernelImage K i j)).1 hr
  · intro hx
    funext r
    exact (QuotientGroup.eq_one_iff
      (N := (rowSingleKernel K j).subgroupOf (rowKernelImage K i j))
      (⟨x.val r, x.property.2 r⟩ : rowKernelImage K i j)).2 (hx r)

def rowTotalHom {A : Type*} [CommGroup A] : (I → A) →* A where
  toFun q := ∏ r, q r
  map_one' := by simp
  map_mul' q t := by simp [Finset.prod_mul_distrib]

def rowZeroProduct {A : Type*} [CommGroup A] : Subgroup (I → A) := rowTotalHom.ker

theorem row_ordering_product_eq_univ {A : Type*} [CommMonoid A] (j : I) (q : I → A) :
    ((rowOrdering j).map q).prod = ∏ r, q r := by
  have henum : (rowOrdering j).toFinset = Finset.univ := by
    ext r
    simp [row_ordering_mem]
  rw [← List.prod_toFinset q (row_ordering_nodup j), henum]

theorem rowN_quotient_total_iff (K : Subgroup (I → H)) (hinv : RowAltInvariant K)
    (hs : RowSubdirect K) (hcard : 5 ≤ Fintype.card I) {i j : I} (hij : i ≠ j)
    (x : I → rowKernelImage K i j) :
    letI : (rowSingleKernel K j).Normal := row_single_normal K hs j
    letI := rowQuotientCommGroup K hinv hs hcard hij
    (∏ r, (QuotientGroup.mk (x r) : (rowKernelImage K i j) ⧸
      (rowSingleKernel K j).subgroupOf (rowKernelImage K i j))) = 1 ↔
      ((rowOrdering j).map (fun r => (x r : H))).prod ∈ rowSingleKernel K j := by
  letI : (rowSingleKernel K j).Normal := row_single_normal K hs j
  letI := rowQuotientCommGroup K hinv hs hcard hij
  rw [← row_ordering_product_eq_univ j]
  have hmap := map_list_prod
    (QuotientGroup.mk' ((rowSingleKernel K j).subgroupOf (rowKernelImage K i j)))
    ((rowOrdering j).map x)
  simp only [List.map_map, Function.comp_def, QuotientGroup.mk'_apply] at hmap
  rw [← hmap, QuotientGroup.eq_one_iff]
  change (rowKernelImage K i j).subtype (((rowOrdering j).map x).prod) ∈ rowSingleKernel K j ↔ _
  rw [map_list_prod]
  simp only [List.map_map, Function.comp_def]
  rfl

/-- The actual quotient map on M has exactly the zero-product subgroup as its range. -/
theorem rowMQuotientHom_range (K : Subgroup (I → H)) (hinv : RowAltInvariant K)
    (hs : RowSubdirect K) (hcard : 5 ≤ Fintype.card I) {i j : I} (hij : i ≠ j) :
    letI : (rowSingleKernel K j).Normal := row_single_normal K hs j
    letI := rowQuotientCommGroup K hinv hs hcard hij
    (rowMQuotientHom K hs i j).range = rowZeroProduct := by
  letI : (rowSingleKernel K j).Normal := row_single_normal K hs j
  letI := rowQuotientCommGroup K hinv hs hcard hij
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    change (∏ r, (QuotientGroup.mk (⟨x.val r, x.property.2 r⟩ : rowKernelImage K i j) :
      (rowKernelImage K i j) ⧸ (rowSingleKernel K j).subgroupOf (rowKernelImage K i j))) = 1
    apply (rowN_quotient_total_iff K hinv hs hcard hij (fun r => ⟨x.val r, x.property.2 r⟩)).2
    exact (row_membership_iff_total_mem_single K hinv hcard hij x.val x.property.2).1 x.property.1
  · intro hq
    change (∏ r, q r) = 1 at hq
    have hlift : ∀ r, ∃ n : rowKernelImage K i j, QuotientGroup.mk n = q r :=
      fun r => QuotientGroup.mk_surjective (q r)
    choose x hx using hlift
    let y : I → H := fun r => (x r : H)
    have hyN : ∀ r, y r ∈ rowKernelImage K i j := fun r => (x r).property
    have htotal : ((rowOrdering j).map y).prod ∈ rowSingleKernel K j := by
      apply (rowN_quotient_total_iff K hinv hs hcard hij x).1
      simpa only [hx] using hq
    have hyK := (row_membership_iff_total_mem_single K hinv hcard hij y hyN).2 htotal
    refine ⟨⟨y, hyK, hyN⟩, ?_⟩
    funext r
    exact hx r

/-- The group-level zero-sum normal form M/Mstar, with N/Nstar written multiplicatively. -/
noncomputable def rowZeroProductEquiv (K : Subgroup (I → H)) (hinv : RowAltInvariant K)
    (hs : RowSubdirect K) (hcard : 5 ≤ Fintype.card I) {i j : I} (hij : i ≠ j) :
    letI : (rowSingleKernel K j).Normal := row_single_normal K hs j
    letI := rowQuotientCommGroup K hinv hs hcard hij
    letI : ((rowMstar K j).subgroupOf (rowM K i j)).Normal := rowMstar_normal_in_M K hs i j
    (rowM K i j) ⧸ (rowMstar K j).subgroupOf (rowM K i j) ≃*
      (rowZeroProduct : Subgroup (I → (rowKernelImage K i j) ⧸
        (rowSingleKernel K j).subgroupOf (rowKernelImage K i j))) := by
  letI : (rowSingleKernel K j).Normal := row_single_normal K hs j
  letI := rowQuotientCommGroup K hinv hs hcard hij
  letI : ((rowMstar K j).subgroupOf (rowM K i j)).Normal := rowMstar_normal_in_M K hs i j
  exact (QuotientGroup.quotientMulEquivOfEq (rowMQuotientHom_ker K hs i j).symm).trans
    ((QuotientGroup.quotientKerEquivRange (rowMQuotientHom K hs i j)).trans
      (MulEquiv.subgroupCongr (rowMQuotientHom_range K hinv hs hcard hij)))

end GI
