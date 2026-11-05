module

public import Workspace.RowNormalForm
public import Mathlib.GroupTheory.QuotientGroup.Basic

@[expose] public section

open scoped commutatorElement

/-! Exact multiplicative zero-sum description of the coordinate kernel quotient. -/
namespace GI
variable {I H : Type*} [DecidableEq I] [Group H]

/-- Pointwise evaluation of a product of transfers with a common second row. -/
theorem row_transfer_product_apply (l : List I) (hn : l.Nodup) (j : I) (hj : j ∉ l)
    (x : I → H) (r : I) :
    (l.map (fun a => rowTransfer a j (x a))).prod r =
      if r = j then (l.map (fun a => (x a)⁻¹)).prod else if r ∈ l then x r else 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨han, hln⟩ := List.nodup_cons.mp hn
    have hja : j ≠ a := fun he => hj (by simp [he])
    have hjl : j ∉ l := fun he => hj (List.mem_cons_of_mem a he)
    rw [List.map_cons, List.prod_cons, Pi.mul_apply, ih hln hjl]
    by_cases hrj : r = j
    · subst r
      simp [rowTransfer, hja]
    by_cases hra : r = a
    · subst r
      simp [rowTransfer, hrj, han]
    · simp [rowTransfer, hrj, hra]

variable [Fintype I]

/-- An enumeration of every row once, with the distinguished row last. -/
noncomputable def rowOrdering (j : I) : List I :=
  (Finset.univ.erase j).toList.reverse ++ [j]

theorem row_ordering_mem (j r : I) : r ∈ rowOrdering j := by
  by_cases hr : r = j <;> simp [rowOrdering, hr]

theorem row_ordering_nodup (j : I) : (rowOrdering j).Nodup := by
  simp [rowOrdering, List.nodup_append, List.disjoint_left, Finset.nodup_toList]

theorem row_ordered_product (j : I) (x : I → H) :
    ((Finset.univ.erase j).toList.map (fun r => (x r)⁻¹)).prod⁻¹ * x j =
      ((rowOrdering j).map x).prod := by
  simp only [rowOrdering, List.map_append, List.prod_append, List.map_reverse,
    List.map_singleton, List.prod_singleton, List.prod_reverse_noncomm,
    List.map_map, Function.comp_def]

/-- The product of transfers removes every coordinate except the distinguished one. -/
theorem row_concentrate_identity (j : I) (x : I → H) :
    (((Finset.univ.erase j).toList.map (fun r => rowTransfer r j (x r))).prod)⁻¹ * x =
      rowSingle j (((rowOrdering j).map x).prod) := by
  funext r
  have heval := row_transfer_product_apply (Finset.univ.erase j).toList
    (Finset.nodup_toList _) j (by simp) x r
  by_cases hr : r = j
  · subst r
    simp only [Pi.mul_apply, Pi.inv_apply, heval, if_pos rfl, rowSingle]
    simp only [ite_true]
    rw [row_ordered_product]
  · simp [Pi.mul_apply, Pi.inv_apply, heval, hr, rowSingle]

/-- Exact membership test before taking quotients: no group normality is assumed. -/
theorem row_membership_iff_total_mem_single (K : Subgroup (I → H))
    (hinv : RowAltInvariant K) (hcard : 5 ≤ Fintype.card I) {i j : I} (hij : i ≠ j)
    (x : I → H) (hxN : ∀ r, x r ∈ rowKernelImage K i j) :
    x ∈ K ↔ ((rowOrdering j).map x).prod ∈ rowSingleKernel K j := by
  let t := ((Finset.univ.erase j).toList.map (fun r => rowTransfer r j (x r))).prod
  have ht : t ∈ K := by
    apply list_prod_mem
    intro y hy
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hy
    have hrj : r ≠ j := (Finset.mem_erase.mp (Finset.mem_toList.mp hr)).1
    exact row_transfers_from_kernel K hinv hcard hij hrj (hxN r)
  have heq : t⁻¹ * x = rowSingle j (((rowOrdering j).map x).prod) :=
    row_concentrate_identity j x
  constructor
  · intro hx
    have hh := K.mul_mem (K.inv_mem ht) hx
    rwa [heq] at hh
  · intro hx
    have hh : t⁻¹ * x ∈ K := by rw [heq]; exact hx
    have hhh := K.mul_mem ht hh
    simpa using hhh

/-- The image of N in H/N* is abelian, derived from the isolated commutators. -/
theorem row_kernel_quotient_commute (K : Subgroup (I → H)) (hinv : RowAltInvariant K)
    (hs : RowSubdirect K) (hcard : 5 ≤ Fintype.card I) {i j : I} (hij : i ≠ j)
    {n p : H} (hn : n ∈ rowKernelImage K i j) (hp : p ∈ rowKernelImage K i j) :
    letI : (rowSingleKernel K j).Normal := row_single_normal K hs j
    Commute (QuotientGroup.mk n : H ⧸ rowSingleKernel K j) (QuotientGroup.mk p) := by
  letI : (rowSingleKernel K j).Normal := row_single_normal K hs j
  apply commutatorElement_eq_one_iff_commute.mp
  have hc : ⁅n, p⁆ ∈ rowSingleKernel K j :=
    row_kernel_commutator_le_single K hinv hcard hij (Subgroup.commutator_mem_commutator hn hp)
  have he := (QuotientGroup.eq_one_iff (N := rowSingleKernel K j) ⁅n, p⁆).2 hc
  simpa only [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_inv] using he

/-- Exact zero-sum criterion in multiplicative notation; normality is proved from
subdirectness rather than supplied as an additional conclusion. -/
theorem row_membership_iff_zero_product (K : Subgroup (I → H))
    (hinv : RowAltInvariant K) (hs : RowSubdirect K) (hcard : 5 ≤ Fintype.card I)
    {i j : I} (hij : i ≠ j) (x : I → H) (hxN : ∀ r, x r ∈ rowKernelImage K i j) :
    letI : (rowSingleKernel K j).Normal := row_single_normal K hs j
    x ∈ K ↔ ((rowOrdering j).map (fun r =>
      (QuotientGroup.mk (x r) : H ⧸ rowSingleKernel K j))).prod = 1 := by
  letI : (rowSingleKernel K j).Normal := row_single_normal K hs j
  rw [row_membership_iff_total_mem_single K hinv hcard hij x hxN,
    ← QuotientGroup.eq_one_iff]
  change (QuotientGroup.mk' (rowSingleKernel K j)) (((rowOrdering j).map x).prod) = 1 ↔ _
  rw [map_list_prod]
  simp only [List.map_map, Function.comp_def, QuotientGroup.mk'_apply]

/-- The image of K intersected with N^I is exactly the zero-product subgroup
of the coordinatewise image of N in H/N*. This is the zero-sum assertion of A.18. -/
theorem row_quotient_image_zero_product (K : Subgroup (I → H))
    (hinv : RowAltInvariant K) (hs : RowSubdirect K) (hcard : 5 ≤ Fintype.card I)
    {i j : I} (hij : i ≠ j) :
    letI : (rowSingleKernel K j).Normal := row_single_normal K hs j
    ∀ q : I → H ⧸ rowSingleKernel K j,
      (∃ x : I → H, x ∈ K ∧ (∀ r, x r ∈ rowKernelImage K i j) ∧
        ∀ r, QuotientGroup.mk (x r) = q r) ↔
      (∀ r, q r ∈ (rowKernelImage K i j).map (QuotientGroup.mk' (rowSingleKernel K j))) ∧
        ((rowOrdering j).map q).prod = 1 := by
  letI : (rowSingleKernel K j).Normal := row_single_normal K hs j
  intro q
  constructor
  · rintro ⟨x, hx, hxN, hxq⟩
    refine ⟨?_, ?_⟩
    · intro r
      exact ⟨x r, hxN r, hxq r⟩
    · have he := (row_membership_iff_zero_product K hinv hs hcard hij x hxN).1 hx
      simpa only [hxq] using he
  · rintro ⟨hq, hzero⟩
    have hlift : ∀ r, ∃ n : H, n ∈ rowKernelImage K i j ∧ QuotientGroup.mk n = q r := hq
    choose x hxN hxq using hlift
    refine ⟨x, ?_, hxN, hxq⟩
    apply (row_membership_iff_zero_product K hinv hs hcard hij x hxN).2
    simpa only [hxq] using hzero

omit [Fintype I] in
/-- The coordinate image used above is canonically isomorphic to the paper's N/N*. -/
theorem row_quotient_equiv_image (K : Subgroup (I → H)) (hs : RowSubdirect K) (i j : I) :
    letI : (rowSingleKernel K j).Normal := row_single_normal K hs j
    Nonempty ((rowKernelImage K i j) ⧸ (rowSingleKernel K j).subgroupOf (rowKernelImage K i j) ≃*
      (rowKernelImage K i j).map (QuotientGroup.mk' (rowSingleKernel K j))) := by
  letI : (rowSingleKernel K j).Normal := row_single_normal K hs j
  let f := (QuotientGroup.mk' (rowSingleKernel K j)).comp (rowKernelImage K i j).subtype
  have hker : f.ker = (rowSingleKernel K j).subgroupOf (rowKernelImage K i j) := by
    ext n
    simp [f, MonoidHom.mem_ker]
    rfl
  have hrange : f.range =
      (rowKernelImage K i j).map (QuotientGroup.mk' (rowSingleKernel K j)) := by
    ext q
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n.val, n.property, rfl⟩
    · rintro ⟨n, hn, hq⟩
      exact ⟨⟨n, hn⟩, hq⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hrange))⟩

/-- The quotient N/N* itself is abelian. -/
theorem row_N_quotient_mul_comm (K : Subgroup (I → H)) (hinv : RowAltInvariant K)
    (hs : RowSubdirect K) (hcard : 5 ≤ Fintype.card I) {i j : I} (hij : i ≠ j) :
    letI : (rowSingleKernel K j).Normal := row_single_normal K hs j
    ∀ u v : (rowKernelImage K i j) ⧸
        (rowSingleKernel K j).subgroupOf (rowKernelImage K i j), u * v = v * u := by
  letI : (rowSingleKernel K j).Normal := row_single_normal K hs j
  obtain ⟨e⟩ := row_quotient_equiv_image K hs i j
  intro u v
  apply e.injective
  simp only [map_mul]
  apply Subtype.ext
  obtain ⟨n, hn, hen⟩ := (e u).property
  obtain ⟨p, hp, hep⟩ := (e v).property
  have hc := row_kernel_quotient_commute K hinv hs hcard hij hn hp
  change Commute ((QuotientGroup.mk' (rowSingleKernel K j)) n)
    ((QuotientGroup.mk' (rowSingleKernel K j)) p) at hc
  rw [hen, hep] at hc
  exact hc.eq

end GI
