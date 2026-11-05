module

public import Workspace.Impl.LinCoordinateSlp

@[expose] public section

/-! A checked prefix SLP family gives every hypothesis of linPresentationEquiv.
Surjectivity, triangularity and the order calculation are derived here. -/
namespace GI.Impl
open GI.Cited
open scoped IsMulCommutative
set_option maxHeartbeats 1000000

private theorem linList_finRange {α : Type*} (xs : List α) :
    (List.finRange xs.length).map (fun i => xs[i.val]) = xs := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp

/-- The zero/unit assignments have exactly the required quotient images. -/
theorem linPrefixVectors_images {G Q : Type*} [Group G] [CommGroup Q]
    (π : G →* Q) (ns as : List G) (hns : ∀ g ∈ ns, π g = 1) (i : ℕ) :
    (ns ++ as.take i).map π =
      ((linPrefixVectors as.length ns.length i).map Multiplicative.ofAdd).map
        (linCoordHom (fun j => π as[j.val])) := by
  have hn : ns.map π = List.replicate ns.length 1 := List.map_eq_replicate_iff.mpr hns
  have hz : linCoordHom (fun j : Fin as.length => π as[j.val]) (Multiplicative.ofAdd 0) = 1 := map_one _
  simp only [linPrefixVectors, List.map_append, List.map_replicate, List.map_map,
    Function.comp_def, hz, linCoordHom_single, zpow_one, hn]
  rw [List.map_take, List.map_take]
  have hh := congrArg (List.map π) (linList_finRange as)
  simp only [List.map_map, Function.comp_def] at hh
  rw [hh]

/-- The cyclic orders used by the permutation-prefix program. -/
noncomputable def linCyclicOrders {G : Type*} [Group G] (N : Subgroup G) (as : List G) : Fin as.length → ℕ :=
  fun i => (linChain N as i.val).relIndex (linChain N as (i.val + 1))

theorem linCyclicOrders_pos {G : Type*} [Group G] [Finite G] (N : Subgroup G) (as : List G) :
    ∀ i, 0 < linCyclicOrders N as i := by
  intro i
  change 0 < ((linChain N as i.val).subgroupOf (linChain N as (i.val + 1))).index
  exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite

theorem linCyclicOrders_product {G : Type*} [Group G] (N : Subgroup G) (as : List G)
    (hgen : N ⊔ Subgroup.closure {g | g ∈ as} = ⊤) :
    ∏ i, linCyclicOrders N as i = Nat.card (G ⧸ N) := by
  have h := linChain_product_quotient N as hgen
  rw [Finset.prod_range] at h
  exact h

/-- The hypotheses needed by linPresentationEquiv for the actual quotient map. -/
def linPresentationCertificate {t : ℕ} {Q : Type*} [AddCommGroup Q]
    (M : Matrix (Fin t) (Fin t) ℤ) (f : (Fin t → ℤ) →ₗ[ℤ] Q) : Prop :=
  M.det ≠ 0 ∧ Function.Surjective f ∧ linRelations M ≤ LinearMap.ker f ∧
    Nat.card Q = M.det.natAbs

/-- Constructive-membership SLPs in the prefixes prove the complete presentation.
No row-relation, support, surjectivity or cardinality hypothesis is left to the caller. -/
theorem linAbelianCertificate {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] [IsMulCommutative (G ⧸ N)]
    (ns as : List G) (hns : ∀ g ∈ ns, g ∈ N)
    (hgen : N ⊔ Subgroup.closure {g | g ∈ as} = ⊤)
    (prog : Fin as.length → List SlpInstr)
    (C : Matrix (Fin as.length) (Fin as.length) ℤ)
    (hp : ∀ i, linSlpValue (ns ++ as.take i.val) (prog i) =
      some (as[i.val] ^ linCyclicOrders N as i))
    (hC : ∀ i, linExponentValue (linPrefixVectors as.length ns.length i.val) (prog i) = some (C i)) :
    linPresentationCertificate (linRelationMatrix (linCyclicOrders N as) C)
      (linCoordMap (fun i : Fin as.length => QuotientGroup.mk' N as[i.val])) := by
  let π := QuotientGroup.mk' N
  let e := linCyclicOrders N as
  let v : Fin as.length → G ⧸ N := fun i => π as[i.val]
  let f := linCoordMap v
  have hns' : ∀ g ∈ ns, π g = 1 := by
    intro g hg
    exact (QuotientGroup.eq_one_iff g).mpr (hns g hg)
  have hc : linEarlierCoefficients C := by
    intro i j hij
    exact linExponentValue_zero _ j (linPrefixVectors_zero _ _ _ j hij) _ _ (hC i)
  have hrel : ∀ i, f (Pi.single i (e i : ℤ)) = f (C i) := by
    intro i
    have hh := linExponent_relation π (linCoordHom v) (ns ++ as.take i.val)
      (linPrefixVectors as.length ns.length i.val) (linPrefixVectors_images π ns as hns' i.val)
      (prog i) _ (hp i) (C i) (hC i)
    have heq : linCoordHom v (Multiplicative.ofAdd (Pi.single i (e i : ℤ))) =
        linCoordHom v (Multiplicative.ofAdd (C i)) := by
      rw [linCoordHom_single, hh, map_pow]
      simp [v, e]
    exact congrArg Additive.ofMul heq
  have hs : Set.range (fun i : Fin as.length => as[i.val]) = {g | g ∈ as} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact List.getElem_mem i.isLt
    · intro hx
      obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hx
      exact ⟨⟨i, hi⟩, heq⟩
  have hgen' : N ⊔ Subgroup.closure (Set.range (fun i : Fin as.length => as[i.val])) = ⊤ := by
    rw [hs]
    exact hgen
  have hf : Function.Surjective f := linCoordMap_surjective π (QuotientGroup.mk'_surjective N)
    N (by rw [QuotientGroup.ker_mk']) _ hgen'
  have hpos := linCyclicOrders_pos N as
  have hdet := linRelationMatrix_det_ne e hpos C hc
  refine ⟨hdet, hf, linRelationMatrix_relations e C f hrel, ?_⟩
  rw [linRelationMatrix_det e C hc, ← Int.natAbsHom_apply, map_prod]
  simpa only [Int.natAbsHom_apply, Int.natAbs_natCast, e, Additive] using
    (linCyclicOrders_product N as hgen).symm

end GI.Impl
