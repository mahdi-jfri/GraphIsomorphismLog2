module

public import Workspace.Impl.LinPermChain

@[expose] public section

/-! The presentation certificate on permutation inputs. All quotient calculations
are carried out inside A = <as>, while the SLPs use ambient permutations. -/
namespace GI.Impl
open GI.Cited
open scoped IsMulCommutative

noncomputable def linIntoSubgroup {G : Type*} [Group G] (A : Subgroup G) (x : G) : A := by
  classical
  exact if hx : x ∈ A then ⟨x, hx⟩ else 1

@[simp] theorem linIntoSubgroup_val {G : Type*} [Group G] (A : Subgroup G) (x : G) (hx : x ∈ A) :
    A.subtype (linIntoSubgroup A x) = x := by
  classical
  simp [linIntoSubgroup, hx]

theorem linIntoSubgroup_map {G : Type*} [Group G] (A : Subgroup G) (xs : List G)
    (hxs : ∀ x ∈ xs, x ∈ A) : (xs.map (linIntoSubgroup A)).map A.subtype = xs := by
  simp only [List.map_map]
  calc
    _ = xs.map id := List.map_congr_left (by intro x hx; exact linIntoSubgroup_val A x (hxs x hx))
    _ = xs := List.map_id xs

/-- The complete presentation property, with the canonical quotient of A. -/
def linPermPresentation {n : ℕ} (ns as : List (Equiv.Perm (Fin n)))
    (M : Matrix (Fin as.length) (Fin as.length) ℤ) : Prop :=
  ∃ hN : ((gens ns).subgroupOf (gens as)).Normal,
    letI := hN
    ∃ hQ : IsMulCommutative ((gens as) ⧸ (gens ns).subgroupOf (gens as)),
      letI := hQ
      linPresentationCertificate M (linCoordMap (fun i : Fin as.length =>
        QuotientGroup.mk' ((gens ns).subgroupOf (gens as)) (linIntoSubgroup (gens as) as[i.val])))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem linPermCertificate {n : ℕ} (ns as : List (Equiv.Perm (Fin n)))
    (hle : gens ns ≤ gens as)
    (hc : ∀ x ∈ gens as, ∀ y ∈ gens as, x * y * x⁻¹ * y⁻¹ ∈ gens ns)
    (prog : Fin as.length → List SlpInstr) (C : Matrix (Fin as.length) (Fin as.length) ℤ)
    (hp : ∀ i, SlpReaches (ns ++ as.take i.val) (prog i)
      (as[i.val] ^ linCyclicOrders (gens ns) as i))
    (hC : ∀ i, linExponentValue (linPrefixVectors as.length ns.length i.val) (prog i) = some (C i)) :
    linPermPresentation ns as (linRelationMatrix (linCyclicOrders (gens ns) as) C) := by
  let A := gens as
  let N := (gens ns).subgroupOf A
  let bs := as.map (linIntoSubgroup A)
  let ms := ns.map (linIntoSubgroup A)
  have has : ∀ x ∈ as, x ∈ A := fun x hx => Subgroup.subset_closure hx
  have hns : ∀ x ∈ ns, x ∈ A := fun x hx => hle (Subgroup.subset_closure hx)
  have hbs : bs.map A.subtype = as := linIntoSubgroup_map A as has
  have hms : ms.map A.subtype = ns := linIntoSubgroup_map A ns hns
  have hNmap : N.map A.subtype = gens ns := Subgroup.map_subgroupOf_eq_of_le hle
  have hcomm : ∀ x y : A, x * y * x⁻¹ * y⁻¹ ∈ N := fun x y => hc x x.property y y.property
  letI hnormal : N.Normal := by
    have hh := linChain_normal N bs hcomm 0
    simpa only [linChain_zero] using hh
  letI hquot : IsMulCommutative (A ⧸ N) := linQuotient_comm N hcomm
  have hmN : ∀ x ∈ ms, x ∈ N := by
    intro x hx
    obtain ⟨g, hg, he⟩ := List.mem_map.mp (show x ∈ ns.map (linIntoSubgroup A) from hx)
    rw [← he]
    change A.subtype (linIntoSubgroup A g) ∈ gens ns
    rw [linIntoSubgroup_val A g (hns g hg)]
    exact Subgroup.subset_closure hg
  have htopMap : (⊤ : Subgroup A).map A.subtype = A := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_top, true_and]
    constructor
    · rintro ⟨a, rfl⟩; exact a.property
    · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
  have hgen : N ⊔ Subgroup.closure {x | x ∈ bs} = ⊤ := by
    apply (Subgroup.map_injective A.subtype_injective)
    have hh := linChain_map A.subtype N bs bs.length
    simp only [linChain, List.take_length, hNmap, hbs] at hh
    rw [htopMap, hh]
    change gens ns ⊔ Subgroup.closure {x | x ∈ as.take bs.length} = A
    have hlen : bs.length = as.length := by simp [bs]
    rw [hlen, List.take_length]
    exact sup_eq_right.mpr hle
  have hidx (i : ℕ) : (linChain N bs i).relIndex (linChain N bs (i + 1)) =
      (linChain (gens ns) as i).relIndex (linChain (gens ns) as (i + 1)) := by
    have hh := linChain_relIndex_map A.subtype A.subtype_injective N bs i
    simpa only [hNmap, hbs] using hh
  let π := QuotientGroup.mk' N
  let e := linCyclicOrders (gens ns) as
  let v : Fin as.length → A ⧸ N := fun i => π (linIntoSubgroup A as[i.val])
  let f := linCoordMap v
  let q := linCoordHom v
  have hlist : (List.finRange as.length).map (fun i => linIntoSubgroup A as[i.val]) = bs := by
    have hh : (List.finRange as.length).map (fun i => as[i.val]) = as := by
      apply List.ext_getElem (by simp)
      intro i hi hj
      simp
    simpa only [List.map_map, Function.comp_def] using congrArg (List.map (linIntoSubgroup A)) hh
  have himages : (List.finRange as.length).map v = bs.map π := by
    simpa only [List.map_map, Function.comp_def, v] using congrArg (List.map π) hlist
  have hnimages : ms.map π = List.replicate ns.length 1 := by
    have hh : ms.map π = List.replicate ms.length 1 := List.map_eq_replicate_iff.mpr
      (fun x hx => (QuotientGroup.eq_one_iff x).mpr (hmN x hx))
    simpa only [ms, List.length_map] using hh
  have hCearlier : linEarlierCoefficients C := by
    intro i j hij
    exact linExponentValue_zero _ j (linPrefixVectors_zero _ _ _ j hij) _ _ (hC i)
  have hrel : ∀ i, f (Pi.single i (e i : ℤ)) = f (C i) := by
    intro i
    have hg : (ms ++ bs.take i.val).map A.subtype = ns ++ as.take i.val := by
      rw [List.map_append, List.map_take, hms, hbs]
    have hpval : linSlpValue (ns ++ as.take i.val) (prog i) =
        some (as[i.val] ^ e i) := by
      obtain ⟨es, he, hlast⟩ := hp i
      simp only [linSlpValue, linSlpEntries_perm, he, Option.map_some, hlast]
      rfl
    have hpA : linSlpValue (ms ++ bs.take i.val) (prog i) =
        some (linIntoSubgroup A as[i.val] ^ e i) := by
      apply Option.map_injective A.subtype_injective
      rw [← linSlpValue_map, hg, hpval]
      simp only [Option.map_some, map_pow]
      rw [linIntoSubgroup_val A as[i.val] (has _ (List.getElem_mem i.isLt))]
    have hmatch : (ms ++ bs.take i.val).map π =
        ((linPrefixVectors as.length ns.length i.val).map Multiplicative.ofAdd).map q := by
      have hz : q (Multiplicative.ofAdd 0) = 1 := map_one q
      simp only [List.map_append, List.map_take, hnimages, linPrefixVectors,
        List.map_append, List.map_replicate, List.map_map, Function.comp_def, hz]
      rw [← himages]
      simp only [q, linCoordHom_single, zpow_one, List.map_take]
    have hh := linExponent_relation π q _ _ hmatch (prog i) _ hpA (C i) (hC i)
    have heq : q (Multiplicative.ofAdd (Pi.single i (e i : ℤ))) = q (Multiplicative.ofAdd (C i)) := by
      rw [linCoordHom_single, hh, map_pow]
      simp [v]
    exact congrArg Additive.ofMul heq
  have hs : Set.range (fun i : Fin as.length => linIntoSubgroup A as[i.val]) = {x | x ∈ bs} := by
    rw [← hlist]
    ext x
    simp only [List.mem_map, List.mem_finRange, true_and, Set.mem_setOf_eq, Set.mem_range]
  have hgen' : N ⊔ Subgroup.closure (Set.range (fun i : Fin as.length => linIntoSubgroup A as[i.val])) = ⊤ := by
    rw [hs]
    exact hgen
  have hf : Function.Surjective f := linCoordMap_surjective π (QuotientGroup.mk'_surjective N)
    N (by rw [QuotientGroup.ker_mk']) _ hgen'
  have hprod : ∏ i, e i = Nat.card (A ⧸ N) := by
    have hh := linChain_product_quotient N bs hgen
    have hlen : bs.length = as.length := by simp [bs]
    rw [hlen, Finset.prod_range] at hh
    rw [← hh]
    apply Finset.prod_congr rfl
    intro i _
    exact (hidx i.val).symm
  have hpos := linCyclicOrders_pos (gens ns) as
  have hdet := linRelationMatrix_det_ne e hpos C hCearlier
  refine ⟨hnormal, hquot, hdet, hf, linRelationMatrix_relations e C f hrel, ?_⟩
  rw [linRelationMatrix_det e C hCearlier, ← Int.natAbsHom_apply, map_prod]
  simpa only [Int.natAbsHom_apply, Int.natAbs_natCast] using
    (hprod.trans (Nat.card_congr Additive.toMul).symm).symm

end GI.Impl
