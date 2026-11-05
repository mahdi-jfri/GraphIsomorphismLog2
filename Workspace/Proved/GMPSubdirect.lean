module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

/-!
# Solvability of the normalizer quotient of a subdirect product

This is the solvability assertion of Guralnick--Maróti--Pyber, Lemma 2.2.
Each coordinate kernel maps onto the quotient, because the subgroup projects
onto that coordinate. Taking commutators lets us intersect these kernels.
Their full intersection is trivial, so the quotient is solvable.
-/

namespace GI.Proved

open scoped commutatorElement

private theorem gmp_finset_inf_normal {G : Type*} [Group G]
    {ι : Type*} (K : ι → Subgroup G) (hK : ∀ i, (K i).Normal) (s : Finset ι) :
    (s.inf K).Normal := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have := hK i
    have := ih
    simpa only [Finset.inf_insert] using
      (inferInstance : (K i ⊓ s.inf K).Normal)

/-- If every member of a finite family of normal subgroups maps onto a group,
then its derived series is covered by the images of successive intersections. -/
theorem gmp_derivedSeries_le_map_inf {G Q : Type*} [Group G] [Group Q]
    (q : G →* Q) (hq : Function.Surjective q) {ι : Type*}
    (K : ι → Subgroup G) (hK : ∀ i, (K i).Normal)
    (hmap : ∀ i, (K i).map q = ⊤) (s : Finset ι) :
    derivedSeries Q s.card ≤ (s.inf K).map q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Subgroup.map_top, q.range_eq_top_of_surjective hq]
  | @insert i s hi ih =>
    rw [Finset.card_insert_of_notMem hi, derivedSeries_succ, Finset.inf_insert]
    have := hK i
    have := gmp_finset_inf_normal K hK s
    have htop : derivedSeries Q s.card ≤ (K i).map q := by rw [hmap i]; exact le_top
    exact (Subgroup.commutator_le_map_commutator htop ih).trans
      (Subgroup.map_mono (Subgroup.commutator_le_inf _ _))

/-- A quotient covered by each of finitely many normal subgroups with trivial
intersection is solvable. No finiteness assumption on the groups is needed. -/
theorem gmp_solvable_of_normal_cover {G Q : Type*} [Group G] [Group Q]
    (q : G →* Q) (hq : Function.Surjective q) {ι : Type*} [Fintype ι]
    (K : ι → Subgroup G) (hK : ∀ i, (K i).Normal)
    (hmap : ∀ i, (K i).map q = ⊤) (hinf : (Finset.univ.inf K) = ⊥) :
    Group.IsSolvable Q := by
  refine ⟨⟨Fintype.card ι, le_bot_iff.mp ?_⟩⟩
  have h := gmp_derivedSeries_le_map_inf q hq K hK hmap Finset.univ
  simpa only [Finset.card_univ, hinf, Subgroup.map_bot] using h

/-- GMP, Lemma 2.2, also for any subgroup of the normalizer containing `J`.
The subdirect hypothesis says that `J` projects onto every factor. -/
theorem gmp_subdirect_quotient_solvable {ι : Type*} [Fintype ι]
    (X : ι → Type*) [∀ i, Group (X i)]
    (J N : Subgroup (∀ i, X i)) (hJN : J ≤ N) [(J.subgroupOf N).Normal]
    (hsub : ∀ i, Function.Surjective (fun j : J => j.val i)) :
    Group.IsSolvable (N ⧸ J.subgroupOf N) := by
  classical
  let q := QuotientGroup.mk' (J.subgroupOf N)
  let f (i : ι) : N →* X i := (Pi.evalMonoidHom X i).comp N.subtype
  let K (i : ι) : Subgroup N := (f i).ker
  have hmap (i : ι) : (K i).map q = ⊤ := by
    apply top_unique
    intro z _
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (J.subgroupOf N) z
    obtain ⟨j, hj⟩ := hsub i (n.val i)
    let jN : N := ⟨j.val, hJN j.property⟩
    have hjq : q jN = 1 := by
      exact (QuotientGroup.eq_one_iff jN).mpr j.property
    refine ⟨n * jN⁻¹, ?_, ?_⟩
    · change (n.val i) * (j.val i)⁻¹ = 1
      change j.val i = n.val i at hj
      rw [hj, mul_inv_cancel]
    · change q (n * jN⁻¹) = q n
      rw [map_mul, map_inv, hjq, inv_one, mul_one]
  have hinf : Finset.univ.inf K = ⊥ := by
    apply bot_unique
    intro n hn
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    funext i
    have hni : n ∈ K i := (Finset.inf_le (f := K) (Finset.mem_univ i) : Finset.univ.inf K ≤ K i) hn
    exact hni
  exact gmp_solvable_of_normal_cover q (QuotientGroup.mk'_surjective _)
    K (fun i => inferInstance) hmap hinf

/-- GMP, Lemma 2.2: the normalizer of a subdirect product has solvable quotient. -/
theorem gmp_subdirect_normalizer_quotient_solvable {ι : Type*} [Fintype ι]
    (X : ι → Type*) [∀ i, Group (X i)] (J : Subgroup (∀ i, X i))
    (hsub : ∀ i, Function.Surjective (fun j : J => j.val i)) :
    Group.IsSolvable (Subgroup.normalizer (J : Set (∀ i, X i)) ⧸
      J.subgroupOf (Subgroup.normalizer (J : Set (∀ i, X i)))) :=
  gmp_subdirect_quotient_solvable X J _ J.le_normalizer hsub

end GI.Proved
