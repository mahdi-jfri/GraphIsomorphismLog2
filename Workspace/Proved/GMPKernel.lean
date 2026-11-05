module

public import Workspace.Proved.GMPSubdirect
public import Workspace.Proved.GMPProducts

@[expose] public section

/-!
# The solvable kernel in GMP, Theorem 2.3

The proof of Lemma 2.2 also works when each coordinate kernel covers
the first derived subgroup of the quotient. This proves solvability
of the intermediate quotient in Theorem 2.3 without naming the two
intermediate products of coordinate subgroups.
-/

namespace GI.Proved

open GI.Composition
open scoped commutatorElement

private theorem gmp_inf_normal {K : Type*} [Group K] {ι : Type*}
    (L : ι → Subgroup K) (hL : ∀ i, (L i).Normal) (s : Finset ι) :
    (s.inf L).Normal := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have := hL i
    have := ih
    simpa only [Finset.inf_insert] using
      (inferInstance : (L i ⊓ s.inf L).Normal)

/-- The normal-cover argument, starting at any term of the derived series. -/
theorem gmp_derivedSeries_shift_le_map_inf {K Q : Type*} [Group K] [Group Q]
    (q : K →* Q) {ι : Type*} (L : ι → Subgroup K)
    (hL : ∀ i, (L i).Normal) (d : ℕ)
    (hmap : ∀ i, derivedSeries Q d ≤ (L i).map q) (s : Finset ι)
    (hq : Function.Surjective q) :
    derivedSeries Q (d + s.card) ≤ (s.inf L).map q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Subgroup.map_top, q.range_eq_top_of_surjective hq]
  | @insert i s hi ih =>
    rw [Finset.card_insert_of_notMem hi, ← Nat.add_assoc, derivedSeries_succ,
      Finset.inf_insert]
    have := hL i
    have := gmp_inf_normal L hL s
    have hfirst : derivedSeries Q (d + s.card) ≤ (L i).map q :=
      (derivedSeries_antitone (G := Q) (Nat.le_add_right d s.card)).trans (hmap i)
    exact (Subgroup.commutator_le_map_commutator hfirst ih).trans
      (Subgroup.map_mono (Subgroup.commutator_le_inf _ _))

/-- If each coordinate of the derived subgroup lies in the corresponding
projection of a normal subgroup, its quotient is solvable. -/
theorem gmp_quotient_solvable_of_derived_projections
    {K : Type*} [Group K] (J : Subgroup K) [J.Normal]
    {ι : Type*} [Fintype ι] (X : ι → Type*) [∀ i, Group (X i)]
    (f : ∀ i, K →* X i) (hfaithful : ∀ k, (∀ i, f i k = 1) → k = 1)
    (hder : ∀ i, (derivedSeries K 1).map (f i) ≤ J.map (f i)) :
    Group.IsSolvable (K ⧸ J) := by
  classical
  let q := QuotientGroup.mk' J
  have hmap (i : ι) : derivedSeries (K ⧸ J) 1 ≤ (f i).ker.map q := by
    rw [← map_derivedSeries_eq (f := q) (QuotientGroup.mk'_surjective J) 1]
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨j, hj, hfj⟩ := hder i (Subgroup.mem_map_of_mem (f i) hk)
    have hjq : q j = 1 := (QuotientGroup.eq_one_iff j).mpr hj
    refine ⟨k * j⁻¹, ?_, ?_⟩
    · change f i (k * j⁻¹) = 1
      rw [map_mul, map_inv, hfj, mul_inv_cancel]
    · rw [map_mul, map_inv, hjq, inv_one, mul_one]
  have hinf : Finset.univ.inf (fun i => (f i).ker) = ⊥ := by
    apply bot_unique
    intro k hk
    apply Subgroup.mem_bot.mpr
    apply hfaithful k
    intro i
    exact (Finset.inf_le (f := fun i => (f i).ker) (Finset.mem_univ i) :
      Finset.univ.inf (fun i => (f i).ker) ≤ (f i).ker) hk
  refine ⟨⟨1 + Fintype.card ι, le_bot_iff.mp ?_⟩⟩
  have h := gmp_derivedSeries_shift_le_map_inf q (fun i => (f i).ker)
    (fun i => inferInstance) 1 hmap Finset.univ (QuotientGroup.mk'_surjective J)
  simpa only [Finset.card_univ, hinf, Subgroup.map_bot] using h

/-- The base-kernel bound of GMP, Theorem 2.3. The commutator condition
comes from normality in the wreath product. Transitivity of its top
action supplies `hdet`, which determines all coordinates modulo `M`
from one coordinate. -/
theorem gmp_wreath_kernel_bound {K : Type*} [Group K] [Finite K]
    (J : Subgroup K) [J.Normal] {ι : Type*} [Fintype ι]
    (X : ι → Type*) [∀ i, Group (X i)] [∀ i, Finite (X i)]
    (f : ∀ i, K →* X i) (M : ∀ i, Subgroup (X i)) [∀ i, (M i).Normal]
    (i₀ : ι) (hfaithful : ∀ k, (∀ i, f i k = 1) → k = 1)
    (hJ : ∀ i, J ≤ (M i).comap (f i))
    (hdet : ∀ k, f i₀ k ∈ M i₀ → ∀ i, f i k ∈ M i)
    (hcomm : ∀ i k l, (∀ j, f j l ∈ M j) → ⁅f i k, f i l⁆ ∈ J.map (f i)) :
    bFac (K ⧸ J) ≤ bFac (X i₀ ⧸ M i₀) := by
  let q : K →* X i₀ ⧸ M i₀ := (QuotientGroup.mk' (M i₀)).comp (f i₀)
  have hJL : J ≤ q.ker := by
    intro j hj
    exact (QuotientGroup.eq_one_iff _).mpr (hJ i₀ hj)
  let fs (i : ι) : q.ker →* X i := (f i).comp q.ker.subtype
  have hfaithful' : ∀ k : q.ker, (∀ i, fs i k = 1) → k = 1 := by
    intro k hk
    exact Subtype.ext (hfaithful k.val hk)
  have hder (i : ι) : (derivedSeries q.ker 1).map (fs i) ≤
      (J.subgroupOf q.ker).map (fs i) := by
    change (⁅(⊤ : Subgroup q.ker), ⊤⁆ : Subgroup q.ker).map (fs i) ≤ _
    rw [Subgroup.map_le_iff_le_comap]
    apply Subgroup.commutator_le.mpr
    intro k _ l _
    obtain ⟨j, hj, hfj⟩ := hcomm i k.val l.val
      (hdet l.val ((QuotientGroup.eq_one_iff _).mp l.property))
    refine ⟨⟨j, hJL hj⟩, hj, ?_⟩
    change f i j = f i ⁅k.val, l.val⁆
    rw [map_commutatorElement]
    exact hfj
  have := gmp_quotient_solvable_of_derived_projections (J.subgroupOf q.ker)
    X fs hfaithful' hder
  rw [gmp_bFac_quotient_chain J q.ker hJL, bFac_of_solvable, one_mul,
    bFac_congr (QuotientGroup.quotientKerEquivRange q)]
  exact gmp_bFac_subgroup_le q.range

end GI.Proved
