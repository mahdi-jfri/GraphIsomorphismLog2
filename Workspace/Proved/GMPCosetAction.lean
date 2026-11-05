module

public import Workspace.Proved.GMPTransitive
public import Workspace.RadicalCentralizers

@[expose] public section

/-!
# The chief-factor coset action for the radical computation

Conjugation on `U/V`, viewed inside the ambient quotient, has kernel
equal to the preimage of its centralizer. For a nonabelian chief factor,
the number of these cosets is bounded by the nonabelian composition
product of the quotient by the transitive normal subgroup.
-/

namespace GI.Proved

open GI.Composition GI.RadicalSocle GI.RadicalFreeOrder GI.PrimitiveStructure

variable {H : Type*} [Group H]

/-- Forgetting the automorphism structure in conjugation does not
change its kernel: it is the centralizer of the normal subgroup. -/
theorem gmp_conjugation_ker (U : Subgroup H) [U.Normal] :
    ((MulAut.toPerm U).comp (MulAut.conjNormal (H := U))).ker =
      Subgroup.centralizer (U : Set H) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx u hu
    have h := congrArg (fun p : Equiv.Perm U => (p ⟨u, hu⟩ : H)) hx
    change x * u * x⁻¹ = u at h
    calc
      u * x = (x * u * x⁻¹) * x := congrArg (fun y => y * x) h.symm
      _ = x * u := by group
  · intro hx
    apply Equiv.ext
    intro u
    apply Subtype.ext
    change x * u.val * x⁻¹ = u.val
    rw [← hx u.val u.property, mul_assoc, mul_inv_cancel, mul_one]

/-- Conjugation on the right cosets of `V` in `U`, represented as the
image of `U` in `H/V`. Normality of both terms makes this an action. -/
def gmpCosetAction (U V : Subgroup H) [U.Normal] [V.Normal] :
    H →* Equiv.Perm (U.map (QuotientGroup.mk' V)) := by
  have : (U.map (QuotientGroup.mk' V)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective V)
  exact ((MulAut.toPerm (U.map (QuotientGroup.mk' V))).comp
    (MulAut.conjNormal (H := U.map (QuotientGroup.mk' V)))).comp (QuotientGroup.mk' V)

/-- The kernel computed by fixing all coset labels is exactly the
quotient-centralizer preimage used in the radical characterization. -/
theorem gmpCosetAction_ker (U V : Subgroup H) [U.Normal] [V.Normal] :
    (gmpCosetAction U V).ker = GI.RadicalCentralizers.centPre U V inferInstance := by
  have : (U.map (QuotientGroup.mk' V)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective V)
  change (((MulAut.toPerm (U.map (QuotientGroup.mk' V))).comp
    (MulAut.conjNormal (H := U.map (QuotientGroup.mk' V)))).comp
      (QuotientGroup.mk' V)).ker = _
  rw [← MonoidHom.comap_ker, gmp_conjugation_ker]
  rfl

/-- The image model has exactly one point per right coset. -/
theorem gmpCosetAction_degree (U V : Subgroup H) [V.Normal] :
    Nat.card (U.map (QuotientGroup.mk' V)) = (V.subgroupOf U).index := by
  let f := (QuotientGroup.mk' V).comp U.subtype
  have hrange : f.range = U.map (QuotientGroup.mk' V) := by
    change ((QuotientGroup.mk' V).comp U.subtype).range = _
    rw [← MonoidHom.map_range, Subgroup.range_subtype]
  have hker : f.ker = V.subgroupOf U := by
    ext u
    exact QuotientGroup.eq_one_iff u.val
  have h := Subgroup.index_ker f
  rw [hrange, hker] at h
  exact h.symm

/-- A nonabelian minimal normal subgroup has no abelian composition
factors, even when the ambient group has a nontrivial solvable radical. -/
theorem gmp_nonabelian_minimal_bFac [Finite H] (M : Subgroup H)
    (hM : MinimalNormal M) (hna : ¬ ∀ x y : M, x * y = y * x) :
    bFac M = Nat.card M := by
  have hrad : solvableRadical M = ⊥ := by
    rcases minimalNormal_characteristic_subgroup hM (solvableRadical M) with hb | ht
    · exact hb
    · let e : solvableRadical M ≃* M :=
        (MulEquiv.subgroupCongr ht).trans Subgroup.topEquiv
      have := Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
      exact (hna (minimalNormal_solvable_comm hM)).elim
  have rf : ∀ K : Subgroup M, K.Normal → Group.IsSolvable K → K = ⊥ := by
    intro K hK hs
    have := hK
    have := hs
    have h := le_solvableRadical K
    rw [hrad] at h
    exact le_bot_iff.mp h
  let e : socle M ≃* M :=
    (MulEquiv.subgroupCongr (minimalNormal_socle_eq_top hM)).trans Subgroup.topEquiv
  calc
    bFac M = bFac (socle M) := (bFac_congr e).symm
    _ = Nat.card (socle M) := bFac_socle rf
    _ = Nat.card M := Nat.card_congr e.toEquiv

/-- The nonabelian product of the ambient group pays for the whole
order of each nonabelian chief factor. -/
theorem gmp_nonabelian_minimal_card_le [Finite H] (M : Subgroup H)
    (hM : MinimalNormal M) (hna : ¬ ∀ x y : M, x * y = y * x) :
    Nat.card M ≤ bFac H := by
  have := hM.1
  rw [bFac_mul M, gmp_nonabelian_minimal_bFac M hM hna]
  exact Nat.le_mul_of_pos_right _ bFac_pos

/-- The coset-action degree for a nonabelian chief factor above a
transitive normal kernel lies within the quasipolynomial GMP bound. -/
theorem gmpCosetAction_degree_bound {n : ℕ} (hn : 1 ≤ n)
    (A : Subgroup (Equiv.Perm (Fin n))) (N U V : Subgroup A)
    [N.Normal] [U.Normal] [V.Normal] [MulAction.IsPretransitive N (Fin n)]
    (hNV : N ≤ V) (hchief : MinimalNormal (U.map (QuotientGroup.mk' V)))
    (hna : ¬ ∀ x y : U.map (QuotientGroup.mk' V), x * y = y * x) :
    (Nat.card (U.map (QuotientGroup.mk' V)) : ℝ) ≤ (n : ℝ) ^ Real.logb 2 n := by
  have hnat := (gmp_nonabelian_minimal_card_le _ hchief hna).trans
    (gmp_bFac_quotient_antitone N V hNV)
  exact (show (Nat.card (U.map (QuotientGroup.mk' V)) : ℝ) ≤
    (bFac (A ⧸ N) : ℝ) by exact_mod_cast hnat).trans (gmp_degreeBound n hn A N)

end GI.Proved
