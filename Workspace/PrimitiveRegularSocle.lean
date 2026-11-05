module

public import Workspace.PrimitiveMinimalNormals
public import Mathlib.GroupTheory.NoncommCoprod

@[expose] public section

namespace GI.PrimitiveStructure

open RadicalSocle

variable {G : Type*} [Group G]

/-- The actual multiplication homomorphism of two distinct minimal normal
subgroups; their commutation is proved by minimal normality. -/
def minimalNormalPairHom {M N : Subgroup G}
    (hM : MinimalNormal M) (hN : MinimalNormal N) (hne : M ≠ N) : M × N →* G :=
  M.subtype.noncommCoprod N.subtype (minimalNormal_commute hM hN hne)

theorem minimalNormalPairHom_injective {M N : Subgroup G}
    (hM : MinimalNormal M) (hN : MinimalNormal N) (hne : M ≠ N) :
    Function.Injective (minimalNormalPairHom hM hN hne) := by
  apply (MonoidHom.noncommCoprod_injective M.subtype N.subtype _).mpr
  refine ⟨M.subtype_injective, N.subtype_injective, ?_⟩
  rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff_inf_le,
    minimalNormal_inf_eq_bot hM hN hne]

theorem minimalNormalPairHom_range {M N : Subgroup G}
    (hM : MinimalNormal M) (hN : MinimalNormal N) (hne : M ≠ N) :
    (minimalNormalPairHom hM hN hne).range = M ⊔ N := by
  exact (MonoidHom.noncommCoprod_range M.subtype N.subtype _).trans (by
    rw [Subgroup.range_subtype, Subgroup.range_subtype])

section Action

variable {V : Type*} [MulAction G V] [FaithfulSMul G V]

omit [FaithfulSMul G V] in
/-- Commuting regular subgroups are actually isomorphic, via inversion
and their evaluation bijections at a common point. -/
noncomputable def commutingRegularEquiv (M N : Subgroup G) (a : V)
    (comm : ∀ m : M, ∀ n : N, (m : G) * (n : G) = (n : G) * (m : G))
    (hM : Function.Bijective (fun m : M => m • a))
    (hN : Function.Bijective (fun n : N => n • a)) : M ≃* N := by
  let eM : M ≃ V := Equiv.ofBijective _ hM
  let eN : N ≃ V := Equiv.ofBijective _ hN
  let e : M ≃ N := (Equiv.inv M).trans (eM.trans eN.symm)
  have heval (m : M) : e m • a = m⁻¹ • a := by
    change eN (eN.symm (eM m⁻¹)) = eM m⁻¹
    exact eN.apply_symm_apply _
  refine { e with map_mul' := ?_ }
  intro x y
  apply hN.injective
  change e (x * y) • a = (e x * e y) • a
  calc
    e (x * y) • a = (x * y)⁻¹ • a := heval _
    _ = y⁻¹ • (x⁻¹ • a) := by rw [mul_inv_rev, mul_smul]
    _ = y⁻¹ • (e x • a) := by rw [heval]
    _ = e x • (y⁻¹ • a) := by
      change (y⁻¹ : G) • ((e x : G) • a) = (e x : G) • ((y⁻¹ : G) • a)
      have hc : (y : G)⁻¹ * (e x : G) = (e x : G) * (y : G)⁻¹ := by
        simpa only [Subgroup.coe_inv] using comm y⁻¹ (e x)
      rw [← mul_smul, hc, mul_smul]
    _ = e x • (e y • a) := by rw [heval]
    _ = (e x * e y) • a := (mul_smul _ _ _).symm

variable [MulAction.IsPreprimitive G V]

noncomputable def distinctMinimalNormalsEquiv {M N : Subgroup G}
    (hM : MinimalNormal M) (hN : MinimalNormal N) (hne : M ≠ N) (a : V) : M ≃* N :=
  commutingRegularEquiv M N a (minimalNormal_commute hM hN hne)
    (distinct_minimal_normals_regular hM hN hne a).1
    (distinct_minimal_normals_regular hM hN hne a).2

/-- In the case of two minimal normal subgroups the full socle is their
actual direct product, without a supplied decomposition. -/
noncomputable def twoMinimalSocleEquiv {M N : Subgroup G}
    (hM : MinimalNormal M) (hN : MinimalNormal N) (hne : M ≠ N) (a : V) :
    (M × N) ≃* socle G :=
  (MonoidHom.ofInjective (minimalNormalPairHom_injective hM hN hne)).trans
    (MulEquiv.subgroupCongr ((minimalNormalPairHom_range hM hN hne).trans
      (socle_eq_sup_of_distinct_minimal_normals hM hN hne a).symm))

/-- The exact square-degree identity underlying the two-regular-normal
case of the primitive degree estimate. -/
theorem two_minimal_socle_card_eq_degree_sq {M N : Subgroup G}
    (hM : MinimalNormal M) (hN : MinimalNormal N) (hne : M ≠ N) (a : V) :
    Nat.card (socle G) = (Nat.card V) ^ 2 := by
  rw [← Nat.card_congr (twoMinimalSocleEquiv hM hN hne a).toEquiv, Nat.card_prod,
    (distinct_minimal_normals_card_degree hM hN hne a).1,
    (distinct_minimal_normals_card_degree hM hN hne a).2, pow_two]

end Action
end GI.PrimitiveStructure
