module

public import Workspace.Proved.GMPProducts
public import Workspace.RadicalFreeOrder
public import Workspace.Schreier

@[expose] public section

/-!
# The solvable outer layer in the GMP bound

For a radical-free finite group, the kernel of the action on the simple
socle factors maps to their outer automorphism groups, with socle kernel.
Schreier's theorem makes the image solvable. Thus, after quotienting by
the socle, only the permutation action on the factors contributes to `b`.
-/

namespace GI.Proved

open GI.Composition GI.RadicalSocle GI.RadicalFreeOrder GI.SocleOuter

universe u

/-- A finite product of solvable groups is solvable. -/
theorem gmp_solvable_pi {ι : Type u} [Fintype ι]
    (X : ι → Type u) [∀ i, Group (X i)] (hX : ∀ i, Group.IsSolvable (X i)) :
    Group.IsSolvable (∀ i, X i) := by
  revert X
  refine Fintype.induction_empty_option (P := fun ι _ =>
    ∀ (X : ι → Type u) [∀ i, Group (X i)],
      (∀ i, Group.IsSolvable (X i)) → Group.IsSolvable (∀ i, X i)) ?_ ?_ ?_ ι
  · intro α β _ e ih X _ hX
    have := ih (fun i => X (e i)) (fun i => hX (e i))
    exact Group.isSolvable_of_surjective
      (f := (piCongrMulEquiv e X).symm.toMonoidHom) (piCongrMulEquiv e X).symm.surjective
  · intro X _ _
    infer_instance
  · intro α _ ih X _ hX
    have := hX none
    have := ih (fun i => X (some i)) (fun i => hX (some i))
    exact Group.isSolvable_of_surjective
      (f := (piOptionMulEquiv X).symm.toMonoidHom) (piOptionMulEquiv X).symm.surjective

variable {G : Type u} [Group G] [Finite G]

/-- Schreier's theorem applies to each actual simple factor of the socle. -/
theorem gmp_socle_outer_solvable
    (rf : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) :
    Group.IsSolvable (∀ N : MinimalNormals (socle G), OuterAut N.val) := by
  letI := Fintype.ofFinite (MinimalNormals (socle G))
  apply gmp_solvable_pi
  intro N
  have := socle_intrinsic_factor_simple N
  exact GI.schreier N.val (socle_intrinsic_factor_nonabelian rf N)

/-- The kernel of the factor action has exactly the nonabelian product
of the socle. Its remaining quotient is solvable by Schreier's theorem. -/
theorem gmp_bFac_factorAction_kernel
    (rf : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) :
    bFac (factorAction (G := G)).ker = Nat.card (socle G) := by
  have := gmp_socle_outer_solvable rf
  have hker : bFac (kernelToOuter (G := G)).ker = Nat.card (socle G) := by
    rw [bFac_congr (MulEquiv.subgroupCongr (kernelToOuter_ker rf)),
      ← bFac_congr (MonoidHom.ofInjective (f := socleToKernel (G := G))
        (Subgroup.inclusion_injective _)), bFac_socle rf]
  rw [bFac_ker_range (kernelToOuter (G := G)), hker, bFac_of_solvable, mul_one]

/-- The nonabelian composition product above the socle equals that of
the induced permutation group on the simple factors. -/
theorem gmp_bFac_quotient_socle
    (rf : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) :
    bFac (G ⧸ socle G) = bFac (factorAction (G := G)).range := by
  have h := bFac_ker_range (factorAction (G := G))
  rw [gmp_bFac_factorAction_kernel rf, bFac_mul (socle G), bFac_socle rf] at h
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h

/-- In particular, the quotient above the socle has nonabelian product
at most the factorial of the number of simple socle factors. -/
theorem gmp_bFac_quotient_socle_le_factorial
    (rf : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) :
    bFac (G ⧸ socle G) ≤ (Nat.card (MinimalNormals (socle G))).factorial := by
  rw [gmp_bFac_quotient_socle rf]
  calc
    bFac (factorAction (G := G)).range ≤
        Nat.card (Equiv.Perm (MinimalNormals (socle G))) :=
      bFac_le_card.trans (Subgroup.card_le_card_group _)
    _ = _ := Nat.card_perm

end GI.Proved
