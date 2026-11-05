module

public import Workspace.RadicalSocleSimpleFactors
public import Mathlib.Algebra.Group.Equiv.Basic

@[expose] public section

namespace GI.RadicalSocle

variable {G : Type*} [Group G]

/-- Actual simple factors are obtained by taking minimal normal subgroups
inside each actual minimal normal subgroup. -/
abbrev SimpleFactors (G : Type*) [Group G] :=
  Σ N : MinimalNormals G, MinimalNormals N.val

abbrev SimpleFactor (i : SimpleFactors G) := i.2.val

def simpleFactorsCurry :
    (∀ i : SimpleFactors G, SimpleFactor i) ≃*
      (∀ N : MinimalNormals G, ∀ K : MinimalNormals N.val, K.val) where
  toFun f N K := f ⟨N, K⟩
  invFun f i := f i.1 i.2
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem simpleFactor_isSimple [Finite G] (i : SimpleFactors G) :
    IsSimpleGroup (SimpleFactor i) :=
  minimalNormal_simple_factors i.1.property i.2

theorem simpleFactor_nonabelian [Finite G]
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    (i : SimpleFactors G) : ∃ x y : SimpleFactor i, x * y ≠ y * x :=
  minimalNormal_factors_nonabelian radicalFree i.1.property i.2

/-- The actual socle is a direct product of actual finite nonabelian simple
groups. Every factor and the product equivalence are constructed here. -/
noncomputable def socleSimpleProductEquiv [Finite G]
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥) :
    (∀ i : SimpleFactors G, SimpleFactor i) ≃* socle G :=
  simpleFactorsCurry.trans
    ((MulEquiv.piCongrRight (fun N : MinimalNormals G =>
      minimalNormalProductEquiv radicalFree N.property)).trans
        (socleProductEquiv radicalFree))

theorem socle_card_simple_product [Finite G] [Fintype (SimpleFactors G)]
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥) :
    Nat.card (socle G) = ∏ i : SimpleFactors G, Nat.card (SimpleFactor i) := by
  rw [← Nat.card_congr (socleSimpleProductEquiv radicalFree).toEquiv, Nat.card_pi]

theorem simpleFactor_card_two_le [Finite G] (i : SimpleFactors G) :
    2 ≤ Nat.card (SimpleFactor i) := by
  letI := simpleFactor_isSimple i
  letI := Fintype.ofFinite (SimpleFactor i)
  rw [Nat.card_eq_fintype_card]
  exact Fintype.one_lt_card

/-- The number of actual simple factors is logarithmic in the socle's
order, stated in an integral form that needs no rounding convention. -/
theorem two_pow_factor_count_le_socle_card [Finite G] [Fintype (SimpleFactors G)]
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥) :
    2 ^ Nat.card (SimpleFactors G) ≤ Nat.card (socle G) := by
  rw [socle_card_simple_product radicalFree, Nat.card_eq_fintype_card]
  calc
    2 ^ Fintype.card (SimpleFactors G) = ∏ _i : SimpleFactors G, 2 := by simp
    _ ≤ ∏ i : SimpleFactors G, Nat.card (SimpleFactor i) :=
      Finset.prod_le_prod (fun i _ => simpleFactor_card_two_le i)

/-- An unconditional decomposition for the actual solvable-radical quotient. -/
noncomputable def radical_quotient_socleSimpleProductEquiv [Finite G] :
    (∀ i : SimpleFactors (G ⧸ solvableRadical G), SimpleFactor i) ≃*
      socle (G ⧸ solvableRadical G) :=
  socleSimpleProductEquiv radical_quotient_radicalFree

theorem radical_quotient_simpleFactor_nonabelian [Finite G]
    (i : SimpleFactors (G ⧸ solvableRadical G)) :
    ∃ x y : SimpleFactor i, x * y ≠ y * x :=
  simpleFactor_nonabelian radical_quotient_radicalFree i

end GI.RadicalSocle
