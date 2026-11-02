import Workspace.PrimitiveTwoNormalDegree
import Workspace.SocleFactorKernel
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace GI.RadicalSocle

variable {G : Type*} [Group G] [Finite G]

theorem minimalNormal_card_two_le (N : MinimalNormals G) : 2 ≤ Nat.card N.val := by
  letI : Nontrivial N.val := (Subgroup.nontrivial_iff_ne_bot N.val).mpr N.property.2.1
  letI := Fintype.ofFinite N.val
  rw [Nat.card_eq_fintype_card]
  exact Fintype.one_lt_card

/-- Counts the actual intrinsic direct factors, rather than a supplied index set. -/
theorem minimalNormal_count_pow_le_card
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    (hsoc : socle G = ⊤) : 2 ^ Nat.card (MinimalNormals G) ≤ Nat.card G := by
  letI := Fintype.ofFinite (MinimalNormals G)
  have hc : Nat.card G = ∏ N : MinimalNormals G, Nat.card N.val := by
    rw [← Nat.card_congr (intrinsicProductEquiv radicalFree hsoc).toEquiv, Nat.card_pi]
  rw [hc, Nat.card_eq_fintype_card]
  calc
    2 ^ Fintype.card (MinimalNormals G) = ∏ _N : MinimalNormals G, 2 := by simp
    _ ≤ ∏ N : MinimalNormals G, Nat.card N.val :=
      Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun N _ => minimalNormal_card_two_le N)

theorem socle_intrinsic_count_pow_le_card
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥) :
    2 ^ Nat.card (MinimalNormals (socle G)) ≤ Nat.card (socle G) :=
  minimalNormal_count_pow_le_card
    (normal_subgroup_radicalFree radicalFree (socle G)) socle_idempotent

end GI.RadicalSocle

namespace GI.PrimitiveStructure

open RadicalSocle

variable {G V : Type*} [Group G] [Finite G] [MulAction G V] [FaithfulSMul G V]
variable [MulAction.IsPreprimitive G V]

/-- The factor count is tied to the physical action degree in the actual
two-minimal-normal case. -/
theorem two_minimal_intrinsic_count_pow_le_degree_sq {M N : Subgroup G}
    (hM : MinimalNormal M) (hN : MinimalNormal N) (hne : M ≠ N) (a : V) :
    2 ^ Nat.card (MinimalNormals (socle G)) ≤ (Nat.card V) ^ 2 := by
  rw [← two_minimal_socle_card_eq_degree_sq hM hN hne a]
  exact socle_intrinsic_count_pow_le_card (two_minimal_radical_free hM hN hne a)

theorem two_minimal_intrinsic_count_log_degree {M N : Subgroup G}
    (hM : MinimalNormal M) (hN : MinimalNormal N) (hne : M ≠ N) (a : V) :
    (Nat.card (MinimalNormals (socle G)) : ℝ) ≤
      (2 / Real.log 2) * Real.log (Nat.card V : ℝ) := by
  have hp := two_minimal_intrinsic_count_pow_le_degree_sq hM hN hne a
  have hpr : (2 : ℝ) ^ Nat.card (MinimalNormals (socle G)) ≤ (Nat.card V : ℝ) ^ 2 := by
    exact_mod_cast hp
  have hlog := Real.log_le_log
    (pow_pos (by norm_num : (0 : ℝ) < 2) _) hpr
  rw [Real.log_pow, Real.log_pow] at hlog
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    (Nat.card (MinimalNormals (socle G)) : ℝ) ≤
        (2 * Real.log (Nat.card V : ℝ)) / Real.log 2 :=
      (le_div_iff₀ hpos).mpr (by simpa using hlog)
    _ = (2 / Real.log 2) * Real.log (Nat.card V : ℝ) := by ring

end GI.PrimitiveStructure
