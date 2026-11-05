module

public import Workspace.PrimitiveSocleBudget

@[expose] public section

namespace GI.SocleOuter

open RadicalSocle

variable {G : Type*} [Group G] [Finite G]

/-- A quadratic actual socle-order bound gives a logarithmic bound on
the number of its actual intrinsic simple factors. -/
theorem quadratic_socle_factor_log_bound
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    {d : ℕ} (orderBound : Nat.card (socle G) ≤ d ^ 2) :
    (Nat.card (MinimalNormals (socle G)) : ℝ) ≤
      (2 / Real.log 2) * Real.log (d : ℝ) := by
  have hp := (socle_intrinsic_count_pow_le_card radicalFree).trans orderBound
  have hpr : (2 : ℝ) ^ Nat.card (MinimalNormals (socle G)) ≤ (d : ℝ) ^ 2 := by
    exact_mod_cast hp
  have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _) hpr
  rw [Real.log_pow, Real.log_pow] at hlog
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    (Nat.card (MinimalNormals (socle G)) : ℝ) ≤ (2 * Real.log (d : ℝ)) / Real.log 2 :=
      (le_div_iff₀ hpos).mpr (by simpa using hlog)
    _ = (2 / Real.log 2) * Real.log (d : ℝ) := by ring

/-- Both proved kernel charges are logarithmic when actual socle order
is at most the square of the degree parameter. -/
theorem quadratic_socle_inner_factor_log_bound
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    {d : ℕ} (orderBound : Nat.card (socle G) ≤ d ^ 2) :
    (6 * padicValNat 3 (Nat.card (socle G)) +
      3 * (Nat.card (MinimalNormals (socle G)) - 1) : ℕ) ≤
      (12 / Real.log 3 + 6 / Real.log 2) * Real.log (d : ℝ) := by
  have hval := valuation_log_bound (by decide : 2 ≤ 3) (Nat.card_pos (α := socle G))
  have hposcard : (0 : ℝ) < Nat.card (socle G) := by
    exact_mod_cast (Nat.card_pos (α := socle G))
  have hlogcard := Real.log_le_log hposcard
    (show (Nat.card (socle G) : ℝ) ≤ (d : ℝ) ^ 2 by exact_mod_cast orderBound)
  rw [Real.log_pow] at hlogcard
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hvalBound : (padicValNat 3 (Nat.card (socle G)) : ℝ) ≤
      (2 / Real.log 3) * Real.log (d : ℝ) := by
    calc
      (padicValNat 3 (Nat.card (socle G)) : ℝ) ≤ (2 * Real.log (d : ℝ)) / Real.log 3 :=
        (le_div_iff₀ hlog3).mpr (by simpa only [Nat.cast_ofNat] using hval.trans hlogcard)
      _ = (2 / Real.log 3) * Real.log (d : ℝ) := by ring
  have hcount := quadratic_socle_factor_log_bound radicalFree orderBound
  have hsmall : 3 * (Nat.card (MinimalNormals (socle G)) - 1) ≤
      3 * Nat.card (MinimalNormals (socle G)) :=
    Nat.mul_le_mul_left 3 (Nat.sub_le _ _)
  calc
    (6 * padicValNat 3 (Nat.card (socle G)) +
        3 * (Nat.card (MinimalNormals (socle G)) - 1) : ℕ) ≤
        6 * (padicValNat 3 (Nat.card (socle G)) : ℝ) +
          3 * (Nat.card (MinimalNormals (socle G)) : ℝ) := by
      exact_mod_cast Nat.add_le_add_left hsmall (6 * padicValNat 3 (Nat.card (socle G)))
    _ ≤ 6 * ((2 / Real.log 3) * Real.log (d : ℝ)) +
          3 * ((2 / Real.log 2) * Real.log (d : ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left hvalBound (by norm_num))
        (mul_le_mul_of_nonneg_left hcount (by norm_num))
    _ = (12 / Real.log 3 + 6 / Real.log 2) * Real.log (d : ℝ) := by ring

/-- Every hereditary chain is reduced to an actual outer-factor chain,
with the entire inner and factor-permutation cost charged to log degree. -/
theorem quadratic_socle_chain_outer_reduction
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    {d : ℕ} (orderBound : Nat.card (socle G) ≤ d ^ 2)
    {cutoff w : ℕ} (hcutoff : 64 ≤ cutoff) {H : Subgroup G}
    (chain : QuotientChain cutoff H w) :
    ∃ v : ℕ, (w : ℝ) ≤
        (12 / Real.log 3 + 6 / Real.log 2) * Real.log (d : ℝ) + v ∧
      QuotientChain cutoff
        (⊤ : Subgroup (∀ K : MinimalNormals (socle G), OuterAut K.val)) v := by
  obtain ⟨v, hv, chainv⟩ := radicalFree_chain_outer_reduction radicalFree hcutoff chain
  refine ⟨v, ?_, chainv⟩
  calc
    (w : ℝ) ≤ (6 * padicValNat 3 (Nat.card (socle G)) +
        3 * (Nat.card (MinimalNormals (socle G)) - 1) : ℕ) + (v : ℝ) := by exact_mod_cast hv
    _ ≤ (12 / Real.log 3 + 6 / Real.log 2) * Real.log (d : ℝ) + v :=
      add_le_add_left (quadratic_socle_inner_factor_log_bound radicalFree orderBound) _

variable {V : Type*} [Fintype V] {H : Subgroup (Equiv.Perm V)}

/-- Applies the generic hereditary reduction to an actual marked chain. -/
theorem quadratic_socle_marked_chain_outer_reduction
    (radicalFree : ∀ N : Subgroup H, N.Normal → IsSolvable N → N = ⊥)
    {d : ℕ} (orderBound : Nat.card (socle H) ≤ d ^ 2)
    {cutoff w : ℕ} (hcutoff : 64 ≤ cutoff) {a : V}
    (chain : MarkedChain cutoff a H w) :
    ∃ v : ℕ, (w : ℝ) ≤
        (12 / Real.log 3 + 6 / Real.log 2) * Real.log (d : ℝ) + v ∧
      QuotientChain cutoff
        (⊤ : Subgroup (∀ K : MinimalNormals (socle H), OuterAut K.val)) v := by
  exact quadratic_socle_chain_outer_reduction radicalFree orderBound hcutoff
    (QuotientExtension.chain_subgroupOf chain.toQuotientChain le_rfl)

/-- The full sigma chain yields an explicit residual outer-factor chain. -/
theorem quadratic_socle_sigma_outer_reduction
    (radicalFree : ∀ N : Subgroup H, N.Normal → IsSolvable N → N = ⊥)
    {d : ℕ} (orderBound : Nat.card (socle H) ≤ d ^ 2)
    {cutoff : ℕ} (hcutoff : 64 ≤ cutoff) (a : V) :
    ∃ v : ℕ, (sigma cutoff a H : ℝ) ≤
        (12 / Real.log 3 + 6 / Real.log 2) * Real.log (d : ℝ) + v ∧
      QuotientChain cutoff
        (⊤ : Subgroup (∀ K : MinimalNormals (socle H), OuterAut K.val)) v :=
  quadratic_socle_marked_chain_outer_reduction radicalFree orderBound hcutoff
    (sigma_achieved (by omega) a H)

/-- Conditional only on the explicitly displayed outer-solvability
obligation; the structural and chain reductions are already proved. -/
theorem quadratic_socle_sigma_bound_of_outer_solvable
    (radicalFree : ∀ N : Subgroup H, N.Normal → IsSolvable N → N = ⊥)
    {d : ℕ} (orderBound : Nat.card (socle H) ≤ d ^ 2)
    (outerSolvable : ∀ K : MinimalNormals (socle H), IsSolvable (OuterAut K.val))
    {cutoff : ℕ} (hcutoff : 64 ≤ cutoff) (a : V) :
    (sigma cutoff a H : ℝ) ≤ (12 / Real.log 3 + 6 / Real.log 2) * Real.log (d : ℝ) := by
  letI := Fintype.ofFinite (MinimalNormals (socle H))
  obtain ⟨v, hb, hv⟩ := quadratic_socle_sigma_outer_reduction radicalFree orderBound hcutoff a
  have hz := SectionCaps.quotient_chain_zero_of_cap (by omega : 5 ≤ cutoff)
    (by omega : 4 < cutoff) (SectionCaps.product_cap_four_of_solvable outerSolvable) hv
  simpa only [hz, Nat.cast_zero, add_zero] using hb

/-- Failure of the proved numerical target produces a concrete intrinsic
nonabelian simple factor whose outer automorphism group is nonsolvable. -/
theorem quadratic_socle_failure_has_nonsolvable_outer
    (radicalFree : ∀ N : Subgroup H, N.Normal → IsSolvable N → N = ⊥)
    {d : ℕ} (orderBound : Nat.card (socle H) ≤ d ^ 2)
    {cutoff : ℕ} (hcutoff : 64 ≤ cutoff) (a : V)
    (failure : (12 / Real.log 3 + 6 / Real.log 2) * Real.log (d : ℝ) <
      (sigma cutoff a H : ℝ)) :
    ∃ K : MinimalNormals (socle H), IsSimpleGroup K.val ∧
      (∃ x y : K.val, x * y ≠ y * x) ∧ ¬ IsSolvable (OuterAut K.val) := by
  classical
  by_contra hn
  have solvable : ∀ K : MinimalNormals (socle H), IsSolvable (OuterAut K.val) := by
    intro K
    by_contra hs
    exact hn ⟨K, socle_intrinsic_factor_simple K,
      socle_intrinsic_factor_nonabelian radicalFree K, hs⟩
  exact not_lt_of_ge
    (quadratic_socle_sigma_bound_of_outer_solvable radicalFree orderBound solvable hcutoff a) failure

end GI.SocleOuter
