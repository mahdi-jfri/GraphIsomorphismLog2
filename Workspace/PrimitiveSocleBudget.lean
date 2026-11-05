module

public import Workspace.SocleFactorDegree
public import Workspace.SocleOuterBudget

@[expose] public section

namespace GI.SocleOuter

open RadicalSocle

theorem valuation_log_bound {p n : ℕ} (hp : 2 ≤ p) (hn : 0 < n) :
    (padicValNat p n : ℝ) * Real.log (p : ℝ) ≤ Real.log (n : ℝ) := by
  have hpow : p ^ padicValNat p n ≤ n := Nat.le_of_dvd hn pow_padicValNat_dvd
  have hpowR : (p : ℝ) ^ padicValNat p n ≤ (n : ℝ) := by exact_mod_cast hpow
  have hpos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hlog := Real.log_le_log (pow_pos hpos _) hpowR
  rwa [Real.log_pow] at hlog

variable {V : Type*} [Fintype V]

/-- Lifts an actual physical marked chain into its ambient subgroup and
then performs the proved socle/outer splitting. -/
theorem marked_chain_outer_reduction {H : Subgroup (Equiv.Perm V)}
    (radicalFree : ∀ N : Subgroup H, N.Normal → IsSolvable N → N = ⊥)
    {cutoff w : ℕ} (hcutoff : 64 ≤ cutoff) {a : V}
    (chain : MarkedChain cutoff a H w) :
    ∃ v, w ≤ 6 * padicValNat 3 (Nat.card (socle H)) +
        3 * (Nat.card (MinimalNormals (socle H)) - 1) + v ∧
      QuotientChain cutoff
        (⊤ : Subgroup (∀ N : MinimalNormals (socle H), OuterAut N.val)) v := by
  exact radicalFree_chain_outer_reduction radicalFree hcutoff
    (QuotientExtension.chain_subgroupOf chain.toQuotientChain le_rfl)

end GI.SocleOuter

namespace GI.PrimitiveStructure

open RadicalSocle SocleOuter

variable {G V : Type*} [Group G] [Finite G] [MulAction G V] [FaithfulSMul G V]
variable [MulAction.IsPreprimitive G V]

/-- The inner and coordinate charges are logarithmic in the actual
physical degree; no estimate for automorphism groups is used. -/
theorem two_minimal_inner_factor_log_bound {M N : Subgroup G}
    (hM : MinimalNormal M) (hN : MinimalNormal N) (hne : M ≠ N) (a : V) :
    (6 * padicValNat 3 (Nat.card (socle G)) +
      3 * (Nat.card (MinimalNormals (socle G)) - 1) : ℕ) ≤
      (12 / Real.log 3 + 6 / Real.log 2) * Real.log (Nat.card V : ℝ) := by
  have hval := valuation_log_bound (by decide : 2 ≤ 3)
    (Nat.card_pos (α := socle G))
  have hlogcard : Real.log (Nat.card (socle G) : ℝ) =
      2 * Real.log (Nat.card V : ℝ) := by
    rw [two_minimal_socle_card_eq_degree_sq hM hN hne a, Nat.cast_pow, Real.log_pow]
    norm_num
  rw [hlogcard] at hval
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hvalBound : (padicValNat 3 (Nat.card (socle G)) : ℝ) ≤
      (2 / Real.log 3) * Real.log (Nat.card V : ℝ) := by
    calc
      (padicValNat 3 (Nat.card (socle G)) : ℝ) ≤
          (2 * Real.log (Nat.card V : ℝ)) / Real.log 3 :=
        (le_div_iff₀ hlog3).mpr (by simpa only [Nat.cast_ofNat] using hval)
      _ = (2 / Real.log 3) * Real.log (Nat.card V : ℝ) := by ring
  have hcount := two_minimal_intrinsic_count_log_degree hM hN hne a
  have hsmall : 3 * (Nat.card (MinimalNormals (socle G)) - 1) ≤
      3 * Nat.card (MinimalNormals (socle G)) :=
    Nat.mul_le_mul_left 3 (Nat.sub_le _ _)
  calc
    (6 * padicValNat 3 (Nat.card (socle G)) +
        3 * (Nat.card (MinimalNormals (socle G)) - 1) : ℕ) ≤
        6 * (padicValNat 3 (Nat.card (socle G)) : ℝ) +
          3 * (Nat.card (MinimalNormals (socle G)) : ℝ) := by
      exact_mod_cast Nat.add_le_add_left hsmall (6 * padicValNat 3 (Nat.card (socle G)))
    _ ≤ 6 * ((2 / Real.log 3) * Real.log (Nat.card V : ℝ)) +
          3 * ((2 / Real.log 2) * Real.log (Nat.card V : ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left hvalBound (by norm_num))
        (mul_le_mul_of_nonneg_left hcount (by norm_num))
    _ = (12 / Real.log 3 + 6 / Real.log 2) * Real.log (Nat.card V : ℝ) := by ring

end GI.PrimitiveStructure

namespace GI.PrimitiveStructure

open RadicalSocle SocleOuter

variable {V : Type*} [Fintype V] {H : Subgroup (Equiv.Perm V)}
variable [MulAction.IsPreprimitive H V]

/-- Unconditional reduction of each actual marked chain to an actual
outer-group chain, with an explicit logarithmic physical-degree charge. -/
theorem two_minimal_marked_chain_outer_reduction {M N : Subgroup H}
    (hM : MinimalNormal M) (hN : MinimalNormal N) (hne : M ≠ N)
    {cutoff w : ℕ} (hcutoff : 64 ≤ cutoff) (a : V)
    (chain : MarkedChain cutoff a H w) :
    ∃ v : ℕ, (w : ℝ) ≤
        (12 / Real.log 3 + 6 / Real.log 2) * Real.log (Nat.card V : ℝ) + v ∧
      QuotientChain cutoff
        (⊤ : Subgroup (∀ K : MinimalNormals (socle H), OuterAut K.val)) v := by
  obtain ⟨v, hv, chainv⟩ := marked_chain_outer_reduction
    (two_minimal_radical_free hM hN hne a) hcutoff chain
  have hcost := two_minimal_inner_factor_log_bound hM hN hne a
  refine ⟨v, ?_, chainv⟩
  calc
    (w : ℝ) ≤ (6 * padicValNat 3 (Nat.card (socle H)) +
        3 * (Nat.card (MinimalNormals (socle H)) - 1) : ℕ) + (v : ℝ) := by
      exact_mod_cast hv
    _ ≤ (12 / Real.log 3 + 6 / Real.log 2) * Real.log (Nat.card V : ℝ) + v :=
      add_le_add_left hcost _

/-- With the remaining outer-solvability premise displayed explicitly,
the full hereditary sigma budget of the two-minimal-normal case follows.
The premise is not proved by this file. -/
theorem two_minimal_sigma_bound_of_outer_solvable {M N : Subgroup H}
    (hM : MinimalNormal M) (hN : MinimalNormal N) (hne : M ≠ N)
    (outerSolvable : ∀ K : MinimalNormals (socle H), IsSolvable (OuterAut K.val))
    {cutoff : ℕ} (hcutoff : 64 ≤ cutoff) (a : V) :
    (sigma cutoff a H : ℝ) ≤
      (12 / Real.log 3 + 6 / Real.log 2) * Real.log (Nat.card V : ℝ) := by
  letI := Fintype.ofFinite (MinimalNormals (socle H))
  obtain ⟨v, hb, hv⟩ := two_minimal_marked_chain_outer_reduction hM hN hne
    hcutoff a (sigma_achieved (by omega) a H)
  have hz := SectionCaps.quotient_chain_zero_of_cap (by omega : 5 ≤ cutoff)
    (by omega : 4 < cutoff) (SectionCaps.product_cap_four_of_solvable outerSolvable) hv
  simpa only [hz, Nat.cast_zero, add_zero] using hb

/-- Any failure in this physical two-normal branch produces an actual
finite nonabelian simple factor with a nonsolvable outer automorphism group.
This isolates the remaining structural obligation without assuming it. -/
theorem two_minimal_failure_has_nonsolvable_outer {M N : Subgroup H}
    (hM : MinimalNormal M) (hN : MinimalNormal N) (hne : M ≠ N)
    {cutoff : ℕ} (hcutoff : 64 ≤ cutoff) (a : V)
    (failure : (12 / Real.log 3 + 6 / Real.log 2) * Real.log (Nat.card V : ℝ) <
      (sigma cutoff a H : ℝ)) :
    ∃ K : MinimalNormals (socle H), IsSimpleGroup K.val ∧
      (∃ x y : K.val, x * y ≠ y * x) ∧ ¬ IsSolvable (OuterAut K.val) := by
  classical
  by_contra hn
  have solvable : ∀ K : MinimalNormals (socle H), IsSolvable (OuterAut K.val) := by
    intro K
    by_contra hs
    exact hn ⟨K, socle_intrinsic_factor_simple K,
      socle_intrinsic_factor_nonabelian (two_minimal_radical_free hM hN hne a) K, hs⟩
  exact not_lt_of_ge
    (two_minimal_sigma_bound_of_outer_solvable hM hN hne solvable hcutoff a) failure

end GI.PrimitiveStructure
