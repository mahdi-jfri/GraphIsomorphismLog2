module

public import Workspace.QuotientChainExtension
public import Workspace.SocleOuter
public import Workspace.SocleFactorCaps

@[expose] public section

namespace GI.SocleOuter

open RadicalSocle QuotientExtension

variable {G : Type*} [Group G] [Finite G]

/-- The actual inner kernel has order dividing the actual group order.
This uses the constructed surjection, not an automorphism-order bound. -/
theorem factorOuter_kernel_card_dvd
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    (hsoc : socle G = ⊤) : Nat.card (factorOuterHom (G := G)).ker ∣ Nat.card G := by
  rw [factorOuterHom_ker_eq_innerFactor_range radicalFree hsoc,
    ← Nat.card_congr (intrinsicProductEquiv radicalFree hsoc).toEquiv]
  exact Subgroup.card_range_dvd (innerFactorHom radicalFree hsoc)

theorem inner_kernel_chain_bound
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    (hsoc : socle G = ⊤) {cutoff w : ℕ} (hcutoff : 64 ≤ cutoff)
    {H : Subgroup (FactorKernel G)} (hle : H ≤ (factorOuterHom (G := G)).ker)
    (chain : QuotientChain cutoff H w) : w ≤ 6 * padicValNat 3 (Nat.card G) := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hb := quotient_chain_valuation_bound (Or.inl rfl) hcutoff chain
  have hd := (Subgroup.card_dvd_of_le hle).trans (factorOuter_kernel_card_dvd radicalFree hsoc)
  have hm := primeValuation_mono (p := 3) (Nat.ne_of_gt (Nat.card_pos (α := G))) hd
  omega

/-- Every hereditary chain in the full automorphism group splits into
an inner charge, a factor-permutation charge, and one actual chain in the
product of the actual factor outer automorphism groups. -/
theorem automorphism_chain_outer_reduction
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    (hsoc : socle G = ⊤) {cutoff w : ℕ} (hcutoff : 64 ≤ cutoff)
    {H : Subgroup (MulAut G)} (chain : QuotientChain cutoff H w) :
    ∃ v, w ≤ 6 * padicValNat 3 (Nat.card G) +
        3 * (Nat.card (MinimalNormals G) - 1) + v ∧
      QuotientChain cutoff (⊤ : Subgroup (∀ N : MinimalNormals G, OuterAut N.val)) v := by
  letI := Fintype.ofFinite (MinimalNormals G)
  obtain ⟨u, t, hw, hu, ht⟩ := chain_split minimalNormalAction (by omega) chain
  have htbound := quotient_chain_permutation_card_bound hcutoff ht
  rw [← Nat.card_eq_fintype_card] at htbound
  have hu' := chain_subgroupOf hu (show H ⊓ (minimalNormalAction (G := G)).ker ≤
      FactorKernel G from inf_le_right)
  obtain ⟨x, y, huweight, hx, hy⟩ := chain_split factorOuterHom (by omega) hu'
  have hxbound := inner_kernel_chain_bound radicalFree hsoc hcutoff inf_le_right hx
  exact ⟨y, by omega, .restrict le_top hy⟩

/-- This reduction is unconditional on the outer automorphism groups.
The source group is embedded by its actual faithful socle conjugation map. -/
theorem radicalFree_chain_outer_reduction
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    {cutoff w : ℕ} (hcutoff : 64 ≤ cutoff) {H : Subgroup G}
    (chain : QuotientChain cutoff H w) :
    ∃ v, w ≤ 6 * padicValNat 3 (Nat.card (socle G)) +
        3 * (Nat.card (MinimalNormals (socle G)) - 1) + v ∧
      QuotientChain cutoff
        (⊤ : Subgroup (∀ N : MinimalNormals (socle G), OuterAut N.val)) v := by
  have imageChain := chain_map_of_injective socleConjugation
    (socleConjugation_injective radicalFree) chain
  exact automorphism_chain_outer_reduction
    (normal_subgroup_radicalFree radicalFree (socle G)) socle_idempotent hcutoff imageChain

end GI.SocleOuter

namespace GI.SectionCaps

variable {G : Type*} [Group G]

theorem quotient_chain_zero_of_cap {b cutoff w : ℕ} (hcutoff : 5 ≤ cutoff)
    (hsmall : b < cutoff) (bound : Cap G b) {H : Subgroup G}
    (chain : QuotientChain cutoff H w) : w = 0 := by
  induction chain with
  | stop H => rfl
  | restrict _ _ ih => exact ih
  | @mark H L w k hk s _ _ =>
    have h := bound H k (hcutoff.trans hk) s.quotient s.onto
    omega

theorem cap_four_of_solvable [Group.IsSolvable G] : Cap G 4 := by
  intro H k hk q onto
  exact (no_alternating_surjection_of_solvable hk q onto).elim

theorem product_cap_four_of_solvable {I : Type*} [Fintype I]
    {D : I → Type*} [∀ i, Group (D i)] (solvable : ∀ i, IsSolvable (D i)) :
    Cap (∀ i, D i) 4 := by
  apply faithful_group_family (fun i => Pi.evalMonoidHom D i) ?_ ?_
  · intro g hg
    exact funext hg
  · intro i
    letI : Group.IsSolvable (D i) := solvable i
    exact cap_four_of_solvable

end GI.SectionCaps

namespace GI.SocleOuter

open RadicalSocle

variable {G : Type*} [Group G] [Finite G]

/-- Explicitly conditional corollary: outer solvability is an external
mathematical obligation, not a hidden conclusion of the construction. -/
theorem radicalFree_chain_bound_of_outer_solvable
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    (outerSolvable : ∀ N : MinimalNormals (socle G), IsSolvable (OuterAut N.val))
    {cutoff w : ℕ} (hcutoff : 64 ≤ cutoff) {H : Subgroup G}
    (chain : QuotientChain cutoff H w) :
    w ≤ 6 * padicValNat 3 (Nat.card (socle G)) +
      3 * (Nat.card (MinimalNormals (socle G)) - 1) := by
  letI := Fintype.ofFinite (MinimalNormals (socle G))
  obtain ⟨v, hb, hv⟩ := radicalFree_chain_outer_reduction radicalFree hcutoff chain
  have hz := SectionCaps.quotient_chain_zero_of_cap (by omega : 5 ≤ cutoff)
    (by omega : 4 < cutoff) (SectionCaps.product_cap_four_of_solvable outerSolvable) hv
  omega

end GI.SocleOuter
