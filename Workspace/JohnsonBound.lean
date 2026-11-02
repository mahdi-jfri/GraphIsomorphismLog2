import Workspace.JohnsonExtraction
import Workspace.JohnsonNatural
import Workspace.JohnsonDirect
import Workspace.JohnsonNumerics
import Workspace.JohnsonAction

namespace GI.Johnson

variable {V α : Type*} [DecidableEq α] [Fintype α]

namespace JohnsonCover

/-- The complete Johnson charge bound for any actual injectively labeled
subset action. The only structural hypothesis is the paper's stated induction
hypothesis for the natural symmetric actions. -/
theorem chain_log_bound {cutoff w : ℕ} {C : ℝ} (hcutoff : 64 ≤ cutoff)
    {H : Subgroup (Equiv.Perm V)} {a : V} (c : JohnsonCover H α)
    (hC : 128 ≤ C) (natural : NaturalActionBound cutoff C (C + 6) (Fintype.card α))
    (htwo : 2 ≤ (c.label a).card) (hhalf : 2 * (c.label a).card ≤ Fintype.card α)
    (chain : MarkedChain cutoff a H w) :
    (w : ℝ) ≤ C * Real.log ((Fintype.card α).choose (c.label a).card : ℝ) - (C + 6) := by
  classical
  let m := Fintype.card α
  let T := c.label a
  let t := T.card
  change 2 ≤ t at htwo
  change 2 * t ≤ m at hhalf
  change (w : ℝ) ≤ C * Real.log (m.choose t : ℝ) - (C + 6)
  have htpos : 0 < t := by omega
  have htm : t ≤ m := by omega
  have hlog := choose_log_lower htpos htm
  have hc0 : 0 ≤ C := by linarith
  have htReal : (2 : ℝ) ≤ t := by exact_mod_cast htwo
  have hhReal : 2 * (t : ℝ) ≤ m := by exact_mod_cast hhalf
  by_cases hsmall : 4 * t ≤ m
  · obtain ⟨u, v, hw, hu, hv⟩ := c.chain_split_anchor_bound hcutoff chain
    have hvtop : AnchoredChain cutoff T (⊤ : Subgroup (Equiv.Perm α)) v := .restrict le_top hv
    have hTne : T.Nonempty := Finset.card_pos.mp htpos
    let x : α := Classical.choose hTne
    have horbit := orbitFinset_top x
    have hnatural := fun H x hs => natural_bound_on_orbit (by omega : 5 ≤ cutoff) natural H x hs
    obtain ⟨r, hr, hrt, hbound⟩ := hvtop.entropy_bound (by omega) C (C + 6) hc0 hnatural x
      hTne (by rw [horbit]; exact Finset.subset_univ T)
      (by rw [horbit, Finset.card_univ]; change 3 ≤ m; omega)
    rw [horbit, Finset.card_univ] at hbound
    change r ≤ t at hrt
    have hrReal : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hrtReal : (r : ℝ) ≤ t := by exact_mod_cast hrt
    have hsmallReal : 4 * (t : ℝ) ≤ m := by exact_mod_cast hsmall
    change u ≤ 3 * (t - 1) at hu
    have huReal : (u : ℝ) ≤ 3 * ((t - 1 : ℕ) : ℝ) := by exact_mod_cast hu
    rw [Nat.cast_sub (by omega : 1 ≤ t), Nat.cast_one] at huReal
    have hwReal : (w : ℝ) = (u : ℝ) + v := by exact_mod_cast hw
    have hnum := small_subset_charge_bound hC hrReal hrtReal hsmallReal hlog
    unfold forestPotential at hbound
    change (v : ℝ) ≤ C * ((r : ℝ) * Real.log ((m : ℝ) / r) + ((r : ℝ) - 1)) - (C + 6) * r at hbound
    nlinarith
  · by_cases hdegree : m < cutoff
    · have hwzero := c.chain_zero_of_degree (by omega) hdegree chain
      rw [hwzero]
      have hnum := anchor_only_charge_bound hC htReal hhReal hlog
      norm_num only [Nat.cast_zero]
      nlinarith
    · have hm : (64 : ℝ) ≤ m := by exact_mod_cast (by omega : 64 ≤ m)
      have htlow : (m : ℝ) ≤ 4 * t := by exact_mod_cast (by omega : m ≤ 4 * t)
      have hwNat := c.direct_chain_bound hcutoff chain
      have hwNat' : w ≤ 3 * m := hwNat.trans (Nat.mul_le_mul_left 3 (Nat.sub_le _ _))
      have hwReal : (w : ℝ) ≤ 3 * m := by exact_mod_cast hwNat'
      exact hwReal.trans (large_subset_charge_bound hC hm htlow hhReal hlog)

theorem sigma_log_bound [Fintype V] {cutoff : ℕ} {C : ℝ} (hcutoff : 64 ≤ cutoff)
    {H : Subgroup (Equiv.Perm V)} (c : JohnsonCover H α) (a : V)
    (hC : 128 ≤ C) (natural : NaturalActionBound cutoff C (C + 6) (Fintype.card α))
    (htwo : 2 ≤ (c.label a).card) (hhalf : 2 * (c.label a).card ≤ Fintype.card α) :
    (sigma cutoff a H : ℝ) ≤
      C * Real.log ((Fintype.card α).choose (c.label a).card : ℝ) - (C + 6) :=
  c.chain_log_bound hcutoff hC natural htwo hhalf (sigma_achieved (by omega) a H)

end JohnsonCover

/-- Appendix A.7 for the actual symmetric action on t-subsets of Fin m.
Anchor localization, chain decomposition, orbit-refinement forest extraction,
entropy accounting, and both numerical regimes are proved dependencies. -/
theorem johnson_anchor_bound {m t cutoff : ℕ} {C : ℝ}
    (hcutoff : 64 ≤ cutoff) (hC : 128 ≤ C) (htwo : 2 ≤ t) (hhalf : 2 * t ≤ m)
    (natural : NaturalActionBound cutoff C (C + 6) m) (s : SubsetVertex (Fin m) t) :
    (sigma cutoff s (subsetImage t) : ℝ) ≤ C * Real.log (m.choose t : ℝ) - (C + 6) := by
  let c := finCover (by omega : 1 ≤ t) (by omega : t < m)
  have hc : (c.label s).card = t := s.property
  have hn : NaturalActionBound cutoff C (C + 6) (Fintype.card (Fin m)) := by
    simpa only [Fintype.card_fin] using natural
  have hh := c.sigma_log_bound hcutoff s hC hn (by rwa [hc]) (by simpa only [hc, Fintype.card_fin] using hhalf)
  simpa only [hc, Fintype.card_fin] using hh

end GI.Johnson
