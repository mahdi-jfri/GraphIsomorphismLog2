import Workspace.QuotientChains
import Workspace.OrbitBudget

namespace GI

/-- The alternating group above degree `n` has order larger than `n!`.
This is the elementary order obstruction behind the small-degree base case. -/
theorem alternating_order_gt_factorial {n k : ℕ} (hk : 5 ≤ k) (hnk : n < k) :
    n.factorial < Nat.card (alternatingGroup (Fin k)) := by
  haveI : Nontrivial (Fin k) := Fintype.one_lt_card_iff_nontrivial.mp
    (by simpa using (show 1 < k by omega))
  have hc := two_mul_card_alternatingGroup (α := Fin k)
  rw [Fintype.card_perm, Fintype.card_fin, ← Nat.card_eq_fintype_card] at hc
  have hsucc : k - 1 + 1 = k := by omega
  have hf := Nat.factorial_succ (k - 1)
  rw [hsucc] at hf
  have hmono := Nat.factorial_le (show n ≤ k - 1 by omega)
  have hmul : k * n.factorial ≤ k.factorial := by
    rw [hf]
    exact Nat.mul_le_mul_left k hmono
  have hlower := (Nat.mul_le_mul_right n.factorial hk).trans hmul
  have hpos := Nat.factorial_pos n
  nlinarith

theorem no_alternating_surjection_of_small_order {G : Type*} [Group G] [Finite G]
    {n k : ℕ} (hk : 5 ≤ k) (hnk : n < k) (hcard : Nat.card G ≤ n.factorial)
    (q : G →* alternatingGroup (Fin k)) : ¬ Function.Surjective q := by
  intro hq
  have hle := Nat.card_le_card_of_surjective q hq
  exact (not_lt_of_ge (hle.trans hcard)) (alternating_order_gt_factorial hk hnk)

theorem subgroup_card_mono_generic {G : Type*} [Group G] [Finite G]
    {H L : Subgroup G} (hle : L ≤ H) : Nat.card L ≤ Nat.card H := by
  apply Nat.card_le_card_of_injective (Subgroup.inclusion hle)
  intro x y h
  exact Subtype.ext (congrArg (fun z : H => (z : G)) h)

theorem no_quotient_step_of_small_order {G : Type*} [Group G] [Finite G]
    {H L : Subgroup G} {n k : ℕ} (hk : 5 ≤ k) (hnk : n < k)
    (hcard : Nat.card H ≤ n.factorial) (s : AlternatingQuotientStep H L k) : False := by
  have hf := quotient_step_card_factorization s
  have hpositive : 1 ≤ Nat.card L := Nat.card_pos
  have hproduct := Nat.mul_le_mul_right (Nat.card (alternatingGroup (Fin k))) hpositive
  have hle : Nat.card (alternatingGroup (Fin k)) ≤ Nat.card H := by
    simpa only [one_mul, hf] using hproduct
  exact (not_lt_of_ge (hle.trans hcard)) (alternating_order_gt_factorial hk hnk)

/-- Every quotient chain in a group too small to contain a permitted
alternating quotient has weight zero; arbitrary subgroup restrictions are allowed. -/
theorem quotient_chain_zero_of_card {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} {n cutoff w : ℕ} (hcutoff : 5 ≤ cutoff) (hn : n < cutoff)
    (chain : QuotientChain cutoff H w) : Nat.card H ≤ n.factorial → w = 0 := by
  induction chain with
  | stop H => intro _; rfl
  | restrict hle _ ih =>
      intro hcard
      exact ih ((subgroup_card_mono_generic hle).trans hcard)
  | mark hk s _ _ =>
      intro hcard
      exact (no_quotient_step_of_small_order (hcutoff.trans hk) (hn.trans_le hk) hcard s).elim

def VisibleStep.toAlternatingQuotientStep {V : Type*} {a : V}
    {H L : Subgroup (Equiv.Perm V)} {k : ℕ} (s : VisibleStep a H L k) :
    AlternatingQuotientStep H L k where
  lower := s.lower
  quotient := s.quotient
  onto := s.onto
  kernel := s.kernel

theorem MarkedChain.toQuotientChain {V : Type*} {a : V}
    {H : Subgroup (Equiv.Perm V)} {cutoff w : ℕ} (chain : MarkedChain cutoff a H w) :
    QuotientChain cutoff H w := by
  induction chain with
  | stop H => exact .stop H
  | restrict hle _ ih => exact .restrict hle ih
  | mark hk s _ ih => exact .mark hk s.toAlternatingQuotientStep ih

theorem sigma_zero_of_group_order {V : Type*} [Fintype V]
    {H : Subgroup (Equiv.Perm V)} {n cutoff : ℕ} (hcutoff : 5 ≤ cutoff)
    (hn : n < cutoff) (hcard : Nat.card H ≤ n.factorial) (a : V) :
    sigma cutoff a H = 0 :=
  quotient_chain_zero_of_card hcutoff hn (sigma_achieved hcutoff a H).toQuotientChain hcard

theorem permutation_subgroup_card_le_factorial {A : Type*} [Fintype A]
    (H : Subgroup (Equiv.Perm A)) : Nat.card H ≤ (Fintype.card A).factorial := by
  classical
  have hle := Nat.card_le_card_of_injective H.subtype Subtype.val_injective
  simpa only [Nat.card_eq_fintype_card, Fintype.card_perm] using hle

theorem sigma_zero_of_degree {A : Type*} [Fintype A] {cutoff : ℕ}
    (hcutoff : 5 ≤ cutoff) (hdegree : Fintype.card A < cutoff)
    (H : Subgroup (Equiv.Perm A)) (a : A) : sigma cutoff a H = 0 :=
  sigma_zero_of_group_order hcutoff hdegree (permutation_subgroup_card_le_factorial H) a

/-- The representation may be nonfaithful and its target may be much larger
than the original natural domain. Only the original group's degree is used. -/
theorem sigma_image_zero_of_card {A V : Type*} [Fintype A] [Fintype V]
    {cutoff : ℕ} (hcutoff : 5 ≤ cutoff) (hdegree : Fintype.card A < cutoff)
    {H : Subgroup (Equiv.Perm A)} (p : H →* Equiv.Perm V) (v : V) :
    sigma cutoff v p.range = 0 := by
  have hp : Function.Surjective p.rangeRestrict := by
    rintro ⟨q, hq⟩
    obtain ⟨h, rfl⟩ := hq
    exact ⟨h, rfl⟩
  have hcard := (Nat.card_le_card_of_surjective p.rangeRestrict hp).trans
    (permutation_subgroup_card_le_factorial H)
  exact sigma_zero_of_group_order hcutoff hdegree hcard v

theorem sigma_image_zero_of_degree {V : Type*} [Fintype V] {n cutoff : ℕ}
    (hcutoff : 5 ≤ cutoff) (hn : n < cutoff)
    {H : Subgroup (Equiv.Perm (Fin n))} (p : H →* Equiv.Perm V) (v : V) :
    sigma cutoff v p.range = 0 :=
  sigma_image_zero_of_card hcutoff (by simpa using hn) p v

theorem sigma_zero_of_orbit_card {V : Type*} [Fintype V] {cutoff : ℕ}
    (hcutoff : 5 ≤ cutoff) (H : Subgroup (Equiv.Perm V)) (a : V)
    [Fintype (ActiveOrbit H a)] (hdegree : Fintype.card (ActiveOrbit H a) < cutoff) :
    sigma cutoff a H = 0 := by
  rw [sigma_faithfulOrbit cutoff H a]
  exact sigma_zero_of_degree hcutoff hdegree (faithfulOrbitImage H a) (activeOrbitBase H a)

theorem sigma_zero_of_orbit_card_le_two {V : Type*} [Fintype V] {cutoff : ℕ}
    (hcutoff : 5 ≤ cutoff) (H : Subgroup (Equiv.Perm V)) (a : V)
    [Fintype (ActiveOrbit H a)] (hdegree : Fintype.card (ActiveOrbit H a) ≤ 2) :
    sigma cutoff a H = 0 :=
  sigma_zero_of_orbit_card hcutoff H a (by omega)

end GI
