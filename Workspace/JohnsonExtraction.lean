module

public import Workspace.JohnsonOrbits
public import Workspace.JohnsonAssembly

@[expose] public section

namespace GI.Johnson

open RefinementTree

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
theorem zero_forest (C B : ℝ) {T E : Finset α} (hT : T.Nonempty)
    (hsub : T ⊆ E) (hsize : 3 ≤ E.card) (remaining : ℕ) :
    ∃ t : RefinementTree α, t.Valid T ∧ t.region = E ∧
      (0 : ℝ) ≤ (remaining : ℝ) + t.extraAllowance C B := by
  obtain ⟨a, ha⟩ := hT
  refine ⟨.leaf E, ⟨hsize, a, Finset.mem_inter.mpr ⟨hsub ha, ha⟩⟩, rfl, ?_⟩
  simpa only [extraAllowance_leaf, add_zero] using (Nat.cast_nonneg remaining : (0 : ℝ) ≤ remaining)

/-- Construct the anchored refinement forest from the actual chain.
The stronger invariant retains the current orbit's actual sigma and charges
only new branches against fresh natural-action bounds. -/
theorem forest_of_bounded_chain {cutoff : ℕ} (hcutoff : 5 ≤ cutoff) (C B : ℝ)
    (natural : ∀ (H : Subgroup (Equiv.Perm α)) (a : α), 3 ≤ (orbitFinset H a).card →
      (sigma cutoff a H : ℝ) ≤ C * Real.log ((orbitFinset H a).card : ℝ) - B) :
    ∀ (d : ℕ) (H : Subgroup (Equiv.Perm α)) (T : Finset α) (a : α) (w : ℕ),
      T.Nonempty → T ⊆ orbitFinset H a → 3 ≤ (orbitFinset H a).card →
      BoundedAnchoredChain cutoff T H w d →
      ∃ t : RefinementTree α, t.Valid T ∧ t.region = orbitFinset H a ∧
        (w : ℝ) ≤ (sigma cutoff a H : ℝ) + t.extraAllowance C B := by
  classical
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro H T a w hTne hT hsize chain
      cases chain with
      | stop H =>
          simpa only [Nat.cast_zero] using zero_forest C B hTne hT hsize (sigma cutoff a H)
      | @restrict H L w d hle tail =>
          let I := ↥(trackedOrbits L T)
          let regions : I → Finset α := Subtype.val
          obtain ⟨weights, hw, hchains⟩ := tail.partition regions
            (fun x hx => trackedOrbits_cover L T hx)
          have hrepr : ∀ i : I, ∃ b ∈ T, orbitFinset L b = i.val :=
            fun i => mem_trackedOrbits.mp i.property
          let reps : I → α := fun i => Classical.choose (hrepr i)
          have hreps (i : I) : reps i ∈ T ∧ orbitFinset L (reps i) = i.val :=
            Classical.choose_spec (hrepr i)
          let retained : Finset I := Finset.univ.filter (fun i => 3 ≤ i.val.card)
          have hret (i : I) : i ∈ retained ↔ 3 ≤ i.val.card := by simp [retained]
          have hzero (i : I) (hi : i ∉ retained) : weights i = 0 := by
            have hc : i.val.card ≤ 2 := by have := (hret i).not.mp hi; omega
            apply anchored_small_orbit_zero hcutoff (reps i) _ _ (hchains i)
            · rw [(hreps i).2]
              exact Finset.inter_subset_right
            · rwa [(hreps i).2]
          have hsum : (∑ i ∈ retained, weights i) = w := by
            calc
              (∑ i ∈ retained, weights i) = ∑ i, weights i := by
                apply Finset.sum_subset (Finset.filter_subset _ _)
                intro i _ hi
                exact hzero i hi
              _ = w := hw
          by_cases hempty : retained = ∅
          · have hwzero : w = 0 := by simpa [hempty] using hsum.symm
            simpa only [hwzero, Nat.cast_zero] using
              zero_forest C B hTne hT hsize (sigma cutoff a H)
          · have hnonempty : retained.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
            have outcomes : ∀ i ∈ retained, ∃ t : RefinementTree α,
                t.Valid T ∧ t.region = i.val ∧
                  (weights i : ℝ) ≤ (sigma cutoff (reps i) L : ℝ) + t.extraAllowance C B := by
              intro i hi
              have hiT : (T ∩ i.val).Nonempty := by
                simpa only [Finset.inter_comm] using trackedOrbits_meet L T i
              have hisub : T ∩ i.val ⊆ orbitFinset L (reps i) := by
                rw [(hreps i).2]
                exact Finset.inter_subset_right
              have hisize : 3 ≤ (orbitFinset L (reps i)).card := by
                rw [(hreps i).2]
                exact (hret i).mp hi
              obtain ⟨t, ht, hregion, hcharge⟩ := ih d (Nat.lt_succ_self d)
                L (T ∩ i.val) (reps i) (weights i) hiT hisub hisize (hchains i)
              exact ⟨t, ht.mono_anchors Finset.inter_subset_left,
                hregion.trans (hreps i).2, hcharge⟩
            let trees : I → RefinementTree α := fun i =>
              if hi : i ∈ retained then Classical.choose (outcomes i hi) else .leaf i.val
            have htrees (i : I) (hi : i ∈ retained) :
                (trees i).Valid T ∧ (trees i).region = i.val ∧
                  (weights i : ℝ) ≤ (sigma cutoff (reps i) L : ℝ) + (trees i).extraAllowance C B := by
              simpa only [trees, dif_pos hi] using Classical.choose_spec (outcomes i hi)
            obtain ⟨t, ht, hregion, hcharge⟩ := assemble_forests C B (sigma cutoff a H : ℝ)
              T (orbitFinset H a) retained hnonempty trees
              (fun i => (weights i : ℝ)) (fun i => (sigma cutoff (reps i) L : ℝ))
              (fun i hi => (htrees i hi).1)
              (by
                intro i hi
                rw [(htrees i hi).2.1]
                exact trackedOrbits_subset hle hT i)
              (by
                intro i hi j hj hij
                rw [(htrees i hi).2.1, (htrees j hj).2.1]
                exact trackedOrbits_disjoint L T i j hij)
              (fun i hi => (htrees i hi).2.2)
              (by
                intro i _
                have hm := sigma_subgroup_mono hcutoff (reps i) hle
                have hb := sigma_basepoint cutoff H (mem_orbitFinset.mp (hT (hreps i).1))
                rw [← hb] at hm
                change (sigma cutoff (reps i) L : ℝ) ≤ (sigma cutoff a H : ℝ)
                exact_mod_cast hm)
              (by
                intro i hi
                have hn := natural L (reps i) (by rw [(hreps i).2]; exact (hret i).mp hi)
                simpa only [(hreps i).2, (htrees i hi).2.1] using hn)
            have hsumReal : (∑ i ∈ retained, (weights i : ℝ)) = (w : ℝ) := by exact_mod_cast hsum
            rw [hsumReal] at hcharge
            exact ⟨t, ht, hregion, hcharge⟩
      | @mark H L w d k x hx hk s tail =>
          have horbit : orbitFinset L x = orbitFinset H a :=
            (marked_orbitFinset_eq s).trans (orbitFinset_eq_of_mem (hT hx))
          obtain ⟨t, ht, hregion, hcharge⟩ := ih d (Nat.lt_succ_self d) L T x w hTne
            (by rwa [horbit]) (by rwa [horbit]) tail
          have hpay := sigma_marked_decrease hcutoff hk s
          have hb := sigma_basepoint cutoff H (mem_orbitFinset.mp (hT hx))
          rw [← hb] at hpay
          have hpayReal : (sigma cutoff x L : ℝ) + k ≤ (sigma cutoff a H : ℝ) := by exact_mod_cast hpay
          refine ⟨t, ht, hregion.trans horbit, ?_⟩
          push_cast
          linarith

/-- The arbitrary anchored chain has the paper's forest charge bound, with
its number of starts proved to lie between one and the number of anchors. -/
theorem AnchoredChain.entropy_bound {cutoff w : ℕ} (hcutoff : 5 ≤ cutoff) (C B : ℝ)
    (hC : 0 ≤ C)
    (natural : ∀ (H : Subgroup (Equiv.Perm α)) (a : α), 3 ≤ (orbitFinset H a).card →
      (sigma cutoff a H : ℝ) ≤ C * Real.log ((orbitFinset H a).card : ℝ) - B)
    {H : Subgroup (Equiv.Perm α)} {T : Finset α} (a : α)
    (hTne : T.Nonempty) (hT : T ⊆ orbitFinset H a) (hsize : 3 ≤ (orbitFinset H a).card)
    (chain : AnchoredChain cutoff T H w) :
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ T.card ∧
      (w : ℝ) ≤ C * forestPotential ((orbitFinset H a).card : ℝ) (r : ℝ) - B * r := by
  obtain ⟨d, hd⟩ := chain.bounded
  obtain ⟨t, ht, hroot, hw⟩ := forest_of_bounded_chain hcutoff C B natural d H T a w hTne hT hsize hd
  have hn := natural H a hsize
  rw [← hroot] at hn
  have hb := charge_bound_of_extra hw hn
  have he := mul_le_mul_of_nonneg_left (RefinementTree.entropy ht) hC
  rw [hroot] at he
  refine ⟨t.leaves, Nat.succ_le_of_lt (leaves_positive t), leaves_le_anchors ht, ?_⟩
  linarith

end GI.Johnson
