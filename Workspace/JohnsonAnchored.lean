import Workspace.JohnsonChains

namespace GI.Johnson

variable {α : Type*} [DecidableEq α]

/-- Height records the finite chain witness, so restricting its anchor set
preserves the induction measure used to construct the refinement forest. -/
inductive BoundedAnchoredChain (cutoff : ℕ) (anchors : Finset α) :
    Subgroup (Equiv.Perm α) → ℕ → ℕ → Prop
  | stop (H) : BoundedAnchoredChain cutoff anchors H 0 0
  | restrict {H L w d} : L ≤ H → BoundedAnchoredChain cutoff anchors L w d →
      BoundedAnchoredChain cutoff anchors H w (d + 1)
  | mark {H L w d k a} : a ∈ anchors → cutoff ≤ k → VisibleStep a H L k →
      BoundedAnchoredChain cutoff anchors L w d → BoundedAnchoredChain cutoff anchors H (w + k) (d + 1)

omit [DecidableEq α] in
theorem AnchoredChain.bounded {cutoff w : ℕ} {T : Finset α}
    {H : Subgroup (Equiv.Perm α)} (h : AnchoredChain cutoff T H w) :
    ∃ d, BoundedAnchoredChain cutoff T H w d := by
  induction h with
  | stop H => exact ⟨0, .stop H⟩
  | restrict hle _ ih => obtain ⟨d, hd⟩ := ih; exact ⟨d + 1, .restrict hle hd⟩
  | mark ha hk s _ ih => obtain ⟨d, hd⟩ := ih; exact ⟨d + 1, .mark ha hk s hd⟩

omit [DecidableEq α] in
theorem BoundedAnchoredChain.forget {cutoff w d : ℕ} {T : Finset α}
    {H : Subgroup (Equiv.Perm α)} (h : BoundedAnchoredChain cutoff T H w d) :
    AnchoredChain cutoff T H w := by
  induction h with
  | stop H => exact .stop H
  | restrict hle _ ih => exact .restrict hle ih
  | mark ha hk s _ ih => exact .mark ha hk s ih

/-- Filtering charges by a fixed region preserves the actual descending
subgroups and the chain height. Discarded marks become unmarked restrictions. -/
theorem BoundedAnchoredChain.split {cutoff w d : ℕ} {T : Finset α}
    {H : Subgroup (Equiv.Perm α)} (h : BoundedAnchoredChain cutoff T H w d) (E : Finset α) :
    ∃ u v, w = u + v ∧ BoundedAnchoredChain cutoff (T ∩ E) H u d ∧
      BoundedAnchoredChain cutoff (T \ E) H v d := by
  induction h with
  | stop H => exact ⟨0, 0, rfl, .stop H, .stop H⟩
  | restrict hle _ ih =>
      obtain ⟨u, v, hw, hu, hv⟩ := ih
      exact ⟨u, v, hw, .restrict hle hu, .restrict hle hv⟩
  | @mark H L w d k a ha hk s h ih =>
      obtain ⟨u, v, hw, hu, hv⟩ := ih
      by_cases he : a ∈ E
      · exact ⟨u + k, v, by omega, .mark (Finset.mem_inter.mpr ⟨ha, he⟩) hk s hu,
          .restrict s.lower hv⟩
      · exact ⟨u, v + k, by omega, .restrict s.lower hu,
          .mark (Finset.mem_sdiff.mpr ⟨ha, he⟩) hk s hv⟩

omit [DecidableEq α] in
theorem BoundedAnchoredChain.mono_anchors {cutoff w d : ℕ} {T U : Finset α}
    {H : Subgroup (Equiv.Perm α)} (hTU : T ⊆ U)
    (h : BoundedAnchoredChain cutoff T H w d) : BoundedAnchoredChain cutoff U H w d := by
  induction h with
  | stop H => exact .stop H
  | restrict hle _ ih => exact .restrict hle ih
  | mark ha hk s _ ih => exact .mark (hTU ha) hk s ih

omit [DecidableEq α] in
theorem BoundedAnchoredChain.empty_weight {cutoff w d : ℕ}
    {H : Subgroup (Equiv.Perm α)} (h : BoundedAnchoredChain cutoff (∅ : Finset α) H w d) : w = 0 := by
  induction h with
  | stop H => rfl
  | restrict _ _ ih => exact ih
  | mark ha _ _ _ _ => simp at ha

variable [Fintype α]

omit [DecidableEq α] in
theorem AnchoredChain.zero_of_sigma {cutoff w : ℕ} (hcutoff : 5 ≤ cutoff)
    {T : Finset α} {H : Subgroup (Equiv.Perm α)} (h : AnchoredChain cutoff T H w)
    (hz : ∀ a ∈ T, sigma cutoff a H = 0) : w = 0 := by
  induction h with
  | stop H => rfl
  | @restrict H L w hle h ih =>
      apply ih
      intro a ha
      have hm := sigma_subgroup_mono hcutoff a hle
      rw [hz a ha] at hm
      exact Nat.eq_zero_of_le_zero hm
  | mark ha hk s h ih =>
      have hm := sigma_marked_decrease hcutoff hk s
      rw [hz _ ha] at hm
      omega

omit [DecidableEq α] in
theorem AnchoredChain.zero_of_orbit_sigma {cutoff w : ℕ} (hcutoff : 5 ≤ cutoff)
    {T : Finset α} {H : Subgroup (Equiv.Perm α)} (a : α)
    (hT : ∀ b ∈ T, ∃ g : H, (g : Equiv.Perm α) a = b)
    (hz : sigma cutoff a H = 0) (h : AnchoredChain cutoff T H w) : w = 0 := by
  apply h.zero_of_sigma hcutoff
  intro b hb
  rw [← sigma_basepoint cutoff H (hT b hb), hz]

omit [DecidableEq α] in
/-- Payment may be measured at any point of the charged natural orbit. -/
theorem marked_payment_on_orbit {cutoff k : ℕ} (hcutoff : 5 ≤ cutoff)
    {H L : Subgroup (Equiv.Perm α)} {a b : α} (hk : cutoff ≤ k)
    (s : VisibleStep b H L k) (ha : ∃ g : H, (g : Equiv.Perm α) b = a) :
    sigma cutoff a L + k ≤ sigma cutoff a H := by
  obtain ⟨g, hg⟩ := ha
  obtain ⟨l, hl⟩ := s.transitiveKernel g
  have hl' : (l : Equiv.Perm α) b = a := hl.trans hg
  have hm := sigma_marked_decrease hcutoff hk s
  rw [sigma_basepoint cutoff L ⟨l, hl'⟩, sigma_basepoint cutoff H ⟨g, hg⟩] at hm
  exact hm

omit [DecidableEq α] [Fintype α] in
/-- A marked kernel preserves the whole charged orbit as one natural orbit. -/
theorem marked_orbit_eq {H L : Subgroup (Equiv.Perm α)} {b : α} {k : ℕ}
    (s : VisibleStep b H L k) : MulAction.orbit L b = MulAction.orbit H b := by
  ext a
  constructor
  · rintro ⟨l, hl⟩
    exact ⟨Subgroup.inclusion s.lower l, hl⟩
  · rintro ⟨h, hh⟩
    obtain ⟨l, hl⟩ := s.transitiveKernel h
    exact ⟨l, hl.trans hh⟩

end GI.Johnson
