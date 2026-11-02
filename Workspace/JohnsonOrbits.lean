import Workspace.JohnsonAnchored
import Workspace.SmallDegreeBudget

namespace GI.Johnson

variable {α I : Type*} [DecidableEq α]

/-- Partition the actual marked weights among any finite covering family of
anchor regions, retaining the same subgroup sequence and the same height. -/
theorem BoundedAnchoredChain.partition [Fintype I] {cutoff w d : ℕ} {T : Finset α}
    {H : Subgroup (Equiv.Perm α)} (h : BoundedAnchoredChain cutoff T H w d)
    (regions : I → Finset α) (cover : ∀ a ∈ T, ∃ i, a ∈ regions i) :
    ∃ weights : I → ℕ, (∑ i, weights i) = w ∧
      ∀ i, BoundedAnchoredChain cutoff (T ∩ regions i) H (weights i) d := by
  classical
  induction h with
  | stop H => exact ⟨fun _ => 0, by simp, fun _ => .stop H⟩
  | restrict hle _ ih =>
      obtain ⟨weights, hw, hc⟩ := ih
      exact ⟨weights, hw, fun i => .restrict hle (hc i)⟩
  | @mark H L w d k a ha hk s h ih =>
      obtain ⟨weights, hw, hc⟩ := ih
      obtain ⟨i, hi⟩ := cover a ha
      let weights' : I → ℕ := fun j => weights j + if j = i then k else 0
      refine ⟨weights', ?_, ?_⟩
      · simp [weights', Finset.sum_add_distrib, hw]
      · intro j
        by_cases hji : j = i
        · subst j
          have hh := BoundedAnchoredChain.mark (Finset.mem_inter.mpr ⟨ha, hi⟩) hk s (hc i)
          simpa [weights'] using hh
        · have hh := BoundedAnchoredChain.restrict s.lower (hc j)
          simpa [weights', hji] using hh

variable [Fintype α]

noncomputable def orbitFinset (H : Subgroup (Equiv.Perm α)) (a : α) : Finset α :=
  by classical exact (MulAction.orbit H a).toFinset

omit [DecidableEq α] in
@[simp] theorem mem_orbitFinset {H : Subgroup (Equiv.Perm α)} {a b : α} :
    b ∈ orbitFinset H a ↔ ∃ h : H, (h : Equiv.Perm α) a = b := by
  classical
  simp only [orbitFinset, Set.mem_toFinset]
  rfl

omit [DecidableEq α] in
theorem self_mem_orbitFinset (H : Subgroup (Equiv.Perm α)) (a : α) : a ∈ orbitFinset H a :=
  mem_orbitFinset.mpr ⟨1, rfl⟩

omit [DecidableEq α] in
theorem orbitFinset_eq_of_mem {H : Subgroup (Equiv.Perm α)} {a b : α}
    (hb : b ∈ orbitFinset H a) : orbitFinset H b = orbitFinset H a := by
  classical
  have hs : MulAction.orbit H b = MulAction.orbit H a :=
    MulAction.orbit_eq_iff.mpr (by simpa only [orbitFinset, Set.mem_toFinset] using hb)
  ext x
  simp only [orbitFinset, Set.mem_toFinset, hs]

omit [DecidableEq α] in
theorem orbitFinset_disjoint_or_eq (H : Subgroup (Equiv.Perm α)) (a b : α) :
    Disjoint (orbitFinset H a) (orbitFinset H b) ∨ orbitFinset H a = orbitFinset H b := by
  classical
  by_cases hd : Disjoint (orbitFinset H a) (orbitFinset H b)
  · exact Or.inl hd
  · right
    obtain ⟨x, hxa, hxb⟩ := Finset.not_disjoint_iff.mp hd
    exact (orbitFinset_eq_of_mem hxa).symm.trans (orbitFinset_eq_of_mem hxb)

omit [DecidableEq α] in
theorem orbitFinset_subgroup_subset {H L : Subgroup (Equiv.Perm α)} (hle : L ≤ H) (a : α) :
    orbitFinset L a ⊆ orbitFinset H a := by
  intro x hx
  obtain ⟨l, hl⟩ := mem_orbitFinset.mp hx
  exact mem_orbitFinset.mpr ⟨Subgroup.inclusion hle l, hl⟩

omit [DecidableEq α] in
theorem orbitFinset_subset_of_anchor {H L : Subgroup (Equiv.Perm α)} (hle : L ≤ H)
    {a b : α} (hb : b ∈ orbitFinset H a) : orbitFinset L b ⊆ orbitFinset H a := by
  rw [← orbitFinset_eq_of_mem hb]
  exact orbitFinset_subgroup_subset hle b

omit [DecidableEq α] in
theorem orbitFinset_card (H : Subgroup (Equiv.Perm α)) (a : α)
    [Fintype (ActiveOrbit H a)] : (orbitFinset H a).card = Fintype.card (ActiveOrbit H a) := by
  classical
  simp [orbitFinset, ActiveOrbit, Fintype.card_subtype]

noncomputable def trackedOrbits (H : Subgroup (Equiv.Perm α)) (T : Finset α) :
    Finset (Finset α) := T.image (orbitFinset H)

theorem mem_trackedOrbits {H : Subgroup (Equiv.Perm α)} {T E : Finset α} :
    E ∈ trackedOrbits H T ↔ ∃ a ∈ T, orbitFinset H a = E := by
  classical
  exact Finset.mem_image

theorem trackedOrbits_cover (H : Subgroup (Equiv.Perm α)) (T : Finset α)
    {a : α} (ha : a ∈ T) : ∃ E : trackedOrbits H T, a ∈ E.val := by
  refine ⟨⟨orbitFinset H a, mem_trackedOrbits.mpr ⟨a, ha, rfl⟩⟩, self_mem_orbitFinset H a⟩

theorem trackedOrbits_meet (H : Subgroup (Equiv.Perm α)) (T : Finset α)
    (E : trackedOrbits H T) : (E.val ∩ T).Nonempty := by
  obtain ⟨a, ha, he⟩ := mem_trackedOrbits.mp E.property
  refine ⟨a, Finset.mem_inter.mpr ⟨?_, ha⟩⟩
  rw [← he]
  exact self_mem_orbitFinset H a

theorem trackedOrbits_disjoint (H : Subgroup (Equiv.Perm α)) (T : Finset α)
    (E F : trackedOrbits H T) (hne : E ≠ F) : Disjoint E.val F.val := by
  obtain ⟨a, _, ha⟩ := mem_trackedOrbits.mp E.property
  obtain ⟨b, _, hb⟩ := mem_trackedOrbits.mp F.property
  rcases orbitFinset_disjoint_or_eq H a b with hd | he
  · simpa only [ha, hb] using hd
  · exact False.elim (hne (Subtype.ext (ha.symm.trans (he.trans hb))))

theorem trackedOrbits_subset {H L : Subgroup (Equiv.Perm α)} (hle : L ≤ H)
    {T : Finset α} {a : α} (hT : T ⊆ orbitFinset H a)
    (E : trackedOrbits L T) : E.val ⊆ orbitFinset H a := by
  obtain ⟨b, hb, he⟩ := mem_trackedOrbits.mp E.property
  rw [← he]
  exact orbitFinset_subset_of_anchor hle (hT hb)

omit [DecidableEq α] in
theorem marked_orbitFinset_eq {H L : Subgroup (Equiv.Perm α)} {a : α} {k : ℕ}
    (s : VisibleStep a H L k) : orbitFinset L a = orbitFinset H a := by
  classical
  ext x
  simp only [orbitFinset, Set.mem_toFinset, marked_orbit_eq s]

omit [DecidableEq α] in
theorem anchored_small_orbit_zero {cutoff w d : ℕ} (hcutoff : 5 ≤ cutoff)
    {H : Subgroup (Equiv.Perm α)} {T : Finset α} (a : α)
    (hT : T ⊆ orbitFinset H a) (hc : (orbitFinset H a).card ≤ 2)
    (h : BoundedAnchoredChain cutoff T H w d) : w = 0 := by
  classical
  have hz : sigma cutoff a H = 0 :=
    sigma_zero_of_orbit_card_le_two hcutoff H a (by rwa [← orbitFinset_card])
  apply h.forget.zero_of_orbit_sigma hcutoff a _ hz
  intro b hb
  exact mem_orbitFinset.mp (hT hb)

end GI.Johnson
