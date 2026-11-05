module

public import Workspace.CertificateEndpoint

@[expose] public section

/-!
# Termination of the endpoint procedure and the two certificates

Paper, Appendix A, `sec:certificates`, "Endpoint construction":

* "The extra union in step 4 is the modification. It is nonempty."
  (`extraSet_nonempty`), proved as in the paper: the image of `(A_i)_{(U_i)}` is
  normal in `Alt(T)`, hence trivial, and a nonabelian simple quotient that kills
  the pointwise stabilizer of `U_i` is visible on one orbit (Lemma A.4, through
  `GI.simple_quotient_localization`).
* "Every update adds a nonempty `A_i`-invariant set, so there are at most `n`
  updates." (`win_card_lt`, `stopped_card`, `stopTime_le`).
* "At full termination, `K(T)` preserves `x` on `W_i` and fixes its complement,
  so `K(T) ≤ Aut_G(x)` and its image contains the required alternating group.
  At nonfull termination, `Aut_{P_T}(x) ≤ A_i` has proper image."
  (`full_certificate`, `nonfull_certificate`).

Throughout, `Q` is a nonabelian simple group (in the paper `Q = Alt(T)` with
`|T| = κ ≥ 5`).
-/

namespace GI.Endpoint

open Equiv Equiv.Perm

variable {V C Q : Type*} [Group Q] [DecidableEq V] [Fintype V]
  {P : Subgroup (Perm V)} (phi : P →* Q)

/-- The test map restricted to a subgroup `A ≤ P`. -/
def restrictTo {A : Subgroup (Perm V)} (hAP : A ≤ P) : A →* Q :=
  phi.comp (Subgroup.inclusion hAP)

omit [DecidableEq V] [Fintype V] in
theorem restrictTo_apply {A : Subgroup (Perm V)} (hAP : A ≤ P) (a : A) :
    restrictTo phi hAP a = phi ⟨a, hAP a.2⟩ := rfl

omit [DecidableEq V] [Fintype V] in
theorem restrictTo_surjective {A : Subgroup (Perm V)} (hAP : A ≤ P) (hA : Full phi A) :
    Function.Surjective (restrictTo phi hAP) := by
  intro q
  have hq : q ∈ img phi A := by rw [hA]; trivial
  obtain ⟨a, ha, rfl⟩ := (mem_img phi).1 hq
  exact ⟨⟨a, ha⟩, rfl⟩

omit [DecidableEq V] [Fintype V] in
theorem outside_invariant {A : Subgroup (Perm V)} {W : Finset V} (hW : Invariant A W)
    {a : Perm V} (ha : a ∈ A) {u : V} (hu : u ∈ outside W) : a u ∈ outside W := by
  simp only [outside, Set.mem_setOf_eq] at *
  rwa [hW a ha u]

omit [DecidableEq V] [Fintype V] in
/-- At a full stage, the pointwise stabilizer of `U = Ω \ W` has a normal image in
`φ(A) = Q`, so if it is not all of `Q`, it is trivial. -/
theorem fixOutside_killed [IsSimpleGroup Q] {A : Subgroup (Perm V)} (hAP : A ≤ P)
    {W : Finset V} (hW : Invariant A W) (hA : Full phi A)
    (hnot : ¬ Full phi (fix A (outside W))) :
    ((fix A (outside W)).subgroupOf A).map (restrictTo phi hAP) = ⊥ := by
  have hnormal : ((fix A (outside W)).subgroupOf A).Normal := by
    constructor
    intro k hk a
    rw [Subgroup.mem_subgroupOf, mem_fix] at hk ⊢
    refine ⟨(a * k * a⁻¹).2, fun u hu => ?_⟩
    have hu' := outside_invariant hW (A.inv_mem a.2) hu
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply]
    rw [hk.2 _ hu']
    simp
  rcases (hnormal.map _ (restrictTo_surjective phi hAP hA)).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    apply hnot
    rw [Full, eq_top_iff]
    intro q _
    have hq : q ∈ ((fix A (outside W)).subgroupOf A).map (restrictTo phi hAP) := by
      rw [h]; trivial
    obtain ⟨a, ha, rfl⟩ := hq
    exact (mem_img phi).2 ⟨⟨a, hAP a.2⟩, Subgroup.mem_subgroupOf.1 ha, rfl⟩

/-- **Rule 4 is productive**: "The extra union in step 4 ... is nonempty." -/
theorem extraSet_nonempty [IsSimpleGroup Q] (nonabelian : ∃ a b : Q, a * b ≠ b * a)
    {A : Subgroup (Perm V)} (hAP : A ≤ P) {W : Finset V} (hW : Invariant A W)
    (hA : Full phi A) (hnot : ¬ Full phi (fix A (outside W))) :
    (extraSet phi A W).Nonempty := by
  classical
  let ψ := restrictTo phi hAP
  have hψ := restrictTo_surjective phi hAP hA
  have hkilled := fixOutside_killed phi hAP hW hA hnot
  let points := (Finset.univ.filter (fun v : V => v ∉ W)).toList
  let kernels := points.map (GI.orbitKernel A)
  have hnormal : ∀ K ∈ kernels, K.Normal := by
    intro K hK
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hK
    exact GI.orbitKernel_normal A v
  -- The common kernel fixes `U` pointwise, so it is killed.
  have hcommon : GI.commonKernel kernels ≤ ψ.ker := by
    intro u hu
    have hfixU : (u : Perm V) ∈ fix A (outside W) := by
      refine mem_fix.2 ⟨u.2, fun v hv => ?_⟩
      have hpoint : v ∈ points := by simpa [points, outside] using hv
      have hK : GI.orbitKernel A v ∈ kernels := List.mem_map.mpr ⟨v, hpoint, rfl⟩
      have hfix := (GI.mem_commonKernel_iff kernels u).mp hu _ hK (1 : A)
      simpa [Perm.smul_def] using hfix
    have : ψ u ∈ ((fix A (outside W)).subgroupOf A).map ψ :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hfixU)
    rw [hkilled, Subgroup.mem_bot] at this
    exact this
  -- Localization (Lemma A.4): some orbit kernel is killed.
  obtain ⟨K, hK, hbot⟩ := GI.simple_quotient_localization ψ hψ nonabelian kernels hnormal hcommon
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hK
  have hvout : v ∉ W := by simpa [points] using hv
  refine ⟨v, (mem_extraSet phi).2 ⟨hvout, ?_⟩⟩
  rw [VisibleOrbit, eq_bot_iff]
  intro q hq
  obtain ⟨a, ha, rfl⟩ := (mem_img phi).1 hq
  obtain ⟨haA, hafix⟩ := mem_fix.1 ha
  have hmem : (⟨a, haA⟩ : A) ∈ GI.orbitKernel A v := by
    intro w
    simpa [Perm.smul_def] using hafix _ ⟨w, w.2, rfl⟩
  have : ψ ⟨a, haA⟩ ∈ (GI.orbitKernel A v).map ψ := Subgroup.mem_map_of_mem _ hmem
  rw [hbot] at this
  exact this

theorem increment_eq_empty_of_stopped {A : Subgroup (Perm V)} {W : Finset V}
    (h : Stopped phi A W) : increment phi A W = ∅ := by
  classical
  unfold increment
  rcases h with h | ⟨hE, hK⟩
  · simp [h]
  · simp [hE, hK]

theorem increment_disjoint (A : Subgroup (Perm V)) (W : Finset V) {v : V}
    (hv : v ∈ increment phi A W) : v ∉ W := by
  classical
  unfold increment at hv
  split_ifs at hv <;>
    first
    | exact absurd hv (Finset.notMem_empty v)
    | exact ((mem_affectedSet phi).1 hv).1
    | exact ((mem_extraSet phi).1 hv).1

/-- "Every update adds a nonempty `A_i`-invariant set." -/
theorem increment_nonempty [IsSimpleGroup Q] (nonabelian : ∃ a b : Q, a * b ≠ b * a)
    {A : Subgroup (Perm V)} (hAP : A ≤ P) {W : Finset V} (hW : Invariant A W)
    (h : ¬ Stopped phi A W) : (increment phi A W).Nonempty := by
  classical
  have hA : Full phi A := by by_contra hn; exact h (Or.inl hn)
  unfold increment
  by_cases hE : (affectedSet phi A W).Nonempty
  · simp [hA, hE]
  · have hK : ¬ Full phi (fix A (outside W)) := by
      intro hK
      exact h (Or.inr ⟨Finset.not_nonempty_iff_eq_empty.1 hE, hK⟩)
    simp only [hA, not_true_eq_false, ↓reduceIte, hE, hK]
    exact extraSet_nonempty phi nonabelian hAP hW hA hK

theorem stage_succ_of_stopped (x : V → C) {t : ℕ}
    (h : Stopped phi (grp phi x t) (win phi x t)) : stage phi x (t + 1) = stage phi x t := by
  have he : inc phi x t = ∅ := increment_eq_empty_of_stopped phi h
  apply Prod.ext
  · change grp phi x (t + 1) = grp phi x t
    rw [grp_succ, he, automorphisms_mask_empty]
  · change win phi x (t + 1) = win phi x t
    rw [win_succ, he, Finset.union_empty]

/-- A stopped stage stays stopped and the sequence is constant from there on. -/
theorem stage_eq_of_stopped (x : V → C) {t : ℕ}
    (h : Stopped phi (grp phi x t) (win phi x t)) : ∀ s, t ≤ s → stage phi x s = stage phi x t := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => rfl
  | succ s _ ih =>
    have hs : Stopped phi (grp phi x s) (win phi x s) := by
      simp only [grp, win, ih]; exact h
    rw [stage_succ_of_stopped phi x hs, ih]

/-- An update strictly enlarges the window. -/
theorem win_card_lt [IsSimpleGroup Q] (nonabelian : ∃ a b : Q, a * b ≠ b * a) (x : V → C)
    {t : ℕ} (h : ¬ Stopped phi (grp phi x t) (win phi x t)) :
    (win phi x t).card < (win phi x (t + 1)).card := by
  obtain ⟨v, hv⟩ := increment_nonempty phi nonabelian (grp_le phi x t) (win_invariant phi x t) h
  have hvout := increment_disjoint phi _ _ hv
  rw [win_succ]
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, fun he => hvout ?_⟩
  rw [he]
  exact Finset.mem_union_right _ hv

/-- A window that is all of `Ω` gives a stop. -/
theorem stopped_of_win_univ {A : Subgroup (Perm V)} {W : Finset V} (hW : W = Finset.univ) :
    Stopped phi A W := by
  by_cases hA : Full phi A
  · right
    refine ⟨?_, ?_⟩
    · ext v; simp [mem_affectedSet, hW]
    · have : fix A (outside W) = A := by
        ext g; simp [mem_fix, outside, hW]
      rw [this]; exact hA
  · exact Or.inl hA

theorem stopped_or_card [IsSimpleGroup Q] (nonabelian : ∃ a b : Q, a * b ≠ b * a)
    (x : V → C) (t : ℕ) : Stopped phi (grp phi x t) (win phi x t) ∨ t ≤ (win phi x t).card := by
  induction t with
  | zero => exact Or.inr (Nat.zero_le _)
  | succ t ih =>
    by_cases hs : Stopped phi (grp phi x t) (win phi x t)
    · left
      simp only [grp, win, stage_succ_of_stopped phi x hs]
      exact hs
    · right
      exact Nat.succ_le_of_lt ((ih.resolve_left hs).trans_lt (win_card_lt phi nonabelian x hs))

/-- **At most `n` updates.** The stage with index `n = |Ω|` is stopped. -/
theorem stopped_card [IsSimpleGroup Q] (nonabelian : ∃ a b : Q, a * b ≠ b * a) (x : V → C) :
    Stopped phi (grp phi x (Fintype.card V)) (win phi x (Fintype.card V)) := by
  rcases stopped_or_card phi nonabelian x (Fintype.card V) with h | h
  · exact h
  · apply stopped_of_win_univ
    apply Finset.eq_univ_of_card
    exact le_antisymm (Finset.card_le_univ _) h

/-- The number of updates: the first stopped stage. -/
noncomputable def stopTime [IsSimpleGroup Q] (nonabelian : ∃ a b : Q, a * b ≠ b * a)
    (x : V → C) : ℕ := by
  classical
  exact Nat.find (p := fun t => Stopped phi (grp phi x t) (win phi x t))
    ⟨_, stopped_card phi nonabelian x⟩

theorem stopTime_stopped [IsSimpleGroup Q] (nonabelian : ∃ a b : Q, a * b ≠ b * a)
    (x : V → C) :
    Stopped phi (grp phi x (stopTime phi nonabelian x)) (win phi x (stopTime phi nonabelian x)) := by
  classical
  exact Nat.find_spec (p := fun t => Stopped phi (grp phi x t) (win phi x t))
    ⟨_, stopped_card phi nonabelian x⟩

theorem not_stopped_of_lt_stopTime [IsSimpleGroup Q] (nonabelian : ∃ a b : Q, a * b ≠ b * a)
    (x : V → C) {t : ℕ} (ht : t < stopTime phi nonabelian x) :
    ¬ Stopped phi (grp phi x t) (win phi x t) := by
  classical
  exact Nat.find_min (p := fun t => Stopped phi (grp phi x t) (win phi x t))
    ⟨_, stopped_card phi nonabelian x⟩ ht

/-- "There are at most `n` updates." -/
theorem stopTime_le [IsSimpleGroup Q] (nonabelian : ∃ a b : Q, a * b ≠ b * a) (x : V → C) :
    stopTime phi nonabelian x ≤ Fintype.card V := by
  classical
  exact Nat.find_min' (p := fun t => Stopped phi (grp phi x t) (win phi x t))
    ⟨_, stopped_card phi nonabelian x⟩ (stopped_card phi nonabelian x)

/-- The final stage, taken at index `n = |Ω|`, equals the stage at the stopping time. -/
theorem stage_card_eq_stopTime [IsSimpleGroup Q] (nonabelian : ∃ a b : Q, a * b ≠ b * a)
    (x : V → C) :
    stage phi x (Fintype.card V) = stage phi x (stopTime phi nonabelian x) :=
  stage_eq_of_stopped phi x (stopTime_stopped phi nonabelian x) _ (stopTime_le phi nonabelian x)

/-! ### The final stage and the two certificates -/

/-- The final group `A_final` (stage `n = |Ω|`; the sequence is constant after the stop). -/
noncomputable abbrev finalGrp (x : V → C) : Subgroup (Perm V) := grp phi x (Fintype.card V)

/-- The final window `W(x, T)`. -/
noncomputable abbrev finalWin (x : V → C) : Finset V := win phi x (Fintype.card V)

/-- The full certificate `K(T) = (A_final)_{(Ω \ W_final)}`. -/
noncomputable abbrev fullCert (x : V → C) : Subgroup (Perm V) :=
  fix (finalGrp phi x) (outside (finalWin phi x))

/-- The certificate is full when `φ(A_final) = Q`. -/
def IsFull (x : V → C) : Prop := Full phi (finalGrp phi x)

/-- **Full termination.** `K(T)` consists of automorphisms of the whole string
`x` (in `P`), and its image is all of `Q`. -/
theorem full_certificate [IsSimpleGroup Q] (nonabelian : ∃ a b : Q, a * b ≠ b * a)
    (x : V → C) (hfull : IsFull phi x) :
    fullCert phi x ≤ automorphisms P x ∧ Full phi (fullCert phi x) := by
  refine ⟨fun g hg => ?_, ?_⟩
  · obtain ⟨hgA, hgfix⟩ := mem_fix.1 hg
    refine ⟨grp_le phi x _ hgA, fun v => ?_⟩
    by_cases hv : v ∈ finalWin phi x
    · exact grp_colors phi x _ g hgA v hv
    · rw [hgfix v hv]
  · rcases stopped_card phi nonabelian x with h | ⟨_, h⟩
    · exact absurd hfull h
    · exact h

/-- The full certificate is a subgroup of actual automorphisms with no proof
obligations on `Q`. -/
theorem fullCert_le_automorphisms (x : V → C) : fullCert phi x ≤ automorphisms P x := by
  intro g hg
  obtain ⟨hgA, hgfix⟩ := mem_fix.1 hg
  refine ⟨grp_le phi x _ hgA, fun v => ?_⟩
  by_cases hv : v ∈ finalWin phi x
  · exact grp_colors phi x _ g hgA v hv
  · rw [hgfix v hv]

/-- **Nonfull termination.** `Aut_P(x) ≤ A_final` has a proper image. -/
theorem nonfull_certificate (x : V → C) (h : ¬ IsFull phi x) :
    automorphisms P x ≤ finalGrp phi x ∧ ¬ Full phi (automorphisms P x) := by
  refine ⟨automorphisms_le_grp phi x _, fun hf => h ?_⟩
  exact eq_top_iff.2 (hf ▸ img_mono phi (automorphisms_le_grp phi x _))

end GI.Endpoint
