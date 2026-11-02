import Workspace.CleanComplementLog

/-! The odd and even completions of Theorem A.17 under the logarithmic
threshold (LG1). The constructions are the earlier ones
(`CleanComplementOdd`, `CleanComplementOldRows`, `CleanComplementEven`,
`CleanComplementAssemble`); only the source of the localized lifts changes:
(LG2) now comes from Lemma A.15 (`CleanComplementLog.lean`) instead of the
linear bound `k > f`. -/

namespace GI

open Equiv

/-- The `(LG1)`-hypothesis on a block action: every block has degree below the
logarithmic threshold of `k`. -/
def CleanBlockAction.BelowLogThreshold {I V : Type*} [Fintype I] [DecidableEq I]
    [Fintype V] {G : Subgroup (Perm V)} (A : CleanBlockAction G I) (k : ℕ) : Prop :=
  ∀ i, max 8 (2 + Real.logb 2 (Fintype.card {x : V // A.label x = i})) < (k : ℝ)

namespace CleanBlockAction
variable {I : Type*} {V W : Type} [Fintype I] [DecidableEq I]
variable {G : Subgroup (Perm V)} (A : CleanBlockAction G I)

theorem KernelTransitive.relabel (hker : A.KernelTransitive) (e : V ≃ W) :
    (A.relabel e).KernelTransitive := by
  intro x y hxy
  obtain ⟨g, hg, hgxy⟩ := hker (e.symm x) (e.symm y) hxy
  refine ⟨relabelEquiv (G := G) e g, ?_, ?_⟩
  · rw [A.relabel_top e g, hg]
  · change e (g.val (e.symm x)) = y
    rw [hgxy, e.apply_symm_apply]

theorem BelowLogThreshold.relabel [Fintype V] [Fintype W] {k : ℕ}
    (h : A.BelowLogThreshold k) (e : V ≃ W) : (A.relabel e).BelowLogThreshold k := by
  intro i
  have he := Fintype.card_congr (A.relabelFiberEquiv e i)
  rw [← he]
  exact h i

end CleanBlockAction

variable {I : Type*} {V : Type} [Fintype I] [DecidableEq I] [Fintype V]
variable {G : Subgroup (Perm V)}

/-- The threshold of (LG1) forces `k ≥ 9`, once there is a block. -/
theorem nine_le_of_belowLogThreshold {A : CleanBlockAction G I} {k : ℕ}
    (h : A.BelowLogThreshold k) (i : I) : 9 ≤ k := by
  have h8 : (8 : ℝ) < k := lt_of_le_of_lt (le_max_left _ _) (h i)
  have : 8 < k := by exact_mod_cast h8
  omega

theorem localLiftAvailable_log (hcite : GI.Cited.TransitiveAffected)
    (A : CleanBlockAction G I) (hker : A.KernelTransitive) {k : ℕ}
    (hthr : A.BelowLogThreshold k) (T : Finset I) (hT : T.card = k) (hk : 5 ≤ k) :
    LocalLiftAvailable A (T : Set I) := by
  classical
  have hc : Fintype.card T = k := by rw [Fintype.card_coe, hT]
  exact CleanLocalization.localLiftAvailable_of_transitive_kernel A hcite hker T
    (Fintype.equivFinOfCardEq hc).symm hk (fun i _ => hthr i)

/-- The paper: "Choose `k`-sets `T₁, T₂` meeting in exactly one block index;
(LG1) ensures their existence. Use (LG2) to lift a `k`-cycle on `T₁` to `g` and
a `k`-cycle on `T₂` to `h`, fixing the complement pointwise. The cycles are
even because `k` is odd." -/
theorem localizedPair_exists_log (hcite : GI.Cited.TransitiveAffected)
    (A : CleanBlockAction G I) (hker : A.KernelTransitive) {k : ℕ}
    (hthr : A.BelowLogThreshold k) (hodd : Odd k) (hm : 2 * k - 1 ≤ Fintype.card I) :
    Nonempty (LocalizedBlockPair A) := by
  classical
  obtain ⟨i⟩ : Nonempty I := by
    obtain ⟨x⟩ : Nonempty (Fin (Fintype.card I)) := by
      have : 0 < Fintype.card I := by
        by_contra h0
        push Not at h0
        have hc : Fintype.card I = 0 := by omega
        rw [hc] at hm
        -- `2 * k - 1 ≤ 0` forces `k = 0`, contradicting oddness.
        have : k = 0 := by omega
        subst this
        exact (Nat.not_odd_zero hodd).elim
      exact ⟨⟨0, this⟩⟩
    exact ⟨(Fintype.equivFin I).symm x⟩
  have hk := nine_le_of_belowLogThreshold hthr i
  obtain ⟨T, U, a, hT, hU, hmeet⟩ := CleanLocalization.exists_pair_sets (by omega) hm
  obtain ⟨p, hp⟩ := CleanLocalization.even_full_support T (by omega) (by simpa [hT] using hodd)
  obtain ⟨q, hq⟩ := CleanLocalization.even_full_support U (by omega) (by simpa [hU] using hodd)
  obtain ⟨d, _⟩ := localized_pair_of_LG2 A T U
    (localLiftAvailable_log hcite A hker hthr T hT (by omega))
    (localLiftAvailable_log hcite A hker hthr U hU (by omega)) p q a hp hq hmeet
  exact ⟨d⟩

namespace CleanEvenConstruction
variable {I B W : Type} [Fintype I] [DecidableEq I] [Fintype B] [Fintype W]
variable {G : Subgroup (Perm ((B × I) ⊕ W))}
variable (A : CleanBlockAction G (Option I))

/-- The even case: "Choose a `k`-set `T` containing `a, ℓ` and avoiding `b, c`;
it exists by (LG1). Using (LG2), choose `h` with a `k`-cycle top on `T`
sending `a` to `ℓ`." Here `ℓ` is the index `none`. -/
theorem extraLift_exists_log (hcite : GI.Cited.TransitiveAffected)
    (hker : A.KernelTransitive) {k : ℕ} (hthr : A.BelowLogThreshold k) (hodd : Odd k)
    (hm : 2 * k - 1 ≤ Fintype.card (Option I))
    (a b c : I) (hab : a ≠ b) (hac : a ≠ c) : Nonempty (ExtraLift A a b c) := by
  classical
  have hk := nine_le_of_belowLogThreshold hthr none
  -- (LG1) gives `k + 2 ≤ 2k - 1 ≤ m`.
  obtain ⟨T, hT, ha, hz, hb, hc⟩ := CleanLocalization.exists_two_containing_avoiding
    (k := k) (by omega) (by omega) (some a) none (some b) (some c)
    (by simp) (by simpa using Ne.symm hab) (by simp) (by simpa using Ne.symm hac) (by simp)
  obtain ⟨p, hp, hsend⟩ := CleanLocalization.even_full_support_send T (by omega)
    (by simpa [hT] using hodd) (some a) none ha hz (by simp)
  exact extraLift_of_LG2 A T (localLiftAvailable_log hcite A hker hthr T hT (by omega))
    p a b c hp hsend hb hc

end CleanEvenConstruction

variable {J : Type} [Fintype J] [DecidableEq J]

/-- The odd completion, `m = 2r + 1`, with blocks indexed by
`Option (J × Bool)`: the central block is `none`, and the pairs are
`(some (j, false), some (j, true))`. -/
noncomputable def logOddComplement (hcite : GI.Cited.TransitiveAffected)
    (A : CleanBlockAction G (Option (J × Bool))) (hker : A.KernelTransitive) {k : ℕ}
    (hthr : A.BelowLogThreshold k) (hodd : Odd k)
    (hm : 2 * k - 1 ≤ Fintype.card (Option (J × Bool))) : PureComplement A := by
  classical
  let d := Classical.choice (localizedPair_exists_log hcite A hker hthr hodd hm)
  have hk := nine_le_of_belowLogThreshold hthr none
  have hc : 5 ≤ Fintype.card (Option (J × Bool)) := by omega
  exact {
    Fiber := (CleanOddConstruction.system d hc).Center
    base := (CleanOddConstruction.system d hc).centerBase
    coordinates := (CleanOddConstruction.system d hc).coordinates
    sectionHom := CleanOddConstruction.sectionHom d hc
    label_coordinates := CleanOddConstruction.coordinates_label d hc
    pure := CleanOddConstruction.section_pure d hc
    top_section := CleanOddConstruction.top_section d hc
    isComplement := CleanOddConstruction.kernel_complement d hc }

/-- The even completion, `m = 2r + 2`: first the odd construction on the blocks
other than `none`, then one extra clean cycle through the block `none`. -/
noncomputable def logEvenComplement (hcite : GI.Cited.TransitiveAffected)
    (A : CleanBlockAction G (Option (Option (J × Bool)))) (hker : A.KernelTransitive)
    {k : ℕ} (hthr : A.BelowLogThreshold k) (hodd : Odd k)
    (hm : 2 * k - 1 ≤ Fintype.card (Option (Option (J × Bool)))) : PureComplement A := by
  classical
  let d := Classical.choice (localizedPair_exists_log hcite A hker hthr hodd hm)
  have hk := nine_le_of_belowLogThreshold hthr none
  have hc : 5 ≤ Fintype.card (Option (Option (J × Bool))) := by omega
  have holdcard : 2 < (Finset.univ : Finset (Option (J × Bool))).card := by
    rw [Finset.card_univ]
    have he := Fintype.card_option (α := Option (J × Bool))
    omega
  have hex : ∃ t : Option (J × Bool) × Option (J × Bool) × Option (J × Bool),
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 := by
    obtain ⟨a, b, c, _, _, _, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp holdcard
    exact ⟨(a, b, c), hab, hac, hbc⟩
  let a := (Classical.choose hex).1
  let b := (Classical.choose hex).2.1
  let c := (Classical.choose hex).2.2
  have hab : a ≠ b := (Classical.choose_spec hex).1
  have hac : a ≠ c := (Classical.choose_spec hex).2.1
  have hbc : b ≠ c := (Classical.choose_spec hex).2.2
  have hker' : (CleanEvenAssembly.oldAction d hc).KernelTransitive :=
    hker.relabel A (CleanOldRows.coordinates d hc).symm
  have hthr' : (CleanEvenAssembly.oldAction d hc).BelowLogThreshold k :=
    hthr.relabel A (CleanOldRows.coordinates d hc).symm
  let z := Classical.choice (CleanEvenConstruction.extraLift_exists_log
    (CleanEvenAssembly.oldAction d hc) hcite hker' hthr' hodd hm a b c hab hac)
  exact {
    Fiber := (CleanOldRows.system d hc).Center
    base := (CleanOldRows.system d hc).centerBase
    coordinates := CleanEvenAssembly.coordinates d hc z hab hbc
    sectionHom := CleanEvenAssembly.sectionHom d hc z hab hac hbc
    label_coordinates := CleanEvenAssembly.coordinates_label d hc z hab hbc
    pure := CleanEvenAssembly.section_pure d hc z hab hac hbc
    top_section := CleanEvenAssembly.top_section d hc z hab hac hbc
    isComplement := CleanEvenAssembly.kernel_complement d hc z hab hac hbc }

end GI
