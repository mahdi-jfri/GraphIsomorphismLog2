import Workspace.PairRefinement

namespace GI.PairRefinement

variable {n : ℕ}

def agreeingPairs (c : Coloring n) : Finset (Domain n × Domain n) :=
  Finset.univ.filter (fun ab => c ab.1 = c ab.2)

def Stable (c : Coloring n) : Prop :=
  ∀ a b : Domain n, c a = c b → step c a = step c b

instance stableDecidable (c : Coloring n) : Decidable (Stable c) :=
  inferInstanceAs (Decidable (∀ a b : Domain n, c a = c b → step c a = step c b))

theorem agreeingPairs_step_subset (c : Coloring n) : agreeingPairs (step c) ⊆ agreeingPairs c := by
  intro ab hab
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, step_refines c (Finset.mem_filter.mp hab).2⟩

theorem strict_progress (c : Coloring n) (h : ¬ Stable c) :
    (agreeingPairs (step c)).card < (agreeingPairs c).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨agreeingPairs_step_subset c, ?_⟩
  intro heq
  apply h
  intro a b hab
  have hm : (a, b) ∈ agreeingPairs c := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩
  rw [← heq] at hm
  exact (Finset.mem_filter.mp hm).2

theorem agreeingPairs_card_le (c : Coloring n) :
    (agreeingPairs c).card ≤ (Fintype.card (Domain n)) ^ 2 := by
  exact (Finset.card_filter_le _ _).trans (by simp [pow_two])

/-- Fuel is discharged by a proved strict drop of actual agreeing pairs.
The stable branch returns immediately. Every refinement materializes its arrays. -/
def settle : ℕ → Coloring n → Coloring n
  | 0, c => c
  | fuel + 1, c => if Stable c then c else settle fuel (step c)

theorem settle_stable (fuel : ℕ) (c : Coloring n)
    (hbound : (agreeingPairs c).card ≤ fuel) : Stable (settle fuel c) := by
  induction fuel generalizing c with
  | zero =>
      change Stable c
      by_contra hc
      have hp := strict_progress c hc
      omega
  | succ fuel ih =>
      by_cases hc : Stable c
      · simpa only [settle, if_pos hc] using hc
      · simp only [settle, if_neg hc]
        apply ih
        have hp := strict_progress c hc
        omega

theorem settle_refines (fuel : ℕ) (c : Coloring n) {a b : Domain n}
    (h : settle fuel c a = settle fuel c b) : c a = c b := by
  induction fuel generalizing c with
  | zero => exact h
  | succ fuel ih =>
      by_cases hc : Stable c
      · simpa only [settle, if_pos hc] using h
      · simp only [settle, if_neg hc] at h
        exact step_refines c (ih (step c) h)

theorem settle_transports_iff (fuel : ℕ) (c : Coloring n) (source target : Bool)
    (p : Equiv.Perm (Fin n)) : Transports (settle fuel c) source target p ↔
      Transports c source target p := by
  induction fuel generalizing c with
  | zero => rfl
  | succ fuel ih =>
      by_cases hc : Stable c
      · simp only [settle, if_pos hc]
      · simp only [settle, if_neg hc]
        exact (ih (step c)).trans (step_transports_iff c source target p)

def run (c : Coloring n) : Coloring n := settle ((agreeingPairs c).card) c

theorem run_stable (c : Coloring n) : Stable (run c) := settle_stable _ c le_rfl

theorem run_refines (c : Coloring n) {a b : Domain n} (h : run c a = run c b) : c a = c b :=
  settle_refines _ c h

theorem run_transports_iff (c : Coloring n) (source target : Bool)
    (p : Equiv.Perm (Fin n)) : Transports (run c) source target p ↔
      Transports c source target p := settle_transports_iff _ c source target p

/-- Intersection numbers, converse colors and the diagonal depend only on
the returned color, also across the two jointly refined domains. -/
def Coherent (c : Coloring n) : Prop :=
  ∀ a b : Domain n, c a = c b →
    diagonal a = diagonal b ∧ c (transpose a) = c (transpose b) ∧
      ∀ i j : Color n, intersection c a i j = intersection c b i j

theorem stable_coherent (c : Coloring n) (h : Stable c) : Coherent c := by
  intro a b hab
  have hs := (signature_eq_iff c a b).mp ((step_eq_iff c a b).mp (h a b hab))
  exact ⟨hs.2.2.1, hs.2.1, hs.2.2.2⟩

theorem run_coherent (c : Coloring n) : Coherent (run c) :=
  stable_coherent (run c) (run_stable c)

end GI.PairRefinement
