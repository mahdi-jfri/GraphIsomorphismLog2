import Workspace.Paper.Caps

/-!
# Lemma A.12 with an explicit label threshold

Lemma A.12 (`GI.Paper.lem_exact_configuration`) says "for every fixed `β > max{1-δ, 1/2}` and all
sufficiently large `q`". Its proof picks an integer `N ≥ 4` with `1/2 + 1/N ≤ β` and works for
`q ≥ 2(4·4^N + 8)`. This file states the lemma with that threshold
(`lem_exact_configuration_explicit`), so that the parameters can be checked against it
(Section 7.5 (i): "Enlarge it [`q₀`] as needed for the coherent-configuration cap bounds").

For `β ≥ 3/4` one can take `N = 4`, and the threshold is `a12Threshold = 2(4·4⁴ + 8) = 2064`
(`lem_exact_configuration_2064`). The example value `β = 9/10` of Section 7.5 is of this kind.
-/

namespace GI.Paper

open Equiv GI.PairRefinement GI.ExactConfiguration

/-- **Lemma A.12 with an explicit threshold.** For an integer `N ≥ 4` with `1/2 + 1/N ≤ β`, the
conclusions of `lem_exact_configuration` hold for every `q ≥ 2(4·4^N + 8)`. -/
theorem lem_exact_configuration_explicit {δ β : ℝ} (hβ : max (1 - δ) (1 / 2) < β) {N : ℕ}
    (hN : 4 ≤ N) (hβN : 1 / 2 + 1 / (N : ℝ) ≤ β) :
    ∀ (Γ : Type) [Fintype Γ] [DecidableEq Γ] (n : ℕ) (c : Coloring n)
      (side : Bool) (ι : Fin n ↪ Γ), Coherent c → Homogeneous c side →
      NontrivialOffDiagonal c side → δ * Fintype.card Γ ≤ n →
      2 * (4 * 4 ^ N + 8) ≤ Fintype.card Γ →
      n * n ≤ Fintype.card Γ * Fintype.card Γ ∧
      (∀ (target : Bool) (g₀ : Perm Γ), g₀ ∈ configTransporter ι c side target →
        ∀ g, g ∈ configTransporter ι c side target ↔ g₀⁻¹ * g ∈ configGroup ι c side) ∧
      ∀ K : Subgroup (Perm Γ), K ≤ configGroup ι c side →
        (aw K : ℝ) ≤ β * Fintype.card Γ := by
  have hδβ : 1 - δ < β := lt_of_le_of_lt (le_max_left _ _) hβ
  intro Γ _ _ n c side ι hc hh hn hC hq
  refine ⟨?_, ?_, ?_⟩
  · have : n ≤ Fintype.card Γ := by simpa using Fintype.card_le_of_injective ι ι.injective
    exact Nat.mul_le_mul this this
  · exact fun target g₀ h₀ g => configTransporter_coset ι c side target h₀ g
  · intro K hK
    have hcap := config_cap c hc side hh hn ι K hK hN hβN hδβ hC hq
    have hle := (aw_le_iff _).mpr hcap
    have hβq : 0 ≤ β * Fintype.card Γ := by
      have : (0 : ℝ) ≤ Fintype.card Γ := Nat.cast_nonneg _
      have : (0 : ℝ) < β := by
        have := le_max_right (1 - δ) (1 / 2 : ℝ)
        linarith
      positivity
    exact (Nat.cast_le.mpr hle).trans (Nat.floor_le hβq)

/-- The threshold of Lemma A.12 for `β ≥ 3/4`: `2(4·4⁴ + 8) = 2064`. -/
def a12Threshold : ℕ := 2 * (4 * 4 ^ 4 + 8)

theorem a12Threshold_eq : a12Threshold = 2064 := by norm_num [a12Threshold]

/-- **Lemma A.12 for `β ≥ 3/4`, with threshold `2064`** (take `N = 4`: `1/2 + 1/4 ≤ β`). -/
theorem lem_exact_configuration_2064 {δ β : ℝ} (hβ : max (1 - δ) (1 / 2) < β) (h34 : 3 / 4 ≤ β) :
    ∀ (Γ : Type) [Fintype Γ] [DecidableEq Γ] (n : ℕ) (c : Coloring n)
      (side : Bool) (ι : Fin n ↪ Γ), Coherent c → Homogeneous c side →
      NontrivialOffDiagonal c side → δ * Fintype.card Γ ≤ n →
      a12Threshold ≤ Fintype.card Γ →
      n * n ≤ Fintype.card Γ * Fintype.card Γ ∧
      (∀ (target : Bool) (g₀ : Perm Γ), g₀ ∈ configTransporter ι c side target →
        ∀ g, g ∈ configTransporter ι c side target ↔ g₀⁻¹ * g ∈ configGroup ι c side) ∧
      ∀ K : Subgroup (Perm Γ), K ≤ configGroup ι c side →
        (aw K : ℝ) ≤ β * Fintype.card Γ :=
  lem_exact_configuration_explicit hβ le_rfl (by norm_num; linarith)

end GI.Paper
