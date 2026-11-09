module

public import Workspace.Degree.LinearHard

/-!
# Completely reducible linear groups in the class

`GI.Degree.deg_linear`: if `H ≤ GL(V)` is completely reducible and in `Γ̂_D`, `D ≥ 6`, then
`D³ q⁶ |H|³ ≤ |V|^E`, with `E = O(log D)`. So `log |H| ≤ C log D log |V|`
(`GI.Degree.log_card_linear_le`).

The proof is the induction of `GI.Proved.palfyLinear`, with `GI.Degree.deg_imprimitive`,
`GI.Degree.deg_field_step` and `GI.Degree.deg_hard` for the three cases.
-/

@[expose] public section

namespace GI.Degree

open GI.Proved

theorem deg_linear_aux {D : ℕ} (hD : 6 ≤ D) : ∀ (n d : ℕ) (K V : Type) [Field K] [Finite K]
    [AddCommGroup V] [Module K V] [Finite V] [Nontrivial V], Nat.card V = n →
    Nat.card V - Nat.card K = d →
    ∀ H : Subgroup (Module.End K V)ˣ, GammaHat D H → palfyCR H →
      D ^ 3 * Nat.card K ^ 6 * Nat.card H ^ 3 ≤ Nat.card V ^ degE D := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
  intro K V _ _ _ _ _ _ hn hd H hs hcr
  -- the two induction hypotheses
  have ihV : DegIH D K (degE D) n := by
    intro W _ _ _ _ hW G hG hGcr
    exact ihn _ hW _ K W rfl rfl G hG hGcr
  have ihF : DegIH2 D (degE D) n (Nat.card K) := by
    intro L _ _ W _ _ _ _ hW hL G hG hGcr
    have hLW := palfy_card_field_le L W
    exact ihd _ (by omega) L W hW rfl G hG hGcr
  by_cases hred : ∃ W : Submodule K V, palfyInv H W ∧ W ≠ ⊥ ∧ W ≠ ⊤
  · -- reducible
    obtain ⟨W, hW, hW0, hWt⟩ := hred
    obtain ⟨W', hW', hc⟩ := hcr W hW
    obtain ⟨hcard, hVc⟩ := palfy_card_le_split hW hW' hc
    haveI : Nontrivial W := (Submodule.nontrivial_iff_ne_bot).mpr hW0
    haveI : Nontrivial W' := (Submodule.nontrivial_iff_ne_bot).mpr (fun h => hWt (by
      have := hc.sup_eq_top
      rwa [h, sup_bot_eq] at this))
    have h1 : 1 < Nat.card W := Finite.one_lt_card
    have h2 : 1 < Nat.card W' := Finite.one_lt_card
    have hWlt : Nat.card W < Nat.card V := by rw [hVc]; nlinarith
    have hW'lt : Nat.card W' < Nat.card V := by rw [hVc]; nlinarith
    have b1 := ihV W (hn ▸ hWlt) _ (hs.of_surjective _ (palfyRes H W hW).rangeRestrict_surjective)
      (palfyCR_res hcr hW)
    have b2 := ihV W' (hn ▸ hW'lt) _
      (hs.of_surjective _ (palfyRes H W' hW').rangeRestrict_surjective) (palfyCR_res hcr hW')
    set c := D ^ 3 * Nat.card K ^ 6
    have hc1 : 1 ≤ c := Nat.mul_pos (pow_pos (by omega) 3) (pow_pos Nat.card_pos 6)
    calc c * Nat.card H ^ 3
        ≤ c * (Nat.card (palfyResGrp H W hW) * Nat.card (palfyResGrp H W' hW')) ^ 3 := by
          gcongr
      _ = (c * Nat.card (palfyResGrp H W hW) ^ 3) * Nat.card (palfyResGrp H W' hW') ^ 3 := by
          ring
      _ ≤ (c * Nat.card (palfyResGrp H W hW) ^ 3) *
          (c * Nat.card (palfyResGrp H W' hW') ^ 3) := by
          gcongr
          exact Nat.le_mul_of_pos_left _ hc1
      _ ≤ Nat.card W ^ degE D * Nat.card W' ^ degE D := Nat.mul_le_mul b1 b2
      _ = Nat.card V ^ degE D := by rw [hVc, mul_pow]
  push Not at hred
  have hH : palfyIrr H := by
    intro W hW
    by_cases h0 : W = ⊥
    · exact Or.inl h0
    · exact Or.inr (hred W hW h0)
  by_cases hab : palfyAbSc H
  · exact deg_hard hD hs hH hab
  -- a non-scalar abelian normal subgroup
  unfold palfyAbSc at hab
  push Not at hab
  obtain ⟨A, hAH, hAc, a, ha, hna⟩ := hab
  have hR := palfyAdj_alg hAH hAc
  by_cases hid : ∃ f ∈ palfyAdj A, IsIdempotentElem f ∧ f ≠ 0 ∧ f ≠ 1
  · obtain ⟨f, hfR, hf, hf0, hf1⟩ := hid
    exact deg_imprimitive hD (hn ▸ ihV) hs hH hR hfR hf hf0 hf1
  push Not at hid
  have hF : IsField (palfyAdj A) := palfy_isField hH hR (fun e he hidem => by
    by_cases h0 : e = 0
    · exact Or.inl h0
    · exact Or.inr (hid e he hidem h0))
  have hne : palfyAdj A ≠ ⊥ := by
    intro hbot
    apply hna
    have : (a : Module.End K V) ∈ (⊥ : Subalgebra K (Module.End K V)) := hbot ▸ palfyAdj_mem ha
    obtain ⟨k, hk⟩ := Algebra.mem_bot.mp this
    exact ⟨k, hk⟩
  exact deg_field_step (hn ▸ ihF) hs hH hAH hAc hF hne

/-- **The bound for linear groups, in integers.** -/
theorem deg_linear {D : ℕ} (hD : 6 ≤ D) (K V : Type) [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [Finite V] [Nontrivial V] (H : Subgroup (Module.End K V)ˣ) (hcl : GammaHat D H)
    (hcr : palfyCR H) :
    D ^ 3 * Nat.card K ^ 6 * Nat.card H ^ 3 ≤ Nat.card V ^ degE D :=
  deg_linear_aux hD _ _ K V rfl rfl H hcl hcr

/-- The constant of `GI.Degree.log_card_linear_le`. -/
noncomputable def linC : ℝ := 561 / Real.log 2

theorem linC_nonneg : 0 ≤ linC := by
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  unfold linC
  positivity

/-- **The bound for linear groups.** A completely reducible linear group in `Γ̂_D` has
`log |H| ≤ C log D log |V|`. -/
theorem log_card_linear_le {D : ℕ} (hD : 6 ≤ D) (K V : Type) [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [Finite V] [Nontrivial V] (H : Subgroup (Module.End K V)ˣ) (hcl : GammaHat D H)
    (hcr : palfyCR H) :
    Real.log (Nat.card H) ≤ linC * Real.log D * Real.log (Nat.card V) := by
  have h := deg_linear hD K V H hcl hcr
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx0 : 0 ≤ Real.log (Nat.card V) := Real.log_natCast_nonneg _
  have hDpos : 0 < D := by omega
  have h1 : Nat.card H ^ 3 ≤ Nat.card V ^ degE D :=
    (Nat.le_mul_of_pos_left _ (Nat.mul_pos (pow_pos hDpos 3) (pow_pos Nat.card_pos 6))).trans h
  have hHpos : (0 : ℝ) < Nat.card H := by exact_mod_cast Nat.card_pos
  have hVpos : (0 : ℝ) < Nat.card V := by exact_mod_cast Nat.card_pos
  have h2 : ((Nat.card H : ℝ)) ^ 3 ≤ (Nat.card V : ℝ) ^ degE D := by exact_mod_cast h1
  have h3 := Real.log_le_log (by positivity) h2
  rw [Real.log_pow, Real.log_pow] at h3
  -- `E ≤ 1683 log₂ D`
  have hL : ((Nat.log 2 D : ℕ) : ℝ) ≤ Real.log D / Real.log 2 := natLog_two_le (by omega)
  have hy1 : 1 ≤ Real.log D / Real.log 2 := by
    rw [le_div_iff₀ hl, one_mul]
    exact Real.log_le_log (by norm_num) (by
      have : (6 : ℝ) ≤ D := by exact_mod_cast hD
      linarith)
  have hE : (degE D : ℝ) ≤ 1683 * (Real.log D / Real.log 2) := by
    unfold degE
    push_cast
    linarith
  have h4 : (degE D : ℝ) * Real.log (Nat.card V) ≤
      1683 * (Real.log D / Real.log 2) * Real.log (Nat.card V) :=
    mul_le_mul_of_nonneg_right hE hx0
  have h5 : linC * Real.log D * Real.log (Nat.card V) =
      (1683 * (Real.log D / Real.log 2) * Real.log (Nat.card V)) / 3 := by
    unfold linC
    ring
  rw [h5]
  push_cast at h3
  linarith

end GI.Degree
