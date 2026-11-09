module

public import Workspace.Degree.AffineBound
public import Workspace.Degree.NonaffineBound
public import Workspace.Degree.Interface
public import Workspace.Degree.MarotiWreath
import Maroti.Assembly.Ranges
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Primitive groups in the class

`GI.Degree.primitiveAlternatives` proves `GI.Degree.PrimitiveAlternatives`, which is GNS
Theorem 3.13 and Lemma 8.2 of the paper, without their algorithmic claims.

Take a minimal normal subgroup of the primitive group `P`. If it is abelian, use
`GI.Degree.log_card_affine_le`. If not, use `GI.Degree.nonaffine_alternatives`, which leaves a Johnson
product with parameters `(q, h, r)`. Such a product has `|P| ≤ D^(r-1) (q!)^r` and degree
`binom(q,h)^r`, so its order is small when `q ≤ q₀` or `2^q ≤ binom(q,h)^4`
(`GI.Degree.log_card_johnson_le`).
-/

@[expose] public section

namespace GI.Degree

open Equiv MulAction Maroti CFSG.Holt.General.AltRecPrim

/-- The constant of `GI.Degree.primitive_dichotomy`. -/
noncomputable def primC : ℝ := nonC₁ + linC

theorem primC_nonneg : 0 ≤ primC := add_nonneg nonC₁_nonneg linC_nonneg

/-- A primitive group in the class has small order or is a Johnson product. -/
theorem primitive_dichotomy {D : ℕ} (hD : 6 ≤ D) {α : Type} [Finite α] [Nontrivial α]
    (P : Subgroup (Perm α)) (hp : IsPreprimitive P α) (hG : GammaHat D P) :
    Real.log (Nat.card P) ≤ (primC * Real.log D + 17) * Real.log (Nat.card α) ∨
      ∃ (q h r : ℕ) (e : α ≃ JohnsonTuple q h r), 5 ≤ q ∧ 1 ≤ h ∧ 2 * h < q ∧ 1 ≤ r ∧
        WreathStructure P e := by
  have hL0 : 0 ≤ Real.log D := Real.log_natCast_nonneg D
  have hx0 : 0 ≤ Real.log (Nat.card α) := Real.log_natCast_nonneg _
  have hnon := nonC₁_nonneg
  have hlin := linC_nonneg
  have hnt : Nontrivial P := by
    by_contra hsub
    rw [not_nontrivial_iff_subsingleton] at hsub
    haveI := hp.toIsPretransitive
    obtain ⟨a, b, hab⟩ := exists_pair_ne α
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P a b
    have : g = 1 := Subsingleton.elim _ _
    rw [this, one_smul] at hg
    exact hab hg
  obtain ⟨N, hN, hNne, hmin⟩ := exists_minimal_normal P
  by_cases hab : ∃ a ∈ N, ∃ b ∈ N, a * b ≠ b * a
  · obtain ⟨F⟩ := CFSG.Holt.General.AltRecPrim.nonempty_simpleFactors hN hNne hmin hab
    rcases nonaffine_alternatives F hD hG hN hNne with h | h
    · right
      exact wreathStructure_of_productAction P (IsWreathType.isProductActionType h)
    · left
      refine h.trans (mul_le_mul_of_nonneg_right ?_ hx0)
      have : nonC₁ * Real.log D ≤ primC * Real.log D :=
        mul_le_mul_of_nonneg_right (by unfold primC; linarith) hL0
      linarith
  · left
    push Not at hab
    have hN' : GI.RadicalSocle.MinimalNormal N := ⟨hN, hNne, hmin⟩
    have h := log_card_affine_le (α := α) hD hG hN' fun x y => Subtype.ext (hab x x.2 y y.2)
    refine h.trans (mul_le_mul_of_nonneg_right ?_ hx0)
    have : linC * Real.log D ≤ primC * Real.log D :=
      mul_le_mul_of_nonneg_right (by unfold primC; linarith) hL0
    linarith

theorem card_johnsonTuple (q h r : ℕ) :
    Nat.card (JohnsonTuple q h r) = q.choose h ^ r := by
  rw [Nat.card_eq_fintype_card, Fintype.card_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Fintype.card_finset_len, Fintype.card_fin]

variable {α : Type} [Finite α] {P : Subgroup (Perm α)} {q h r : ℕ} {e : α ≃ JohnsonTuple q h r}

omit [Finite α] in
/-- The coordinate group has at most `D^(r-1)` elements. -/
theorem card_range_wreathPerm_le {D : ℕ} (hD : 6 ≤ D) (hG : GammaHat D P)
    (hS : WreathStructure P e) (h1 : 1 ≤ h) (h2 : h < q) (hr : 1 ≤ r) :
    Nat.card (wreathPerm hS h1 h2).range ≤ D ^ (r - 1) := by
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have := card_le_pow hD (wreathPerm hS h1 h2).range
    (hG.of_surjective _ (wreathPerm hS h1 h2).rangeRestrict_surjective)
  simpa using this

/-- The order of a Johnson product in logarithms. -/
theorem log_card_wreath_le {D : ℕ} (hD : 6 ≤ D) (hG : GammaHat D P)
    (hS : WreathStructure P e) (h1 : 1 ≤ h) (h2 : h < q) (hr : 1 ≤ r) :
    Real.log (Nat.card P) ≤ r * Real.log D + r * Real.log q.factorial := by
  have hc := (card_le_range_mul hS h1 h2).trans
    (Nat.mul_le_mul_right _ (card_range_wreathPerm_le hD hG hS h1 h2 hr))
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hF : (0 : ℝ) < q.factorial := by exact_mod_cast Nat.factorial_pos q
  have h3 : (Nat.card P : ℝ) ≤ (D : ℝ) ^ (r - 1) * (q.factorial : ℝ) ^ r := by exact_mod_cast hc
  have h4 := Real.log_le_log (by exact_mod_cast Nat.card_pos) h3
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h4
  have hL0 : 0 ≤ Real.log D := Real.log_natCast_nonneg D
  have h5 : ((r - 1 : ℕ) : ℝ) ≤ r := by exact_mod_cast Nat.sub_le _ _
  have h6 := mul_le_mul_of_nonneg_right h5 hL0
  linarith

/-- A Johnson product with a small parameter `q` has small order. `q₀` is the cutoff. -/
theorem log_card_johnson_le {D : ℕ} (hD : 6 ≤ D) (hG : GammaHat D P)
    (hS : WreathStructure P e) (hq : 5 ≤ q) (h1 : 1 ≤ h) (h2 : 2 * h < q) (hr : 1 ≤ r) (q₀ : ℕ)
    (hsm : q ≤ q₀ ∨ 2 ^ q ≤ q.choose h ^ 4) :
    Real.log (Nat.card P) ≤
      ((1 + 4 / Real.log 2) * Real.log D + Real.log q₀.factorial) * Real.log (Nat.card α) := by
  have h3 : h < q := by omega
  have hqD : q ≤ D := alternating_section_le hS h1 h3 hr hq hG
  have hmain := log_card_wreath_le hD hG hS h1 h3 hr
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL0 : 0 ≤ Real.log D := Real.log_natCast_nonneg D
  have hC : q ≤ q.choose h := le_choose h1 h3
  set C := q.choose h with hCdef
  have hlogC : 1 ≤ Real.log C := one_le_log_of_four_le (by omega)
  have hn : Real.log (Nat.card α) = r * Real.log C := by
    rw [Nat.card_congr e, card_johnsonTuple]
    push_cast
    rw [Real.log_pow]
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hF0 : 0 ≤ Real.log q₀.factorial := Real.log_natCast_nonneg _
  have hqF : Real.log q.factorial ≤ q * Real.log D := by
    have h4 := log_factorial_le q
    have h5 : Real.log q ≤ Real.log D :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < q)) (by exact_mod_cast hqD)
    have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ q)
    linarith
  rw [hn]
  have hLC : Real.log D ≤ Real.log D * Real.log C := le_mul_of_one_le_right hL0 hlogC
  have hkey : Real.log q.factorial ≤ (4 / Real.log 2) * Real.log D * Real.log C +
      Real.log q₀.factorial * Real.log C := by
    rcases hsm with hle | hle
    · have h4 : Real.log q.factorial ≤ Real.log q₀.factorial :=
        Real.log_le_log (by exact_mod_cast Nat.factorial_pos q)
          (by exact_mod_cast Nat.factorial_le hle)
      have h5 : Real.log q₀.factorial ≤ Real.log q₀.factorial * Real.log C :=
        le_mul_of_one_le_right hF0 hlogC
      have h6 : 0 ≤ (4 / Real.log 2) * Real.log D * Real.log C := by positivity
      linarith
    · have h4 : ((2 : ℝ) ^ q) ≤ (C : ℝ) ^ 4 := by exact_mod_cast hle
      have h5 := Real.log_le_log (by positivity) h4
      rw [Real.log_pow, Real.log_pow] at h5
      have h6 : (q : ℝ) ≤ 4 * Real.log C / Real.log 2 := by
        rw [le_div_iff₀ hl]
        push_cast at h5
        linarith
      have h7 := mul_le_mul_of_nonneg_right h6 hL0
      have h8 : 4 * Real.log C / Real.log 2 * Real.log D =
          (4 / Real.log 2) * Real.log D * Real.log C := by ring
      have h9 : 0 ≤ Real.log q₀.factorial * Real.log C := by positivity
      linarith
  have h10 := mul_le_mul_of_nonneg_left hkey hr0
  have h11 := mul_le_mul_of_nonneg_left hLC hr0
  calc _ ≤ _ := hmain
    _ ≤ r * (Real.log D * Real.log C) + r * ((4 / Real.log 2) * Real.log D * Real.log C +
        Real.log q₀.factorial * Real.log C) := by linarith
    _ = _ := by ring

/-- The fields of `JohnsonProduct`. -/
theorem johnsonProduct_of_wreath {D : ℕ} (hD : 6 ≤ D) (hG : GammaHat D P)
    (hS : WreathStructure P e) (hq : 5 ≤ q) (h1 : 1 ≤ h) (h2 : 2 * h < q) (hr : 1 ≤ r)
    (hlarge : q.choose h ^ 4 < 2 ^ q) : JohnsonProduct D P e := by
  have h3 : h < q := by omega
  have hset : (coordinateSet P e).ncard = Nat.card (wreathPerm hS h1 h3).range := by
    rw [coordinateSet_eq hS h1 h3]
    rfl
  refine ⟨hq, alternating_section_le hS h1 h3 hr hq hG, h1, h2, hr, hlarge, hS, ?_, ?_, ?_⟩
  · intro g hg s hs
    obtain ⟨σ, a, hw⟩ := hS.mem_wreath g hg
    exact socle_conj_mem hw hs
  · rw [hset]
    exact index_le hS h1 h3
  · rw [hset]
    exact card_range_wreathPerm_le hD hG hS h1 h3 hr

/-- **GNS Theorem 3.13 and Lemma 8.2 of the paper**, without the algorithmic claims. -/
theorem primitiveAlternatives : PrimitiveAlternatives := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨primC + (1 + 4 / Real.log 2), add_nonneg primC_nonneg (by positivity), fun q₀ => ?_⟩
  refine ⟨17 + Real.log q₀.factorial, add_nonneg (by norm_num) (Real.log_natCast_nonneg _), ?_⟩
  intro D b hD hb P hp hG
  have : Nontrivial (Fin b) := Fin.nontrivial_iff_two_le.2 hb
  have hL0 : 0 ≤ Real.log D := Real.log_natCast_nonneg D
  have hx0 : 0 ≤ Real.log b := Real.log_natCast_nonneg b
  have hC := primC_nonneg
  have hF0 : 0 ≤ Real.log q₀.factorial := Real.log_natCast_nonneg _
  have hc4 : 0 ≤ 1 + 4 / Real.log 2 := by positivity
  have hbcard : Nat.card (Fin b) = b := by simp
  rcases primitive_dichotomy hD P hp hG with h | ⟨q, k, r, e, hq, h1, h2, hr, hS⟩
  · left
    rw [hbcard] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ hx0)
    have : 0 ≤ (1 + 4 / Real.log 2) * Real.log D := by positivity
    nlinarith
  · by_cases hsm : q ≤ q₀ ∨ 2 ^ q ≤ q.choose k ^ 4
    · left
      have h := log_card_johnson_le hD hG hS hq h1 h2 hr q₀ hsm
      rw [hbcard] at h
      refine h.trans (mul_le_mul_of_nonneg_right ?_ hx0)
      have : 0 ≤ primC * Real.log D := by positivity
      nlinarith
    · right
      push Not at hsm
      exact ⟨q, k, r, e, hsm.1, johnsonProduct_of_wreath hD hG hS hq h1 h2 hr hsm.2⟩

end GI.Degree
