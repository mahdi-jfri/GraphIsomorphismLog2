module

public import Workspace.Degree.Children
public import Workspace.Degree.OrderBound
public import Workspace.Degree.CaseD
public import Workspace.Algorithm.SingleFactor
public import Workspace.Algorithm.Expose

@[expose] public section

/-!
# The cases of a primitive quotient

The test of `Degree/CaseD.lean` compares the order of a primitive quotient with `b^(E (⌊log₂ D⌋ + 1))`,
where `b` is its degree. This file proves what that test gives, for a fixed large `E` (`caseE`).

* `recog_promise`: if the order is above the threshold, the quotient has degree at least `25` and a
  Johnson structure, by Lemma 8.2 of the paper (`PrimitiveAlternatives`). This is the promise of
  recognition.
* `recog_le_D`, `index_coordinate_le_pow`, `recog_q₀_lt`: facts on the structure that recognition
  returns, which need not be the one of Lemma 8.2. Its `m` is at most `D`, the index of its
  coordinate subgroup is at most `D^(r-1)`, and for `r = 1` its `m` is above `q₀`.
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly Equiv Equiv.Perm Real
open GI.Cited (MarotiStructure)

variable {Ω C : Type}

/-- `2^h ≤ binom(q,h)` when `2 h ≤ q`. Each of the `h` factors of `binom(q,h)` is at least `2`. -/
theorem two_pow_le_choose : ∀ {q h : ℕ}, 2 * h ≤ q → 2 ^ h ≤ q.choose h := by
  intro q h
  induction h generalizing q with
  | zero => simp
  | succ h ih =>
    intro hq
    obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have h1 := ih (q := q) (by omega)
    have h2 := Nat.add_one_mul_choose_eq q h
    have h3 : 2 * (h + 1) * q.choose h ≤ (q + 1).choose (h + 1) * (h + 1) := by
      rw [← h2]
      exact Nat.mul_le_mul_right _ hq
    have h4 : 2 * q.choose h ≤ (q + 1).choose (h + 1) := by
      refine Nat.le_of_mul_le_mul_right ?_ (Nat.succ_pos h)
      calc 2 * q.choose h * (h + 1) = 2 * (h + 1) * q.choose h := by ring
        _ ≤ _ := h3
    calc 2 ^ (h + 1) = 2 * 2 ^ h := by ring
      _ ≤ 2 * q.choose h := Nat.mul_le_mul_left _ h1
      _ ≤ _ := h4

/-- The condition `binom(q,h)^4 < 2^q` of a Johnson product gives `3 h ≤ q`. -/
theorem three_mul_le_of_large {q h : ℕ} (h2 : 2 * h < q) (hl : q.choose h ^ 4 < 2 ^ q) :
    3 * h ≤ q := by
  by_contra hc
  have h3 := Nat.pow_le_pow_left (two_pow_le_choose h2.le) 4
  have h4 : (2 : ℕ) ^ q ≤ (2 ^ h) ^ 4 := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  exact absurd hl (not_lt.2 (h4.trans h3))

/-- On `Fin b`, a Maróti structure is the structure of `Degree/JohnsonWreath.lean`. -/
theorem wreath_of_maroti {b q h r : ℕ} {P : Subgroup (Perm (Fin b))}
    {e : Fin b ≃ JohnsonTuple q h r} (hM : MarotiStructure P e) : WreathStructure P e :=
  ⟨hM.1, fun _ ⟨a, ha, hs⟩ => hs ▸ hM.2 a fun i => ha i (Set.mem_univ i)⟩

theorem RecogRange.h1 {m k : ℕ} (h : RecogRange m k) : 1 ≤ k := h.one_le

theorem RecogRange.h2 {m k : ℕ} (h : RecogRange m k) : k < m := by
  have := h.three_mul
  have := h.eight_le
  omega

/-- **The `m` of a structure is at most `D`.** The group holds a copy of `Alt(m)`. -/
theorem recog_le_D {b m k r D : ℕ} {P : Subgroup (Perm (Fin b))}
    {e : Fin b ≃ JohnsonTuple m k r} (hR : RecogRange m k) (hr : 1 ≤ r)
    (hM : MarotiStructure P e) (hD : GammaHat D P) : m ≤ D :=
  alternating_section_le (wreath_of_maroti hM) hR.h1 hR.h2 hr (by have := hR.eight_le; omega) hD

/-- **The coordinate permutations of a structure are at most `D^(r-1)`**, by GNS Lemma 2.2 for
the image in `Sym(r)`. -/
theorem coordinateSet_ncard_le {b m k r D : ℕ} {P : Subgroup (Perm (Fin b))}
    {e : Fin b ≃ JohnsonTuple m k r} (hR : RecogRange m k) (hr : 1 ≤ r) (hD6 : 6 ≤ D)
    (hM : MarotiStructure P e) (hD : GammaHat D P) :
    (coordinateSet P e).ncard ≤ D ^ (r - 1) := by
  have hW := wreath_of_maroti hM
  rw [coordinateSet_eq hW hR.h1 hR.h2]
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hg : GammaHat D (wreathPerm hW hR.h1 hR.h2).range :=
    GammaHat.of_surjective (wreathPerm hW hR.h1 hR.h2).rangeRestrict
      (wreathPerm hW hR.h1 hR.h2).rangeRestrict_surjective hD
  have h1 := card_le_pow hD6 _ hg
  rw [show Nat.card (Fin r) = r by simp] at h1
  rw [← _root_.Nat.card_coe_set_eq]
  exact h1

section Quotient

variable {S : State Ω C} (Q : PrimitiveQuotient S)

/-- **The index of the coordinate subgroup is at most `D^(r-1)`**. The quotient by
the coordinate subgroup is the group of coordinate permutations of `P`. -/
theorem index_coordinate_le_pow {D m k r : ℕ} {e : Fin Q.d ≃ JohnsonTuple m k r}
    (hS : Q.ProductStructure m k r e) (hR : RecogRange m k) (hr : 1 ≤ r) (hD6 : 6 ≤ D)
    (hM : MarotiStructure Q.ρ.range e) (hD : GammaHat D Q.ρ.range) (hb : 2 ≤ m.choose k) :
    ((Q.coordinateGroup e hS hb).subgroupOf S.G).index ≤ D ^ (r - 1) := by
  have h1 : (Q.coordinateGroup e hS hb).subgroupOf S.G =
      ((Product.coordHom e Q.ρ.range hS.1 hb).comp Q.ρ.rangeRestrict).ker := by
    ext g; simp [PrimitiveQuotient.coordinateGroup, Subgroup.mem_subgroupOf]
  rw [h1, Subgroup.index_ker]
  refine le_trans ?_ (coordinateSet_ncard_le hR hr hD6 hM hD)
  rw [← _root_.Nat.card_coe_set_eq]
  have hmem : ∀ x : ((Product.coordHom e Q.ρ.range hS.1 hb).comp Q.ρ.rangeRestrict).range,
      (x : Perm (Fin r))⁻¹ ∈ coordinateSet Q.ρ.range e := by
    rintro ⟨_, g, rfl⟩
    obtain ⟨a, ha⟩ := Product.coord_spec e Q.ρ.range hS.1 (Q.ρ.rangeRestrict g)
    refine ⟨_, (Q.ρ.rangeRestrict g).2, a, ?_⟩
    have e1 : ((Product.coordHom e Q.ρ.range hS.1 hb).comp Q.ρ.rangeRestrict g)⁻¹ =
        Product.coord e Q.ρ.range hS.1 (Q.ρ.rangeRestrict g) := inv_inv _
    rw [e1]
    exact ha
  refine Nat.card_le_card_of_injective (fun x => ⟨(x : Perm (Fin r))⁻¹, hmem x⟩) ?_
  intro x y hxy
  exact Subtype.ext (inv_injective (congrArg Subtype.val hxy))

end Quotient

/-- The constant of the test, for the constants `c₁, c₂` of Lemma 8.2 at `q₀`. -/
noncomputable def caseE (c₁ c₂ : ℝ) (q₀ : ℕ) : ℕ := ⌈c₁ + c₂⌉₊ + q₀.factorial + 25

theorem le_degExp (c₁ c₂ : ℝ) (q₀ D : ℕ) : q₀.factorial + 25 ≤ degExp (caseE c₁ c₂ q₀) D := by
  unfold degExp caseE
  nlinarith [Nat.le_mul_of_pos_right (⌈c₁ + c₂⌉₊ + q₀.factorial + 25) (Nat.succ_pos (Nat.log 2 D))]

/-- A group of order at most `d!` with `d < 25` is below the threshold. -/
theorem card_le_of_small_degree {d o T : ℕ} (hd : 2 ≤ d) (hd25 : d < 25) (ho : o ≤ d.factorial)
    (hT : 25 ≤ T) : o ≤ d ^ T :=
  ho.trans ((Nat.factorial_le_pow d).trans (Nat.pow_le_pow_right (by omega) (by omega)))

/-- **For one coordinate, the `m` of a structure is above `q₀`** when the order is above the
threshold. The group lies in `Sym(m)`, so its order is at most `m!`. -/
theorem recog_q₀_lt {b m k q₀ T : ℕ} {P : Subgroup (Perm (Fin b))}
    {e : Fin b ≃ JohnsonTuple m k 1} (hR : RecogRange m k) (hM : MarotiStructure P e)
    (hb : 2 ≤ b) (hT : q₀.factorial ≤ T) (hc : ¬ Nat.card P ≤ b ^ T) : q₀ < m := by
  by_contra hq
  have hW := wreath_of_maroti hM
  have h1 := card_le_range_mul hW hR.h1 hR.h2
  have h2 : Nat.card (wreathPerm hW hR.h1 hR.h2).range ≤ 1 := by
    refine (Subgroup.card_le_card_group _).trans ?_
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have h3 : Nat.card P ≤ q₀.factorial := by
    calc Nat.card P ≤ 1 * m.factorial ^ 1 := h1.trans (Nat.mul_le_mul_right _ h2)
      _ = m.factorial := by ring
      _ ≤ _ := Nat.factorial_le (by omega)
  refine hc (h3.trans ?_)
  calc q₀.factorial ≤ T := hT
    _ ≤ 2 ^ T := Nat.lt_two_pow_self.le
    _ ≤ b ^ T := Nat.pow_le_pow_left hb T

/-- The threshold of the test is at least the bound of Lemma 8.2. -/
theorem log_threshold {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (q₀ D b : ℕ) (hb : 2 ≤ b) :
    (c₁ * Real.log D + c₂) * Real.log b ≤ degExp (caseE c₁ c₂ q₀) D * Real.log b := by
  have hb0 : 0 ≤ Real.log b := Real.log_natCast_nonneg b
  refine mul_le_mul_of_nonneg_right ?_ hb0
  set x := Nat.log 2 D with hx
  have h1 : Real.log D ≤ (x : ℝ) + 1 := by
    rcases Nat.eq_zero_or_pos D with rfl | hD
    · have : (0 : ℝ) ≤ x := Nat.cast_nonneg _
      simp only [Nat.cast_zero, Real.log_zero]
      linarith
    have h2 : D < 2 ^ (x + 1) := Nat.lt_pow_succ_log_self (by norm_num) D
    have h3 : (D : ℝ) ≤ 2 ^ (x + 1) := by exact_mod_cast h2.le
    have h4 := Real.log_le_log (by exact_mod_cast hD) h3
    rw [Real.log_pow] at h4
    have h5 := Real.log_two_lt_d9
    have h6 : (0 : ℝ) ≤ (x : ℝ) + 1 := by positivity
    push_cast at h4
    nlinarith
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg _
  have h5 : c₁ * Real.log D + c₂ ≤ (c₁ + c₂) * ((x : ℝ) + 1) := by nlinarith
  have h6 : c₁ + c₂ ≤ (caseE c₁ c₂ q₀ : ℝ) := by
    have h7 := Nat.le_ceil (c₁ + c₂)
    unfold caseE
    push_cast
    have : (0 : ℝ) ≤ (q₀.factorial : ℝ) := Nat.cast_nonneg _
    linarith
  unfold degExp
  push_cast
  rw [← hx]
  nlinarith

/-- **The promise of recognition.** Let `hA` be Lemma 8.2 at `q₀ ≥ 8`. A primitive group `P ∈ Γ̂_D`
of degree `b` above the threshold has degree at least `25` and a Johnson structure in the range of
recognition. -/
theorem recog_promise {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) {q₀ : ℕ} (hq₀ : 8 ≤ q₀)
    (hA : ∀ (D b : ℕ), 6 ≤ D → 2 ≤ b → ∀ P : Subgroup (Perm (Fin b)),
      MulAction.IsPreprimitive P (Fin b) → GammaHat D P →
        Real.log (Nat.card P) ≤ (c₁ * Real.log D + c₂) * Real.log b ∨
        ∃ (q h r : ℕ) (e : Fin b ≃ JohnsonTuple q h r), q₀ < q ∧ JohnsonProduct D P e)
    {D b : ℕ} (hD : 6 ≤ D) (hb : 2 ≤ b) {P : Subgroup (Perm (Fin b))}
    (hp : MulAction.IsPreprimitive P (Fin b)) (hG : GammaHat D P)
    (hc : ¬ Nat.card P ≤ b ^ degExp (caseE c₁ c₂ q₀) D) :
    25 ≤ b ∧ ∃ (m k r : ℕ) (e : Fin b ≃ JohnsonTuple m k r),
      RecogRange m k ∧ 1 ≤ r ∧ MarotiStructure P e := by
  set T := degExp (caseE c₁ c₂ q₀) D with hT
  have hT25 : q₀.factorial + 25 ≤ T := le_degExp c₁ c₂ q₀ D
  constructor
  · by_contra h25
    refine hc (card_le_of_small_degree hb (by omega) ?_ (by omega))
    calc Nat.card P ≤ Nat.card (Perm (Fin b)) := Subgroup.card_le_card_group P
      _ = b.factorial := by rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rcases hA D b hD hb P hp hG with h | ⟨q, h', r, e, hq, hJ⟩
  · exfalso
    refine hc ?_
    have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    have hP0 : (0 : ℝ) < Nat.card P := by exact_mod_cast Nat.card_pos
    have h1 := h.trans (log_threshold hc₁ hc₂ q₀ D b hb)
    rw [← Real.log_pow] at h1
    have h2 := (Real.log_le_log_iff hP0 (by positivity)).1 h1
    exact_mod_cast h2
  · exact ⟨q, h', r, e, ⟨by omega, hJ.one_le_h, three_mul_le_of_large hJ.two_mul_lt hJ.large⟩,
      hJ.one_le_r, hJ.marotiStructure⟩

end GI.Degree
