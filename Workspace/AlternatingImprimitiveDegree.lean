import Workspace.ImprimitiveIndexBound
import Workspace.PrimitiveSocleBudget

namespace GI.AlternatingActions

open GI.ImprimitiveIndex

variable {A V : Type*} [Fintype A] [DecidableEq A]
  (G : Subgroup (Equiv.Perm A)) [MulAction G V] [MulAction.IsPretransitive G V]

/-- For an explicit natural group containing Alt(A), a naturally
imprimitive physical stabilizer gives an exponential lower bound on
the actual physical degree, with only the ambient index-two loss. -/
theorem imprimitive_stabilizer_exponential_degree
    (giant : alternatingGroup A ≤ G) (v : V) (x : A)
    [MulAction.IsPretransitive ((MulAction.stabilizer G v).map G.subtype) A]
    (imprimitive : ¬ MulAction.IsPreprimitive
      ((MulAction.stabilizer G v).map G.subtype) A) :
    ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ a * b = Nat.card A ∧
      2 ^ ((a - 1) * (b - 1)) ≤ 2 * Nat.card V := by
  obtain ⟨a, b, ha, hb, hab, hindex⟩ := imprimitive_exponential_index x imprimitive
  haveI : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp (by
    rw [← Nat.card_eq_fintype_card, ← hab]
    nlinarith)
  have hG := Subgroup.index_antitone giant
  rw [alternatingGroup.index_eq_two] at hG
  rw [Subgroup.index_map_subtype, MulAction.index_stabilizer_of_transitive G v] at hindex
  refine ⟨a, b, ha, hb, hab, hindex.trans ?_⟩
  exact (Nat.mul_le_mul_left (Nat.card V) hG).trans_eq (Nat.mul_comm _ _)

/-- The exponent furnished by nontrivial block parameters is at least
one fourth of the natural degree. -/
theorem block_exponent_degree_bound {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    a * b ≤ 4 * ((a - 1) * (b - 1)) := by
  have ha' : a ≤ 2 * (a - 1) := by omega
  have hb' : b ≤ 2 * (b - 1) := by omega
  nlinarith [Nat.mul_le_mul ha' hb']

variable [Fintype V] [Nontrivial V]

/-- Consequently the explicit natural alternating degree is logarithmic
in the actual physical action degree in this imprimitive-stabilizer case. -/
theorem imprimitive_stabilizer_natural_degree_log_bound
    (giant : alternatingGroup A ≤ G) (v : V) (x : A)
    [MulAction.IsPretransitive ((MulAction.stabilizer G v).map G.subtype) A]
    (imprimitive : ¬ MulAction.IsPreprimitive
      ((MulAction.stabilizer G v).map G.subtype) A) :
    (Nat.card A : ℝ) ≤ (8 / Real.log 2) * Real.log (Nat.card V : ℝ) := by
  obtain ⟨a, b, ha, hb, hab, hexp⟩ := imprimitive_stabilizer_exponential_degree
    G giant v x imprimitive
  have he : (Nat.card A : ℝ) ≤ 4 * (((a - 1) * (b - 1) : ℕ) : ℝ) := by
    exact_mod_cast (hab ▸ block_exponent_degree_bound ha hb)
  have hexpR : (2 : ℝ) ^ ((a - 1) * (b - 1)) ≤ 2 * (Nat.card V : ℝ) := by
    exact_mod_cast hexp
  have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _) hexpR
  have hn : (2 : ℝ) ≤ Nat.card V := by
    exact_mod_cast (show 2 ≤ Nat.card V by rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card)
  have hpos : (0 : ℝ) < Nat.card V := by linarith
  rw [Real.log_pow, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hpos)] at hlog
  have hlog2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hn
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he' := mul_le_mul_of_nonneg_right he hlog2pos.le
  have hbnd : (Nat.card A : ℝ) * Real.log 2 ≤ 8 * Real.log (Nat.card V : ℝ) := by
    nlinarith
  calc
    (Nat.card A : ℝ) ≤ (8 * Real.log (Nat.card V : ℝ)) / Real.log 2 :=
      (le_div_iff₀ hlog2pos).mpr hbnd
    _ = (8 / Real.log 2) * Real.log (Nat.card V : ℝ) := by ring

end GI.AlternatingActions
