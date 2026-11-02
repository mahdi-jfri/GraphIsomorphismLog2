import Workspace.AlternatingImprimitiveBudget
import Workspace.BochertExponential

namespace GI.AlternatingActions

variable {A V : Type*} [Fintype A] [DecidableEq A]
  (G : Subgroup (Equiv.Perm A)) [MulAction G V] [MulAction.IsPretransitive G V]

/-- A physical point stabilizer containing the natural alternating group
would have physical index at most two. Thus physical degree at least
three excludes this possibility, without using faithfulness or CFSG. -/
theorem natural_stabilizer_not_giant (hdegree : 3 ≤ Nat.card A)
    (hphysical : 3 ≤ Nat.card V) (v : V) :
    ¬ alternatingGroup A ≤ (MulAction.stabilizer G v).map G.subtype := by
  haveI : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp (by
    rw [← Nat.card_eq_fintype_card]
    omega)
  intro halt
  have hindex := Subgroup.index_antitone halt
  rw [alternatingGroup.index_eq_two, Subgroup.index_map_subtype,
    MulAction.index_stabilizer_of_transitive G v] at hindex
  have hG : 0 < G.index := Nat.pos_of_ne_zero G.index_ne_zero_of_finite
  nlinarith

/-- Bochert's proved natural index bound transfers to the actual
physical degree through the explicit alternating overgroup realization. -/
theorem primitive_stabilizer_exponential_degree
    (giant : alternatingGroup A ≤ G) (hdegree : 3 ≤ Nat.card A)
    (hphysical : 3 ≤ Nat.card V) (v : V)
    (primitive : MulAction.IsPreprimitive ((MulAction.stabilizer G v).map G.subtype) A) :
    2 ^ ((Nat.card A + 1) / 2 - 1) ≤ 2 * Nat.card V := by
  haveI : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp (by
    rw [← Nat.card_eq_fintype_card]
    omega)
  have hb := GI.Bochert.two_pow_le_index_of_isPreprimitive primitive
    (natural_stabilizer_not_giant G hdegree hphysical v)
  have hG := Subgroup.index_antitone giant
  rw [alternatingGroup.index_eq_two] at hG
  rw [Subgroup.index_map_subtype, MulAction.index_stabilizer_of_transitive G v] at hb
  exact hb.trans ((Nat.mul_le_mul_left (Nat.card V) hG).trans_eq (Nat.mul_comm _ _))

/-- The primitive natural-stabilizer branch has logarithmic natural
degree, using the concrete Bochert exponent and the physical degree. -/
theorem primitive_stabilizer_natural_degree_log_bound
    (giant : alternatingGroup A ≤ G) (hdegree : 3 ≤ Nat.card A)
    (hphysical : 3 ≤ Nat.card V) (v : V)
    (primitive : MulAction.IsPreprimitive ((MulAction.stabilizer G v).map G.subtype) A) :
    (Nat.card A : ℝ) ≤ (6 / Real.log 2) * Real.log (Nat.card V : ℝ) := by
  let q := (Nat.card A + 1) / 2 - 1
  have hq : Nat.card A ≤ 2 * q + 2 := by dsimp [q]; omega
  have hqR : (Nat.card A : ℝ) ≤ 2 * (q : ℝ) + 2 := by exact_mod_cast hq
  have hexp := primitive_stabilizer_exponential_degree G giant hdegree hphysical v primitive
  have hexpR : (2 : ℝ) ^ q ≤ 2 * (Nat.card V : ℝ) := by exact_mod_cast hexp
  have hn : (2 : ℝ) ≤ Nat.card V := by exact_mod_cast (show 2 ≤ Nat.card V by omega)
  have hpos : (0 : ℝ) < Nat.card V := by linarith
  have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _) hexpR
  rw [Real.log_pow, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hpos)] at hlog
  have hlog2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hn
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hm := mul_le_mul_of_nonneg_right hqR hlog2pos.le
  have hbnd : (Nat.card A : ℝ) * Real.log 2 ≤ 6 * Real.log (Nat.card V : ℝ) := by
    nlinarith
  calc
    (Nat.card A : ℝ) ≤ (6 * Real.log (Nat.card V : ℝ)) / Real.log 2 :=
      (le_div_iff₀ hlog2pos).mpr hbnd
    _ = (6 / Real.log 2) * Real.log (Nat.card V : ℝ) := by ring

theorem primitive_stabilizer_valuation_log_bound
    (giant : alternatingGroup A ≤ G) (hdegree : 3 ≤ Nat.card A)
    (hphysical : 3 ≤ Nat.card V) (v : V)
    (primitive : MulAction.IsPreprimitive ((MulAction.stabilizer G v).map G.subtype) A) :
    6 * (padicValNat 3 (Nat.card (MulAction.toPermHom G V).range) : ℝ) ≤
      (18 / Real.log 2) * Real.log (Nat.card V : ℝ) := by
  have hv : 6 * (padicValNat 3 (Nat.card (MulAction.toPermHom G V).range) : ℝ) ≤
      3 * (Nat.card A : ℝ) := by exact_mod_cast physical_image_three_valuation_le G
  have hd := primitive_stabilizer_natural_degree_log_bound G giant hdegree hphysical v primitive
  calc
    6 * (padicValNat 3 (Nat.card (MulAction.toPermHom G V).range) : ℝ) ≤
        3 * (Nat.card A : ℝ) := hv
    _ ≤ 3 * ((6 / Real.log 2) * Real.log (Nat.card V : ℝ)) :=
      mul_le_mul_of_nonneg_left hd (by norm_num)
    _ = (18 / Real.log 2) * Real.log (Nat.card V : ℝ) := by ring

end GI.AlternatingActions

namespace GI.BudgetInduction

/-- Direct physical-image valuation alternative for the proved Bochert
primitive natural-stabilizer case. -/
theorem primitive_alternative_of_primitive_natural_stabilizer {m n : ℕ} {A₀ : ℝ}
    (G : Subgroup (Equiv.Perm (Fin m))) [MulAction G (Fin n)]
    [MulAction.IsPretransitive G (Fin n)]
    (giant : alternatingGroup (Fin m) ≤ G) (hm : 3 ≤ m) (hn : 3 ≤ n) (v : Fin n)
    (primitive : MulAction.IsPreprimitive ((MulAction.stabilizer G v).map G.subtype) (Fin m))
    (hA : 18 / Real.log 2 ≤ A₀) :
    PrimitiveReductionAlternative A₀ (MulAction.toPermHom G (Fin n)).range := by
  have hmcard : Nat.card (Fin m) = m := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  have hncard : Nat.card (Fin n) = n := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  have hb := AlternatingActions.primitive_stabilizer_valuation_log_bound G giant
    (by rwa [hmcard]) (by rwa [hncard]) v primitive
  rw [hncard] at hb
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  exact Or.inl ⟨3, Or.inl rfl, hb.trans (mul_le_mul_of_nonneg_right hA hlog)⟩

end GI.BudgetInduction
