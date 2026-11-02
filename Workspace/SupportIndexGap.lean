import Workspace.BochertExponential
import Workspace.AlternatingImprimitiveDegree
import Workspace.AlternatingSimple

/-!
# Index facts for Lemma A.24

The transitive-index gap and the minimum-index fact used in the proof of
`lem:low-index-alt-support` (paper, Lemma A.24).

The paper proves the gap with Maróti's bound `|U| < 3^s` for primitive `U`.
Here Bochert's bound (`GI.Bochert.two_pow_le_index_of_isPreprimitive`,
proved without CFSG) gives the same intermediate claim, "index greater than
`s^3` for large `s`". This replaces the cited input.
-/

namespace GI.SupportThresholds

open Equiv Equiv.Perm

/-- The degree from which the transitive-index gap is proved here. -/
def gapThreshold : ℕ := 200

theorem cube_lt_two_pow {e : ℕ} (he : 50 ≤ e) : 128 * e ^ 3 < 2 ^ e := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ e he ih =>
    rw [pow_succ 2 e]
    have h : 128 * (e + 1) ^ 3 ≤ 2 * (128 * e ^ 3) := by
      have : (e + 1) ^ 3 ≤ 2 * e ^ 3 := by
        have h1 : 4 ≤ e := by omega
        nlinarith [sq_nonneg e, mul_le_mul h1 h1 (by omega) (by omega)]
      omega
    omega

/-- If `s ≤ 4e` and `s ≥ 200`, then `2 s^3 < 2^e`. -/
theorem two_cube_lt {s e : ℕ} (hs : gapThreshold ≤ s) (hse : s ≤ 4 * e) :
    2 * s ^ 3 < 2 ^ e := by
  unfold gapThreshold at hs
  have he : 50 ≤ e := by omega
  have h := cube_lt_two_pow he
  have : s ^ 3 ≤ (4 * e) ^ 3 := Nat.pow_le_pow_left hse 3
  nlinarith

/-- **Minimum-index fact**, in the form used: a proper subgroup `V` of a finite
simple group `H` gives a faithful coset action, so `|H| ≤ [H : V]!`. -/
theorem card_le_factorial_index {H : Type*} [Group H] [Finite H] [IsSimpleGroup H]
    (V : Subgroup H) (hV : V ≠ ⊤) : Nat.card H ≤ V.index.factorial := by
  classical
  have hcore : V.normalCore = ⊥ := by
    rcases (Subgroup.normalCore_normal V).eq_bot_or_eq_top with h | h
    · exact h
    · exact absurd (top_le_iff.mp (h ▸ V.normalCore_le)) hV
  have hinj : Function.Injective (MulAction.toPermHom H (H ⧸ V)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker, hcore]
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_perm] at hle
  exact hle

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The index in `Sym(α)` of the image of `P ≤ Alt(α)` is twice its index in
`Alt(α)`. -/
theorem index_map_subtype_alt [Nontrivial α] (P : Subgroup (alternatingGroup α)) :
    (P.map (alternatingGroup α).subtype).index = P.index * 2 := by
  rw [Subgroup.index_map_subtype, alternatingGroup.index_eq_two]

/-- **Transitive-index gap** (proof of Lemma A.24, first paragraph). For
`s ≥ 200`, a proper subgroup `P < Alt(s)` that is transitive on the `s`
points has index greater than `s^3`.

The paper's primitive case uses Maróti's bound; here Bochert's bound is used
instead. The imprimitive case is the block-system count. -/
theorem transitive_index_gap (hs : gapThreshold ≤ Fintype.card α)
    (P : Subgroup (alternatingGroup α)) (hP : P ≠ ⊤)
    [MulAction.IsPretransitive (P.map (alternatingGroup α).subtype) α] :
    Fintype.card α ^ 3 < P.index := by
  classical
  unfold gapThreshold at hs
  haveI : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  set U := P.map (alternatingGroup α).subtype with hUdef
  have hU : U.index = P.index * 2 := index_map_subtype_alt P
  have hPpos : P.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  -- `U` does not contain `Alt(α)`, since `P` is proper.
  have halt : ¬ alternatingGroup α ≤ U := by
    intro h
    have h2 := Subgroup.index_antitone h
    rw [alternatingGroup.index_eq_two, hU] at h2
    have h1 : P.index = 1 := by omega
    exact hP (Subgroup.index_eq_one.mp h1)
  have hcard : Nat.card α = Fintype.card α := Nat.card_eq_fintype_card
  -- Both cases give an exponent `e` with `s ≤ 4e` and `2^e ≤ [Sym : U]`.
  obtain ⟨e, hse, he⟩ : ∃ e, Fintype.card α ≤ 4 * e ∧ 2 ^ e ≤ U.index := by
    by_cases hprim : MulAction.IsPreprimitive U α
    · -- primitive case: Bochert's bound
      refine ⟨(Nat.card α + 1) / 2 - 1, by omega, ?_⟩
      exact GI.Bochert.two_pow_le_index_of_isPreprimitive hprim halt
    · -- imprimitive case: a preserved block system with `b` blocks of size `a`
      obtain ⟨x⟩ : Nonempty α := inferInstance
      obtain ⟨a, b, ha, hb, hab, hidx⟩ :=
        GI.ImprimitiveIndex.imprimitive_exponential_index (K := U) x hprim
      refine ⟨(a - 1) * (b - 1), ?_, hidx⟩
      have := GI.AlternatingActions.block_exponent_degree_bound ha hb
      omega
  have hlt := two_cube_lt (show gapThreshold ≤ Fintype.card α from hs) hse
  omega

end GI.SupportThresholds
