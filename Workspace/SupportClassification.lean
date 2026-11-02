import Workspace.SupportLowIndex

/-!
# The classification of Lemma A.24

Subgroups of `Alt(α)` of index below `C(m, 3)`, `m = |α| ≥ 201`, are the four
groups of `lem:low-index-alt-support`. The proof follows the paper: the
transitive-index gap forces intransitivity, a small invariant subset has size
one or two, and the minimum-index fact finishes each case.
-/

namespace GI.SupportThresholds

open Equiv Equiv.Perm
open scoped Pointwise

attribute [local instance 2000] Subtype.fintype

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The absolute constant `m₀` of Lemma A.24: the gap holds at `m` and `m - 1`. -/
def lowIndexThreshold : ℕ := gapThreshold + 1

theorem card_orderedPair : Fintype.card (GI.Pairs.OrderedPair α) =
    Fintype.card α * Fintype.card α - Fintype.card α := by
  have hdiag : Fintype.card {p : α × α // p.1 = p.2} = Fintype.card α :=
    Fintype.card_congr
      { toFun := fun p => p.1.1
        invFun := fun a => ⟨(a, a), rfl⟩
        left_inv := fun p => Subtype.ext (Prod.ext rfl p.2)
        right_inv := fun _ => rfl }
  change Fintype.card {p : α × α // ¬ (p.1 = p.2)} = _
  rw [Fintype.card_subtype_compl, hdiag, Fintype.card_prod]

/-- `[Alt(α) : Alt(α)_{(a,b)}] = m(m - 1)`. -/
theorem index_pointwise (h4 : 4 ≤ Fintype.card α) (a b : α) (hab : a ≠ b) :
    (GI.Pairs.pointwise a b hab).index = Fintype.card α * (Fintype.card α - 1) := by
  haveI : MulAction.IsPretransitive (alternatingGroup α) (GI.Pairs.OrderedPair α) :=
    ⟨GI.Pairs.ordered_transitive h4⟩
  unfold GI.Pairs.pointwise
  rw [MulAction.index_stabilizer_of_transitive, Nat.card_eq_fintype_card, card_orderedPair,
    Nat.mul_sub_one]

theorem card_complementLabels (a b : α) (hab : a ≠ b) :
    (GI.Pairs.complementLabels a b).card = Fintype.card α - 2 := by
  unfold GI.Pairs.complementLabels
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Finset.card_pair hab]

theorem extend_erase_range (a : α) :
    (GI.AlternatingSimple.extend (Finset.univ.erase a)).range =
      MulAction.stabilizer (alternatingGroup α) a := by
  ext g
  rw [mem_extend_range, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    exact h a (by simp)
  · intro h x hx
    have : x = a := by simpa using hx
    subst this
    exact h

/-- **Lemma A.24, classification part.** -/
theorem low_index_classification (hm : lowIndexThreshold ≤ Fintype.card α)
    (P : Subgroup (alternatingGroup α)) (hI : P.index < (Fintype.card α).choose 3) :
    P = ⊤ ∨ (∃ a : α, P = MulAction.stabilizer (alternatingGroup α) a) ∨
      (∃ (a b : α) (hab : a ≠ b), P = GI.Pairs.pointwise a b hab) ∨
      (∃ (a b : α) (hab : a ≠ b), P = GI.Pairs.setwise a b hab) := by
  classical
  set m := Fintype.card α with hmdef
  unfold lowIndexThreshold gapThreshold at hm
  have h6 := six_mul_choose_three m
  have h3le : 3 ≤ m := by omega
  have hIpos : P.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  by_cases htop : P = ⊤
  · exact Or.inl htop
  -- `I < C(m,3) < m^3`, so the gap shows that `P` is intransitive.
  have hintr : ¬ MulAction.IsPretransitive (P.map (alternatingGroup α).subtype) α := by
    intro ht
    have hgap := transitive_index_gap (by unfold gapThreshold; omega) P htop
    change m ^ 3 < P.index at hgap
    have hcube : m * (m - 1) * (m - 2) ≤ m ^ 3 := by
      calc m * (m - 1) * (m - 2) ≤ m * m * m :=
            Nat.mul_le_mul (Nat.mul_le_mul le_rfl (Nat.sub_le _ _)) (Nat.sub_le _ _)
        _ = m ^ 3 := by ring
    omega
  -- A smallest orbit, or here a small invariant subset, has size `e ≤ 2`.
  obtain ⟨D, hD0, hD2, hPD⟩ := exists_small_invariant P hintr
  have hidx : m.choose D.card ≤ P.index := by
    rw [← index_setStabilizer h3le D]
    exact Subgroup.index_antitone hPD
  have he : D.card ≤ 2 := by
    by_contra h
    have := choose_le_choose_of_le_half (m := m) (show 3 ≤ D.card by omega) hD2
    omega
  rcases (show D.card = 1 ∨ D.card = 2 by omega) with he1 | he2
  · -- `e = 1`: `P` fixes a point `a`.
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp he1
    rw [setStabilizer_singleton] at hPD
    set sa : Finset α := Finset.univ.erase a
    have hA1 := extend_erase_range a
    have hA1idx : (MulAction.stabilizer (alternatingGroup α) a).index = m := by
      rw [← setStabilizer_singleton, index_setStabilizer h3le, Finset.card_singleton,
        Nat.choose_one_right]
    set P' := P.comap (GI.AlternatingSimple.extend sa)
    have hP'idx : P'.index = P.relIndex (MulAction.stabilizer (alternatingGroup α) a) := by
      rw [Subgroup.index_comap, hA1]
    have hIj := Subgroup.relIndex_mul_index hPD
    rw [hA1idx, ← hP'idx] at hIj
    -- `j = [Alt(m-1) : P]` satisfies `6 j < (m-1)(m-2)`.
    have hj : 6 * P'.index < (m - 1) * (m - 2) := by
      have h1 : 6 * P'.index * m < (m - 1) * (m - 2) * m := by
        calc 6 * P'.index * m = 6 * P.index := by rw [← hIj]; ring
          _ < 6 * m.choose 3 := by omega
          _ = (m - 1) * (m - 2) * m := by rw [h6]; ring
      exact Nat.lt_of_mul_lt_mul_right h1
    by_cases hP'top : P' = ⊤
    · -- `P = Alt(Γ ∖ {a})`
      refine Or.inr (Or.inl ⟨a, le_antisymm hPD ?_⟩)
      rw [← hA1]
      rintro _ ⟨p, rfl⟩
      have : p ∈ P' := hP'top ▸ Subgroup.mem_top p
      exact this
    have hsa : Fintype.card sa = m - 1 := by
      simp [sa]; rfl
    -- On the `m - 1` remaining points, `P` is again intransitive, by the gap at `m - 1`.
    have hintr' : ¬ MulAction.IsPretransitive (P'.map (alternatingGroup sa).subtype) sa := by
      intro ht
      have hgap := transitive_index_gap (by rw [hsa]; unfold gapThreshold; omega) P' hP'top
      rw [hsa] at hgap
      have : (m - 1) * (m - 2) ≤ (m - 1) ^ 3 := by
        calc (m - 1) * (m - 2) ≤ (m - 1) * (m - 1) * (m - 1) := by
              apply Nat.mul_le_mul _ (Nat.sub_le_sub_left (by omega) _)
              exact Nat.le_mul_of_pos_right _ (by omega)
          _ = (m - 1) ^ 3 := by ring
      omega
    obtain ⟨D', hD'0, hD'2, hP'D'⟩ := exists_small_invariant P' hintr'
    rw [hsa] at hD'2
    have hidx' : (m - 1).choose D'.card ≤ P'.index := by
      rw [← hsa, ← index_setStabilizer (by rw [hsa]; omega) D']
      exact Subgroup.index_antitone hP'D'
    have he' : D'.card = 1 := by
      by_contra h
      have h2 := choose_le_choose_of_le_half (m := m - 1) (show 2 ≤ D'.card by omega) hD'2
      have h22 := two_mul_choose_two (m - 1)
      have : m - 1 - 1 = m - 2 := by omega
      rw [this] at h22
      omega
    obtain ⟨b', rfl⟩ := Finset.card_eq_one.mp he'
    rw [setStabilizer_singleton] at hP'D'
    set b : α := (b' : α)
    have hab : a ≠ b := by
      have := b'.property
      simp only [sa, Finset.mem_erase] at this
      exact this.1.symm
    -- `P` fixes `a` and `b`.
    have hPT : P ≤ GI.Pairs.pointwise a b hab := by
      intro g hg
      have hgA := hPD hg
      rw [← hA1] at hgA
      obtain ⟨p, rfl⟩ := hgA
      have hp : p ∈ P' := hg
      have hpb := hP'D' hp
      rw [MulAction.mem_stabilizer_iff] at hpb
      refine (GI.Pairs.mem_pointwise a b hab _).mpr ⟨?_, ?_⟩
      · exact ofSubtype_apply_of_not_mem p.val (by simp)
      · rw [extend_apply_coe]
        exact congrArg Subtype.val hpb
    -- `[Alt(m-2) : P] < (m-2)/6`, so the minimum-index fact gives equality.
    have hTidx := Subgroup.relIndex_mul_index hPT
    rw [index_pointwise (by omega)] at hTidx
    have hrel : P.relIndex (GI.Pairs.pointwise a b hab) < m - 2 := by
      have h1 : P.relIndex (GI.Pairs.pointwise a b hab) * (m - 1) = P'.index := by
        apply Nat.eq_of_mul_eq_mul_right (show 0 < m by omega)
        rw [hIj, ← hTidx]; ring
      have h2 : 6 * P.relIndex (GI.Pairs.pointwise a b hab) * (m - 1) < (m - 2) * (m - 1) := by
        rw [mul_assoc, h1]; linarith
      have := Nat.lt_of_mul_lt_mul_right h2
      omega
    rw [← GI.Pairs.complement_alternating_range a b hab] at hPT hrel
    have hT := extend_range_le_of_relIndex_lt _
      (by rw [card_complementLabels a b hab]; omega) P
      (by rw [card_complementLabels a b hab]; exact hrel)
    rw [GI.Pairs.complement_alternating_range a b hab] at hT hPT
    exact Or.inr (Or.inr (Or.inl ⟨a, b, hab, le_antisymm hPT hT⟩))
  · -- `e = 2`: `P` stabilizes a two-set `D = {a, b}`.
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp he2
    have hSidx : (GI.Pairs.setwise a b hab).index = m.choose 2 := by
      rw [← setStabilizer_pair a b hab, index_setStabilizer h3le, Finset.card_pair hab]
    rw [setStabilizer_pair a b hab] at hPD
    have hIS := Subgroup.relIndex_mul_index hPD
    rw [hSidx] at hIS
    have h2 := two_mul_choose_two m
    -- `[S : P] = I / C(m,2) < (m-2)/3`
    have hSP : 3 * P.relIndex (GI.Pairs.setwise a b hab) < m - 2 := by
      have hq : 0 < m * (m - 1) := Nat.mul_pos (by omega) (by omega)
      have h1 : 3 * P.relIndex (GI.Pairs.setwise a b hab) * (m * (m - 1)) <
          (m - 2) * (m * (m - 1)) := by
        calc 3 * P.relIndex (GI.Pairs.setwise a b hab) * (m * (m - 1))
            = 6 * P.index := by rw [← hIS, ← h2]; ring
          _ < 6 * m.choose 3 := by omega
          _ = (m - 2) * (m * (m - 1)) := by rw [h6]; ring
      exact Nat.lt_of_mul_lt_mul_right h1
    have hSne : P.relIndex (GI.Pairs.setwise a b hab) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hIS; exact hIpos hIS.symm
    -- `[T : T ∩ P] ≤ [S : P]` for `T = Alt(Γ ∖ D)`
    have hTS : P.relIndex (GI.Pairs.pointwise a b hab) ≤ P.relIndex (GI.Pairs.setwise a b hab) :=
      Subgroup.relIndex_le_of_le_right (GI.Pairs.pointwise_le_setwise a b hab) hSne
    rw [← GI.Pairs.complement_alternating_range a b hab] at hTS
    have hT := extend_range_le_of_relIndex_lt _
      (by rw [card_complementLabels a b hab]; omega) P
      (by rw [card_complementLabels a b hab]; omega)
    have hdich := GI.Pairs.support_two_stabilizer_dichotomy a b hab P hT hPD
    rcases hdich with h | h
    · exact Or.inr (Or.inr (Or.inl ⟨a, b, hab, h⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨a, b, hab, h⟩))

end GI.SupportThresholds
