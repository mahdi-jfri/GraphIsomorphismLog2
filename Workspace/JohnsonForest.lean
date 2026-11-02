import Workspace.JohnsonEntropy
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

namespace GI.Johnson

/-- A refinement forest rooted at one region. Unary nodes record discarded
untracked mass. At a binary split, the first child continues the existing token. -/
inductive RefinementTree (α : Type*)
  | leaf (region : Finset α)
  | shrink (region : Finset α) (child : RefinementTree α)
  | fork (region : Finset α) (continuing fresh : RefinementTree α)

namespace RefinementTree

variable {α : Type*} [DecidableEq α]

def region : RefinementTree α → Finset α
  | .leaf E => E
  | .shrink E _ => E
  | .fork E _ _ => E

def leaves : RefinementTree α → ℕ
  | .leaf _ => 1
  | .shrink _ t => t.leaves
  | .fork _ t u => t.leaves + u.leaves

def extraStarts : RefinementTree α → List ℕ
  | .leaf _ => []
  | .shrink _ t => t.extraStarts
  | .fork _ t u => t.extraStarts ++ (u.region.card :: u.extraStarts)

def starts (t : RefinementTree α) : List ℕ := t.region.card :: t.extraStarts

noncomputable def weight (t : RefinementTree α) : ℝ :=
  (t.starts.map fun (n : ℕ) => Real.log (n : ℝ)).sum

/-- Every retained region contains an anchor and has at least three points.
Siblings are physically disjoint subsets of their parent, and the continuing
child is at least as large as the fresh child. -/
def Valid (anchors : Finset α) : RefinementTree α → Prop
  | .leaf E => 3 ≤ E.card ∧ (E ∩ anchors).Nonempty
  | .shrink E t => 3 ≤ E.card ∧ t.Valid anchors ∧ t.region ⊆ E
  | .fork E t u => 3 ≤ E.card ∧ t.Valid anchors ∧ u.Valid anchors ∧
      t.region ⊆ E ∧ u.region ⊆ E ∧ Disjoint t.region u.region ∧
      u.region.card ≤ t.region.card

omit [DecidableEq α] in
theorem leaves_positive (t : RefinementTree α) : 0 < t.leaves := by
  induction t with
  | leaf E => exact Nat.zero_lt_one
  | shrink E t ih => exact ih
  | fork E t u iht ihu => exact Nat.add_pos_left iht _

omit [DecidableEq α] in
/-- The root and fresh children start exactly one token per terminal path. -/
theorem starts_length (t : RefinementTree α) : t.starts.length = t.leaves := by
  induction t with
  | leaf E => rfl
  | shrink E t ih => exact ih
  | fork E t u iht ihu =>
      simp only [starts, extraStarts, List.length_cons, List.length_append, leaves] at *
      omega

theorem valid_card {anchors : Finset α} {t : RefinementTree α} (h : t.Valid anchors) :
    3 ≤ t.region.card := by
  cases t <;> exact h.1

theorem leaves_le_region_anchors {anchors : Finset α} {t : RefinementTree α}
    (h : t.Valid anchors) : t.leaves ≤ (t.region ∩ anchors).card := by
  induction t with
  | leaf E => exact Finset.card_pos.mpr h.2
  | shrink E t ih =>
      obtain ⟨_, ht, hsub⟩ := h
      apply (ih ht).trans (Finset.card_le_card ?_)
      intro x hx
      exact Finset.mem_inter.mpr ⟨hsub (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩
  | fork E t u iht ihu =>
      obtain ⟨_, ht, hu, hts, hus, hdis, _⟩ := h
      have hd : Disjoint (t.region ∩ anchors) (u.region ∩ anchors) :=
        hdis.mono Finset.inter_subset_left Finset.inter_subset_left
      have hs : (t.region ∩ anchors) ∪ (u.region ∩ anchors) ⊆ E ∩ anchors := by
        intro x hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact Finset.mem_inter.mpr ⟨hts (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩
        · exact Finset.mem_inter.mpr ⟨hus (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩
      have hc := Finset.card_le_card hs
      rw [Finset.card_union_of_disjoint hd] at hc
      exact (Nat.add_le_add (iht ht) (ihu hu)).trans hc

/-- Terminated paths consume pairwise distinct anchors, including paths that
terminate because all subsequent children have size at most two. -/
theorem leaves_le_anchors {anchors : Finset α} {t : RefinementTree α}
    (h : t.Valid anchors) : t.leaves ≤ anchors.card :=
  (leaves_le_region_anchors h).trans (Finset.card_le_card Finset.inter_subset_right)

omit [DecidableEq α] in
theorem weight_shrink (E : Finset α) (t : RefinementTree α) :
    (shrink E t).weight = Real.log (E.card : ℝ) - Real.log (t.region.card : ℝ) + t.weight := by
  simp only [weight, starts, region, extraStarts, List.map_cons, List.sum_cons]
  ring

omit [DecidableEq α] in
theorem weight_fork (E : Finset α) (t u : RefinementTree α) :
    (fork E t u).weight = Real.log (E.card : ℝ) - Real.log (t.region.card : ℝ) +
      t.weight + u.weight := by
  simp only [weight, starts, region, extraStarts, List.map_cons, List.map_append,
    List.sum_cons, List.sum_append]
  ring

/-- The refinement entropy bound is derived from the concrete list of token
start sizes, rather than postulated for the forest. -/
theorem entropy {anchors : Finset α} {t : RefinementTree α} (h : t.Valid anchors) :
    t.weight ≤ forestPotential (t.region.card : ℝ) (t.leaves : ℝ) := by
  induction t with
  | leaf E => simp [weight, starts, extraStarts, region, leaves, forestPotential]
  | shrink E t ih =>
      obtain ⟨hE, ht, hsub⟩ := h
      have hx : 0 < (t.region.card : ℝ) := by exact_mod_cast (by have := valid_card ht; omega : 0 < t.region.card)
      have hw : 0 < (E.card : ℝ) := by exact_mod_cast (by omega : 0 < E.card)
      have hm : (t.region.card : ℝ) ≤ E.card := by exact_mod_cast Finset.card_le_card hsub
      have hr : (1 : ℝ) ≤ t.leaves := by exact_mod_cast Nat.succ_le_of_lt (leaves_positive t)
      have he := unary_entropy_step hx hm hr
      rw [weight_shrink, ← Real.log_div hw.ne' hx.ne']
      exact (add_le_add_right (ih ht) _).trans he
  | fork E t u iht ihu =>
      obtain ⟨hE, ht, hu, hts, hus, hdis, hlarge⟩ := h
      have hx : 0 < (t.region.card : ℝ) := by exact_mod_cast (by have := valid_card ht; omega : 0 < t.region.card)
      have hy : 0 < (u.region.card : ℝ) := by exact_mod_cast (by have := valid_card hu; omega : 0 < u.region.card)
      have hw : 0 < (E.card : ℝ) := by exact_mod_cast (by omega : 0 < E.card)
      have ha : 0 < (t.leaves : ℝ) := by exact_mod_cast leaves_positive t
      have hb : 0 < (u.leaves : ℝ) := by exact_mod_cast leaves_positive u
      have hc := Finset.card_le_card (Finset.union_subset hts hus)
      rw [Finset.card_union_of_disjoint hdis] at hc
      have hm : (t.region.card : ℝ) + u.region.card ≤ E.card := by exact_mod_cast hc
      have hl : (u.region.card : ℝ) ≤ t.region.card := by exact_mod_cast hlarge
      have hr : (1 : ℝ) ≤ (t.leaves : ℝ) + u.leaves := by
        have hp := leaves_positive t
        have hq := leaves_positive u
        exact_mod_cast (by omega : 1 ≤ t.leaves + u.leaves)
      have he := binary_entropy_step hx hy ha hb hm hl hr
      rw [weight_fork, ← Real.log_div hw.ne' hx.ne']
      change _ ≤ forestPotential (E.card : ℝ) ((t.leaves + u.leaves : ℕ) : ℝ)
      rw [Nat.cast_add]
      exact (add_le_add (add_le_add_right (iht ht) _) (ihu hu)).trans he

omit [DecidableEq α] in
theorem allowance_sum (C B : ℝ) (t : RefinementTree α) :
    (t.starts.map fun (w : ℕ) => C * Real.log (w : ℝ) - B).sum =
      C * t.weight - B * (t.leaves : ℝ) := by
  have hlist : ∀ xs : List ℕ,
      (xs.map fun (w : ℕ) => C * Real.log (w : ℝ) - B).sum =
        C * (xs.map fun (w : ℕ) => Real.log (w : ℝ)).sum - B * (xs.length : ℝ) := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
        Nat.cast_one, ih]; ring
  rw [hlist, starts_length]
  rfl

end RefinementTree

/-- A token keeps its original allowance while its actual remaining natural
budget decreases. `mark` consumes exactly the charged marked weight. -/
inductive TokenTrace (allowance : ℝ) : ℕ → ℕ → Prop
  | start (remaining : ℕ) : (remaining : ℝ) ≤ allowance → TokenTrace allowance 0 remaining
  | restrict {charge old new : ℕ} : TokenTrace allowance charge old → new ≤ old →
      TokenTrace allowance charge new
  | mark {charge old new k : ℕ} : TokenTrace allowance charge old → new + k ≤ old →
      TokenTrace allowance (charge + k) new

theorem TokenTrace.invariant {allowance : ℝ} {charge remaining : ℕ}
    (h : TokenTrace allowance charge remaining) :
    (charge : ℝ) + remaining ≤ allowance := by
  induction h with
  | start r hr => simpa using hr
  | @restrict charge old new h hle ih =>
      have hh : (new : ℝ) ≤ old := by exact_mod_cast hle
      linarith
  | @mark charge old new k h hle ih =>
      have hh : (new : ℝ) + k ≤ old := by exact_mod_cast hle
      push_cast
      linarith

theorem TokenTrace.charge_le {allowance : ℝ} {charge remaining : ℕ}
    (h : TokenTrace allowance charge remaining) : (charge : ℝ) ≤ allowance := by
  have hi := h.invariant
  have hp : (0 : ℝ) ≤ remaining := Nat.cast_nonneg _
  linarith

end GI.Johnson
