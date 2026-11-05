module

public import Workspace.SemiregularTwins
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace GI.Semiregular

variable {V : Type*} [Fintype V]

omit [Fintype V] in
theorem rectangle_edge_count (M : V → V → Bool) (S T : Finset V) :
    (∑ x ∈ S, (T.filter (fun y => M x y = true)).card) =
      ∑ y ∈ T, (S.filter (fun x => M x y = true)).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

/-- Every independent set in an actual nonempty regular directed relation
has at most half the vertices. No symmetry of the relation is assumed. -/
theorem regular_independent_half (M : V → V → Bool) (d : ℕ)
    (rows : ∀ x, rowDegree M x = d) (columns : ∀ y, columnDegree M y = d)
    (positive : 0 < d) (S : Finset V)
    (independent : ∀ x ∈ S, ∀ y ∈ S, M x y = false) :
    2 * S.card ≤ Fintype.card V := by
  classical
  have hrow : ∀ x ∈ S, (Sᶜ.filter (fun y => M x y = true)).card = d := by
    intro x hx
    have heq : Finset.univ.filter (fun y => M x y = true) =
        Sᶜ.filter (fun y => M x y = true) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
      constructor
      · intro hy
        refine ⟨?_, hy⟩
        intro hys
        rw [independent x hx y hys] at hy
        contradiction
      · exact And.right
    rw [← heq]
    exact rows x
  have hcolumn : ∀ y : V, (S.filter (fun x => M x y = true)).card ≤ d := by
    intro y
    rw [← columns y]
    apply Finset.card_le_card
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
  have hcount : S.card * d ≤ Sᶜ.card * d := by
    calc
      S.card * d = ∑ x ∈ S, (Sᶜ.filter (fun y => M x y = true)).card := by
        rw [Finset.sum_congr rfl hrow]
        simp
      _ = ∑ y ∈ Sᶜ, (S.filter (fun x => M x y = true)).card :=
        rectangle_edge_count M S Sᶜ
      _ ≤ ∑ _y ∈ Sᶜ, d := Finset.sum_le_sum (fun y _ => hcolumn y)
      _ = Sᶜ.card * d := by simp
  have hcard : S.card ≤ Sᶜ.card := by
    by_contra! h
    have hlt : Sᶜ.card < S.card := h
    exact (not_le_of_gt (mul_lt_mul_of_pos_right hlt positive)) hcount
  have htotal : S.card + Sᶜ.card = Fintype.card V := by
    simp
  omega

end GI.Semiregular
