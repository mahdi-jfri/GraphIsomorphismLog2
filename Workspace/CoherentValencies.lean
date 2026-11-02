import Workspace.CoherentRefinementOutput
import Workspace.SemiregularTwins
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace GI.PairRefinement

variable {n : ℕ}

def rowValency (c : Coloring n) (side : Bool) (k : Color n) (x : Fin n) : ℕ :=
  (Finset.univ.filter (fun y => c (side, x, y) = k)).card

def columnValency (c : Coloring n) (side : Bool) (k : Color n) (y : Fin n) : ℕ :=
  (Finset.univ.filter (fun x => c (side, x, y) = k)).card

def Homogeneous (c : Coloring n) (side : Bool) : Prop :=
  ∀ x y : Fin n, c (side, x, x) = c (side, y, y)

theorem rowValency_eq_intersection (c : Coloring n) (hc : Coherent c)
    (side : Bool) (a b x : Fin n) :
    rowValency c side (c (side, a, b)) x =
      intersection c (side, x, x) (c (side, a, b)) (c (side, b, a)) := by
  apply congrArg Finset.card
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hy
    exact ⟨hy, (hc (side, x, y) (side, a, b) hy).2.1⟩
  · exact And.left

theorem columnValency_eq_intersection (c : Coloring n) (hc : Coherent c)
    (side : Bool) (a b x : Fin n) :
    columnValency c side (c (side, a, b)) x =
      intersection c (side, x, x) (c (side, b, a)) (c (side, a, b)) := by
  apply congrArg Finset.card
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hy
    exact ⟨(hc (side, y, x) (side, a, b) hy).2.1, hy⟩
  · exact And.right

theorem rowValency_constant (c : Coloring n) (hc : Coherent c)
    (side : Bool) (hh : Homogeneous c side) (a b x y : Fin n) :
    rowValency c side (c (side, a, b)) x = rowValency c side (c (side, a, b)) y := by
  rw [rowValency_eq_intersection c hc side a b x,
    rowValency_eq_intersection c hc side a b y]
  exact (hc (side, x, x) (side, y, y) (hh x y)).2.2 _ _

theorem columnValency_constant (c : Coloring n) (hc : Coherent c)
    (side : Bool) (hh : Homogeneous c side) (a b x y : Fin n) :
    columnValency c side (c (side, a, b)) x = columnValency c side (c (side, a, b)) y := by
  rw [columnValency_eq_intersection c hc side a b x,
    columnValency_eq_intersection c hc side a b y]
  exact (hc (side, x, x) (side, y, y) (hh x y)).2.2 _ _

theorem valency_sum_eq (c : Coloring n) (side : Bool) (k : Color n) :
    (∑ x : Fin n, rowValency c side k x) = ∑ y : Fin n, columnValency c side k y := by
  simp only [rowValency, columnValency, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

theorem rowValency_eq_columnValency (c : Coloring n) (hc : Coherent c)
    (side : Bool) (hh : Homogeneous c side) (a b x : Fin n) :
    rowValency c side (c (side, a, b)) x = columnValency c side (c (side, a, b)) x := by
  have h := valency_sum_eq c side (c (side, a, b))
  have hr := fun z => rowValency_constant c hc side hh a b z x
  have ht := fun z => columnValency_constant c hc side hh a b z x
  simp_rw [hr, ht] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  have hn : 0 < n := (Nat.zero_le a.val).trans_lt a.isLt
  exact Nat.eq_of_mul_eq_mul_left hn h

theorem rowValency_positive (c : Coloring n) (hc : Coherent c)
    (side : Bool) (hh : Homogeneous c side) (a b x : Fin n) :
    0 < rowValency c side (c (side, a, b)) x := by
  rw [rowValency_constant c hc side hh a b x a]
  exact Finset.card_pos.mpr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

theorem offDiagonal_loop_ne (c : Coloring n) (hc : Coherent c)
    (side : Bool) (a b x : Fin n) (hab : a ≠ b) : c (side, x, x) ≠ c (side, a, b) := by
  intro heq
  have hdiag := (hc (side, x, x) (side, a, b) heq).1
  simp [diagonal, hab] at hdiag

theorem rowValency_lt_degree (c : Coloring n) (hc : Coherent c)
    (side : Bool) (a b x : Fin n) (hab : a ≠ b) :
    rowValency c side (c (side, a, b)) x < n := by
  have hlt : (Finset.univ.filter (fun y => c (side, x, y) = c (side, a, b))).card <
      (Finset.univ : Finset (Fin n)).card := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro heq
    have hm : x ∈ Finset.univ.filter (fun y => c (side, x, y) = c (side, a, b)) := by
      rw [heq]
      exact Finset.mem_univ x
    exact offDiagonal_loop_ne c hc side a b x hab (Finset.mem_filter.mp hm).2
  simpa only [Finset.card_univ, Fintype.card_fin] using hlt

def colorMatrix (c : Coloring n) (side : Bool) (k : Color n) (x y : Fin n) : Bool :=
  decide (c (side, x, y) = k)

theorem rowDegree_colorMatrix (c : Coloring n) (side : Bool) (k : Color n) (x : Fin n) :
    Semiregular.rowDegree (colorMatrix c side k) x = rowValency c side k x := by
  simp [Semiregular.rowDegree, colorMatrix, rowValency]

theorem columnDegree_colorMatrix (c : Coloring n) (side : Bool) (k : Color n) (x : Fin n) :
    Semiregular.columnDegree (colorMatrix c side k) x = columnValency c side k x := by
  simp [Semiregular.columnDegree, colorMatrix, columnValency]

/-- The actual relation of any off-diagonal color in a homogeneous coherent
output is a nontrivial regular binary matrix; semiregularity is derived. -/
theorem colorMatrix_regular (c : Coloring n) (hc : Coherent c) (side : Bool)
    (hh : Homogeneous c side) (a b : Fin n) (hab : a ≠ b) :
    ∃ d : ℕ, 0 < d ∧ d < n ∧
      (∀ x, Semiregular.rowDegree (colorMatrix c side (c (side, a, b))) x = d) ∧
      (∀ y, Semiregular.columnDegree (colorMatrix c side (c (side, a, b))) y = d) := by
  refine ⟨rowValency c side (c (side, a, b)) a,
    rowValency_positive c hc side hh a b a, rowValency_lt_degree c hc side a b a hab, ?_, ?_⟩
  · intro x
    rw [rowDegree_colorMatrix]
    exact rowValency_constant c hc side hh a b x a
  · intro y
    rw [columnDegree_colorMatrix, ← rowValency_eq_columnValency c hc side hh a b y]
    exact rowValency_constant c hc side hh a b y a

end GI.PairRefinement
