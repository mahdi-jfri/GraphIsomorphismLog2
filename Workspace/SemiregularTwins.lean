module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.ByContra
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace GI.Semiregular

variable {L R : Type*} [Fintype L] [Fintype R]

def rowDegree (M : L → R → Bool) (x : L) : ℕ :=
  (Finset.univ.filter fun y => M x y = true).card

def columnDegree (M : L → R → Bool) (y : R) : ℕ :=
  (Finset.univ.filter fun x => M x y = true).card

def twins (M : L → R → Bool) (x : L) : Finset L :=
  Finset.univ.filter fun z => M z = M x

theorem twins_le_column (M : L → R → Bool) (x : L) (y : R) (hxy : M x y = true) :
    (twins M x).card ≤ columnDegree M y := by
  apply Finset.card_le_card
  intro z hz
  have heq := (Finset.mem_filter.mp hz).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, (congrFun heq y).trans hxy⟩

theorem twins_add_column_le (M : L → R → Bool) (x : L) (y : R)
    (hxy : M x y = false) :
    (twins M x).card + columnDegree M y ≤ Fintype.card L := by
  have hd : Disjoint (twins M x) (Finset.univ.filter fun z => M z y = true) := by
    apply Finset.disjoint_left.mpr
    intro z hz hc
    have heq := congrFun (Finset.mem_filter.mp hz).2 y
    have hztrue := (Finset.mem_filter.mp hc).2
    rw [hxy, hztrue] at heq
    contradiction
  classical
  have hc := Finset.card_le_card (Finset.subset_univ
    ((twins M x) ∪ (Finset.univ.filter fun z => M z y = true)))
  rw [Finset.card_union_of_disjoint hd, Finset.card_univ] at hc
  exact hc

/-- A row with both a neighbor and a nonneighbor has at most half the
left vertices as twins in a matrix with constant column degree. -/
theorem twins_half_of_row_nonconstant (M : L → R → Bool) (x : L) (d : ℕ)
    (regular : ∀ y, columnDegree M y = d)
    (neighbor : ∃ y, M x y = true) (nonneighbor : ∃ y, M x y = false) :
    2 * (twins M x).card ≤ Fintype.card L := by
  obtain ⟨y, hy⟩ := neighbor
  obtain ⟨z, hz⟩ := nonneighbor
  have h₁ := twins_le_column M x y hy
  have h₂ := twins_add_column_le M x z hz
  rw [regular] at h₁ h₂
  omega

omit [Fintype L] in
theorem row_neighbor (M : L → R → Bool) (x : L) (positive : 0 < rowDegree M x) :
    ∃ y, M x y = true := by
  obtain ⟨y, hy⟩ := Finset.card_pos.mp positive
  exact ⟨y, (Finset.mem_filter.mp hy).2⟩

omit [Fintype L] in
theorem row_nonneighbor (M : L → R → Bool) (x : L)
    (nonfull : rowDegree M x < Fintype.card R) : ∃ y, M x y = false := by
  by_contra! h
  have hall : ∀ y, M x y = true := fun y => Bool.eq_true_of_not_eq_false (h y)
  have hf : (Finset.univ.filter fun y => M x y = true) = Finset.univ := by
    ext y
    simp [hall]
  have heq : rowDegree M x = Fintype.card R := by simp [rowDegree, hf]
  omega

/-- Semiregular binary matrices with a nonzero, nonfull common row degree
have no left twin class larger than half the left side. -/
theorem twins_half (M : L → R → Bool) (k d : ℕ)
    (rows : ∀ x, rowDegree M x = k) (columns : ∀ y, columnDegree M y = d)
    (positive : 0 < k) (nonfull : k < Fintype.card R) (x : L) :
    2 * (twins M x).card ≤ Fintype.card L := by
  exact twins_half_of_row_nonconstant M x d columns
    (row_neighbor M x (by rw [rows]; exact positive))
    (row_nonneighbor M x (by rw [rows]; exact nonfull))

theorem nontrivial_twins_half (M : L → R → Bool) (k d : ℕ)
    (rows : ∀ x, rowDegree M x = k) (columns : ∀ y, columnDegree M y = d)
    (edge : ∃ a b, M a b = true) (nonedge : ∃ a b, M a b = false) (x : L) :
    2 * (twins M x).card ≤ Fintype.card L := by
  obtain ⟨a, b, hab⟩ := edge
  obtain ⟨c, t, hct⟩ := nonedge
  have positive : 0 < k := by
    rw [← rows a]
    exact Finset.card_pos.mpr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ b, hab⟩⟩
  have bounded : k ≤ Fintype.card R := by
    rw [← rows c]
    exact Finset.card_filter_le _ _
  have unequal : k ≠ Fintype.card R := by
    intro heq
    rw [← rows c] at heq
    change (Finset.univ.filter fun y => M c y = true).card = Finset.univ.card at heq
    have ht := Finset.card_filter_eq_iff.mp heq t (Finset.mem_univ t)
    rw [hct] at ht
    contradiction
  exact twins_half M k d rows columns positive (lt_of_le_of_ne bounded unequal) x

end GI.Semiregular
