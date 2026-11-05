module

public import Workspace.RectangleOrbits
public import Workspace.KernelQuotientFacts
public import Mathlib.Tactic.Ring

@[expose] public section

namespace GI.Rectangle

variable {α G V : Type*} [Fintype α] [DecidableEq α] [Group G] [MulAction G V]
variable {φ : G →* alternatingGroup α} {W R : Finset α}

theorem ordered_preimage_is_orbit
    (f : StabilizerQuotient.KernelQuotient φ V (Pairs.OrderedPair α))
    (onto : Function.Surjective φ) (hd : Disjoint W R) (hW : 3 ≤ W.card)
    (x : V) (hx : f.map x ∈ orderedRectangle hd) :
    {y : V | f.map y ∈ orderedRectangle hd} = MulAction.orbit ((permitted W R).comap φ) x :=
  f.preimage_eq_orbit onto (permitted W R) (orderedRectangle hd)
    (orderedRectangle_preserved hd) (orderedRectangle_transitive hd hW) x hx

theorem unordered_preimage_is_orbit
    (f : StabilizerQuotient.KernelQuotient φ V (Johnson.SubsetVertex α 2))
    (onto : Function.Surjective φ) (hd : Disjoint W R) (hW : 3 ≤ W.card)
    (x : V) (hx : f.map x ∈ unorderedRectangle hd) :
    {y : V | f.map y ∈ unorderedRectangle hd} = MulAction.orbit ((permitted W R).comap φ) x :=
  f.preimage_eq_orbit onto (permitted W R) (unorderedRectangle hd)
    (unorderedRectangle_preserved hd) (unorderedRectangle_transitive hd hW) x hx

theorem two_mul_choose_two (m : ℕ) : 2 * m.choose 2 = m * (m - 1) := by
  cases m with
  | zero => simp
  | succ m =>
      simpa [Nat.choose_one_right, Nat.mul_comm] using (Nat.add_one_mul_choose_eq m 1).symm

variable [Fintype V]

/-- Exact integer form of the ordered-pair physical fraction in IR2. -/
theorem ordered_physical_fraction
    (f : StabilizerQuotient.KernelQuotient φ V (Pairs.OrderedPair α))
    (hd : Disjoint W R) (w : Pairs.OrderedPair α) :
    Nat.card {x : V // f.map x ∈ orderedRectangle hd} *
        (Fintype.card α * (Fintype.card α - 1)) = W.card * R.card * Nat.card V := by
  have h := f.subset_fraction (orderedRectangle hd) w
  have hc : Nat.card (Pairs.OrderedPair α) = Fintype.card α * (Fintype.card α - 1) := by
    rw [Nat.card_eq_fintype_card, Pairs.card_orderedPair]
  rw [hc, card_orderedRectangle] at h
  exact h

/-- Exact integer form of the unordered-pair physical fraction in IR2. -/
theorem unordered_physical_fraction
    (f : StabilizerQuotient.KernelQuotient φ V (Johnson.SubsetVertex α 2))
    (hd : Disjoint W R) (w : Johnson.SubsetVertex α 2) :
    Nat.card {x : V // f.map x ∈ unorderedRectangle hd} *
        (Fintype.card α * (Fintype.card α - 1)) = 2 * (W.card * R.card * Nat.card V) := by
  have h := f.subset_fraction (unorderedRectangle hd) w
  have hc : Nat.card (Johnson.SubsetVertex α 2) = (Fintype.card α).choose 2 := by
    rw [Nat.card_eq_fintype_card, Pairs.card_unorderedPair]
  rw [hc, card_unorderedRectangle] at h
  rw [← two_mul_choose_two]
  calc
    _ = 2 * (Nat.card {x : V // f.map x ∈ unorderedRectangle hd} *
        (Fintype.card α).choose 2) := by ring
    _ = _ := congrArg (2 * ·) h

end GI.Rectangle
