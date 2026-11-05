module

public import Workspace.BlockKernelCard
public import Workspace.RectangularFactorial
public import Mathlib.GroupTheory.SpecificGroups.Alternating

@[expose] public section

namespace GI.ImprimitiveIndex

variable {A B : Type*} [Fintype A] [Fintype B] {K : Subgroup (Equiv.Perm A)}
  [MulAction.IsPretransitive K A]

/-- An actual nontrivial block cover forces an exponential lower bound
on the index inside the full natural symmetric group. -/
theorem blockCover_exponential_index (c : BlockCover K B)
    (onto : Function.Surjective c.label) (x : A)
    (hsize : 1 ≤ Nat.card {y : A // c.label y = c.label x}) :
    2 ^ ((Nat.card {y : A // c.label y = c.label x} - 1) * (Nat.card B - 1)) ≤ K.index := by
  classical
  let a := Nat.card {y : A // c.label y = c.label x}
  let b := Nat.card B
  have horder := c.card_le_factorial_pow onto x
  have hfactor := BudgetInduction.blockCover_card_factorization c onto x
  have hab : a * b = Nat.card A := by
    rw [Nat.mul_comm]
    simpa only [a, b, Nat.card_eq_fintype_card] using hfactor
  have hnum := block_factorial_exponential a b hsize
  rw [hab] at hnum
  have hcard : Nat.card K * K.index = (Nat.card A).factorial := by
    rw [K.card_mul_index, Nat.card_perm]
  have hm : 2 ^ ((a - 1) * (b - 1)) * Nat.card K ≤ Nat.card K * K.index := by
    rw [hcard]
    exact (Nat.mul_le_mul_left _ horder).trans hnum
  exact Nat.le_of_mul_le_mul_right (by simpa only [Nat.mul_comm] using hm) (Nat.card_pos (α := K))

omit [Fintype B] in
/-- The block, both block parameters, their exact degree factorization,
and the exponential index bound are all derived from actual imprimitivity. -/
theorem imprimitive_exponential_index (x : A)
    (imprimitive : ¬ MulAction.IsPreprimitive K A) :
    ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ a * b = Nat.card A ∧
      2 ^ ((a - 1) * (b - 1)) ≤ K.index := by
  classical
  have hnot : ¬ ∀ (S : Set A), x ∈ S → MulAction.IsBlock K S → MulAction.IsTrivialBlock S := by
    intro hh
    exact imprimitive (MulAction.IsPreprimitive.of_isTrivialBlock_base x
      (fun hx hS => hh _ hx hS))
  push Not at hnot
  obtain ⟨S, hx, hS, hnt⟩ := hnot
  let p := BudgetInduction.partitionOfBlock hS ⟨x, hx⟩
  letI : Fintype (Quotient p.setoid) := Fintype.ofFinite _
  let a := Nat.card {y : A // p.blockCover.label y = p.blockCover.label x}
  let b := Nat.card (Quotient p.setoid)
  have hc := BudgetInduction.partitionOfBlock_card_bounds hS hx hnt
  change 2 ≤ b ∧ 2 ≤ a at hc
  refine ⟨a, b, hc.2, hc.1, ?_, ?_⟩
  · have hf := BudgetInduction.blockCover_card_factorization p.blockCover p.label_surjective x
    rw [Nat.mul_comm]
    simpa only [a, b, Nat.card_eq_fintype_card] using hf
  · exact blockCover_exponential_index p.blockCover p.label_surjective x (by omega)

end GI.ImprimitiveIndex
