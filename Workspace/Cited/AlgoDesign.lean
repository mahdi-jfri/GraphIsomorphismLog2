-- Not assumed by the main theorem
import Workspace.Cited.AlgoRefinement
import Workspace.Cited.DesignLemma

/-!
# Stage 2 task: the canonical output of the Design Lemma step

**Not assumed by the main theorem.**

[H, Section 5.1], after the proof of Proposition 5.1: "We run through all the possible tuples
`x = (x₁, …, x_ℓ) ∈ Γ^ℓ`, `0 ≤ ℓ < k`, until we find a tuple for which the first or second
conclusion of the Design Lemma is true." The paper branches over the individualized tuple
(Section A.3, "Keep individualized labels as singleton colors"; Section 7.2: "the actual
same-size Design continuation index `q^{O(κ)}`").

*Canonical output.* "The first tuple found" depends on an ordering of `Γ`, so it is not
canonical. The canonical object is the set of all witnesses: for each `ℓ < k`, the tuples `x`
of outcome (a) and the pairs `(x, j)` of outcome (b) of `GI.Cited.DesignLemma`. The task asks
for lists whose members are exactly these witnesses. The witness sets are equivariant: for a
relabeling `σ`, the witnesses of `c ∘ σ⁻¹` are the `σ ∘ x` for the witnesses `x` of `c`
(`designWitnessA_equivariant` below proves this for outcome (a); outcome (b) is the same
computation with `skel₂`). So a caller that branches over all listed witnesses covers every
parent isomorphism. The Design Lemma (`GI.Cited.DesignLemma`) is what makes the lists not both
empty under its hypotheses; the task itself needs no hypothesis, since the lists of all
witnesses always exist (possibly empty).

*Running time.* For fixed `k` there are fewer than `k n^k` tuples `x`, and each test is
polynomial; the output has polynomial size.

*Output size.* The lists are asked to have no repeated entries. Then the list for outcome (a) at
`ℓ` has at most `n^ℓ` tuples, and the list for outcome (b) at most `n^ℓ · n` pairs, since for a
given `x` the color `j` is the color of some point under `skel₁ c x`. Every color is a value of
`c`, so at most `n^k`.

*Fixed parameters.* The arity `k` and the dominance threshold `α` (a rational number) are
parameters of the task.
-/

namespace GI.Cited

open Equiv

/-- Outcome (a) of the Design Lemma at `x`: every vertex class of `X_x^{(1)}` has fewer than
`α n` points. -/
def DesignWitnessA {n k : ℕ} (α : ℚ) (c : (Fin k → Fin n) → ℕ) {ℓ : ℕ} (x : Fin ℓ → Fin n) :
    Prop :=
  ∀ j : ℕ, ((Finset.univ.filter fun z => skel₁ c x z = j).card : ℚ) < α * n

/-- Outcome (b) of the Design Lemma at `(x, j)`: the class `j` has at least `α n` points and
the pair coloring is not constant on its pairs of distinct points. -/
def DesignWitnessB {n k : ℕ} (α : ℚ) (c : (Fin k → Fin n) → ℕ) {ℓ : ℕ} (x : Fin ℓ → Fin n)
    (j : ℕ) : Prop :=
  ℓ + 1 < k ∧ α * n ≤ ((Finset.univ.filter fun z => skel₁ c x z = j).card : ℚ) ∧
    ∃ u v w y : Fin n, skel₁ c x u = j ∧ skel₁ c x v = j ∧ skel₁ c x w = j ∧
      skel₁ c x y = j ∧ u ≠ v ∧ w ≠ y ∧ skel₂ c x u v ≠ skel₂ c x w y

/-- A tuple of points. -/
def encTuple {n ℓ : ℕ} (x : Fin ℓ → Fin n) : Val :=
  .list ((List.finRange ℓ).map fun i => .nat (x i))

/-- A `k`-ary coloring of `Fin n` with values at most `n^k`. -/
structure KColoringInst (k : ℕ) where
  n : ℕ
  c : (Fin k → Fin n) → ℕ
  c_le : ∀ x, c x ≤ n ^ k

/-- The correct outputs: for each `ℓ < k`, a list of exactly the outcome-(a) tuples and a list of
exactly the outcome-(b) pairs, each without repeats. -/
def DesignWitnessLists {n k : ℕ} (α : ℚ) (c : (Fin k → Fin n) → ℕ) (v : Val) : Prop :=
  ∃ (A : (ℓ : Fin k) → List (Fin ℓ → Fin n)) (B : (ℓ : Fin k) → List ((Fin ℓ → Fin n) × ℕ)),
    v = .list ((List.finRange k).map fun ℓ =>
      .list [.list ((A ℓ).map encTuple), .list ((B ℓ).map fun p => .list [encTuple p.1, .nat p.2])]) ∧
    (∀ ℓ, (A ℓ).Nodup ∧ (B ℓ).Nodup) ∧
    (∀ ℓ x, x ∈ A ℓ ↔ DesignWitnessA α c x) ∧
    (∀ ℓ x j, (x, j) ∈ B ℓ ↔ DesignWitnessB α c x j)

/-- **The Design Lemma step, canonical form** ([H, Section 5.1]). Output, for each `ℓ < k`, the
lists of all witnesses of outcomes (a) and (b). -/
def DesignWitnessTask (k : ℕ) (α : ℚ) : Task (KColoringInst k) :=
  Task.ofVal (fun I => .list [.list (List.replicate I.n (.nat 0)), encKColoring I.c])
    (fun I v => DesignWitnessLists α I.c v)

/-- Not assumed by the main theorem. For a fixed arity `k` and threshold `α`. -/
def DesignWitnesses (k : ℕ) (α : ℚ) : Prop := ∃ p, PolyTimeAt (DesignWitnessTask k α) p

/-- Relabeling a padded tuple. -/
theorem padTuple_comp {n k ℓ : ℕ} (σ : Perm (Fin n)) (x : Fin ℓ → Fin n) (z : Fin n) :
    (padTuple (k := k) (σ ∘ x) (σ z)) = σ ∘ padTuple x z := by
  funext i
  simp only [padTuple, Function.comp]
  split_ifs <;> rfl

/-- **Equivariance of the outcome-(a) witnesses**: `x` is a witness for `c` exactly when
`σ ∘ x` is a witness for the relabeled coloring `c ∘ σ⁻¹`. -/
theorem designWitnessA_equivariant {n k ℓ : ℕ} (α : ℚ) (c : (Fin k → Fin n) → ℕ)
    (σ : Perm (Fin n)) (x : Fin ℓ → Fin n) :
    DesignWitnessA α (fun y => c (σ.symm ∘ y)) (σ ∘ x) ↔ DesignWitnessA α c x := by
  have hskel : ∀ z, skel₁ (fun y => c (σ.symm ∘ y)) (σ ∘ x) (σ z) = skel₁ c x z := by
    intro z
    simp only [skel₁, padTuple_comp]
    congr 1
    funext i
    simp
  have hcard : ∀ j, (Finset.univ.filter fun z =>
      skel₁ (fun y => c (σ.symm ∘ y)) (σ ∘ x) z = j).card =
      (Finset.univ.filter fun z => skel₁ c x z = j).card := by
    intro j
    refine Finset.card_bij (fun z _ => σ.symm z) ?_ ?_ ?_
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      rw [← hskel, Equiv.apply_symm_apply]
      exact hz
    · intro a _ b _ h
      exact σ.symm.injective h
    · intro z hz
      refine ⟨σ z, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      rw [hskel]
      exact hz
  unfold DesignWitnessA
  simp only [hcard]

end GI.Cited
