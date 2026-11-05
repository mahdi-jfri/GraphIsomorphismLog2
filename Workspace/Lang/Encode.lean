/-
The value encodings of the input graphs and of the answer, used by `Workspace.Lang.Glue`.

**Input.** The input memory of `GI.Statement.InputLayout` has `2 * n * n + 1` meaningful cells:
`n`, then the adjacency matrices of `G` and `H`. The input value `inputVal G H` is the list of
these cells as numbers. So a `GI.Lang` program gets the same data as the machine does.

**Answer.** An answer is a list of numbers `cells`. It is correct (`AnswerOK`) when the cells,
written one after another from any address `r`, form a correct output at `r` in the sense of
`GI.Statement.CorrectOutput`. `answerOK_no` and `answerOK_yes` give the two explicit forms:
`[0]` when the graphs are not isomorphic, and
`[1, σ 0, …, σ (n - 1), k, g₀ 0, …, g₀ (n - 1), …, g_{k-1} (n - 1)]` otherwise.
-/
module

public import Workspace.Lang.Val
public import Workspace.Machine.StatementFacts

@[expose] public section

namespace GI.Lang

open GI.Cited (Val ValAt)
open GI.Statement (InputLayout CorrectOutput autGroup inputLayout_exists inputLayout_unique)

variable {n : ℕ}

/-- The input memory of two graphs: the only memory with `InputLayout G H`. -/
noncomputable def inputMem (G H : SimpleGraph (Fin n)) : ℕ → ℕ :=
  Classical.choose (inputLayout_exists G H)

theorem inputMem_layout (G H : SimpleGraph (Fin n)) : InputLayout G H (inputMem G H) :=
  Classical.choose_spec (inputLayout_exists G H)

theorem inputMem_eq {G H : SimpleGraph (Fin n)} {mem : ℕ → ℕ} (h : InputLayout G H mem) :
    mem = inputMem G H :=
  inputLayout_unique h (inputMem_layout G H)

/-- The meaningful input cells: `n`, then the adjacency matrices of `G` and `H`. -/
noncomputable def inputCells (G H : SimpleGraph (Fin n)) : List ℕ :=
  (List.range (2 * n * n + 1)).map (inputMem G H)

/-- The input value: the list of the input cells, each as a number. -/
noncomputable def inputVal (G H : SimpleGraph (Fin n)) : Val :=
  .list ((inputCells G H).map .nat)

/-- An answer is correct when its cells, written from any address `r`, form a correct output
at `r`. -/
def AnswerOK (G H : SimpleGraph (Fin n)) (v : Val) : Prop :=
  ∃ cells : List ℕ, v = .list (cells.map .nat) ∧
    ∀ (mem : ℕ → ℕ) (r : ℕ), (∀ i (hi : i < cells.length), mem (r + i) = cells[i]) →
      CorrectOutput G H mem r

/-- The cells of a permutation: `σ 0, …, σ (n - 1)`. -/
def permCells (σ : Equiv.Perm (Fin n)) : List ℕ := List.ofFn fun i => (σ i : ℕ)

/-- The cells of a list of permutations, one after another. -/
def permsCells (gs : List (Equiv.Perm (Fin n))) : List ℕ := (gs.map permCells).flatten

theorem length_permCells (σ : Equiv.Perm (Fin n)) : (permCells σ).length = n := by
  simp [permCells]

theorem length_permsCells (gs : List (Equiv.Perm (Fin n))) :
    (permsCells gs).length = n * gs.length := by
  induction gs with
  | nil => simp [permsCells]
  | cons g gs ih =>
    simp only [permsCells, List.map_cons, List.flatten_cons, List.length_append,
      length_permCells] at ih ⊢
    rw [ih, List.length_cons, Nat.mul_succ]; omega

theorem getElem_permsCells (gs : List (Equiv.Perm (Fin n))) (t : Fin gs.length) (i : Fin n)
    (h : n * (t : ℕ) + i < (permsCells gs).length) :
    (permsCells gs)[n * (t : ℕ) + i] = gs.get t i := by
  induction gs with
  | nil => exact t.elim0
  | cons g gs ih =>
    have hi := i.isLt
    simp only [permsCells, List.map_cons, List.flatten_cons] at h ⊢
    rcases t with ⟨_ | t, ht⟩
    · rw [List.getElem_append_left (by simp [length_permCells])]
      simp [permCells]
    · have hlen := length_permCells g
      rw [List.getElem_append_right (by simp only [hlen]; rw [Nat.mul_succ]; omega)]
      have e : n * (t + 1) + i - (permCells g).length = n * t + i := by
        rw [hlen, Nat.mul_succ]; omega
      have := ih ⟨t, by simpa using ht⟩ (by
        rw [length_permsCells gs]
        show n * t + i < _
        have := Nat.mul_le_mul_left n (show t + 1 ≤ gs.length by simp at ht; omega)
        rw [Nat.mul_succ] at this; omega)
      simp only [permsCells] at this
      simp only [e, this]
      rfl

/-- The answer for graphs that are not isomorphic. -/
theorem answerOK_no {G H : SimpleGraph (Fin n)} (h : IsEmpty (G ≃g H)) :
    AnswerOK G H (.list [.nat 0]) :=
  ⟨[0], rfl, fun mem r hm => Or.inl ⟨by simpa using hm 0 (by simp), h⟩⟩

/-- The cells of a positive answer: 1, the isomorphism, the number of generators, and the
generators. -/
def yesCells (σ : Equiv.Perm (Fin n)) (gs : List (Equiv.Perm (Fin n))) : List ℕ :=
  1 :: (permCells σ ++ gs.length :: permsCells gs)

/-- The answer for isomorphic graphs: an isomorphism and generators of the automorphism group
of `G`. -/
theorem answerOK_yes {G H : SimpleGraph (Fin n)} (σ : G ≃g H) (gs : List (Equiv.Perm (Fin n)))
    (hgen : Subgroup.closure {g | g ∈ gs} = autGroup G) :
    AnswerOK G H (.list ((yesCells σ.toEquiv gs).map .nat)) := by
  refine ⟨_, rfl, fun mem r hm => ?_⟩
  have hlen : (yesCells σ.toEquiv gs).length = n + 2 + n * gs.length := by
    simp [yesCells, length_permCells, length_permsCells]; omega
  have hl := length_permCells σ.toEquiv
  refine GI.Machine.correctOutput_of_layout σ gs ?_ ?_ ⟨?_, fun t i => ?_⟩ hgen
  · simpa [yesCells] using hm 0 (by omega)
  · intro i
    have h := hm (1 + i) (by omega)
    rw [← Nat.add_assoc] at h
    rw [h]
    simp only [yesCells, Nat.add_comm 1 (i : ℕ), List.getElem_cons_succ]
    rw [List.getElem_append_left (by omega)]
    simp [permCells]
  · have h := hm (1 + n) (by omega)
    rw [← Nat.add_assoc] at h
    rw [h]
    simp only [yesCells, Nat.add_comm 1 n, List.getElem_cons_succ]
    rw [List.getElem_append_right (by omega)]
    simp [hl]
  · have hc := GI.Machine.permsAt_cell_lt t i
    have h := hm (1 + n + 1 + n * t + i) (by omega)
    rw [show r + (1 + n + 1 + n * ↑t + ↑i) = r + 1 + n + 1 + n * ↑t + ↑i by omega] at h
    rw [h]
    have hp := length_permsCells gs
    simp only [yesCells, show 1 + n + 1 + n * (t : ℕ) + i = (n + 1 + (n * t + i)) + 1 by omega,
      List.getElem_cons_succ]
    rw [List.getElem_append_right (by omega)]
    simp only [hl, show n + 1 + (n * (t : ℕ) + i) - n = (n * t + i) + 1 by omega,
      List.getElem_cons_succ]
    exact getElem_permsCells gs t i (by omega)

end GI.Lang
