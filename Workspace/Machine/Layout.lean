/-
Memory-layout conventions for basic data.

Every layout is a predicate `XAt mem a x`: the memory `mem` holds `x` starting at address `a`.
Each layout occupies the cells `a, …, a + size - 1`, and its predicate depends only on those cells
(the `congr` lemmas).

* A number `v`: one cell, `mem a = v`.
* A block (`BlockAt mem a l`): the entries of the list `l` in `l.length` consecutive cells.
* An array (`ArrayAt mem a l`): the length of `l` in cell `a`, then the block of `l` at `a + 1`.
  Size `l.length + 1`.
* A list of arrays (`ArraysAt mem a ls`): the number of arrays in cell `a`, then the arrays one
  after another. Size `arraysSize ls = 1 + ∑ (length + 1)`.
* A permutation `σ` of `Fin n` (`PermAt mem a σ`): `σ i` in cell `a + i`. Size `n`. The degree `n`
  is not stored; it comes from the context.
* A list of permutations (`PermsAt mem a gs`): the count in cell `a`, then the permutations one
  after another: `gs[t] i` in cell `a + 1 + n * t + i`. Size `1 + n * gs.length`.
* An `n × n` matrix (`MatrixAt mem a M`): row by row, `M i j` in cell `a + n * i + j`. Size `n * n`.
  `adjMatrix G` is the 0/1 adjacency matrix of a graph.

These are the formats of `GI.Statement.InputLayout` and `GI.Statement.CorrectOutput`
(`inputLayout_matrices`, `correctOutput_of_layout`).
-/
module

public import Workspace.Machine.Compose

@[expose] public section

namespace GI.Machine

variable {n : ℕ}

/-- The cells `a, …, a + l.length - 1` hold the list `l`. -/
def BlockAt (mem : ℕ → ℕ) (a : ℕ) (l : List ℕ) : Prop :=
  ∀ i (h : i < l.length), mem (a + i) = l[i]

/-- Cell `a` holds the length of `l`, and the next cells hold `l`. -/
def ArrayAt (mem : ℕ → ℕ) (a : ℕ) (l : List ℕ) : Prop :=
  mem a = l.length ∧ BlockAt mem (a + 1) l

/-- The arrays of `ls`, one after another, starting at `a`, without a count. -/
def ArraysFrom (mem : ℕ → ℕ) : ℕ → List (List ℕ) → Prop
  | _, [] => True
  | a, l :: ls => ArrayAt mem a l ∧ ArraysFrom mem (a + l.length + 1) ls

/-- The number of cells of the arrays of `ls`, without the count. -/
def arraysFromSize (ls : List (List ℕ)) : ℕ := (ls.map (fun l => l.length + 1)).sum

/-- Cell `a` holds the number of arrays, and the arrays follow. -/
def ArraysAt (mem : ℕ → ℕ) (a : ℕ) (ls : List (List ℕ)) : Prop :=
  mem a = ls.length ∧ ArraysFrom mem (a + 1) ls

/-- The number of cells of `ArraysAt`. -/
def arraysSize (ls : List (List ℕ)) : ℕ := 1 + arraysFromSize ls

/-- Cell `a + i` holds `σ i`. -/
def PermAt (mem : ℕ → ℕ) (a : ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i : Fin n, mem (a + i) = σ i

/-- Cell `a` holds the number of permutations, and cell `a + 1 + n * t + i` holds `gs[t] i`. -/
def PermsAt (mem : ℕ → ℕ) (a : ℕ) (gs : List (Equiv.Perm (Fin n))) : Prop :=
  mem a = gs.length ∧ ∀ (t : Fin gs.length) (i : Fin n), mem (a + 1 + n * t + i) = gs.get t i

/-- Cell `a + n * i + j` holds `M i j`. -/
def MatrixAt (mem : ℕ → ℕ) (a : ℕ) (M : Fin n → Fin n → ℕ) : Prop :=
  ∀ i j : Fin n, mem (a + n * i + j) = M i j

open Classical in
/-- The adjacency matrix of a graph: 1 for adjacent vertices, 0 otherwise. -/
noncomputable def adjMatrix (G : SimpleGraph (Fin n)) (i j : Fin n) : ℕ :=
  if G.Adj i j then 1 else 0

/-! ### Sizes and frames -/

@[simp] theorem arraysFromSize_nil : arraysFromSize [] = 0 := rfl
@[simp] theorem arraysFromSize_cons (l : List ℕ) (ls : List (List ℕ)) :
    arraysFromSize (l :: ls) = l.length + 1 + arraysFromSize ls := by
  simp [arraysFromSize]

/-- Two memories that agree on the cells `a, …, a + k - 1`. -/
def AgreeOn (mem mem' : ℕ → ℕ) (a k : ℕ) : Prop := ∀ x, a ≤ x → x < a + k → mem' x = mem x

theorem AgreeOn.mono {mem mem' : ℕ → ℕ} {a k a' k' : ℕ} (h : AgreeOn mem mem' a k)
    (h1 : a ≤ a') (h2 : a' + k' ≤ a + k) : AgreeOn mem mem' a' k' :=
  fun x hx1 hx2 => h x (by omega) (by omega)

theorem BlockAt.congr {mem mem' : ℕ → ℕ} {a : ℕ} {l : List ℕ} (h : BlockAt mem a l)
    (hm : AgreeOn mem mem' a l.length) : BlockAt mem' a l := by
  intro i hi; rw [hm _ (by omega) (by omega)]; exact h i hi

theorem ArrayAt.congr {mem mem' : ℕ → ℕ} {a : ℕ} {l : List ℕ} (h : ArrayAt mem a l)
    (hm : AgreeOn mem mem' a (l.length + 1)) : ArrayAt mem' a l :=
  ⟨by rw [hm a le_rfl (by omega)]; exact h.1, h.2.congr (hm.mono (by omega) (by omega))⟩

theorem ArraysFrom.congr {mem mem' : ℕ → ℕ} {a : ℕ} {ls : List (List ℕ)}
    (h : ArraysFrom mem a ls) (hm : AgreeOn mem mem' a (arraysFromSize ls)) :
    ArraysFrom mem' a ls := by
  induction ls generalizing a with
  | nil => trivial
  | cons l ls ih =>
    simp only [arraysFromSize_cons] at hm
    exact ⟨h.1.congr (hm.mono le_rfl (by omega)), ih h.2 (hm.mono (by omega) (by omega))⟩

theorem ArraysAt.congr {mem mem' : ℕ → ℕ} {a : ℕ} {ls : List (List ℕ)} (h : ArraysAt mem a ls)
    (hm : AgreeOn mem mem' a (arraysSize ls)) : ArraysAt mem' a ls := by
  unfold arraysSize at hm
  exact ⟨by rw [hm a le_rfl (by omega)]; exact h.1,
    h.2.congr (hm.mono (by omega) (by omega))⟩

theorem PermAt.congr {mem mem' : ℕ → ℕ} {a : ℕ} {σ : Equiv.Perm (Fin n)} (h : PermAt mem a σ)
    (hm : AgreeOn mem mem' a n) : PermAt mem' a σ := by
  intro i; rw [hm _ (by omega) (by omega)]; exact h i

theorem permsAt_cell_lt {gs : List (Equiv.Perm (Fin n))} (t : Fin gs.length) (i : Fin n) :
    1 + n * (t : ℕ) + i < 1 + n * gs.length := by
  have := i.isLt
  have h2 : n * (t : ℕ) + n ≤ n * gs.length := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left n t.isLt
  omega

theorem PermsAt.congr {mem mem' : ℕ → ℕ} {a : ℕ} {gs : List (Equiv.Perm (Fin n))}
    (h : PermsAt mem a gs) (hm : AgreeOn mem mem' a (1 + n * gs.length)) : PermsAt mem' a gs := by
  refine ⟨by rw [hm a le_rfl (by omega)]; exact h.1, fun t i => ?_⟩
  have := permsAt_cell_lt t i
  rw [hm _ (by omega) (by omega)]; exact h.2 t i

theorem matrix_cell_lt (i j : Fin n) : n * (i : ℕ) + j < n * n := GI.Statement.cell_lt i.isLt j.isLt

theorem MatrixAt.congr {mem mem' : ℕ → ℕ} {a : ℕ} {M : Fin n → Fin n → ℕ}
    (h : MatrixAt mem a M) (hm : AgreeOn mem mem' a (n * n)) : MatrixAt mem' a M := by
  intro i j
  have := matrix_cell_lt i j
  rw [hm _ (by omega) (by omega)]; exact h i j

/-- A permutation layout determines the permutation. -/
theorem PermAt.unique {mem : ℕ → ℕ} {a : ℕ} {σ τ : Equiv.Perm (Fin n)} (hσ : PermAt mem a σ)
    (hτ : PermAt mem a τ) : σ = τ := by
  ext i; have := hσ i; rw [hτ i] at this; omega

theorem PermAt.lt {mem : ℕ → ℕ} {a : ℕ} {σ : Equiv.Perm (Fin n)} (h : PermAt mem a σ)
    {i : ℕ} (hi : i < n) : mem (a + i) < n := by
  have := h ⟨i, hi⟩; simp only at this; rw [this]; exact (σ _).isLt

theorem adjMatrix_le_one (G : SimpleGraph (Fin n)) (i j : Fin n) : adjMatrix G i j ≤ 1 := by
  unfold adjMatrix; split_ifs <;> omega

/-! ### The formats of the main statement -/

open GI.Statement in
/-- The input layout of the main theorem: `n` in cell 0, the adjacency matrix of `G` at 1 and
that of `H` at `1 + n * n`. -/
theorem inputLayout_matrices {G H : SimpleGraph (Fin n)} {mem : ℕ → ℕ}
    (h : InputLayout G H mem) :
    mem 0 = n ∧ MatrixAt mem 1 (adjMatrix G) ∧ MatrixAt mem (1 + n * n) (adjMatrix H) := by
  classical
  refine ⟨h.size, fun i j => ?_, fun i j => ?_⟩
  · rw [h.left]; unfold adjMatrix; congr 1
  · rw [h.right]; unfold adjMatrix; congr 1

open GI.Statement in
/-- A positive output in the format of `GI.Statement.CorrectOutput`: 1 in cell `r`, the
isomorphism at `r + 1`, and the generators at `r + 1 + n`. -/
theorem correctOutput_of_layout {G H : SimpleGraph (Fin n)} {mem : ℕ → ℕ} {r : ℕ}
    (σ : G ≃g H) (gens : List (Equiv.Perm (Fin n))) (h1 : mem r = 1)
    (hσ : PermAt mem (r + 1) σ.toEquiv) (hg : PermsAt mem (r + 1 + n) gens)
    (hgen : Subgroup.closure {g | g ∈ gens} = autGroup G) :
    CorrectOutput G H mem r := by
  refine Or.inr ⟨h1, σ, fun i => hσ i, gens, hg.1, fun t i => ?_, hgen⟩
  have := hg.2 t i
  rw [show r + 1 + n + 1 + n * (t : ℕ) + i = r + 2 + n + n * t + i by omega] at this
  exact this

open GI.Statement in
/-- A negative output: 0 in cell `r`. -/
theorem correctOutput_of_not_iso {G H : SimpleGraph (Fin n)} {mem : ℕ → ℕ} {r : ℕ}
    (h0 : mem r = 0) (h : IsEmpty (G ≃g H)) : CorrectOutput G H mem r :=
  Or.inl ⟨h0, h⟩

end GI.Machine
