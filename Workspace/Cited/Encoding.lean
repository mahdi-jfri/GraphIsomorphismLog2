/-
One memory format for the data that cited algorithms read and write. This file is part of the
trusted statement, like `Workspace.Cited.Algorithm`: the tasks of the cited algorithms are written
with it, so a reader must check it.

A value is a natural number or a list of values. It is stored in consecutive cells with no
pointers, so it can be placed at any address and copied cell by cell:
* the number `n` takes two cells, `0, n`;
* the list `[v₀, …, v_{k-1}]` takes three header cells `1, k, S`, followed by the cells of
  `v₀, …, v_{k-1}` one after another, where `S` is the number of those cells.

The tag in the first cell and the counts in the header fix where every value ends, so the cells
determine the value. The count `S` lets a program skip an entry without reading it.
-/
module

public import Workspace.Cited.Algorithm
public import Mathlib.GroupTheory.Perm.Basic

@[expose] public section

namespace GI.Cited

/-- A value: a natural number or a list of values. -/
inductive Val where
  | nat (n : ℕ)
  | list (vs : List Val)

mutual
/-- The cells that hold a value, in order. -/
def Val.cells : Val → List ℕ
  | .nat n => [0, n]
  | .list vs => [1, vs.length, (Val.cellsList vs).length] ++ Val.cellsList vs

/-- The cells of a list of values, one value after another. -/
def Val.cellsList : List Val → List ℕ
  | [] => []
  | v :: vs => v.cells ++ Val.cellsList vs
end

/-- The memory `mem` holds the value `v` in the cells starting at address `b`. -/
def ValAt (mem : ℕ → ℕ) (b : ℕ) (v : Val) : Prop :=
  ∀ (i : ℕ) (h : i < v.cells.length), mem (b + i) = v.cells[i]

/-- A task whose instances and outputs are values. Instance `x` is stored as the value `enc x`,
and a correct output for `x` is the address of a value `v` with `Correct x v`. The size of an
instance is the number of cells of `enc x`.

The requirements of `GI.Cited.Task` become: every number inside `enc x` is at most a polynomial in
the number of cells of `enc x`, and for every instance `x` some `v` with `Correct x v` has a number
of cells polynomial in that size. Lean does not check these two requirements. -/
def Task.ofVal {α : Type} (enc : α → Val) (Correct : α → Val → Prop) : Task α where
  size x := (enc x).cells.length
  Input x b mem := ValAt mem b (enc x)
  Output x mem r := ∃ v, ValAt mem r v ∧ Correct x v

/-- A permutation of `Fin n`, as the list of the images of `0, …, n - 1`. -/
def encPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Val :=
  .list ((List.finRange n).map fun i => .nat (σ i))

/-- A list of permutations of `Fin n`, together with `n`: the value `[n, [σ₀, …, σ_{k-1}]]`. A
permutation group is given this way, by a list of generators. -/
def encPerms {n : ℕ} (gs : List (Equiv.Perm (Fin n))) : Val :=
  .list [.nat n, .list (gs.map encPerm)]

end GI.Cited
