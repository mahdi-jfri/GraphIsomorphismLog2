import Workspace.Assembly.Params
import Workspace.Lang.Prims.Repr

/-!
# How a stage 2 program stores states and answers

A `GI.Lang` program works on values (`GI.Cited.Val`). This file says which value stands for a
recursive state (`GI.Algorithm.State`) and which value stands for an answer (a set of
permutations that is empty or a coset). The formats use the predicates of
`Workspace/Lang/Prims/Repr.lean`, so the cited primitives can be called on the parts.

**Positions.** A state lives on a finite type `Ω`. A program sees the positions as the numbers
`0, …, k - 1`, through an enumeration `e : Ω ≃ Fin k`. A permutation `g` of `Ω` is stored as the
permutation `e ∘ g ∘ e⁻¹` of `Fin k` (`toFin e g`), a subgroup as its image, a set of positions
by its indicator, and a partition by labels whose classes are its classes (`PartVal`).

**Colors.** The colors of a state have some type `C`. A program sees them as numbers, through a
code `c : C → ℕ`. Implementations get an injective code (`Implements` in
`Workspace/Assembly/Refinement.lean`), so the stored colorings determine the answer.

**State** (`StateVal e c v S`). `v` is the list
`[k, group, domain, x, y, hierarchy, rows, floor, h, N]`:
* `k`: the number of positions;
* `group`: generators of the image of `S.G` (`GroupVal`);
* `domain`: the indicator of `S.dom` (`DomVal`);
* `x`, `y`: the colors of the positions under the code (`ColorVal`);
* `hierarchy`: the list of the intervals of `S.hier`, each `[partition, ratio, cap, origin]`
  (`IntervalVal`);
* `rows`: `[]` when there is no row record, and `[[m, rows, cols]]` otherwise, where `cols` is
  `[]` or `[partition]` (`RowVal`);
* `floor`: 0 or 1; `h` and `N`: numbers.

The proof fields of a state (`dom_inv`, `h_le`, `counter`) are not stored.

**Answer** (`AnswerVal e v A`). Either `v = []` and `A = ∅`, or `v` is a coset value
`[x, group]` (`CosetVal`) of the image of `A`.
-/

namespace GI.Assembly

open GI.Algorithm GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)
open scoped Pointwise

variable {Ω C : Type} {k : ℕ}

/-- A permutation of `Ω` as a permutation of `Fin k`: `e ∘ g ∘ e⁻¹`. -/
abbrev toFin (e : Ω ≃ Fin k) : Perm Ω ≃* Perm (Fin k) := e.permCongrHom

/-- A subgroup of `Perm Ω` as a subgroup of `Perm (Fin k)`. -/
def groupFin (e : Ω ≃ Fin k) (G : Subgroup (Perm Ω)) : Subgroup (Perm (Fin k)) :=
  G.map (toFin e).toMonoidHom

open Classical in
/-- `v` is the indicator of the set `D`: entry `i` is 1 if position `e⁻¹ i` lies in `D`, and 0
otherwise. -/
def DomVal (e : Ω ≃ Fin k) (v : Val) (D : Set Ω) : Prop :=
  v = encFun fun i => if e.symm i ∈ D then 1 else 0

/-- `v` lists the colors of the coloring `x` under the code `c`, in the order of `e`. -/
def ColorVal (e : Ω ≃ Fin k) (c : C → ℕ) (v : Val) (x : Ω → C) : Prop :=
  v = encFun fun i => c (x (e.symm i))

/-- `v` lists labels whose classes are those of the partition `R` (`PartVal`). -/
def PartitionVal (e : Ω ≃ Fin k) (v : Val) (R : Setoid Ω) : Prop :=
  PartVal k v fun i j => R.r (e.symm i) (e.symm j)

/-- `v = [partition, ratio, cap, origin]` stores an interval of the hierarchy. -/
def IntervalVal (e : Ω ≃ Fin k) (v : Val) (I : Interval Ω) : Prop :=
  ∃ pv, PartitionVal e pv I.part ∧ v = .list [pv, .nat I.ratio, .nat I.cap, .nat I.origin]

/-- `v` is the list of the values of the intervals of the hierarchy `l`, in order. -/
def HierVal (e : Ω ≃ Fin k) (v : Val) (l : List (Interval Ω)) : Prop :=
  ∃ vs : List Val, v = .list vs ∧ List.Forall₂ (IntervalVal e) vs l

/-- An optional object: `[]` for `none`, and `[u]` for `some a` with `u` storing `a`. -/
def OptVal {α : Type} (Q : Val → α → Prop) (v : Val) : Option α → Prop
  | none => v = .list []
  | some a => ∃ u, Q u a ∧ v = .list [u]

/-- `v = [m, rows, cols]` stores a row record; `cols` is an optional partition. -/
def RowVal (e : Ω ≃ Fin k) (v : Val) (R : RowRecord Ω) : Prop :=
  ∃ rv cv, PartitionVal e rv R.rows ∧ OptVal (PartitionVal e) cv R.cols ∧
    v = .list [.nat R.m, rv, cv]

/-- **The value of a state.** `v = [k, group, domain, x, y, hierarchy, rows, floor, h, N]`,
with the parts described in the header of this file. -/
def StateVal (e : Ω ≃ Fin k) (c : C → ℕ) (v : Val) (S : State Ω C) : Prop :=
  ∃ gv dv xv yv hv rv,
    GroupVal k gv (groupFin e S.G) ∧ DomVal e dv S.dom ∧ ColorVal e c xv S.x ∧
    ColorVal e c yv S.y ∧ HierVal e hv S.hier ∧ OptVal (RowVal e) rv S.rows ∧
    v = .list [.nat k, gv, dv, xv, yv, hv, rv, boolVal S.floor, .nat S.h, .nat S.N]

/-- **The value of an answer.** `v = []` for the empty answer, and otherwise a coset value
`[x, group]` whose coset `x · ⟨group⟩` is the image of `A` in `Perm (Fin k)`. -/
def AnswerVal (e : Ω ≃ Fin k) (v : Val) (A : Set (Perm Ω)) : Prop :=
  (v = .list [] ∧ A = ∅) ∨ CosetVal k v (toFin e '' A)

/-! ### Basic facts -/

/-- The value of an answer determines the answer. -/
theorem AnswerVal.unique {e : Ω ≃ Fin k} {v : Val} {A B : Set (Perm Ω)} (hA : AnswerVal e v A)
    (hB : AnswerVal e v B) : A = B := by
  have himg : ∀ {A B : Set (Perm Ω)}, toFin e '' A = toFin e '' B → A = B := fun h =>
    (Set.image_injective.mpr (toFin e).injective) h
  rcases hA with ⟨rfl, rfl⟩ | hA <;> rcases hB with ⟨hv, rfl⟩ | hB
  · rfl
  · obtain ⟨x, gs, h, -⟩ := hB; cases h
  · obtain ⟨x, gs, rfl, -⟩ := hA; cases hv
  · exact himg (hA.unique hB)

/-- The empty answer. -/
theorem answerVal_empty (e : Ω ≃ Fin k) : AnswerVal e (.list []) (∅ : Set (Perm Ω)) :=
  Or.inl ⟨rfl, rfl⟩

/-- The image of a left coset `t • H` is the left coset of the images. -/
theorem toFin_image_coset (e : Ω ≃ Fin k) (t : Perm Ω) (H : Subgroup (Perm Ω)) :
    toFin e '' (t • (H : Set (Perm Ω))) = toFin e t • (groupFin e H : Set (Perm (Fin k))) := by
  ext g
  simp only [Set.mem_image, Set.mem_smul_set, SetLike.mem_coe, groupFin, Subgroup.mem_map,
    smul_eq_mul]
  constructor
  · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨toFin e h, ⟨h, hh, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨t * h, ⟨h, hh, rfl⟩, by simp⟩

/-- A coset `t • H` is stored by the image of `t` and generators of the image of `H`. -/
theorem answerVal_coset (e : Ω ≃ Fin k) {t : Perm Ω} {H : Subgroup (Perm Ω)} {gv : Val}
    (hg : GroupVal k gv (groupFin e H)) :
    AnswerVal e (.list [GI.Cited.encPerm (toFin e t), gv]) (t • (H : Set (Perm Ω))) := by
  right
  rw [toFin_image_coset]
  exact CosetVal.mk hg

end GI.Assembly
