-- Proved as `GI.Proved.johnsonIdentification` in `Workspace/Proved/JohnFinal.lean`
module

public import Workspace.Cited.AlgoPermGroups
public import Workspace.Cited.MarotiPrimitive
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-!
# Stage 2 task: the Johnson identification of one factor `Alt(m)` on `k`-sets

**Proved as `GI.Proved.johnsonIdentification` in `Workspace/Proved/JohnFinal.lean`.**

*Source.* [H] = Helfgott, Bajpai, Dona, *Graph isomorphisms in quasi-polynomial time*,
arXiv:1710.04574v1 (12 October 2017; v1 is the only version), Section 2.8, "Identification of
groups and schemes", pages 1125–15 and 1125–16 of the Bourbaki numbering. Verbatim: "We will have a
permutation group `G < Sym(Γ)`, and we will know that it is isomorphic to the abstract group
`Alt_m`. … there exists a bijection `ι₀ : Γ → S_k(Λ₀)` and an isomorphism `φ₀ : G → Alt(Λ₀)` such
that `ι₀(ω^g) = ι₀(ω)^{φ₀(g)}`. The problem consists in building `ι : Γ → S_k(Λ)` and
`φ : G → Alt(Λ)`, computable in polynomial time, with these properties. … We will suppose that
`m > (k + 1)² − 2`". The section ends: "The applications `φ, ι` are thus the ones we wanted; we
have built an explicit isomorphism between `G` and `Alt(Λ)`."

*The task.* Input: generators of `G ≤ Sym(n)`, and the numbers `m, k`. Promise: `5 ≤ m`, `1 ≤ k`,
`m > (k + 1)² − 2`, and some bijection `ι₀` of the points with the `k`-subsets of `Fin m` carries
`G` onto the action of `Alt(m)` on `k`-subsets. Output: such a bijection `ι`, listed point by point
(each subset as a sorted list). The isomorphism `φ` of [H] is not asked for: it is determined by `ι`.

*Every instance has a correct output*: `ι₀`, by the promise. *Every correct output is small*: it
lists `n` subsets of `k ≤ m` numbers below `m`, and `m ≤ binom(m, k) = n` since `1 ≤ k < m`. The
input numbers `m, k` are also at most `n`.

*Why `5 ≤ m`.* The reduction that uses this task has `m ≥ 5` ([H, Theorem 3.1(b)] also has
`m ≥ 5`). For `m = 3, k = 1` the promise holds with `m > (k+1)² − 2 = 2`, but the two non-diagonal
orbitals of `Alt(3)` on three points are not symmetric, and the construction of [H, §2.8] (the
sets `C(x, y)`) then returns two-point sets instead of points. So the hypothesis restricts the
task to the range where the source's argument is correct.
-/

namespace GI.Cited

open Equiv

/-- The bijection `ι` carries `G` onto the action of `Alt(m)` on `k`-subsets: a permutation is in
`G` exactly when, read through `ι`, it is the action of an even permutation of `Fin m`. -/
def IsJohnsonId {n m k : ℕ} (G : Subgroup (Perm (Fin n)))
    (ι : Fin n ≃ {A : Finset (Fin m) // A.card = k}) : Prop :=
  ∀ g : Perm (Fin n), g ∈ G ↔
    ∃ h ∈ alternatingGroup (Fin m), ∀ x : Fin n, ι (g x) = kSetPerm h (ι x)

/-- The bijection `ι`, listed point by point; each subset is a sorted list. -/
def encKSets {n m k : ℕ} (ι : Fin n ≃ {A : Finset (Fin m) // A.card = k}) : Val :=
  .list ((List.finRange n).map fun x => .list (((ι x).1.sort (· ≤ ·)).map fun a => .nat a))

/-- A group known to be `Alt(m)` acting on `k`-subsets, in the range `m > (k + 1)² − 2`. -/
structure JohnsonInst where
  n : ℕ
  m : ℕ
  k : ℕ
  gs : List (Perm (Fin n))
  five_le : 5 ≤ m
  one_le : 1 ≤ k
  bound : (k + 1) ^ 2 < m + 2
  johnson : ∃ ι : Fin n ≃ {A : Finset (Fin m) // A.card = k}, IsJohnsonId (gens gs) ι

/-- **Johnson identification** ([H, Section 2.8], following [BLS]). -/
def JohnsonIdentificationTask : Task JohnsonInst :=
  Task.ofVal (fun I => .list [encGroup I.gs, .nat I.m, .nat I.k])
    (fun I v => ∃ ι : Fin I.n ≃ {A : Finset (Fin I.m) // A.card = I.k},
      IsJohnsonId (gens I.gs) ι ∧ v = encKSets ι)

/-- Proved as `GI.Proved.johnsonIdentification` in `Workspace/Proved/JohnFinal.lean`. -/
def JohnsonIdentification : Prop := ∃ p, PolyTimeAt JohnsonIdentificationTask p

/-- Every instance has a correct output. -/
theorem johnsonIdentification_total (I : JohnsonInst) :
    ∃ v : Val, ∃ ι : Fin I.n ≃ {A : Finset (Fin I.m) // A.card = I.k},
      IsJohnsonId (gens I.gs) ι ∧ v = encKSets ι := by
  obtain ⟨ι, h⟩ := I.johnson
  exact ⟨_, ι, h, rfl⟩

end GI.Cited
