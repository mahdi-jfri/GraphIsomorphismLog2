-- Proved in `Impl/CamFinal.lean` (`cameronRecognition_of_johnson`)
import Workspace.Cited.AlgoPermGroups
import Workspace.Cited.MarotiPrimitive
import Mathlib.Data.Finset.Sort

/-!
# Stage 2 task: constructive Cameron–Maróti recognition

**Proved in `Impl/CamFinal.lean` (`cameronRecognition_of_johnson`), from Maróti's theorem and
the tasks `JohnsonIdentification`, `GroupOrder`, `ChiefSeriesAlgo` and `QuotientCentralizer`.**

[H] = Helfgott, Bajpai, Dona, arXiv:1710.04574v1, Section 3.1, after Theorem 3.1: "It is
possible [BLS] to find in polynomial time the normal subgroup `M` and the blocks of the action
of `M`. We have already seen in §2.8 how to explicitly identify the action of `M` with that of
`Alt(k)_m`. Besides, the Schreier-Sims algorithm allows us to calculate `|H|` in polynomial
time, and thus also tells us whether we are in case (a)." [H, Section 2.8]: "We will suppose
that `m > (k+1)² − 2` … (14) If `m ≤ (k+1)² − 2`, then `n` is so large that `m! = n^{O(log n)}`.
In that case, we will be able to afford to remove `G` … brutally". The paper (Section A.5,
"Constructive recognition"): "For the Johnson recognition procedure in that source, the range
not covered by its simple polynomial construction has entire constituent order `d^{O(log d)}`
… Enumerate that constituent".

The task follows this: for a primitive group of degree `n ≥ 25`, output one of
* `[0]`: Maróti's case (iii), `|G| < n^{1 + ⌊log₂ n⌋}` (decided by computing `|G|`);
* `[1, m, k, r, E]`: Maróti's case (i) with `m > (k'+1)² - 2`, where `k' = min(k, m - k)`,
  together with the identification `e` of the points with `r`-tuples of `k`-subsets (`E` lists,
  for each point, the `r` subsets as sorted lists);
* `[2]`: Maróti's case (i) holds with some `m ≤ (k'+1)² - 2`, `k' = min(k, m - k)` (the range of
  [H]'s footnote 14, enumerated by the paper).

The condition is on `k' = min(k, m - k)`, not on `k`: a structure on `k`-subsets is also one on
`(m - k)`-subsets, through complements. With `k` alone, `[2]` would be a correct output for the
natural action of `Sym(m)` (take `k = m - 1`), whose order `m!` is not `d^{O(log d)}`.

*Every instance has a correct output*, by Maróti's theorem (`GI.Cited.MarotiPrimitive`, true).

*Output size.* Every correct output is small without an explicit bound. In `[1, m, k, r, E]`
the bijection `e` gives `n = binom(m, k)^r` with `n ≥ 25`, so `binom(m, k) ≥ 2`, hence
`1 ≤ k < m`, `m ≤ binom(m, k) ≤ n` and `r ≤ log₂ n`; `E` lists `n` tuples of `r` sorted lists of
`k` numbers below `m` (`GI.CitedChecks.cameron_params_le`).

*Polynomial time.* `|G|` is computed by Schreier–Sims. In case (i), [BLS] (Babai,
Luks, Seress, 1987/88) finds the socle and its product decomposition; [H, Section 2.8] builds
the Johnson identification of each factor when `m > (k+1)² − 2`. To output `[2]`, the program
must recognise that no candidate with `m > (k+1)² − 2` works: there are few `(m, k, r)` with
`binom(m,k)^r = n`, and each candidate's identification can be built and checked.

*Source check (the source is indirect).* [H] (v1) says after Theorem 3.1:
"It is possible [BLS] to find in polynomial time the normal subgroup `M` and the blocks of the
action of `M`", and Section 2.8 builds the Johnson identification of one factor `Alt_m` on
`k`-sets "computable in polynomial time" when `m > (k+1)² − 2`. The algorithm: compute `|G|`; if
it is below `n^{1+⌊log₂ n⌋}` output `[0]`. Otherwise Maróti's case (i) holds, and then `m ≥ 5`
(for `m ≤ 4`, `|Sym(m) wr Sym(r)| < n^{1+⌊log₂ n⌋}` for `n = binom(m,k)^r ≥ 25`), so the socle
is `Alt(m)^r` (it is normal and has trivial centralizer). Find the socle and its `r` simple
factors (Luks's composition series, Kantor–Luks; [LM, Theorem 3.1(ix)]); `m` is fixed by
`|Alt(m)| = |T|`, and `k ≤ m/2` by `binom(m,k)^r = n`. If `(k+1)² ≥ m + 2`, output `[2]`: a
structure with these `m, k` exists by Maróti, and no structure has `(k'+1)² < m + 2`, since
`k' ∈ {k, m - k}`. Otherwise `k < m/2`; the orbits of the product of the other `r - 1` factors
give the coordinate blocks, [H, Section 2.8] identifies each coordinate, and `G` lies in
`Sym(m) wr Sym(r)` for this `e` because it normalizes the socle and the normalizer of `Alt(m)`
on `k`-sets, `k < m/2`, `m ≥ 5`, is `Sym(m)`. The decomposition into coordinates is folklore
rather than a statement of [BLS] or [H]. -/

namespace GI.Cited

open Equiv

/-- The structure of Maróti's case (i) for `G` with the identification `e`. -/
def MarotiStructure {n m k r : ℕ} (G : Subgroup (Perm (Fin n)))
    (e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})) : Prop :=
  (∀ g ∈ G, ∃ (σ : Perm (Fin r)) (h : Fin r → Perm (Fin m)),
    ∀ x : Fin n, e (g x) = fun i => kSetPerm (h i) (e x (σ i))) ∧
  (∀ h : Fin r → Perm (Fin m), (∀ i, h i ∈ alternatingGroup (Fin m)) →
    (e.trans ((Equiv.piCongrRight fun i => kSetPerm (h i)).trans e.symm) : Perm (Fin n)) ∈ G)

/-- The identification `e`, listed point by point; each subset is a sorted list. -/
def encKSetTuples {n m k r : ℕ} (e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})) :
    Val :=
  .list ((List.finRange n).map fun x => .list ((List.finRange r).map fun i =>
    .list (((e x i).1.sort (· ≤ ·)).map fun a => .nat a)))

/-- A primitive group of degree at least `25`. -/
structure PrimitiveInst where
  n : ℕ
  le_n : 25 ≤ n
  gs : List (Perm (Fin n))
  primitive : MulAction.IsPreprimitive (gens gs) (Fin n)

/-- **Constructive Cameron–Maróti recognition** ([H, Theorem 3.1, Section 2.8], [BLS]). -/
def CameronRecognitionTask : Task PrimitiveInst :=
  Task.ofVal (fun I => encGroup I.gs)
    (fun I v =>
      (v = .list [.nat 0] ∧ Nat.card (gens I.gs) < I.n ^ (1 + Nat.log 2 I.n)) ∨
      (∃ (m k r : ℕ) (e : Fin I.n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})),
        (min k (m - k) + 1) ^ 2 < m + 2 ∧ MarotiStructure (gens I.gs) e ∧
        v = .list [.nat 1, .nat m, .nat k, .nat r, encKSetTuples e]) ∨
      (v = .list [.nat 2] ∧ ∃ (m k r : ℕ) (e : Fin I.n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})),
        m + 2 ≤ (min k (m - k) + 1) ^ 2 ∧ MarotiStructure (gens I.gs) e))

/-- Proved in `Impl/CamFinal.lean` (`cameronRecognition_of_johnson`). -/
def CameronRecognition : Prop := ∃ p, PolyTimeAt CameronRecognitionTask p

/-- Every instance has a correct output, given Maróti's theorem. -/
theorem cameronRecognition_total (hM : MarotiPrimitive) (I : PrimitiveInst) :
    ∃ v : Val, (v = .list [.nat 0] ∧ Nat.card (gens I.gs) < I.n ^ (1 + Nat.log 2 I.n)) ∨
      (∃ (m k r : ℕ) (e : Fin I.n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})),
        (min k (m - k) + 1) ^ 2 < m + 2 ∧ MarotiStructure (gens I.gs) e ∧
        v = .list [.nat 1, .nat m, .nat k, .nat r, encKSetTuples e]) ∨
      (v = .list [.nat 2] ∧ ∃ (m k r : ℕ)
        (e : Fin I.n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})),
        m + 2 ≤ (min k (m - k) + 1) ^ 2 ∧ MarotiStructure (gens I.gs) e) := by
  rcases hM I.n I.le_n (gens I.gs) I.primitive with h | ⟨m, k, r, e, h1, h2⟩
  · exact ⟨_, Or.inl ⟨rfl, h⟩⟩
  · by_cases hmk : (min k (m - k) + 1) ^ 2 < m + 2
    · exact ⟨_, Or.inr (Or.inl ⟨m, k, r, e, hmk, ⟨h1, h2⟩, rfl⟩)⟩
    · exact ⟨_, Or.inr (Or.inr ⟨rfl, m, k, r, e, by omega, ⟨h1, h2⟩⟩)⟩

end GI.Cited
