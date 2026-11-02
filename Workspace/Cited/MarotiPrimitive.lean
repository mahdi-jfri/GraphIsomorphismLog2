import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.Data.Finset.Card

/-!
# Cited input: the Cameron–Maróti theorem on large primitive groups

The paper's dispatcher (Section 3.3, Algorithm 5, Section A.5 "Constructive recognition")
cites "the constructive reduction stated in [H, Theorem 3.1 and Section 2.8]". [H, Theorem 3.1]
is the Cameron–Maróti theorem. This file states its mathematical content. The constructive part
(finding the normal subgroup and the Johnson coordinates, [H, Section 2.8] and [BLS]) is an
algorithm, stated in `Workspace/Cited/AlgoCameron.lean`.
-/

namespace GI.Cited

open Equiv

/-- The action of a permutation of `Fin m` on the `k`-element subsets of `Fin m`. -/
def kSetPerm {m k : ℕ} (h : Perm (Fin m)) : Perm {A : Finset (Fin m) // A.card = k} where
  toFun A := ⟨A.1.map h.toEmbedding, by rw [Finset.card_map]; exact A.2⟩
  invFun A := ⟨A.1.map h.symm.toEmbedding, by rw [Finset.card_map]; exact A.2⟩
  left_inv A := by
    apply Subtype.ext
    simp [Finset.map_map]
  right_inv A := by
    apply Subtype.ext
    simp [Finset.map_map]

/-- **Maróti's theorem on the orders of primitive groups, above the Mathieu degrees**
([H, Theorem 3.1], "[Cam], [Ma]"). For every degree `n ≥ 25` and every primitive
`G ≤ Sym(n)`, either `|G| < n^{1 + ⌊log₂ n⌋}`, or there are `m, k, r` and an identification
`e` of the `n` points with `r`-tuples of `k`-subsets of `Fin m` such that, read through `e`,
every element of `G` acts in the product action of `Sym(m) wr Sym(r)` (a permutation of the
coordinates followed by one permutation of `Fin m` in each coordinate), and `G` contains every
element of `Alt(m)^r` acting coordinatewise.

*Sources.*
* A. Maróti, *On the orders of primitive groups*, J. Algebra 258 (2002) 631–640. We read the
  author's preprint dated 21 February 2002 (renyi.hu/~maroti/primitive.pdf), Theorem 1.1,
  verbatim: "Let `G` be a primitive permutation group of degree `n`. Then one of the following
  holds. (i) `G` is a subgroup of `S_m wr S_r` containing `(A_m)^r`, where the action of `S_m`
  is on `k`-element subsets of `{1, …, m}` and the wreath product has the product action of
  degree `n = binom(m, k)^r`; (ii) `G = M_11, M_12, M_23` or `M_24` with their 4-transitive
  action; (iii) `|G| ≤ n · ∏_{i=0}^{[log₂ n]-1} (n - 2^i) < n^{1+[log₂ n]}`."
* [H] = Helfgott, Bajpai, Dona, *Graph isomorphisms in quasi-polynomial time*,
  arXiv:1710.04574v1 (12 Oct 2017), Theorem 3.1, verbatim: "Let `H < Sym(R)` be a primitive
  group, where `|R| = r` is larger than an absolute constant. Then, either (a)
  `|H| < r^{1+log₂ r}`, or (b) there is a `M ⊳ H` such that `R` is divided into a system of
  `binom(m,k)` blocks on which `M` acts as a group `Alt(k)_m`, `m ≥ 5`. Furthermore,
  `[H : M] ≤ r`." Its footnote 16: "`M` is isomorphic, as a permutation group, to
  `(Alt(k)_m)^s`, `s ≥ 1`. We have `r = binom(m,k)^s`."

*Why it is true.* Maróti proves Theorem 1.1 from the O'Nan–Scott theorem and CFSG. Case (ii)
only occurs in degrees 11, 12, 23, 24, so `n ≥ 25` excludes it. Case (iii) gives the first
disjunct (`<` in `ℕ`, with `Nat.log 2 n = ⌊log₂ n⌋`). Case (i) gives the second: "`G` is a
subgroup of `S_m wr S_r` in the product action" means that, after identifying the points with
`r`-tuples of `k`-subsets, every element of `G` permutes the coordinates and acts on each
coordinate by an element of `S_m`; "containing `(A_m)^r`" is the last clause. The convention
`(g x)_i = h_i (x_{σ i})` describes the same set of permutations as any other convention for the
product action, since `σ` and `h` range over everything.

*Edge cases.* Maróti puts no condition on `m, k, r`. For `n ≥ 25` case (i) forces
`binom(m, k) ≥ 2` and `r ≥ 1` (so `1 ≤ k < m`), since `n = binom(m,k)^r`; we do not add these to
the statement, a user derives them from the cardinality of `e`. For `m ≤ 4` case (i) is still
allowed by the statement, which is harmless: it is only weaker than [H]'s `m ≥ 5`.

*Why it is the weakest form needed.* The dispatcher uses: (a) the order bound, to enumerate the
primitive quotient (`DispatchFacts.enumeration`, index `≤ exp(a (log d)^2)`); (b) the product
coordinates, for the product refinement (`DispatchFacts.product`, index `≤ 2^r r!` from
`G ≤ Sym(m) wr Sym(r)` and `Alt(m)^r ≤ G`), and for `r = 1` the single-factor normalization
(index `≤ 2` and a map onto `Alt(m)`, from `Alt(m) ≤ G ≤ Sym(m)`). We state Maróti's form
rather than [H]'s, because [H]'s "`[H : M] ≤ r`" is weaker than what the paper uses (the paper
uses `2^r r!`, Section A.5 "With `x = log(n+2)`…": "the outer index is at most `2^s s!`").
The statement is for subgroups of `Perm (Fin n)`. -/
def MarotiPrimitive : Prop :=
  ∀ (n : ℕ), 25 ≤ n → ∀ (G : Subgroup (Perm (Fin n))), MulAction.IsPreprimitive G (Fin n) →
    Nat.card G < n ^ (1 + Nat.log 2 n) ∨
    ∃ (m k r : ℕ) (e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})),
      (∀ g ∈ G, ∃ (σ : Perm (Fin r)) (h : Fin r → Perm (Fin m)),
        ∀ x : Fin n, e (g x) = fun i => kSetPerm (h i) (e x (σ i))) ∧
      (∀ h : Fin r → Perm (Fin m), (∀ i, h i ∈ alternatingGroup (Fin m)) →
        (e.trans ((Equiv.piCongrRight fun i => kSetPerm (h i)).trans e.symm) : Perm (Fin n)) ∈ G)

end GI.Cited
