-- The instances at arities 64 and 2 are proved in `Workspace/Proved/KRef.lean`
module

public import Workspace.Cited.Encoding
public import Workspace.Cited.CoherentConfig
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# Stage 2 task: `k`-ary Weisfeiler–Leman refinement, run on two inputs jointly

**The instances at arity `64` (`= P₀.κ`) and arity `2` are proved, as
`GI.Proved.karyRefinement64` and `GI.Proved.karyRefinement2` in `Workspace/Proved/KRef.lean`.**

[H] = Helfgott, Bajpai, Dona, arXiv:1710.04574v1, Section 2.5 and Algorithm 3: "If the
coloring `C = C₀` at the beginning has `r` different colors, it is clear that it can be refined
at most `|Γ|^k − r` times. … the time taken is `O(k² |Γ|^{2k+1} log |Γ|)`." [WeisfeilerLeman68]
is the binary case. The paper uses the binary refinement (Section A.3, Case 2b: "apply the
canonical coherent refinement from Helfgott's exposition to this binary coloring") and the
`k`-ary one for `k = κ` (Section A.3: "Canonical coherent refinement may then be applied to the
resulting full tuple structure"). The arity `k` is a fixed parameter: the running time is
`n^{O(k)}`.

*Canonical output.* A canonical refinement is a function of its input, so a task "for one
input" would have to name that function. Instead the task takes two colorings and asks for a
pair of refined colorings with one palette, such that every relabeling carrying `c` to `c'`
(or `c` to itself, or `c'` to itself) carries the refined colorings in the same way. With the
joint refinement clause this gives `Iso(c, c') = Iso(d, d')`. This is the equivariance the
paper uses (comparing the structures of the two inputs `x, y`); comparisons of the pairs
`(x, x), (x, y), (y, y)` are three calls.

*Why every instance has a correct output.* Take `d = F c`, `d' = F c'` for the `F` of
`GI.Cited.KaryCoherentRefinement` (true; see its docstring), then compress the joint palette
injectively to fewer than `2 n^k` values; all the clauses depend only on equalities of colors
and on counts, so they survive the compression.

*Output size.* The output colors are asked to be below `2 n^k`, the number of tuples of the two
inputs together, so the output has `2 n^k` numbers of `O(k log n)` bits. Renaming the colors by
their rank among the colors that occur is a sort, so every algorithm can meet the bound.

*Input bound.* The coloring values are required to be at most `n^k`, and the encoding contains
`n` padding cells, so every number is at most the number of cells.
-/

namespace GI.Cited

open Equiv

/-- A `k`-ary coloring as the list of its values over all tuples, in the order of
`finFunctionFinEquiv`. -/
def encKColoring {n k : ℕ} (c : (Fin k → Fin n) → ℕ) : Val :=
  .list ((List.finRange (n ^ k)).map fun j => .nat (c (finFunctionFinEquiv.symm j)))

/-- Two `k`-ary colorings of `Fin n`, with values at most `n^k`. -/
structure TwoColoringsInst (k : ℕ) where
  n : ℕ
  c : (Fin k → Fin n) → ℕ
  c' : (Fin k → Fin n) → ℕ
  c_le : ∀ x, c x ≤ n ^ k
  c'_le : ∀ x, c' x ≤ n ^ k

/-- `σ` carries the coloring `a` to the coloring `b`: `b(σ ∘ x) = a(x)`. -/
def Carries {n k : ℕ} (σ : Perm (Fin n)) (a b : (Fin k → Fin n) → ℕ) : Prop :=
  ∀ x, b (σ ∘ x) = a x

/-- The correct outputs of the joint refinement. -/
def JointRefinement {n k : ℕ} (c c' d d' : (Fin k → Fin n) → ℕ) : Prop :=
  IsConfiguration d ∧ IsCoherent d ∧ IsConfiguration d' ∧ IsCoherent d' ∧
  (∀ x y, d x = d y → c x = c y) ∧ (∀ x y, d' x = d' y → c' x = c' y) ∧
  (∀ x y, d x = d' y → c x = c' y) ∧
  ∀ σ : Perm (Fin n),
    (Carries σ c c' → Carries σ d d') ∧ (Carries σ c c → Carries σ d d) ∧
    (Carries σ c' c' → Carries σ d' d')

/-- **Joint `k`-ary coherent refinement** ([H, Sections 2.3–2.5]). Output `[d, d']`: `k`-ary
coherent configurations refining `c, c'` with one palette, carried along by every relabeling
that carries the inputs. -/
def KaryRefinementTask (k : ℕ) : Task (TwoColoringsInst k) :=
  Task.ofVal
    (fun I => .list [.list (List.replicate I.n (.nat 0)), encKColoring I.c, encKColoring I.c'])
    (fun I v => ∃ d d' : (Fin k → Fin I.n) → ℕ,
      v = .list [encKColoring d, encKColoring d'] ∧
      (∀ x, d x < 2 * I.n ^ k) ∧ (∀ x, d' x < 2 * I.n ^ k) ∧ JointRefinement I.c I.c' d d')

/-- For each fixed arity `k`. The two instances used are below. -/
def KaryRefinement (k : ℕ) : Prop := ∃ p, PolyTimeAt (KaryRefinementTask k) p

/-- `KaryRefinement` at arity `64`, the paper's `κ` (`P₀.κ = 64`, `Assembly/Params.lean`). It is named
so that it is a constant. Proved as `GI.Proved.karyRefinement64` in `Workspace/Proved/KRef.lean`. -/
def KaryRefinement64 : Prop := KaryRefinement 64

/-- `KaryRefinement` at arity `2`. It is named so that it is a constant.
Proved as `GI.Proved.karyRefinement2` in `Workspace/Proved/KRef.lean`. -/
def KaryRefinement2 : Prop := KaryRefinement 2

end GI.Cited
