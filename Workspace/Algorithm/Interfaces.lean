import Workspace.Algorithm.State
import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Query scripts and the interfaces of the subroutines

## Query scripts

Several subroutines first ask recursive questions and then compute their output
from the answers: `CheckNewWindow` and the lockstep comparisons ask `Continue` on
kernel orbits (Section 4, Algorithm 2), the row terminal asks `Solve` on rows
(Theorem A.23), and `AuxiliaryReduction` asks `Continue` on a rectangle orbit `Δ` or
`Solve` on a small configuration (Algorithm 3). Later questions may depend on
earlier answers. A `Script α` records this: it is either finished with a value of
type `α`, or it asks one recursive call (a state together with the procedure that
solves it) and continues with a function of the returned answer.

`Script.evalExact` is the value the script produces when every question receives
the exact answer of its state. An interface states what the paper's lemma gives
about `evalExact`. The recursion (`Workspace/Algorithm/Procedure.lean`) runs the
script with actual recursive calls; the proof of Lemma 6.1 shows that, when those
calls are exact, the script returns `evalExact`.

## Interfaces

Each structure below states exactly what one paper result gives the recursion.

* `Reduction` and `Normalization`: the standard primitive-group reduction and
  the single-factor normalization of Section 3.3 and Algorithm 5. The dispatcher step
  `DispatchStep` of the recursion (`Workspace/Algorithm/Dispatch.lean`) computes its
  `Reduction` from the primitive quotient of the state.
* `GiantLabels`, `NaturalRows`: the supplied alternating map and the one-label
  kernel-orbit map of the giant step (Corollary A.25).
* The row terminal (Theorem A.23) and the column step (Lemma A.14 with Theorem A.18) are
  in `Workspace/Algorithm/RowSteps.lean`; they carry the structural data of Theorems A.17
  and A.18, and their scripts and partitions are defined from these data.
* `Aggregation` (in `Workspace/Algorithm/Aggregation.lean`): Section 4.1, Algorithm
  `alg:auxiliary`, Lemma 5.1, Lemmas A.11, A.12, A.27 to A.30.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm
open scoped Pointwise

/-- The procedure that solves a recursive call: `Solve` (a fresh call), `Continue`
(an inherited call), or `GiantStep` (Algorithm 5). -/
inductive Mode
  | solve
  | cont
  | giant
  deriving DecidableEq

/-- A query script with result type `α`: finished, or one recursive call on a state
followed by a continuation that receives its answer. -/
inductive Script (α : Type) : Type 1
  | done (a : α)
  | ask {Ω' C' : Type} (m : Mode) (S : State Ω' C') (k : Set (Perm Ω') → Script α)

namespace Script

variable {α β : Type}

/-- The result of a script when every recursive call returns its exact answer. -/
def evalExact : Script α → α
  | done a => a
  | ask _ S k => (k S.answer).evalExact

/-- Sequential composition of scripts. -/
def bind : Script α → (α → Script β) → Script β
  | done a, f => f a
  | ask m S k, f => ask m S fun A => (k A).bind f

theorem evalExact_bind (s : Script α) (f : α → Script β) :
    (s.bind f).evalExact = (f s.evalExact).evalExact := by
  induction s with
  | done a => rfl
  | ask m S k ih => exact ih S.answer

/-- A script that asks one call and returns its answer. -/
def call {Ω' C' : Type} (m : Mode) (S : State Ω' C') : Script (Set (Perm Ω')) :=
  ask m S done

/-- Run a list of scripts in order and collect their results. -/
def seqList : List (Script α) → Script (List α)
  | [] => done []
  | s :: ss => s.bind fun a => (seqList ss).bind fun as => done (a :: as)

theorem evalExact_seqList (l : List (Script α)) :
    (seqList l).evalExact = l.map evalExact := by
  induction l with
  | nil => rfl
  | cons s ss ih =>
    simp only [seqList, evalExact_bind, List.map_cons]
    rw [ih]
    rfl

/-- Every recursive call that the script makes when each earlier call receives its
exact answer satisfies `p`. (The calls of a script may depend on earlier answers; an
interface states facts about the calls that the paper's procedure actually makes,
which are those along the exact answers.) -/
def CallsExact (p : ∀ {Ω' C' : Type}, Mode → State Ω' C' → Prop) : Script α → Prop
  | done _ => True
  | ask m S k => p m S ∧ (k S.answer).CallsExact p

theorem callsExact_bind {p : ∀ {Ω' C' : Type}, Mode → State Ω' C' → Prop} :
    ∀ (s : Script α) (f : α → Script β), s.CallsExact p → (f s.evalExact).CallsExact p →
      (s.bind f).CallsExact p
  | done _, _, _, hf => hf
  | ask _ S k, f, hs, hf => ⟨hs.1, callsExact_bind (k S.answer) f hs.2 hf⟩

/-- The number of `Continue` calls that the script makes along the exact answers. -/
def numCont : Script α → ℕ
  | done _ => 0
  | ask m S k => (if m = .cont then 1 else 0) + (k S.answer).numCont

/-! #### Calls and counts of composed scripts -/

theorem numCont_bind : ∀ (s : Script α) (f : α → Script β),
    (s.bind f).numCont = s.numCont + (f s.evalExact).numCont
  | .done _, _ => by simp [bind, numCont, evalExact]
  | .ask m _ k, f => by
    simp only [bind, numCont, evalExact]
    rw [numCont_bind (k _) f]
    omega

theorem callsExact_seqList {p : ∀ {Ω' C' : Type}, Mode → State Ω' C' → Prop} :
    ∀ (l : List (Script α)), (∀ s ∈ l, s.CallsExact p) → (seqList l).CallsExact p
  | [], _ => trivial
  | s :: ss, h =>
    callsExact_bind _ _ (h s (by simp))
      (callsExact_bind _ _ (callsExact_seqList ss fun t ht => h t (by simp [ht])) trivial)

theorem numCont_seqList : ∀ (l : List (Script α)),
    (seqList l).numCont = (l.map numCont).sum
  | [] => rfl
  | s :: ss => by
    simp only [seqList, numCont_bind, List.map_cons, List.sum_cons, numCont_seqList ss]
    simp [numCont]

end Script

/-- The fixed parameters of Sections 6 and 7: the exponents `α, γ` of eq.
`scale-constraints`, the base size `N_0` of direct enumeration, the certificate size
`κ`, and the constants of the running-time analysis that the interfaces refer to: the
exponent `a` of Section 7.2 ("an absolute exponent `a ≥ 1` bounding the polynomial
numbers of local and auxiliary calls … and the exponents in small-quotient
enumeration"), the domain fraction `θ` of Lemma 5.1 and Section 7.2, the cap fraction
`β` of Lemma A.12 and eq. `main-cap-payment`, the bounded label cutoff `q₀` below which
an alternating quotient is enumerated (Section 6: "An enumerative reduction includes
the bounded alternating-degree cases"; Section 7.5 (i)), and the bounded multiplicity
`b₀` of a row construction (Section 7.2 table). The phase threshold is `N^γ` and
`λ = N^α`. -/
structure Params where
  α : ℝ
  γ : ℝ
  N₀ : ℕ
  κ : ℕ
  a : ℝ
  θ : ℝ
  β : ℝ
  q₀ : ℕ
  b₀ : ℕ

variable {Ω C : Type}

/-- The orbit `v^G = {g v | g ∈ G}`. -/
def orb (G : Subgroup (Perm Ω)) (v : Ω) : Set Ω := {w | ∃ g ∈ G, g v = w}

/-- The output of an aggregation round, before the parent continuation: exact
pieces of the parent answer (the large-symmetry branch of Lemma A.11) and
overcosets `τ H` of the original parent action (balanced partitions, Lemma 5.1,
Algorithm 3). -/
structure Branches (Ω : Type) where
  pieces : List (Set (Perm Ω))
  overs : List (Perm Ω × Subgroup (Perm Ω))

/-- What the parent needs from the branches of a giant step: every exact piece
consists of parent isomorphisms; every overcoset `τ H` lies in the parent action;
and every parent isomorphism lies in an exact piece or in an overcoset (proof of
Lemma 6.1: "every parent isomorphism is covered by an aggregation branch"; "A
partition, configuration, or rectangle branch returns an overcoset of the parent
isomorphisms in that branch"). -/
structure Branches.Covers (S : State Ω C) (b : Branches Ω) : Prop where
  pieces_sub : ∀ p ∈ b.pieces, p ⊆ S.answer
  overs_mem : ∀ j : Fin b.overs.length, (b.overs.get j).1 ∈ S.G
  overs_le : ∀ j : Fin b.overs.length, (b.overs.get j).2 ≤ S.G
  cover : S.answer ⊆
    (⋃ p ∈ b.pieces, p) ∪ ⋃ j : Fin b.overs.length,
      (b.overs.get j).1 • ((b.overs.get j).2 : Set (Perm Ω))

/-- The kind of a dispatcher reduction: enumeration of a primitive quotient of
degree `d`, or a product refinement with exponent `r`. -/
inductive DispatchKind
  | enumeration (d : ℕ)
  | product (r : ℕ)

/-- The facts that Section 7.2 states for a dispatcher reduction with `n` cosets of
the child group `K` and child hierarchy `hier'`.

* Enumeration of a primitive quotient of degree `d` ("A small primitive quotient of
  degree `d` is an actual quotient of the whole acting group. Its kernel orbits have
  size at most `s/d`, and its index is at most `exp(a(log d)²)`"; "Uniformly for
  `s ≥ d ≥ 2`"): `2 ≤ d ≤ s`, `n ≤ exp(a (log d)²)`, every `K`-orbit in the domain has at
  most `s/d` points, and `ρ` does not increase (Section 7.1: "Restricting to an
  inherited orbit cannot increase it").
* Product refinement with exponent `r` ("For a product exponent `r ≥ 2`, the actual
  coordinate refinement decreases `ρ` by at least `r-1`. Its outer index is at most
  `2^r r!`. Since `r ≤ log₂ s`"): `2 ≤ r ≤ log₂ s`, `n ≤ 2^r r!` and
  `ρ' ≤ ρ - (r-1)`. -/
def DispatchFacts (P : Params) (S : State Ω C) (K : Subgroup (Perm Ω)) (n : ℕ)
    (hier' : List (Interval Ω)) : DispatchKind → Prop
  | .enumeration d => 2 ≤ d ∧ d ≤ S.size ∧ (n : ℝ) ≤ Real.exp (P.a * Real.log d ^ 2) ∧
      State.hierRho hier' ≤ State.hierRho S.hier ∧ ∀ v ∈ S.dom, d * Nat.card (orb K v) ≤ S.size
  | .product r => 2 ≤ r ∧ (r : ℝ) ≤ Real.logb 2 S.size ∧ n ≤ 2 ^ r * r.factorial ∧
      State.hierRho hier' + ((r : ℝ) - 1) ≤ State.hierRho S.hier

/-- **A dispatcher reduction** (Section 3.3, "The standard primitive-group
reduction either enumerates a group of order `d^{O(log d)}` on an actual `d`-block
quotient, or exposes a large alternating action"; "Product actions refine the
actual hierarchy"; Algorithm 5, "if enumeration or a product refinement applies
then apply that reduction and solve its children with `Continue`").

The reduction acts on an actual invariant block system of the current action. Its
children run under a subgroup `K ≤ G` (the kernel on the blocks, or the subgroup
fixing each product coordinate) on the cosets `τ_j K`, which cover `G`, with the
hierarchy `hier'`. Correctness uses only the cover. The running-time analysis uses
the facts of `DispatchFacts` and `Q_le`, which the paper states for the two
reductions in Section 7.2 (rows "Product refinement" and "Primitive enumeration" of
the table). The reduction itself is cited ([H, Theorem 3.1 and Section 2.8]).

This structure only records the facts of a reduction. The recursion does not accept an
arbitrary `Reduction`: its dispatcher step `GI.Algorithm.DispatchStep`
(`Workspace/Algorithm/Dispatch.lean`) carries the primitive quotient of the state, and its
reduction is computed from it. -/
structure Reduction (P : Params) (S : State Ω C) where
  kind : DispatchKind
  /-- The invariant block system of the quotient. -/
  blocks : Setoid Ω
  blocks_inv : ∀ g ∈ S.G, ∀ v w, blocks.r (g v) (g w) ↔ blocks.r v w
  /-- The subgroup under which the children run. -/
  K : Subgroup (Perm Ω)
  K_le : K ≤ S.G
  /-- The coset representatives. -/
  n : ℕ
  τ : Fin n → Perm Ω
  τ_mem : ∀ j, τ j ∈ S.G
  cover : (S.G : Set (Perm Ω)) ⊆ ⋃ j, τ j • (K : Set (Perm Ω))
  /-- The hierarchy of the children (Section 6: "a product reduction refines the
  stored intervals"). -/
  hier' : List (Interval Ω)
  /-- Section 7.1: "Splitting or restricting intervals also cannot increase `Q`,
  because the logarithms of the interval ratios add and every child inherits its old
  width bound." -/
  Q_le : State.hierQ hier' ≤ State.hierQ S.hier
  /-- The facts of the table of Section 7.2 for this reduction. -/
  facts : DispatchFacts P S K n hier' kind

/-- **The single-factor normalization** (Algorithm 5: "Normalize the single
alternating factor, with at most two cosets"; Section 6.1: "The single-factor
normalization has index at most two above the bounded exceptional degrees. Its
preimage is normal."). The normalized preimage `G'` maps onto `Alt(q)`. -/
structure Normalization (S : State Ω C) where
  G' : Subgroup (Perm Ω)
  le : G' ≤ S.G
  normal : (G'.subgroupOf S.G).Normal
  k : ℕ
  k_le : k ≤ 2
  τ : Fin k → Perm Ω
  τ_mem : ∀ j, τ j ∈ S.G
  cover : (S.G : Set (Perm Ω)) ⊆ ⋃ j, τ j • (G' : Set (Perm Ω))
  q : ℕ
  π : G' →* alternatingGroup (Fin q)
  π_surj : Function.Surjective π
  /-- **The hierarchy of the children**: the stored hierarchy with the exposed primitive
  quotient (Section A.5: "Expose the next primitive quotient"; "Refining its product
  coordinates gives each resulting interval cap `q`, clamped by any already smaller valid
  cap"). The children keep the exposed hierarchy. -/
  hier' : List (Interval Ω)
  rho_le : State.hierRho hier' ≤ State.hierRho S.hier
  Q_le : State.hierQ hier' ≤ State.hierQ S.hier
  /-- Exposing a quotient splits an interval (so `ρ` drops) or keeps the bounds' sum. -/
  drop : State.hierRho hier' < State.hierRho S.hier ∨
    (hier'.map Interval.cap).sum ≤ (S.hier.map Interval.cap).sum

/-- The supplied alternating label set of a giant step: `π : G ↠ Alt(Γ)` with
`Γ = Fin q` (Algorithm 5, `GiantStep(S, Γ)`: "Put `q ← |Γ|` for the supplied
alternating label set"). -/
structure GiantLabels (S : State Ω C) where
  q : ℕ
  π : S.G →* alternatingGroup (Fin q)
  π_surj : Function.Surjective π

/-- The physical kernel orbits are indexed by single labels: a natural map
`label : dom → Γ` that is equivariant, onto, and whose fibers are exactly the
kernel orbits (Corollary A.25, the one-label case; Algorithm 5: "Recover the
one-label or two-label map for the physical kernel orbits"; "this map is
natural"). -/
structure NaturalRows (S : State Ω C) (L : GiantLabels S) (label : Ω → Fin L.q) : Prop where
  equivariant : ∀ (g : S.G), ∀ v ∈ S.dom, label (g.val v) = (L.π g).val (label v)
  onto : ∀ i, ∃ v ∈ S.dom, label v = i
  fibers : ∀ v ∈ S.dom, ∀ w ∈ S.dom,
    label v = label w ↔ ∃ k : S.G, L.π k = 1 ∧ k.val v = w

/-- The row case of `GiantStep` (Algorithm 5): `q > λ`, the kernel-orbit map is
natural, and no retained rows have degree at least `q`. -/
def RowCase (α : ℝ) (S : State Ω C) (L : GiantLabels S) : Prop :=
  (S.N : ℝ) ^ α < L.q ∧ (∃ label, NaturalRows S L label) ∧
    ∀ R, S.rows = some R → R.m < L.q

/-- An inherited call of an aggregation round, of the types that Section 7.2 charges
as "Affected test or rectangle" and "Visible unaffected test". It keeps the phase and
the hierarchy (Section 6.1: "Every later call inherits the state of the original orbit
containing it"), runs under a subgroup of the parent action on part of the parent
domain, and each of its points `v` is of one of two types:

* its orbit has at most `θ s` points: an affected certificate call (Lemma 4.1, type
  `(s, σ) ↦ (s/κ, σ)`, `GI.Paper.certificate_call_types`, with `s/κ ≤ θ s`), a
  large-symmetry call on at most half the domain (Lemma A.11: "inherited half-domain
  calls"), or a rectangle query on `Δ` with `|Δ| ≤ θ s` (Lemma 5.1, Section 5.2,
  `GI.Paper.par_returned_parent_cap_fraction`);
* or `σ` drops by `κ`: an extra unaffected certificate call (Lemma 4.1, type
  `(s, σ) ↦ (s, σ - κ)`). -/
structure ChargedCall (P : Params) (S : State Ω C) {C' : Type} (T : State Ω C') : Prop where
  N_eq : T.N = S.N
  le : T.G ≤ S.G
  sub : T.dom ⊆ S.dom
  hier_eq : T.hier = S.hier
  types : ∀ v ∈ T.dom, (Nat.card (orb T.G v) : ℝ) ≤ P.θ * S.size ∨
    GI.sigma P.κ v T.G + P.κ ≤ S.sigma P.κ

/-- The calls of an aggregation round: inherited charged calls (`ChargedCall`) on the
same positions, or fresh configuration calls (Section 6: "An auxiliary configuration
on `q ≤ λ` labels is an allowed exception: it starts a fresh call on at most
`q² ≤ N^{2α}` positions, already below the same threshold"). -/
def AggCall (P : Params) (S : State Ω C) {Ω' C' : Type} (m : Mode) (T : State Ω' C') : Prop :=
  (m = .solve ∧ (T.size : ℝ) ≤ (S.N : ℝ) ^ (2 * P.α)) ∨
    (m = .cont ∧ ∃ e : Ω' = Ω, ChargedCall P S (e ▸ T))

/-- The cap update of a configuration or rectangle continuation (Section 5.1, "`H`
then shrinks the hierarchy cap from at least `q` to `βq`"; Algorithm 3,
`LiftAndContinue`: the selected interval bound becomes `min{c, βq}`; Section 7.2: "A
configuration or rectangle answer changes the selected interval bound from at least
`q` to at most `βq`. … The old cap is at least `q` because the selected alternating
section belongs to that whole constituent"). The selected interval `i` of the parent
hierarchy `l` has cap at least `q` and, being clamped (Section 3.3: "every stored bound
is at most its current interval ratio"), ratio at least its cap. The new hierarchy
`l'` is `l` with that cap replaced by `min{c, ⌊βq⌋}`. -/
def CapUpdate (P : Params) (l : List (Interval Ω)) (q : ℕ) (l' : List (Interval Ω)) : Prop :=
  ∃ i : Fin l.length, q ≤ l[i].cap ∧ l[i].cap ≤ l[i].ratio ∧
    l' = l.set i { l[i] with cap := min l[i].cap ⌊P.β * q⌋₊ }

/-! The interface `Aggregation` of an aggregation round is in
`Workspace/Algorithm/Aggregation.lean`: its script is computed from the structural data of
the paper's aggregation step. -/

end GI.Algorithm
