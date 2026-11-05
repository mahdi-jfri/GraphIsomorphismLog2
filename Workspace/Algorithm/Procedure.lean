module

public import Workspace.Algorithm.Aggregation
public import Workspace.Algorithm.Dispatch
public import Workspace.Algorithm.RowSteps
public import Workspace.Algorithm.FreshState
public import Workspace.Algorithm.NormLabels

@[expose] public section

/-!
# The phase recursion of Section 6, as an abstract procedure

`Run P m S L A` is a run of the procedure `m` (`Solve`, `Continue` or `GiantStep`) on
the state `S` with the labels `L` of the call, returning the set `A`. A `GiantStep` call
carries its supplied alternating labels (`L = some Γ`, Algorithm 4: "for the supplied
alternating label set"); `Solve` and `Continue` carry none. It is a finite tree: each constructor is one
case of Algorithms 4 and 5 (the paper's `alg:row-step` and `alg:main-recursion`),
and its arguments are the recursive runs that the case makes. `Exec P s a` is a run
of a query script `s` with result `a`: every question of the script is answered by
a recursive run.

The constructors follow the pseudocode line by line.

`Solve(Ω, G, x, y)`:
* `direct`: "if `|Ω| ≤ N_0` then return the answer by direct enumeration";
* `fresh`: "Use the faithful action and jointly compressed colors on `Ω`. … Set
  `N ← |Ω|`, `λ ← N^α`, and `h ← 2`. Initialize each original orbit's hierarchy and
  interval bounds. Return `Continue(S)`". The new state lives on the active domain, with
  the faithful image `G|_dom` and an initial tower (`State.FreshOf`,
  `Workspace/Algorithm/FreshState.lean`); its answer is lifted back to `Ω`
  (`State.liftAnswer`).

`Continue(S)`:
* `threshold`: "if `|Ω| ≤ N^γ` then return `Solve(Ω, G, x, y)`";
* `orbitStop`, `orbitChain`: "if `G` is intransitive then return the inherited
  orbit-chain answer" (Section 3.2: a largest orbit first; its answer `t H` is
  absorbed into the target coloring and the rest continues under `H`);
* `floorReset`: "if the active column floor has been entered then clear the row
  record and floor mode; set `h ← 2`", then the general dispatcher on the same core;
* `dispatch`: "if enumeration or a product refinement applies then apply that
  reduction and solve its children with `Continue`; return their exact combined
  answer";
* `normalize`: "Normalize the single alternating factor, with at most two cosets.
  If the normalized group is intransitive then return the combined inherited
  orbit-chain answers for these cosets. Run `GiantStep` immediately in each coset,
  absorbing its representative. Return the exact combination of these answers". The step
  carries the dispatcher's primitive quotient `Q`, which lies above the retained columns and
  fails the integer small test and is a single factor (so the dispatcher found no enumeration;
  the product case cannot also hold at a single factor of degree above `q₀`, so the
  normalization does not test the product case), and the normalization is the one of `Q` (`PrimitiveQuotient.normAboveOf`) for any
  choice of a product structure with one coordinate and of coset representatives
  (`PrimitiveQuotient.NormChoice`). The
  `GiantStep` children are called with the labels of the normalized factor
  (`NormAbove.childLabels`).

`GiantStep(S, Γ)`:
* `rowTerminal`, `rowColumns`: "if `q > λ` … if this map is natural and (no rows are
  retained, or `q` exceeds their degree) then return `RowStep(S, Γ)`", with the two
  branches of `RowStep` (Algorithm 4): the row terminal, or the column partition
  followed by `Continue(S)` in the same phase;
* `aggregate`: the certificate, aggregation and auxiliary-graph path, then
  `LiftAndContinue` on each overcoset and `CombineExact`.

The three constructors of `GiantStep` work on the labels of the call, so the labels of a
giant node are always those of the normalization that called it.

The constructors force the core `(G, dom, x, y)` of each child and the bookkeeping
that the pseudocode states:

* the phase size `N` of every inherited child (Section 6: "All state changes in
  `Continue` retain the phase size `N`");
* the counter updates of `fresh`, `floorReset` and `RowStep` (`h ← 2`, `h ← h - 1`,
  where `RowStep` needs `h ≥ 1`: "A counter `h ∈ {0,1,2}`", and "The one-promotion
  argument ensures that it never becomes negative", Section 7.1); a normalization
  keeps `h` ("A cap contraction or a coordinate change alone does not reset `h`");
* the hierarchy of each child: inherited unchanged by orbit-chain calls and the
  normalization ("Every later call inherits the state of the original orbit
  containing it"), the refined hierarchy `I.hier'` of a dispatcher reduction ("a
  product reduction refines the stored intervals") and of the column step ("Refactor
  the old hierarchy by splitting and reordering its interval factors"), and the cap
  update `min{c, βq}` of `LiftAndContinue` (`Aggregation.newHier`);
* a giant step on `q` labels has `q ≥ q₀` (Section 6: "An enumerative reduction
  includes the bounded alternating-degree cases").

* the bookkeeping (row record, floor mode, `h`) of the orbit-chain children: the first child
  keeps it exactly when the retained columns split its orbit (`State.orbitBook`, which is
  `State.inherit` under the state invariants, `State.inherit_book`), and the second child
  resets it;
* the bookkeeping of the continuations of an aggregation round: kept (`Aggregation.overs_keep`);
* the bookkeeping of the dispatcher's children: kept (`hbk`), and their hierarchy, with its
  origin labels, is the refined hierarchy `I.hier'`.

## Deferred to stage 2

The machine clauses: generators and representatives instead of sets, the joint color
compression at fresh calls (its mathematical content is `GI.Algorithm.answer_recolor`), and
the polynomial bounds on the structural work.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm
open scoped Pointwise

/-- The labels that a call in mode `m` passes down: the supplied alternating labels `L` for
`GiantStep` (Algorithm 5, `GiantStep(S, Γ)`: "for the supplied alternating label set"), and
none for `Solve` and `Continue`. -/
def Mode.labels {Ω C : Type} {T : State Ω C} : Mode → SuppliedLabels T → Option (SuppliedLabels T)
  | .giant, L => some L
  | _, _ => none

/-- The child of a normalization on the coset `τ_j G'`: the normalized group `G'` on the parent
domain, with the colorings `(x, y ∘ τ_j)` and the exposed hierarchy `I.hier'`. The phase, the
counter, the row record and the floor mode are kept, since the normalized group keeps the
carrier of the retained rows (`State.restrict`, `NormAbove.keeps`). -/
noncomputable def NormAbove.child {P : Params} {Ω C : Type} {S : State Ω C} (N : NormAbove P S)
    (j : Fin N.I.k) : State Ω C :=
  S.restrict N.I.G' N.I.le S.x (S.y ∘ N.I.τ j) N.I.hier'

/-- The supplied labels of the child of a normalization on the coset `τ_j G'`: the labels
`π : G' ↠ Alt(q)` of the normalized factor, with their constituent data. -/
noncomputable def NormAbove.childLabels {P : Params} {Ω C : Type} {S : State Ω C} (N : NormAbove P S)
    (j : Fin N.I.k) : SuppliedLabels (N.child j) :=
  N.labels S.x (S.y ∘ N.I.τ j)

-- The injectivity theorems of the constructors are not generated: no proof uses them, and
-- generating them for `aggregate` takes very long.
set_option genInjectivity false in
mutual

/-- **The phase recursion** (Algorithms 4 and 5). `Run P m S L A`: the procedure `m`
on the state `S` returns `A`. The index `L` is the label set passed with the call: the
supplied alternating labels for `GiantStep`, and `none` for `Solve` and `Continue`. -/
inductive Run (P : Params) : Mode → {Ω C : Type} → (S : State Ω C) →
    Option (SuppliedLabels S) → Set (Perm Ω) → Type 1
  /-- `Solve`: direct enumeration below `N_0`. -/
  | direct {Ω C : Type} (S : State Ω C) (hs : S.size ≤ P.N₀) :
      Run P .solve S none S.answer
  /-- `Solve`: start a fresh phase on the faithful image `G|_dom`, on the type of the
  active domain, with `N = |dom|`, `h = 2`, no row record, and an initial tower with bounds
  `c_i = d_i` (`State.FreshOf`); call `Continue` and lift its answer to `Ω`. -/
  | fresh {Ω C : Type} {S : State Ω C} {S' : State S.dom C} {A : Set (Perm S.dom)}
      (hs : P.N₀ < S.size) (hS' : S.FreshOf S') (r : Run P .cont S' none A) :
      Run P .solve S none (S.liftAnswer A)
  /-- `Continue`: at or below the phase threshold, call `Solve`. -/
  | threshold {Ω C : Type} {S : State Ω C} {A : Set (Perm Ω)}
      (hs : (S.size : ℝ) ≤ (S.N : ℝ) ^ P.γ) (r : Run P .solve S none A) :
      Run P .cont S none A
  /-- `Continue`, intransitive: the largest orbit `D₁` has no isomorphism. The child keeps the
  row record, the floor mode and `h` exactly when the retained columns split `D₁`
  (`State.orbitBook`; this is what `State.inherit` gives, `State.inherit_book`). -/
  | orbitStop {Ω C : Type} {S S₁ : State Ω C} {D₁ : Set Ω}
      (hs : (S.N : ℝ) ^ P.γ < S.size) (hint : ¬ S.Transitive) (hD₁ : S.LargestOrbit D₁)
      (h₁ : S₁.Inst S.G D₁ S.x S.y) (hN₁ : S₁.N = S.N)
      (hhier₁ : S₁.hier = S.hier) (hb₁ : S₁.book = S.orbitBook D₁)
      (r₁ : Run P .cont S₁ none ∅) : Run P .cont S none ∅
  /-- `Continue`, intransitive: the orbit chain rule. The largest orbit `D₁` returns
  `A₁`; for `t ∈ A₁` the rest of the domain continues under
  `H = Aut_G(x on D₁)` on `(x, y ∘ t)`, and the answer is `t A₂`. The first child keeps the
  bookkeeping as in `orbitStop`; the second child, in a later original orbit, resets it
  (Section 6.1: "later conditional queries lie in other original orbits of size at most half the
  parent domain and may clear and reset there"). -/
  | orbitChain {Ω C : Type} {S S₁ S₂ : State Ω C} {D₁ : Set Ω} {A₁ A₂ : Set (Perm Ω)}
      (hs : (S.N : ℝ) ^ P.γ < S.size) (hint : ¬ S.Transitive) (hD₁ : S.LargestOrbit D₁)
      (h₁ : S₁.Inst S.G D₁ S.x S.y) (hN₁ : S₁.N = S.N) (hhier₁ : S₁.hier = S.hier)
      (hb₁ : S₁.book = S.orbitBook D₁)
      (r₁ : Run P .cont S₁ none A₁) (t : Perm Ω) (ht : t ∈ A₁)
      (h₂ : S₂.Inst (autGroup S.G D₁ hD₁.invariant S.x) (S.dom \ D₁) S.x (S.y ∘ t))
      (hN₂ : S₂.N = S.N) (hhier₂ : S₂.hier = S.hier) (hb₂ : S₂.book = State.resetBook)
      (r₂ : Run P .cont S₂ none A₂) : Run P .cont S none (t • A₂)
  /-- `Continue`: at a column floor, clear the row record and the floor mode and set
  `h = 2`, then use the general dispatcher on the same state. -/
  | floorReset {Ω C : Type} {S S' : State Ω C} {A : Set (Perm Ω)}
      (hs : (S.N : ℝ) ^ P.γ < S.size) (htr : S.Transitive) (hfl : S.FloorEntered)
      (hcore : S.SameCore S') (hrows : S'.rows = none) (hfloor : S'.floor = false)
      (hh : S'.h = 2) (hN : S'.N = S.N) (hhier : S'.hier = S.hier)
      (r : Run P .cont S' none A) : Run P .cont S none A
  /-- `Continue`: an enumeration or product reduction, with children `Continue`
  under `K` on the cosets `τ_j K`. The step `I` carries the primitive quotient of the state,
  and `K`, `τ_j` and the children's hierarchy are computed from it (`DispatchStep`,
  `Workspace/Algorithm/Dispatch.lean`). The children keep the row record, the floor mode and
  `h` (`hbk`): the child group keeps the carrier of the retained rows (`DispatchStep.keeps`; Section
  A.4: "use full preimages of all quotient restrictions. This keeps the entire kernel `J`"). -/
  | dispatch {Ω C : Type} {S : State Ω C}
      (hs : (S.N : ℝ) ^ P.γ < S.size) (htr : S.Transitive) (hfl : ¬ S.FloorEntered)
      (I : DispatchStep P S) (child : Fin I.n → State Ω C)
      (hchild : ∀ j, (child j).Inst I.K S.dom S.x (S.y ∘ I.τ j))
      (hN : ∀ j, (child j).N = S.N) (hhier : ∀ j, (child j).hier = I.hier')
      (hbk : ∀ j, (child j).book = S.book)
      (A : Fin I.n → Set (Perm Ω)) (r : ∀ j, Run P .cont (child j) none (A j)) :
      Run P .cont S none (⋃ j, I.τ j • A j)
  /-- `Continue`: the single-factor normalization. The dispatcher's primitive quotient `Q` fails
  the integer small test `SmallZ` (which implies the real test `Small`, so a program can decide
  it) and is a single factor through the choice `c` (Algorithm 5: "Normalize the single alternating factor, with at most two cosets"), and the
  normalization is the one of `Q` (`PrimitiveQuotient.normAbove`). Each of the at most two
  cosets `τ_j G'` continues under `G'` on `(x, y ∘ τ_j)` (`NormAbove.child`): by the orbit chain
  if `G'` is intransitive (mode `cont`), and by `GiantStep` on the labels of the normalized
  factor otherwise (mode `giant`, `NormAbove.childLabels`). -/
  | normalize {Ω C : Type} {hfin : Finite Ω} {S : State Ω C}
      (hs : (S.N : ℝ) ^ P.γ < S.size) (htr : S.Transitive) (hfl : ¬ S.FloorEntered)
      (Q : PrimitiveQuotient S) (hsm : ¬ Q.SmallZ P.smallExp)
      (c : Q.NormChoice) (hq : P.q₀ < (Q.normalizationOf c).q)
      (hkc : Q.KillsCols) (hkl : Q.KeepsLevels)
      (N : NormAbove P S) (hN : N = Q.normAboveOf c htr hq hkc hkl) (m : Mode)
      (hmode : ∀ j, (m = .cont ∧ ¬ (N.child j).Transitive) ∨
        (m = .giant ∧ (N.child j).Transitive))
      (A : Fin N.I.k → Set (Perm Ω))
      (r : ∀ j, Run P m (N.child j) (m.labels (N.childLabels j)) (A j)) :
      Run P .cont S none (⋃ j, N.I.τ j • A j)
  /-- `GiantStep` → `RowStep`, transitive within-row variation: the row terminal, on the
  supplied labels `L`. -/
  | rowTerminal {Ω C : Type} {S : State Ω C} {A : Set (Perm Ω)}
      (hs : (S.N : ℝ) ^ P.γ < S.size) (htr : S.Transitive)
      (L : SuppliedLabels S) (hrow : RowCase P.α S L.toGiantLabels)
      (I : RowTerminal P S L.toGiantLabels) (e : Exec P I.script A) : Run P .giant S (some L) A
  /-- `GiantStep` → `RowStep`, intransitive within-row variation, on the supplied labels `L`:
  retain the row action of degree `q` and the column partition, set `h ← h - 1`, and continue
  in the same phase. The child stores the refactored hierarchy without its trivial pieces
  (`dropTriv`; Section 7.1: "Only nontrivial interval ratios occur"). -/
  | rowColumns {Ω C : Type} {S S' : State Ω C} {A : Set (Perm Ω)}
      (hs : (S.N : ℝ) ^ P.γ < S.size) (htr : S.Transitive)
      (L : SuppliedLabels S) (hrow : RowCase P.α S L.toGiantLabels)
      (I : ColumnStep S L.toGiantLabels)
      (hcore : S.SameCore S') (hR : S'.rows = some ⟨L.q, I.rowPart, some I.cols⟩)
      (hh1 : 1 ≤ S.h) (hh : S'.h = S.h - 1) (hN : S'.N = S.N) (hhier : S'.hier = dropTriv I.hier')
      (r : Run P .cont S' none A) : Run P .giant S (some L) A
  /-- `GiantStep`, aggregation path, on the supplied labels `L`: run the certificate and
  auxiliary script, then `LiftAndContinue` on each overcoset `ρ_j H_j` (continue under `H_j` on
  `(x, y ∘ τ_j)` and multiply by `τ_j`), and `CombineExact` (the union). The round selects the
  interval and uses the constituent data that the labels carry (Section 7.2: "the selected
  alternating section belongs to that whole constituent").

  The representative `τ_j` is any element of the overcoset `ρ_j H_j` (`LiftAndContinue`: "lifts
  `E` to a coset `Hτ` in the original parent action"; the coset, not its representative, is what
  the paper fixes). The children keep the row record, the floor mode and `h` (Section 6: "A cap
  contraction or a coordinate change alone does not reset `h`"; Section A.4: "use full preimages
  of all quotient restrictions. This keeps the entire kernel `J`"): the continuation groups
  `π⁻¹(E₀)` keep the carrier of the retained rows (`Aggregation.overs_keep`). -/
  | aggregate {Ω C : Type} {S : State Ω C}
      (hs : (S.N : ℝ) ^ P.γ < S.size) (htr : S.Transitive)
      (L : SuppliedLabels S) (hnot : ¬ RowCase P.α S L.toGiantLabels) (hq₀ : P.q₀ ≤ L.q)
      (I : Aggregation P S L.toGiantLabels) (hsel : I.sel.val = L.sel.val) (hcon : I.con = L.con)
      (b : Branches Ω) (e : Exec P I.script b)
      (τ : Fin b.overs.length → Perm Ω)
      (hτ : ∀ j, τ j ∈ (b.overs.get j).1 • ((b.overs.get j).2 : Set (Perm Ω)))
      (child : Fin b.overs.length → State Ω C)
      (hchild : ∀ j, (child j).Inst (b.overs.get j).2 S.dom S.x (S.y ∘ τ j))
      (hN : ∀ j, (child j).N = S.N) (hhier : ∀ j, (child j).hier = I.newHier (b.overs.get j))
      (hbk : ∀ j, (child j).book = S.book)
      (A : Fin b.overs.length → Set (Perm Ω)) (r : ∀ j, Run P .cont (child j) none (A j)) :
      Run P .giant S (some L) ((⋃ p ∈ b.pieces, p) ∪ ⋃ j, τ j • A j)

/-- A run of a query script: each question is answered by a recursive run of `Solve` or
`Continue`, which takes no labels. -/
inductive Exec (P : Params) : {α : Type} → Script α → α → Type 1
  | done {α : Type} (a : α) : Exec P (Script.done a) a
  | ask {α : Type} {Ω' C' : Type} {m : Mode} {S : State Ω' C'}
      {k : Set (Perm Ω') → Script α} {A : Set (Perm Ω')} {a : α}
      (r : Run P m S none A) (e : Exec P (k A) a) : Exec P (Script.ask m S k) a

end

end GI.Algorithm
