module

public import Workspace.Algorithm.PhaseTree
public import Workspace.Paper.RunningTime

@[expose] public section

/-!
# The total cost of a run (Section 7.4)

A run `r : GI.Algorithm.Run P m S L A` is a finite tree of recursive calls. Stage 2 will
charge each call some work for what it does itself: computing orbits, building the
children's states, combining answers. This work is a function `w : Node P → ℝ` on the
nodes of the tree. The **total cost** of a run is the sum of `w` over all its nodes
(`Run.total`): the node itself, its inherited children, its fresh `Solve` calls, and the
calls of its query scripts, each with all of its own descendants.

The phase structure of Section 7 is part of the tree: a fresh call is a `Solve` node,
and its `fresh` child starts a new phase with `N = |Ω|` and `h = 2`.

## The per-node hypothesis

`NodeBound w cw af` is what the running-time analysis assumes about `w`, in the form of
Section 7.4 ("After increasing `a`, all structural work and all fresh configuration or
row calls at one node have total cost at most `N^a K_N`"):

* the work of a node of a phase with phase size `N` (and at most `N` positions) is at
  most `E_N = exp(cw (log(N+2))²)` (the structural work is polynomial in `N`, and the
  row terminal's extra work is `exp(O((log N)²))`, Section 7.4); a `Solve` node on
  `s` positions does at most `exp(cw (log(s+2))²)` work;
* a node of a phase with phase size `N` makes at most `N^{af}` calls from its query
  scripts (the certificate, configuration and row calls).

The rest of the toll is proved, not assumed: the fresh calls of a node have at most
`⌈N^γ⌉` positions (Section 7.4: "Every fresh leaf has at most `N^γ` positions",
"An auxiliary configuration contributes at most `N^{2α}` positions. A transitive-variation
row terminal calls only on rows of size at most `N^{1-α}`"), so each costs at most
`F(⌈N^γ⌉)`.

## Phase roots

The potential of a phase root must be `O((log N)²)` (proof of Lemma 7.1: "At a phase
root, `ρ = O(log N)`, `σ = O(log(N+2))`, `Q ≤ (log N)²`, and `h ≤ 2`"). `Run.RootsOK cσ r`
says that every fresh phase of `r` starts on a finite position type with these root bounds
(`GI.Paper.RootBounds`). It holds for every run (`GI.Algorithm.Run.rootsOK_all`,
`Workspace/Paper/RootBounds.lean`): a fresh call uses the faithful image on its active domain
(Section 3, then Theorem A.9 bounds `σ`) and initializes a tower of invariant partitions
(`State.FreshOf`; then `ρ` and `Q` are bounded by eq. `main-rho` and eq. `main-Q`).

## The worst-case cost

`worstCost w cσ N` is the paper's `F(N)` ("the monotone worst-case cost for compressed
fresh inputs"): the supremum of the total costs of the runs of `Solve` with
`Run.RootsOK` on at most `N` positions.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm
open scoped Pointwise

variable {P : Params}

/-! ### The node of a run -/

/-- The node of the recursion tree at the root of a run. -/
def Run.node {m : Mode} {Ω C : Type} {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)} (r : Run P m S L A) :
    Node P := ⟨m, Ω, C, S, L, A, r⟩

/-! ### Total cost -/

/-- **The total cost** of a run: the sum of the work `w` over all nodes of its tree. -/
noncomputable def Run.total (w : Node P → ℝ) {m : Mode} {Ω C : Type} {S : State Ω C}
    {L : Option (SuppliedLabels S)}
    {A : Set (Perm Ω)} (r : Run P m S L A) : ℝ :=
  (Run.rec (motive_1 := fun m {Ω' C'} (S : State Ω' C') L A _ => Run P m S L A → ℝ)
    (motive_2 := fun _ _ _ => ULift.{1} ℝ)
    (direct := fun _ _ self => w self.node)
    (fresh := fun _ _ r ih self => w self.node + ih r)
    (threshold := fun _ r ih self => w self.node + ih r)
    (orbitStop := fun _ _ _ _ _ _ _ r₁ ih₁ self => w self.node + ih₁ r₁)
    (orbitChain := fun _ _ _ _ _ _ _ r₁ _ _ _ _ _ _ r₂ ih₁ ih₂ self =>
      w self.node + ih₁ r₁ + ih₂ r₂)
    (floorReset := fun _ _ _ _ _ _ _ _ _ r ih self => w self.node + ih r)
    (dispatch := fun _ _ _ _ _ _ _ _ _ _ r ih self => w self.node + ∑ j, ih j (r j))
    (normalize := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ r ih self => w self.node + ∑ j, ih j (r j))
    (rowTerminal := fun _ _ _ _ _ _ ih self => w self.node + ih.down)
    (rowColumns := fun _ _ _ _ _ _ _ _ _ _ _ r ih self => w self.node + ih r)
    (aggregate := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r ihe ih self =>
      w self.node + ihe.down + ∑ j, ih j (r j))
    (done := fun _ => ⟨0⟩)
    (ask := fun r _ ihr ihe => ⟨ihr r + ihe.down⟩)
    r) r

/-- The total cost of the calls of a script run. -/
noncomputable def Exec.total (w : Node P → ℝ) {α : Type} {s : Script α} {a : α}
    (e : Exec P s a) : ℝ :=
  (Exec.rec (motive_1 := fun m {Ω' C'} (S : State Ω' C') L A _ => Run P m S L A → ℝ)
    (motive_2 := fun _ _ _ => ULift.{1} ℝ)
    (direct := fun _ _ self => w self.node)
    (fresh := fun _ _ r ih self => w self.node + ih r)
    (threshold := fun _ r ih self => w self.node + ih r)
    (orbitStop := fun _ _ _ _ _ _ _ r₁ ih₁ self => w self.node + ih₁ r₁)
    (orbitChain := fun _ _ _ _ _ _ _ r₁ _ _ _ _ _ _ r₂ ih₁ ih₂ self =>
      w self.node + ih₁ r₁ + ih₂ r₂)
    (floorReset := fun _ _ _ _ _ _ _ _ _ r ih self => w self.node + ih r)
    (dispatch := fun _ _ _ _ _ _ _ _ _ _ r ih self => w self.node + ∑ j, ih j (r j))
    (normalize := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ r ih self => w self.node + ∑ j, ih j (r j))
    (rowTerminal := fun _ _ _ _ _ _ ih self => w self.node + ih.down)
    (rowColumns := fun _ _ _ _ _ _ _ _ _ _ _ r ih self => w self.node + ih r)
    (aggregate := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r ihe ih self =>
      w self.node + ihe.down + ∑ j, ih j (r j))
    (done := fun _ => ⟨0⟩)
    (ask := fun r _ ihr ihe => ⟨ihr r + ihe.down⟩)
    e).down

section Equations

variable (w : Node P → ℝ) {Ω C : Type}

theorem Exec.total_done {α : Type} (a : α) : (Exec.done (P := P) a).total w = 0 := rfl

theorem Exec.total_ask {α : Type} {Ω' C' : Type} {m : Mode} {S : State Ω' C'}
    {k : Set (Perm Ω') → Script α} {A : Set (Perm Ω')} {a : α}
    (r : Run P m S none A) (e : Exec P (k A) a) :
    (Exec.ask r e).total w = r.total w + e.total w := rfl

/-- The total cost of a script run is the sum of the total costs of its calls. -/
theorem Exec.total_eq_calls {α : Type} {s : Script α} {a : α} (e : Exec P s a) :
    e.total w = (e.calls.map fun nd => nd.run.total w).sum := by
  refine Exec.rec (motive_1 := fun _ {_ _} _ _ _ _ => True)
    (motive_2 := fun _ _ e => e.total w = (e.calls.map fun nd => nd.run.total w).sum)
    (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (fun _ => rfl) ?_ e
  intro α Ω' C' m S k A a r e' _ ih
  rw [Exec.total_ask, ih]
  rfl

theorem Run.total_direct (S : State Ω C) (hs : S.size ≤ P.N₀) :
    (Run.direct (P := P) S hs).total w = w (Run.direct S hs).node := rfl

theorem Run.total_fresh {S : State Ω C} {S' : State S.dom C} {A : Set (Perm S.dom)}
    (hs : P.N₀ < S.size) (hS' : S.FreshOf S') (r : Run P .cont S' none A) :
    (Run.fresh hs hS' r).total w = w (Run.fresh hs hS' r).node + r.total w := rfl

theorem Run.total_threshold {S : State Ω C} {A : Set (Perm Ω)}
    (hs : (S.size : ℝ) ≤ (S.N : ℝ) ^ P.γ) (r : Run P .solve S none A) :
    (Run.threshold hs r).total w = w (Run.threshold hs r).node + r.total w := rfl

/-- **The total cost is the sum over the nodes**: the work of the root plus the total
costs of its immediate recursive runs (`Run.children`). -/
theorem Run.total_eq {m : Mode} {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)} (r : Run P m S L A) :
    r.total w = w r.node + (r.children.map fun nd => nd.run.total w).sum := by
  cases r with
  | direct => simp [Run.total, Run.children, Run.node]
  | fresh => simp [Run.children]; rfl
  | threshold => simp [Run.children]; rfl
  | orbitStop => simp [Run.children]; rfl
  | orbitChain => simp [Run.children]; rw [← add_assoc]; rfl
  | floorReset => simp [Run.children]; rfl
  | dispatch => simp [Run.children, List.sum_ofFn]; rfl
  | normalize => simp [Run.children, List.sum_ofFn]; rfl
  | rowTerminal _ _ _ _ _ e =>
    simp only [Run.children]
    rw [← Exec.total_eq_calls]
    rfl
  | rowColumns => simp [Run.children]; rfl
  | aggregate _ _ _ _ _ _ _ _ _ e =>
    simp only [Run.children, List.map_append, List.sum_append, List.map_ofFn, List.sum_ofFn]
    rw [← Exec.total_eq_calls, ← add_assoc]
    rfl

end Equations

/-- With nonnegative work, the total cost is nonnegative. -/
theorem Run.total_nonneg {w : Node P → ℝ} (hw : ∀ nd, 0 ≤ w nd) {m : Mode} {Ω C : Type}
    {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)} (r : Run P m S L A) : 0 ≤ r.total w := by
  refine Run.rec (motive_1 := fun _ {_ _} _ _ _ r => 0 ≤ r.total w)
    (motive_2 := fun _ _ e => 0 ≤ e.total w) ?direct ?fresh ?threshold ?orbitStop
    ?orbitChain ?floorReset ?dispatch ?normalize ?rowTerminal ?rowColumns ?aggregate
    ?done ?ask r
  case direct => intros; exact hw _
  case fresh => intros; exact add_nonneg (hw _) (by assumption)
  case threshold => intros; exact add_nonneg (hw _) (by assumption)
  case orbitStop => intros; exact add_nonneg (hw _) (by assumption)
  case orbitChain => intros; refine add_nonneg (add_nonneg (hw _) ?_) ?_ <;> assumption
  case floorReset => intros; exact add_nonneg (hw _) (by assumption)
  case dispatch =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih
    exact add_nonneg (hw _) (Finset.sum_nonneg fun j _ => ih j)
  case normalize =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih
    exact add_nonneg (hw _) (Finset.sum_nonneg fun j _ => ih j)
  case rowTerminal => intros; exact add_nonneg (hw _) (by assumption)
  case rowColumns => intros; exact add_nonneg (hw _) (by assumption)
  case aggregate =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihe ih
    exact add_nonneg (add_nonneg (hw _) ihe) (Finset.sum_nonneg fun j _ => ih j)
  case done => intros; exact le_refl _
  case ask => intros; refine add_nonneg ?_ ?_ <;> assumption

theorem Exec.total_nonneg {w : Node P → ℝ} (hw : ∀ nd, 0 ≤ w nd) {α : Type} {s : Script α}
    {a : α} (e : Exec P s a) : 0 ≤ e.total w := by
  rw [Exec.total_eq_calls]
  exact List.sum_nonneg fun x hx => by
    obtain ⟨nd, -, rfl⟩ := List.mem_map.1 hx
    exact nd.run.total_nonneg hw

/-! ### Phase roots -/

/-- **Every fresh phase of the run has root bounds**: at each `fresh` node, the position
type is finite and the new state `S'` (phase size `N = |Ω|`, `h = 2`) satisfies
`GI.Paper.RootBounds cσ N` (proof of Lemma 7.1: "At a phase root, `ρ = O(log N)`,
`σ = O(log(N+2))`, `Q ≤ (log N)²`, and `h ≤ 2`"). -/
def Run.RootsOK (cσ : ℝ) {m : Mode} {Ω C : Type} {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)}
    (r : Run P m S L A) : Prop :=
  Run.rec (motive_1 := fun _ {_ _} _ _ _ _ => Prop) (motive_2 := fun _ _ _ => Prop)
    (direct := fun _ _ => True)
    (fresh := @fun _ _ S S' _ _ _ _ ih =>
      Finite S.dom ∧ GI.Paper.RootBounds cσ S'.N (S'.res P.κ) ∧ ih)
    (threshold := fun _ _ ih => ih)
    (orbitStop := fun _ _ _ _ _ _ _ _ ih => ih)
    (orbitChain := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ => ih₁ ∧ ih₂)
    (floorReset := fun _ _ _ _ _ _ _ _ _ _ ih => ih)
    (dispatch := fun _ _ _ _ _ _ _ _ _ _ _ ih => ∀ j, ih j)
    (normalize := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => ∀ j, ih j)
    (rowTerminal := fun _ _ _ _ _ _ ih => ih)
    (rowColumns := fun _ _ _ _ _ _ _ _ _ _ _ _ ih => ih)
    (aggregate := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihe ih => ihe ∧ ∀ j, ih j)
    (done := fun _ => True)
    (ask := fun _ _ ihr ihe => ihr ∧ ihe)
    r

/-- Every call of a script run has root bounds. -/
def Exec.RootsOK (cσ : ℝ) {α : Type} {s : Script α} {a : α} (e : Exec P s a) : Prop :=
  Exec.rec (motive_1 := fun _ {_ _} _ _ _ _ => Prop) (motive_2 := fun _ _ _ => Prop)
    (direct := fun _ _ => True)
    (fresh := @fun _ _ S S' _ _ _ _ ih =>
      Finite S.dom ∧ GI.Paper.RootBounds cσ S'.N (S'.res P.κ) ∧ ih)
    (threshold := fun _ _ ih => ih)
    (orbitStop := fun _ _ _ _ _ _ _ _ ih => ih)
    (orbitChain := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ => ih₁ ∧ ih₂)
    (floorReset := fun _ _ _ _ _ _ _ _ _ _ ih => ih)
    (dispatch := fun _ _ _ _ _ _ _ _ _ _ _ ih => ∀ j, ih j)
    (normalize := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => ∀ j, ih j)
    (rowTerminal := fun _ _ _ _ _ _ ih => ih)
    (rowColumns := fun _ _ _ _ _ _ _ _ _ _ _ _ ih => ih)
    (aggregate := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihe ih => ihe ∧ ∀ j, ih j)
    (done := fun _ => True)
    (ask := fun _ _ ihr ihe => ihr ∧ ihe)
    e

/-- The calls of a script run with root bounds have root bounds. -/
theorem Exec.rootsOK_calls {cσ : ℝ} {α : Type} {s : Script α} {a : α} (e : Exec P s a)
    (h : e.RootsOK cσ) : ∀ nd ∈ e.calls, nd.run.RootsOK cσ := by
  revert h
  refine Exec.rec (motive_1 := fun _ {_ _} _ _ _ _ => True)
    (motive_2 := fun _ _ e => e.RootsOK cσ → ∀ nd ∈ e.calls, nd.run.RootsOK cσ)
    (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (fun _ _ nd hnd => by simp [Exec.calls] at hnd) ?_ e
  intro α Ω' C' m S k A a r e' _ ih h nd hnd
  change nd ∈ (⟨m, Ω', C', S, none, A, r⟩ : Node P) :: e'.calls at hnd
  rcases List.mem_cons.1 hnd with rfl | hnd
  · exact h.1
  · exact ih h.2 nd hnd

/-! ### The calls of the query scripts -/

/-- The calls of the query scripts of a node: the row terminal's and the aggregation
round's (certificate, configuration and row calls, and the inherited charged calls). -/
noncomputable def Run.scriptCalls {m : Mode} {Ω C : Type} {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)} :
    Run P m S L A → List (Node P)
  | .rowTerminal _ _ _ _ _ e => e.calls
  | .aggregate _ _ _ _ _ _ _ _ _ e .. => e.calls
  | _ => []

/-! ### The per-node hypothesis -/

/-- `E = exp(c (log(n+2))²)`, the shape of every bound in Section 7. -/
noncomputable def expLogSq (c : ℝ) (n : ℕ) : ℝ := Real.exp (c * Real.log ((n : ℝ) + 2) ^ 2)

/-- **The per-node hypothesis** (Section 7.4), on the work `w` of the nodes:

* `work`: a node of a phase with phase size `N`, on at most `N` positions, does at most
  `E_N = exp(cw (log(N+2))²)` work itself ("all structural work … at one node";
  "The terminal's additional work is `exp(O((log N)²))`");
* `solve`: a `Solve` node on `s` positions does at most `exp(cw (log(s+2))²)` work itself
  (reading the input, the direct enumeration below `N₀`, the initialization of a
  fresh phase);
* `calls`: such a node makes at most `N^{af}` calls from its query scripts.

The costs of the recursive calls are not part of a node's work: they are the total
costs of the children. -/
structure NodeBound (w : Node P → ℝ) (cw af : ℝ) : Prop where
  nonneg : ∀ nd, 0 ≤ w nd
  work : ∀ nd : Node P, nd.m ≠ .solve → nd.S.size ≤ nd.S.N → w nd ≤ expLogSq cw nd.S.N
  solve : ∀ nd : Node P, nd.m = .solve → w nd ≤ expLogSq cw nd.S.size
  calls : ∀ nd : Node P, nd.m ≠ .solve → nd.S.size ≤ nd.S.N →
    (nd.run.scriptCalls.length : ℝ) ≤ (nd.S.N : ℝ) ^ af

/-! ### The worst-case cost `F` -/

/-- The total costs of the runs of `Solve` with root bounds on at most `n` positions. -/
def costSet (w : Node P → ℝ) (cσ : ℝ) (n : ℕ) : Set ℝ :=
  {c | ∃ (Ω C : Type) (S : State Ω C) (L : Option (SuppliedLabels S)) (A : Set (Perm Ω))
    (r : Run P .solve S L A),
    S.size ≤ n ∧ r.RootsOK cσ ∧ r.total w = c}

/-- **The worst-case cost** `F(n)` (Section 7.4: "Let `F` be the monotone worst-case
cost for compressed fresh inputs"): the supremum of the total costs of the runs of
`Solve` with root bounds on at most `n` positions. (A supremum of an unbounded set is
`0` in Lean; the boundedness is proved along the recurrence, `costSet_bddAbove`.) -/
noncomputable def worstCost (w : Node P → ℝ) (cσ : ℝ) (n : ℕ) : ℝ := sSup (costSet w cσ n)

theorem worstCost_nonneg {w : Node P → ℝ} (hw : ∀ nd, 0 ≤ w nd) (cσ : ℝ) (n : ℕ) :
    0 ≤ worstCost w cσ n :=
  Real.sSup_nonneg fun _ ⟨_, _, _, _, _, r, _, _, hc⟩ => hc ▸ r.total_nonneg hw

theorem total_le_worstCost {w : Node P → ℝ} {cσ : ℝ} {n : ℕ}
    (hb : BddAbove (costSet w cσ n)) {Ω C : Type} {S : State Ω C}

    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)} (r : Run P .solve S L A) (hS : S.size ≤ n)
    (hr : r.RootsOK cσ) :
    r.total w ≤ worstCost w cσ n :=
  le_csSup hb ⟨Ω, C, S, L, A, r, hS, hr, rfl⟩

theorem costSet_mono {w : Node P → ℝ} {cσ : ℝ} {m n : ℕ} (h : m ≤ n) :
    costSet w cσ m ⊆ costSet w cσ n :=
  fun _ ⟨Ω, C, S, L, A, r, hS, hr, hc⟩ => ⟨Ω, C, S, L, A, r, hS.trans h, hr, hc⟩

/-- `F` is monotone where it is bounded. -/
theorem worstCost_mono {w : Node P → ℝ} (hw : ∀ nd, 0 ≤ w nd) {cσ : ℝ} {m n : ℕ}
    (h : m ≤ n) (hb : BddAbove (costSet w cσ n)) : worstCost w cσ m ≤ worstCost w cσ n := by
  rcases (costSet w cσ m).eq_empty_or_nonempty with he | hne
  · unfold worstCost; rw [he, Real.sSup_empty]; exact worstCost_nonneg hw cσ n
  · exact csSup_le_csSup hb hne (costSet_mono h)

end GI.Algorithm
