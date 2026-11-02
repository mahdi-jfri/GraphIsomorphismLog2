import Workspace.Paper.RunningTimeInequalities
import Workspace.Paper.RunningTimeParameters
import Workspace.Recurrence
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Section 7: Lemma 7.1 (weighted phase induction) on an abstract recursion tree

The algorithm of Sections 4 to 6 is not formalized yet. Lemma 7.1
(`lem:main-phase-bound`) is therefore stated for an abstract model of one phase
that records exactly the facts its proof uses about each recursive call:

* every node carries the resources `s, ρ, σ, Q, h` of Section 7.1;
* a *threshold leaf* has `s ≤ N^γ` and cost at most `K_N`;
* a *charged node* groups its children into at most `J` classes, one row of the table
  of Section 7.2 each, with a bound on the number of branches and, for every child,
  the decrease in resources stated in that row;
* a *pure orbit node* (an intransitive conditional query, whose state is the original
  transitive orbit's credit) has children on disjoint domains, each smaller and
  without a larger potential;
* every internal node has `s > N^γ` and cost at most `N^a K_N` plus the costs of its
  children (the node toll, including fresh oracle calls).

Each hypothesis says where the paper asserts it. The machine-level proof establishes these
facts about the real algorithm and then applies `GI.Paper.lem_main_phase_bound`.
-/

namespace GI.Paper

open Real

/-! ## The potential -/

/-- The resources of an inherited state used by the potential of Section 7.1: the
domain size `s`, the hierarchy rank `ρ` (equation `eq:main-rho`), the symmetry
measure `σ` (Section 3.3 (i)), the cap moment `Q` (equation `eq:main-Q`) and the row
counter `h` (Section 6.1). -/
structure PotentialState where
  s : ℕ
  ρ : ℝ
  σ : ℝ
  Q : ℝ
  h : ℕ

namespace PotentialState

/-- `x = log(s+2)`. -/
noncomputable def x (S : PotentialState) : ℝ := Real.log ((S.s : ℝ) + 2)

/-- Equation `eq:main-potential`: `Φ = A(x² + ρx + σx + Q) + Bh`. -/
noncomputable def Φ (A B : ℝ) (S : PotentialState) : ℝ :=
  A * (S.x ^ 2 + S.ρ * S.x + S.σ * S.x + S.Q) + B * S.h

/-- Equation `eq:main-weight`: `W = (s+2)^D exp(Φ)`. -/
noncomputable def W (A B : ℝ) (D : ℕ) (S : PotentialState) : ℝ :=
  ((S.s : ℝ) + 2) ^ D * Real.exp (S.Φ A B)

theorem x_nonneg (S : PotentialState) : 0 ≤ S.x :=
  Real.log_nonneg (by have : (0 : ℝ) ≤ S.s := Nat.cast_nonneg _; linarith)

theorem x_mono {S T : PotentialState} (h : (T.s : ℝ) ≤ S.s) : T.x ≤ S.x :=
  Real.log_le_log (by positivity) (by linarith)

end PotentialState

/-! ## The rows of the table of Section 7.2 -/

/-- The six rows of the table "Recursive operation / Multiplicity bound / Potential
decrease" in Section 7.2, with their parameters. -/
inductive Row
  /-- Affected test or rectangle. -/
  | affected
  /-- Visible unaffected test. -/
  | unaffected
  /-- Product refinement with exponent `r ≥ 2`. -/
  | product (r : ℕ)
  /-- Primitive enumeration on a quotient of degree `d`. -/
  | enumeration (d : ℕ)
  /-- Auxiliary-graph continuation on `q` labels. -/
  | continuation (q : ℕ)
  /-- Row initialization or enlargement. -/
  | rowEvent

namespace Row

variable (C : ChargingConstants)

/-- The side conditions on the parameters of a row, at a parent state `S`.
* product: `r ≥ 2` (table) and `r ≤ log₂ s` (Section 7.2, "Since `r ≤ log₂ s`");
* enumeration: `2 ≤ d ≤ s` (Section 7.2, "Uniformly for `s ≥ d ≥ 2`");
* continuation: `q ≥ q₀` (Section 7.5, "The cap row … the same margin by
  (main-constant-cap)", which is used for labels above the cutoff `q₀`). -/
def Valid (S : PotentialState) : Row → Prop
  | affected => True
  | unaffected => True
  | product r => 2 ≤ r ∧ (r : ℝ) ≤ Real.logb 2 S.s
  | enumeration d => 2 ≤ d ∧ d ≤ S.s
  | continuation q => C.q₀ ≤ q
  | rowEvent => True

/-- The resources of a child `T` of a parent `S` in a class of the given row. These
are the facts behind the column "Potential decrease" of the table:
* affected test or rectangle: `s' ≤ θs` (Section 7.2, "(main-domain-payment) pays
  affected local-test calls, rectangle calls, large-symmetry calls, and entries into
  proper columns");
* visible unaffected test: `σ' ≤ σ - κ` ("An extra unaffected local-test call
  decreases `σ` by `κ`");
* product refinement: `ρ' ≤ ρ - (r-1)` ("the actual coordinate refinement decreases
  `ρ` by at least `r-1`");
* primitive enumeration: `s' ≤ s/d` ("Its kernel orbits have size at most `s/d`");
* continuation: `Q' ≤ Q - c_β log q` (equation `eq:main-cap-payment`, proved as
  `GI.Paper.eq_main_cap_payment`);
* row event: `h' ≤ h - 1` ("this event decreases `h` without resetting it").
In every row the other resources do not increase (Section 7.1: restriction does not
increase `ρ`, `Q`; Section 3.3 (i): nor `σ`), and `h` grows by at most two ("The table
allows the worst possible increase `2B` from an admissible counter reset"). -/
def Child (S T : PotentialState) : Row → Prop
  | affected => (T.s : ℝ) ≤ C.θ * S.s ∧ T.ρ ≤ S.ρ ∧ T.σ ≤ S.σ ∧ T.Q ≤ S.Q ∧ T.h ≤ S.h + 2
  | unaffected => T.s ≤ S.s ∧ T.ρ ≤ S.ρ ∧ T.σ ≤ S.σ - C.κ ∧ T.Q ≤ S.Q ∧ T.h ≤ S.h + 2
  | product r => T.s ≤ S.s ∧ T.ρ ≤ S.ρ - ((r : ℝ) - 1) ∧ T.σ ≤ S.σ ∧ T.Q ≤ S.Q ∧
      T.h ≤ S.h + 2
  | enumeration d => d * T.s ≤ S.s ∧ T.ρ ≤ S.ρ ∧ T.σ ≤ S.σ ∧ T.Q ≤ S.Q ∧ T.h ≤ S.h + 2
  | continuation q => T.s ≤ S.s ∧ T.ρ ≤ S.ρ ∧ T.σ ≤ S.σ ∧
      T.Q ≤ S.Q - cBeta C.β * Real.log q ∧ T.h ≤ S.h + 2
  | rowEvent => T.s ≤ S.s ∧ T.ρ ≤ S.ρ ∧ T.σ ≤ S.σ ∧ T.Q ≤ S.Q ∧ T.h + 1 ≤ S.h

/-- The column "Multiplicity bound" of the table, for phase size `N`. -/
noncomputable def mult (N : ℕ) : Row → ℝ
  | affected => (N : ℝ) ^ C.a
  | unaffected => (N : ℝ) ^ C.a
  | product r => (N : ℝ) ^ C.a * ((2 : ℝ) ^ r * (r.factorial : ℝ))
  | enumeration d => (N : ℝ) ^ C.a * Real.exp (C.a * Real.log d ^ 2)
  | continuation q => (q : ℝ) ^ C.a
  | rowEvent => C.b₀

/-- The column "Potential decrease" of the table, at a parent state `S`. -/
noncomputable def drop (S : PotentialState) : Row → ℝ
  | affected => C.A * cTheta C.θ * S.x - 2 * C.B
  | unaffected => C.A * C.κ * S.x - 2 * C.B
  | product r => C.A * ((r : ℝ) - 1) * S.x - 2 * C.B
  | enumeration d => C.A / 3 * S.x * Real.log d - 2 * C.B
  | continuation q => C.A * cBeta C.β * Real.log q - 2 * C.B
  | rowEvent => C.B

end Row

/-! ## The recursion tree of one phase -/

/-- One class of children of a charged node: a row of the table and its branches.
"An entry counts branches; within each branch an intransitive restriction is
expanded into a disjoint orbit forest" (Section 7.2): a branch lists the nodes on its
disjoint orbit domains. -/
structure ChildClass (V : Type*) where
  row : Row
  branches : List (List V)

/-- The three kinds of node in the proof of Lemma 7.1. -/
inductive NodeKind (V : Type*)
  /-- An ordinary threshold leaf. -/
  | leaf
  /-- A charged node, with its children grouped into classes. -/
  | charged (classes : List (ChildClass V))
  /-- A pure orbit node: the expansion of an intransitive conditional query into its
  orbit forest. Its state is the original transitive orbit's credit. -/
  | orbit (children : List V)

namespace NodeKind

variable {V : Type*}

/-- All inherited children of a node. -/
def children : NodeKind V → List V
  | leaf => []
  | charged cls => (cls.map fun c => c.branches.flatten).flatten
  | orbit cs => cs

end NodeKind

/-- The recursion tree of one phase: every node has a state, a kind and a cost. The
cost `cost v` is `T_N` of the paper: the work of the call, including its fresh oracle
calls. -/
structure PhaseTree (V : Type*) where
  state : V → PotentialState
  kind : V → NodeKind V
  cost : V → ℝ

/-- A child of a pure orbit node (Section 7.3): "Each child potential is at most the
original orbit's credit. This is immediate for the first largest child; for a later
child, (main-domain-payment) also pays any increase of `h`." So `ρ, σ, Q` do not
increase, and either `h` does not increase (the first child) or the child lies in a
later original orbit, of size at most `s/2`, and `h` grows by at most two. -/
def OrbitChild (S T : PotentialState) : Prop :=
  T.ρ ≤ S.ρ ∧ T.σ ≤ S.σ ∧ T.Q ≤ S.Q ∧ (T.h ≤ S.h ∨ (2 * T.s ≤ S.s ∧ T.h ≤ S.h + 2))

/-- The facts that the proof of Lemma 7.1 asserts about each node of a phase with
phase size `N` and node toll factor `K` (`K_N` of equation `eq:main-phase-toll`). -/
structure PhaseTree.Hyp (C : ChargingConstants) (N : ℕ) (K : ℝ) {V : Type*}
    (T : PhaseTree V) : Prop where
  /-- `ρ ≥ 0` (a sum of terms `2⌊log₂ d⌋ - 1 ≥ 1`, equation `eq:main-rho`), `σ ≥ 0`
  (Section 3.3 (i): "a nonnegative measure"), `Q ≥ 0` (equation `eq:main-Q`). -/
  nonneg : ∀ v, 0 ≤ (T.state v).ρ ∧ 0 ≤ (T.state v).σ ∧ 0 ≤ (T.state v).Q
  /-- Section 7.4: "Every fresh leaf has at most `N^γ` positions. Ordinary inherited
  calls stop at that threshold." -/
  leaf_small : ∀ v, T.kind v = .leaf → ((T.state v).s : ℝ) ≤ (N : ℝ) ^ C.γ
  /-- Section 7.4: "An ordinary threshold leaf has cost at most `K_N`". -/
  leaf_cost : ∀ v, T.kind v = .leaf → T.cost v ≤ K
  /-- Equation `eq:main-phase-active`: "At every internal node … `s > N^γ`". -/
  internal_large : ∀ v, T.kind v ≠ .leaf → (N : ℝ) ^ C.γ < (T.state v).s
  /-- Section 7.4: "all structural work and all fresh configuration or row calls at
  one node have total cost at most `N^a K_N`"; for an orbit node, "The polynomial
  work of expanding the forest is included in `N^a`". The children's costs add
  ("their recursive costs are not multiplied"). -/
  toll : ∀ v, T.kind v ≠ .leaf →
    T.cost v ≤ (N : ℝ) ^ C.a * K + (((T.kind v).children).map T.cost).sum
  /-- Proof of Lemma 7.1: "group the inherited children into at most `J` classes". -/
  classes_le : ∀ v cls, T.kind v = .charged cls → cls.length ≤ C.J
  /-- The side conditions of each row (see `Row.Valid`). -/
  class_valid : ∀ v cls, T.kind v = .charged cls → ∀ c ∈ cls, c.row.Valid C (T.state v)
  /-- The column "Multiplicity bound" of the table: the number of branches. -/
  class_mult : ∀ v cls, T.kind v = .charged cls → ∀ c ∈ cls,
    (c.branches.length : ℝ) ≤ c.row.mult C N
  /-- The orbit domains of a branch are nonempty. -/
  branch_pos : ∀ v cls, T.kind v = .charged cls → ∀ c ∈ cls, ∀ b ∈ c.branches,
    ∀ u ∈ b, 1 ≤ (T.state u).s
  /-- Proof of Lemma 7.1: "Within one branch, the prefactors of its disjoint orbit
  children sum to at most `(s+2)^D`": the orbit domains of a branch are disjoint
  subsets of the parent domain. -/
  branch_disjoint : ∀ v cls, T.kind v = .charged cls → ∀ c ∈ cls, ∀ b ∈ c.branches,
    ((b.map fun u => (T.state u).s).sum) ≤ (T.state v).s
  /-- The column "Potential decrease" of the table (see `Row.Child`). -/
  branch_child : ∀ v cls, T.kind v = .charged cls → ∀ c ∈ cls, ∀ b ∈ c.branches,
    ∀ u ∈ b, c.row.Child C (T.state v) (T.state u)
  /-- Section 7.1: the orbit domains are nonempty "disjoint subsets of the original
  query domain"; proof of Lemma 7.1: "A pure orbit transition … strictly decreases
  the positive integer domain size". -/
  orbit_pos : ∀ v cs, T.kind v = .orbit cs → ∀ u ∈ cs,
    1 ≤ (T.state u).s ∧ (T.state u).s < (T.state v).s
  /-- Section 7.1: the orbit domains are disjoint subsets of the query domain. -/
  orbit_disjoint : ∀ v cs, T.kind v = .orbit cs →
    ((cs.map fun u => (T.state u).s).sum) ≤ (T.state v).s
  /-- Section 7.3: the child resources are bounded by the credit (see `OrbitChild`). -/
  orbit_child : ∀ v cs, T.kind v = .orbit cs → ∀ u ∈ cs, OrbitChild (T.state v) (T.state u)

/-- Equation `eq:main-phase-toll`: `K_N = E_N (1 + F(M_N))` with
`E_N = exp(c_T (log(N+2))²)` and `M_N = ⌈N^γ⌉`. -/
noncomputable def phaseToll (cT γ : ℝ) (F : ℕ → ℝ) (N : ℕ) : ℝ :=
  Real.exp (cT * Real.log ((N : ℝ) + 2) ^ 2) * (1 + F ⌈(N : ℝ) ^ γ⌉₊)

/-! ## Facts about the potential -/

namespace PotentialState

theorem Φ_nonneg {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) {S : PotentialState} (hρ : 0 ≤ S.ρ)
    (hσ : 0 ≤ S.σ) (hQ : 0 ≤ S.Q) : 0 ≤ S.Φ A B := by
  unfold Φ
  have h1 := mul_nonneg hρ S.x_nonneg
  have h2 := mul_nonneg hσ S.x_nonneg
  have h3 : 0 ≤ S.x ^ 2 + S.ρ * S.x + S.σ * S.x + S.Q := by nlinarith [sq_nonneg S.x]
  exact add_nonneg (mul_nonneg hA h3) (mul_nonneg hB (Nat.cast_nonneg _))

/-- `W ≥ (s+2)^D` when `Φ ≥ 0`. -/
theorem prefactor_le_W {A B : ℝ} {D : ℕ} {S : PotentialState} (hΦ : 0 ≤ S.Φ A B) :
    ((S.s : ℝ) + 2) ^ D ≤ S.W A B D := by
  unfold W
  have := Real.one_le_exp hΦ
  have : (0 : ℝ) ≤ ((S.s : ℝ) + 2) ^ D := by positivity
  nlinarith

theorem one_le_W {A B : ℝ} {D : ℕ} {S : PotentialState} (hΦ : 0 ≤ S.Φ A B) :
    1 ≤ S.W A B D :=
  le_trans (one_le_pow₀ (by have : (0 : ℝ) ≤ S.s := Nat.cast_nonneg _; linarith))
    (prefactor_le_W hΦ)

/-- The common estimate behind every row: if the child's `x` is at most both `S.x`
and `y`, and its other resources are bounded by `ρ', σ', Q', h'`, then
`Φ(T) ≤ A(y² + ρ'x + σ'x + Q') + Bh'`. -/
theorem Φ_le_of {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) {S T : PotentialState}
    {y ρ' σ' Q' h' : ℝ} (hTρ : 0 ≤ T.ρ) (hTσ : 0 ≤ T.σ) (hx : T.x ≤ S.x) (hy : T.x ≤ y)
    (hρ : T.ρ ≤ ρ') (hσ : T.σ ≤ σ') (hQ : T.Q ≤ Q') (hh : (T.h : ℝ) ≤ h') :
    T.Φ A B ≤ A * (y ^ 2 + ρ' * S.x + σ' * S.x + Q') + B * h' := by
  have h1 : T.x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ T.x_nonneg hy 2
  have h2 : T.ρ * T.x ≤ ρ' * S.x := mul_le_mul hρ hx T.x_nonneg (hTρ.trans hρ)
  have h3 : T.σ * T.x ≤ σ' * S.x := mul_le_mul hσ hx T.x_nonneg (hTσ.trans hσ)
  have hsum : T.x ^ 2 + T.ρ * T.x + T.σ * T.x + T.Q ≤ y ^ 2 + ρ' * S.x + σ' * S.x + Q' := by
    linarith
  unfold Φ
  have := mul_le_mul_of_nonneg_left hsum hA
  have := mul_le_mul_of_nonneg_left hh hB
  linarith

end PotentialState

/-! ## The rows: potential decrease, margin and positivity -/

namespace Row

variable (C : ChargingConstants)

theorem xZero_le_x {S : PotentialState} (hS : 6 ≤ (S.s : ℝ)) : xZero ≤ S.x :=
  Real.log_le_log (by norm_num) (by linarith)

/-- Each row of the table: a child `T` in a class of row `R` satisfies
`Φ(T) ≤ Φ(S) - ΔΦ`, with `ΔΦ` from the column "Potential decrease". Here the parent
has `s ≥ 6` (an internal node, since `N^γ ≥ 6`). -/
theorem child_Φ_le {S T : PotentialState} {R : Row} (hS6 : 6 ≤ (S.s : ℝ))
    (hv : R.Valid C S) (hc : R.Child C S T) (hTρ : 0 ≤ T.ρ) (hTσ : 0 ≤ T.σ) :
    T.Φ C.A C.B ≤ S.Φ C.A C.B - R.drop C S := by
  have hA := C.A_nonneg
  have hB := C.B_nonneg
  have hxS := S.x_nonneg
  cases R with
  | affected =>
    obtain ⟨hs, hρ, hσ, hQ, hh⟩ := hc
    have hθ := C.half_lt_θ
    have hθ1 := C.θ_lt_one
    have hTs : (T.s : ℝ) ≤ S.s := hs.trans (by nlinarith)
    have hy : T.x ≤ Real.log (C.θ * S.s + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    have hpay := (eq_main_domain_payment hθ hθ1 hS6).2
    have hh' : (T.h : ℝ) ≤ S.h + 2 := by exact_mod_cast hh
    have := PotentialState.Φ_le_of hA hB hTρ hTσ (PotentialState.x_mono hTs) hy hρ hσ hQ hh'
    have hmul := mul_le_mul_of_nonneg_left hpay hA
    simp only [drop, PotentialState.Φ, PotentialState.x, cTheta] at *
    nlinarith
  | unaffected =>
    obtain ⟨hs, hρ, hσ, hQ, hh⟩ := hc
    have hTs : (T.s : ℝ) ≤ S.s := by exact_mod_cast hs
    have hh' : (T.h : ℝ) ≤ S.h + 2 := by exact_mod_cast hh
    have := PotentialState.Φ_le_of hA hB hTρ hTσ (PotentialState.x_mono hTs)
      (PotentialState.x_mono hTs) hρ hσ hQ hh'
    simp only [drop, PotentialState.Φ] at *
    nlinarith
  | product r =>
    obtain ⟨hs, hρ, hσ, hQ, hh⟩ := hc
    have hTs : (T.s : ℝ) ≤ S.s := by exact_mod_cast hs
    have hh' : (T.h : ℝ) ≤ S.h + 2 := by exact_mod_cast hh
    have := PotentialState.Φ_le_of hA hB hTρ hTσ (PotentialState.x_mono hTs)
      (PotentialState.x_mono hTs) hρ hσ hQ hh'
    simp only [drop, PotentialState.Φ] at *
    nlinarith
  | enumeration d =>
    obtain ⟨hs, hρ, hσ, hQ, hh⟩ := hc
    obtain ⟨hd2, hds⟩ := hv
    have hd2' : (2 : ℝ) ≤ d := by exact_mod_cast hd2
    have hds' : (d : ℝ) ≤ S.s := by exact_mod_cast hds
    have hs' : (d : ℝ) * T.s ≤ S.s := by exact_mod_cast hs
    have hTs' : (T.s : ℝ) ≤ S.s / d := by rw [le_div_iff₀ (by linarith)]; linarith
    have hTs : (T.s : ℝ) ≤ S.s := by
      have : (0 : ℝ) ≤ T.s := Nat.cast_nonneg _
      nlinarith
    have hy : T.x ≤ Real.log (S.s / d + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    have hpay := (eq_main_enumeration_payment hd2' hds').2.2
    have hh' : (T.h : ℝ) ≤ S.h + 2 := by exact_mod_cast hh
    have := PotentialState.Φ_le_of hA hB hTρ hTσ (PotentialState.x_mono hTs) hy hρ hσ hQ hh'
    have hmul := mul_le_mul_of_nonneg_left hpay hA
    simp only [drop, PotentialState.Φ, PotentialState.x] at *
    nlinarith
  | continuation q =>
    obtain ⟨hs, hρ, hσ, hQ, hh⟩ := hc
    have hTs : (T.s : ℝ) ≤ S.s := by exact_mod_cast hs
    have hh' : (T.h : ℝ) ≤ S.h + 2 := by exact_mod_cast hh
    have := PotentialState.Φ_le_of hA hB hTρ hTσ (PotentialState.x_mono hTs)
      (PotentialState.x_mono hTs) hρ hσ hQ hh'
    simp only [drop, PotentialState.Φ] at *
    nlinarith
  | rowEvent =>
    obtain ⟨hs, hρ, hσ, hQ, hh⟩ := hc
    have hTs : (T.s : ℝ) ≤ S.s := by exact_mod_cast hs
    have hh' : (T.h : ℝ) ≤ S.h - 1 := by
      have : (T.h : ℝ) + 1 ≤ S.h := by exact_mod_cast hh
      linarith
    have := PotentialState.Φ_le_of hA hB hTρ hTσ (PotentialState.x_mono hTs)
      (PotentialState.x_mono hTs) hρ hσ hQ hh'
    simp only [drop, PotentialState.Φ] at *
    nlinarith

/-- Every row decreases `Φ` by at least `log(8J) > 0` (proof of Lemma 7.1: "Every
charged transition in the table decreases `Φ` by a fixed positive amount after the
counter updates"). -/
theorem log8J_le_drop {S : PotentialState} {R : Row} (hS6 : 6 ≤ (S.s : ℝ))
    (hv : R.Valid C S) : Real.log (8 * C.J) ≤ R.drop C S := by
  have hx := xZero_le_x hS6
  have haS := C.aStar_nonneg
  have hx0 := S.x_nonneg
  cases R with
  | affected =>
    have := C.margin_domain hx
    have := mul_nonneg haS hx0
    simp only [drop]; linarith
  | unaffected =>
    have := C.margin_symmetry hx
    have := mul_nonneg haS hx0
    simp only [drop]; linarith
  | product r =>
    obtain ⟨hr, hrs⟩ := hv
    have hb := (main_product_index_bound hr hrs)
    have := C.margin_product hx (by exact_mod_cast hr) (hb.1.trans hb.2)
    have := mul_nonneg haS hx0
    have : 0 ≤ Real.log ((2 : ℝ) ^ r * (r.factorial : ℝ)) := Real.log_nonneg (by
      have : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
      have : (1 : ℝ) ≤ r.factorial := by exact_mod_cast Nat.factorial_pos r
      nlinarith)
    simp only [drop]; linarith
  | enumeration d =>
    obtain ⟨hd2, hds⟩ := hv
    have hd2' : (2 : ℝ) ≤ d := by exact_mod_cast hd2
    have hds' : (d : ℝ) ≤ S.s := by exact_mod_cast hds
    have := C.margin_enum hx (Real.log_le_log (by norm_num) hd2')
      (Real.log_le_log (by linarith) (by linarith) : Real.log d ≤ S.x)
    have := mul_nonneg haS hx0
    have := mul_nonneg C.a_pos.le (sq_nonneg (Real.log d))
    simp only [drop]; linarith
  | continuation q =>
    have hq : C.q₀ ≤ q := hv
    have := C.margin_cap hq
    have := mul_nonneg C.a_pos.le (Real.log_nonneg (by linarith [C.one_lt_q₀] : (1 : ℝ) ≤ q))
    simp only [drop]; linarith
  | rowEvent =>
    have hJ : (0 : ℝ) < 8 * C.J := by
      have : (1 : ℝ) ≤ C.J := by exact_mod_cast C.one_le_J
      linarith
    have : Real.log (8 * C.J) ≤ Real.log (8 * C.J * C.b₀) :=
      Real.log_le_log hJ (by nlinarith [C.one_le_b₀])
    simp only [drop]; linarith [C.B_ge]

/-- The margin of Section 7.5 for each row: "each class contributes at most `1/(8J)`
of the parent weight", that is, `M exp(-ΔΦ) ≤ 1/(8J)`. -/
theorem mult_mul_exp_neg_drop_le {S : PotentialState} {R : Row} {N : ℕ}
    (hNs : (N : ℝ) ^ C.γ < S.s) (hS6 : 6 ≤ (S.s : ℝ)) (hv : R.Valid C S) :
    R.mult C N * Real.exp (-R.drop C S) ≤ 1 / (8 * C.J) := by
  have hJ : (0 : ℝ) < 8 * C.J := by
    have : (1 : ℝ) ≤ C.J := by exact_mod_cast C.one_le_J
    linarith
  have hx := xZero_le_x hS6
  -- `N^a ≤ exp(a_* x)` by (main-phase-active).
  have hNa : (N : ℝ) ^ C.a ≤ Real.exp (C.aStar * S.x) :=
    eq_main_phase_active (Nat.cast_nonneg N) C.a_pos.le C.γ_pos hNs
  have hNa0 : (0 : ℝ) ≤ (N : ℝ) ^ C.a := Real.rpow_nonneg (Nat.cast_nonneg N) _
  -- It suffices that `M ≤ exp(ΔΦ - log(8J))`.
  suffices hM : R.mult C N ≤ Real.exp (R.drop C S - Real.log (8 * C.J)) by
    calc R.mult C N * Real.exp (-R.drop C S)
        ≤ Real.exp (R.drop C S - Real.log (8 * C.J)) * Real.exp (-R.drop C S) :=
          mul_le_mul_of_nonneg_right hM (Real.exp_pos _).le
      _ = 1 / (8 * C.J) := by
          rw [← Real.exp_add, show R.drop C S - Real.log (8 * C.J) + -R.drop C S =
            -Real.log (8 * C.J) by ring, Real.exp_neg, Real.exp_log hJ, one_div]
  cases R with
  | affected =>
    have := C.margin_domain hx
    exact hNa.trans (Real.exp_le_exp.mpr (by simp only [drop]; linarith))
  | unaffected =>
    have := C.margin_symmetry hx
    exact hNa.trans (Real.exp_le_exp.mpr (by simp only [drop]; linarith))
  | product r =>
    obtain ⟨hr, hrs⟩ := hv
    have hb := main_product_index_bound hr hrs
    set L := Real.log ((2 : ℝ) ^ r * (r.factorial : ℝ))
    have hm := C.margin_product hx (by exact_mod_cast hr) (hb.1.trans hb.2)
    have hpos : (0 : ℝ) < (2 : ℝ) ^ r * (r.factorial : ℝ) := by positivity
    simp only [mult, drop]
    calc (N : ℝ) ^ C.a * ((2 : ℝ) ^ r * (r.factorial : ℝ))
        ≤ Real.exp (C.aStar * S.x) * Real.exp L := by
          rw [Real.exp_log hpos]; exact mul_le_mul_of_nonneg_right hNa hpos.le
      _ = Real.exp (L + C.aStar * S.x) := by rw [← Real.exp_add, add_comm]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  | enumeration d =>
    obtain ⟨hd2, hds⟩ := hv
    have hd2' : (2 : ℝ) ≤ d := by exact_mod_cast hd2
    have hds' : (d : ℝ) ≤ S.s := by exact_mod_cast hds
    have hm := C.margin_enum hx (Real.log_le_log (by norm_num) hd2')
      (Real.log_le_log (by linarith) (by linarith) : Real.log d ≤ S.x)
    simp only [mult, drop]
    calc (N : ℝ) ^ C.a * Real.exp (C.a * Real.log d ^ 2)
        ≤ Real.exp (C.aStar * S.x) * Real.exp (C.a * Real.log d ^ 2) :=
          mul_le_mul_of_nonneg_right hNa (Real.exp_pos _).le
      _ = Real.exp (C.a * Real.log d ^ 2 + C.aStar * S.x) := by
          rw [← Real.exp_add, add_comm]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  | continuation q =>
    have hq : C.q₀ ≤ q := hv
    have hq0 : (0 : ℝ) < q := by linarith [C.one_lt_q₀]
    have hm := C.margin_cap hq
    simp only [mult, drop]
    rw [Real.rpow_def_of_pos hq0]
    exact Real.exp_le_exp.mpr (by linarith)
  | rowEvent =>
    have hm := C.B_ge
    simp only [mult, drop]
    have hb : (0 : ℝ) < 8 * C.J * C.b₀ := by nlinarith [C.one_le_b₀]
    calc C.b₀ = Real.exp (Real.log (8 * C.J * C.b₀) - Real.log (8 * C.J)) := by
          rw [Real.exp_sub, Real.exp_log hb, Real.exp_log hJ]; field_simp
          have : (C.J : ℝ) ≠ 0 := by linarith
          field_simp
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Row

/-! ## Sums of weights over disjoint orbits -/

theorem list_sum_map_flatten {α : Type*} (l : List (List α)) (g : α → ℝ) :
    (l.flatten.map g).sum = (l.map fun b => (b.map g).sum).sum := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.flatten_cons, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons, ih]

theorem list_sum_le_length_mul {α : Type*} (l : List α) (f : α → ℝ) (c : ℝ)
    (h : ∀ a ∈ l, f a ≤ c) : (l.map f).sum ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
    have h1 := h a (by simp)
    have h2 := ih (fun b hb => h b (by simp [hb]))
    linarith

/-- `GI.Paper.prefactor_sum_le` for a list of states. -/
theorem list_prefactor_sum_le {D : ℕ} (hD : 3 ≤ D) (l : List PotentialState) {s : ℝ}
    (hpos : ∀ T ∈ l, 1 ≤ T.s) (hsum : (l.map fun T => (T.s : ℝ)).sum ≤ s) :
    (l.map fun T => ((T.s : ℝ) + 2) ^ D).sum ≤ (s + 2) ^ D := by
  rw [← Fin.sum_univ_fun_getElem] at hsum ⊢
  exact prefactor_sum_le hD (fun i : Fin l.length => (l[i.1].s : ℝ)) Finset.univ
    (fun i _ => by
      show (1 : ℝ) ≤ (l[i.1].s : ℝ)
      exact_mod_cast hpos _ (List.getElem_mem _)) hsum

/-- `GI.Paper.eq_main_orbit_slack_sum` for a list of states, also allowing zero or one
child of smaller size. -/
theorem list_orbit_prefactor_le {D : ℕ} (hD : 3 ≤ D) (l : List PotentialState) {s : ℕ}
    (hpos : ∀ T ∈ l, 1 ≤ T.s ∧ T.s < s) (hsum : (l.map fun T => (T.s : ℝ)).sum ≤ s) :
    (l.map fun T => ((T.s : ℝ) + 2) ^ D).sum ≤ ((s : ℝ) + 1) ^ D + 3 ^ D := by
  rcases Nat.lt_or_ge l.length 2 with hl | hl
  · have h3 : (0 : ℝ) ≤ 3 ^ D := by positivity
    rcases Nat.lt_or_ge l.length 1 with hl1 | hl1
    · have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      simp only [List.map_nil, List.sum_nil]
      positivity
    · obtain ⟨T, rfl⟩ := List.length_eq_one_iff.mp (by omega : l.length = 1)
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      have hT := (hpos T (by simp)).2
      have : (T.s : ℝ) + 2 ≤ (s : ℝ) + 1 := by
        have : (T.s : ℝ) + 1 ≤ s := by exact_mod_cast hT
        linarith
      have := pow_le_pow_left₀ (by positivity) this D
      linarith
  · rw [← Fin.sum_univ_fun_getElem] at hsum ⊢
    exact eq_main_orbit_slack_sum hD (fun i : Fin l.length => (l[i.1].s : ℝ)) Finset.univ
      (fun i _ => by
        show (1 : ℝ) ≤ (l[i.1].s : ℝ)
        exact_mod_cast (hpos _ (List.getElem_mem _)).1)
      (by simpa using hl) hsum

/-- The weight of disjoint nonempty orbits inside the parent domain, each with
potential at most `Φ(S) - Δ`, is at most `exp(-Δ) W(S)`. This is the step "For a class
of multiplicity `M` and minimum potential decrease `ΔΦ`, its total child weight is …"
in the proof of Lemma 7.1, for one branch. -/
theorem list_weight_sum_le (C : ChargingConstants) (l : List PotentialState)
    (S : PotentialState) (Δ : ℝ) (hpos : ∀ T ∈ l, 1 ≤ T.s)
    (hsum : (l.map fun T => (T.s : ℝ)).sum ≤ S.s)
    (hΦ : ∀ T ∈ l, T.Φ C.A C.B ≤ S.Φ C.A C.B - Δ) :
    (l.map fun T => T.W C.A C.B C.D).sum ≤ Real.exp (-Δ) * S.W C.A C.B C.D := by
  calc (l.map fun T => T.W C.A C.B C.D).sum
      ≤ (l.map fun T => ((T.s : ℝ) + 2) ^ C.D * Real.exp (S.Φ C.A C.B - Δ)).sum := by
        apply List.sum_le_sum
        intro T hT
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hΦ T hT)) (by positivity)
    _ = (l.map fun T => ((T.s : ℝ) + 2) ^ C.D).sum * Real.exp (S.Φ C.A C.B - Δ) := by
        rw [List.sum_map_mul_right]
    _ ≤ ((S.s : ℝ) + 2) ^ C.D * Real.exp (S.Φ C.A C.B - Δ) :=
        mul_le_mul_of_nonneg_right (list_prefactor_sum_le C.three_le_D l hpos hsum)
          (Real.exp_pos _).le
    _ = Real.exp (-Δ) * S.W C.A C.B C.D := by
        unfold PotentialState.W
        rw [sub_eq_add_neg, Real.exp_add]; ring

/-! ## Powers of `N` -/

theorem N_pos_of (C : ChargingConstants) {N : ℕ} (hN6 : 6 ≤ (N : ℝ) ^ C.γ) : 0 < (N : ℝ) := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; rw [Nat.cast_zero, Real.zero_rpow C.γ_pos.ne'] at hN6; linarith
  · exact_mod_cast h

/-- The second inequality of `eq:main-charged-induction`, `W ≥ 2N^a`, from `s > N^γ`
and the base-size condition `N^{γD-a} ≥ 2`. -/
theorem two_rpow_a_le (C : ChargingConstants) {N : ℕ} {s : ℝ} (hN6 : 6 ≤ (N : ℝ) ^ C.γ)
    (hN2 : 2 ≤ (N : ℝ) ^ (C.γ * C.D - C.a)) (hs : (N : ℝ) ^ C.γ < s) :
    2 * (N : ℝ) ^ C.a ≤ (s + 2) ^ C.D := by
  have hN := N_pos_of C hN6
  have h1 : ((N : ℝ) ^ C.γ) ^ C.D ≤ (s + 2) ^ C.D :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have h2 : ((N : ℝ) ^ C.γ) ^ C.D = (N : ℝ) ^ (C.γ * C.D - C.a) * (N : ℝ) ^ C.a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le, ← Real.rpow_add hN]; ring_nf
  have := mul_le_mul_of_nonneg_right hN2 (Real.rpow_nonneg hN.le C.a)
  linarith

/-- Section 7.3: "We take `D > a/γ + 2`; then at every internal phase size the
displayed slack exceeds `N^a`", that is, `N^a ≤ (D/2) s^{D-1}` when `s > N^γ`. -/
theorem rpow_a_le_slack (C : ChargingConstants) {N : ℕ} {s : ℝ} (hN6 : 6 ≤ (N : ℝ) ^ C.γ)
    (hs : (N : ℝ) ^ C.γ < s) : (N : ℝ) ^ C.a ≤ (C.D / 2 : ℝ) * s ^ (C.D - 1) := by
  have hN := N_pos_of C hN6
  have hN1 : (1 : ℝ) ≤ N := by
    have : 0 < N := by exact_mod_cast hN
    exact_mod_cast this
  have hD3 : (3 : ℝ) ≤ C.D := by exact_mod_cast C.three_le_D
  have hDc : ((C.D - 1 : ℕ) : ℝ) = (C.D : ℝ) - 1 := by
    rw [Nat.cast_sub (by linarith [C.three_le_D] : 1 ≤ C.D)]; simp
  -- `a < γ(D-2) ≤ γ(D-1)`.
  have haD : C.a ≤ C.γ * ((C.D - 1 : ℕ) : ℝ) := by
    have h := C.D_gt
    have hγ := C.γ_pos
    rw [hDc]
    have : C.a / C.γ < C.D - 2 := by linarith
    rw [div_lt_iff₀ hγ] at this
    nlinarith
  have h1 : (N : ℝ) ^ C.a ≤ (N : ℝ) ^ (C.γ * ((C.D - 1 : ℕ) : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hN1 haD
  have h2 : (N : ℝ) ^ (C.γ * ((C.D - 1 : ℕ) : ℝ)) ≤ s ^ (C.D - 1) := by
    rw [Real.rpow_mul hN.le, Real.rpow_natCast]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hN.le _) hs.le _
  have hs0 : 0 ≤ s ^ (C.D - 1) := pow_nonneg ((Real.rpow_nonneg hN.le _).trans hs.le) _
  nlinarith

/-! ## The charged and orbit nodes -/

section Nodes

variable (C : ChargingConstants) {V : Type*} (T : PhaseTree V) (N : ℕ) (K : ℝ)

/-- Children of a charged node, by class and branch. -/
theorem mem_children_charged {v u : V} {cls : List (ChildClass V)}
    (hv : T.kind v = .charged cls) (hu : u ∈ (T.kind v).children) :
    ∃ c ∈ cls, ∃ b ∈ c.branches, u ∈ b := by
  rw [hv] at hu
  simp only [NodeKind.children] at hu
  obtain ⟨l, hl, hul⟩ := List.mem_flatten.mp hu
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hl
  obtain ⟨b, hb, hub⟩ := List.mem_flatten.mp hul
  exact ⟨c, hc, b, hb, hub⟩

theorem internal_six (hT : T.Hyp C N K) (hN6 : 6 ≤ (N : ℝ) ^ C.γ) {v : V}
    (hv : T.kind v ≠ .leaf) : 6 ≤ ((T.state v).s : ℝ) :=
  hN6.trans (hT.internal_large v hv).le

/-- A child of a charged node has potential at most the parent's minus its row's
decrease. -/
theorem charged_child_Φ_le (hT : T.Hyp C N K) (hN6 : 6 ≤ (N : ℝ) ^ C.γ) {v : V}
    {cls : List (ChildClass V)} (hv : T.kind v = .charged cls) {c : ChildClass V}
    (hc : c ∈ cls) {b : List V} (hb : b ∈ c.branches) {u : V} (hu : u ∈ b) :
    (T.state u).Φ C.A C.B ≤ (T.state v).Φ C.A C.B - c.row.drop C (T.state v) :=
  Row.child_Φ_le C (internal_six C T N K hT hN6 (by rw [hv]; simp))
    (hT.class_valid v cls hv c hc) (hT.branch_child v cls hv c hc b hb u hu)
    (hT.nonneg u).1 (hT.nonneg u).2.1

/-- A child of a pure orbit node has potential at most the credit (Section 7.3:
"Each child potential is at most the original orbit's credit"). -/
theorem orbit_child_Φ_le (hT : T.Hyp C N K) (hN6 : 6 ≤ (N : ℝ) ^ C.γ) {v : V}
    {cs : List V} (hv : T.kind v = .orbit cs) {u : V} (hu : u ∈ cs) :
    (T.state u).Φ C.A C.B ≤ (T.state v).Φ C.A C.B := by
  have h6 := internal_six C T N K hT hN6 (v := v) (by rw [hv]; simp)
  obtain ⟨hρ, hσ, hQ, hh⟩ := hT.orbit_child v cs hv u hu
  have hlt := (hT.orbit_pos v cs hv u hu).2
  have hTs : ((T.state u).s : ℝ) ≤ (T.state v).s := by exact_mod_cast hlt.le
  rcases hh with hh | ⟨hs2, hh⟩
  · -- The first largest child: nothing increases.
    have hh' : ((T.state u).h : ℝ) ≤ (T.state v).h := by exact_mod_cast hh
    have := PotentialState.Φ_le_of C.A_nonneg C.B_nonneg (hT.nonneg u).1 (hT.nonneg u).2.1
      (PotentialState.x_mono hTs) (PotentialState.x_mono hTs) hρ hσ hQ hh'
    simp only [PotentialState.Φ] at this ⊢; linarith
  · -- A later child: its domain is at most `s/2 ≤ θs`, and (main-domain-payment)
    -- pays the increase of `h`.
    have hθ : ((T.state u).s : ℝ) ≤ C.θ * (T.state v).s := by
      have : (2 : ℝ) * (T.state u).s ≤ (T.state v).s := by exact_mod_cast hs2
      nlinarith [C.half_lt_θ, (Nat.cast_nonneg _ : (0 : ℝ) ≤ (T.state v).s)]
    have hrow := Row.child_Φ_le C (R := .affected) h6 trivial ⟨hθ, hρ, hσ, hQ, hh⟩
      (hT.nonneg u).1 (hT.nonneg u).2.1
    have hpos := Row.log8J_le_drop C (R := .affected) h6 trivial
    have := C.log8J_pos
    linarith

/-- Equation `eq:main-charged-induction`: at a charged node,
`Σ_j W(S_j) ≤ W(S)/2` and `W(S) ≥ 2N^a`. -/
theorem eq_main_charged_induction (hT : T.Hyp C N K) (hN6 : 6 ≤ (N : ℝ) ^ C.γ)
    (hN2 : 2 ≤ (N : ℝ) ^ (C.γ * C.D - C.a)) {v : V} {cls : List (ChildClass V)}
    (hv : T.kind v = .charged cls) :
    (((T.kind v).children).map fun u => (T.state u).W C.A C.B C.D).sum ≤
      1 / 2 * (T.state v).W C.A C.B C.D ∧
    2 * (N : ℝ) ^ C.a ≤ (T.state v).W C.A C.B C.D := by
  set S := T.state v
  have h6 : 6 ≤ (S.s : ℝ) := internal_six C T N K hT hN6 (v := v) (by rw [hv]; simp)
  have hlarge : (N : ℝ) ^ C.γ < S.s := hT.internal_large v (by rw [hv]; simp)
  have hΦ0 : 0 ≤ S.Φ C.A C.B := PotentialState.Φ_nonneg C.A_nonneg C.B_nonneg
    (hT.nonneg v).1 (hT.nonneg v).2.1 (hT.nonneg v).2.2
  have hW0 : 0 ≤ S.W C.A C.B C.D := zero_le_one.trans (PotentialState.one_le_W hΦ0)
  have hJ : (0 : ℝ) < 8 * C.J := by
    have : (1 : ℝ) ≤ C.J := by exact_mod_cast C.one_le_J
    linarith
  let Wf : V → ℝ := fun u => (T.state u).W C.A C.B C.D
  -- One branch: at most `exp(-ΔΦ) W(S)`.
  have hbranch : ∀ c ∈ cls, ∀ b ∈ c.branches,
      (b.map Wf).sum ≤ Real.exp (-c.row.drop C S) * S.W C.A C.B C.D := by
    intro c hc b hb
    have := list_weight_sum_le C (b.map T.state) S (c.row.drop C S)
      (by
        intro U hU
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hU
        exact hT.branch_pos v cls hv c hc b hb u hu)
      (by
        have := hT.branch_disjoint v cls hv c hc b hb
        have h' : ((b.map fun u => (T.state u).s).sum : ℝ) ≤ S.s := by exact_mod_cast this
        simpa [Nat.cast_list_sum, List.map_map] using h')
      (by
        intro U hU
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hU
        exact charged_child_Φ_le C T N K hT hN6 hv hc hb hu)
    simpa [List.map_map] using this
  -- One class: at most `M exp(-ΔΦ) W(S) ≤ W(S)/(8J)`.
  have hclass : ∀ c ∈ cls, (c.branches.flatten.map Wf).sum ≤ S.W C.A C.B C.D / (8 * C.J) := by
    intro c hc
    rw [list_sum_map_flatten]
    have hm := Row.mult_mul_exp_neg_drop_le C hlarge h6 (hT.class_valid v cls hv c hc)
    have hlen := hT.class_mult v cls hv c hc
    calc (c.branches.map fun b => (b.map Wf).sum).sum
        ≤ c.branches.length * (Real.exp (-c.row.drop C S) * S.W C.A C.B C.D) :=
          list_sum_le_length_mul _ _ _ (hbranch c hc)
      _ ≤ c.row.mult C N * (Real.exp (-c.row.drop C S) * S.W C.A C.B C.D) :=
          mul_le_mul_of_nonneg_right hlen (mul_nonneg (Real.exp_pos _).le hW0)
      _ = (c.row.mult C N * Real.exp (-c.row.drop C S)) * S.W C.A C.B C.D := by ring
      _ ≤ 1 / (8 * C.J) * S.W C.A C.B C.D := mul_le_mul_of_nonneg_right hm hW0
      _ = S.W C.A C.B C.D / (8 * C.J) := by ring
  refine ⟨?_, ?_⟩
  · -- All classes: at most `J · W/(8J) = W/8 ≤ W/2`.
    have hsum : (((T.kind v).children).map Wf).sum =
        (cls.map fun c => (c.branches.flatten.map Wf).sum).sum := by
      rw [hv]; simp only [NodeKind.children]; rw [list_sum_map_flatten, List.map_map]; rfl
    have hcls : (cls.length : ℝ) ≤ C.J := by exact_mod_cast hT.classes_le v cls hv
    calc (((T.kind v).children).map Wf).sum
        ≤ cls.length * (S.W C.A C.B C.D / (8 * C.J)) := by
          rw [hsum]; exact list_sum_le_length_mul _ _ _ hclass
      _ ≤ C.J * (S.W C.A C.B C.D / (8 * C.J)) :=
          mul_le_mul_of_nonneg_right hcls (div_nonneg hW0 hJ.le)
      _ = S.W C.A C.B C.D / 8 := by
          have : (C.J : ℝ) ≠ 0 := by linarith
          field_simp
      _ ≤ 1 / 2 * S.W C.A C.B C.D := by linarith
  · exact (two_rpow_a_le C hN6 hN2 hlarge).trans (PotentialState.prefactor_le_W hΦ0)

/-- At a pure orbit node, (main-orbit-slack) supplies `W(S) - Σ_j W(S_j) ≥ N^a`. -/
theorem orbit_node_slack (hT : T.Hyp C N K) (hN6 : 6 ≤ (N : ℝ) ^ C.γ) {v : V}
    {cs : List V} (hv : T.kind v = .orbit cs) :
    (((T.kind v).children).map fun u => (T.state u).W C.A C.B C.D).sum + (N : ℝ) ^ C.a ≤
      (T.state v).W C.A C.B C.D := by
  set S := T.state v
  have h6 : 6 ≤ (S.s : ℝ) := internal_six C T N K hT hN6 (v := v) (by rw [hv]; simp)
  have hlarge : (N : ℝ) ^ C.γ < S.s := hT.internal_large v (by rw [hv]; simp)
  have hΦ0 : 0 ≤ S.Φ C.A C.B := PotentialState.Φ_nonneg C.A_nonneg C.B_nonneg
    (hT.nonneg v).1 (hT.nonneg v).2.1 (hT.nonneg v).2.2
  rw [hv]
  simp only [NodeKind.children]
  -- Sharper: the prefactors sum to at most `(s+1)^D + 3^D`.
  have hpre := list_orbit_prefactor_le C.three_le_D (cs.map T.state) (s := S.s)
    (by
      intro U hU
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hU
      exact hT.orbit_pos v cs hv u hu)
    (by
      have := hT.orbit_disjoint v cs hv
      have h' : ((cs.map fun u => (T.state u).s).sum : ℝ) ≤ S.s := by exact_mod_cast this
      simpa [Nat.cast_list_sum, List.map_map] using h')
  have hWsum : (cs.map fun u => (T.state u).W C.A C.B C.D).sum ≤
      (((S.s : ℝ) + 1) ^ C.D + 3 ^ C.D) * Real.exp (S.Φ C.A C.B) := by
    calc (cs.map fun u => (T.state u).W C.A C.B C.D).sum
        = ((cs.map T.state).map fun U => U.W C.A C.B C.D).sum := by rw [List.map_map]; rfl
      _ ≤ ((cs.map T.state).map fun U => ((U.s : ℝ) + 2) ^ C.D * Real.exp (S.Φ C.A C.B)).sum := by
          apply List.sum_le_sum
          intro U hU
          obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hU
          exact mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (orbit_child_Φ_le C T N K hT hN6 hv hu)) (by positivity)
      _ = ((cs.map T.state).map fun U => ((U.s : ℝ) + 2) ^ C.D).sum *
            Real.exp (S.Φ C.A C.B) := by rw [List.sum_map_mul_right]
      _ ≤ _ := mul_le_mul_of_nonneg_right hpre (Real.exp_pos _).le
  have hgap := eq_main_orbit_slack_gap C.three_le_D h6
  have hNa := rpow_a_le_slack C hN6 hlarge
  have he := Real.one_le_exp hΦ0
  have hbr : 0 ≤ ((S.s : ℝ) + 2) ^ C.D - ((S.s : ℝ) + 1) ^ C.D - 3 ^ C.D := by
    have : (0 : ℝ) ≤ (C.D / 2 : ℝ) * (S.s : ℝ) ^ (C.D - 1) := by positivity
    linarith
  have hmul := mul_le_mul_of_nonneg_left he hbr
  simp only [PotentialState.W] at hWsum ⊢
  nlinarith

end Nodes

/-! ## Lemma 7.1 -/

section Lemma

variable (C : ChargingConstants) {V : Type*} (T : PhaseTree V) (N : ℕ) (K : ℝ)

/-- The termination part of the proof of Lemma 7.1: "an infinite inherited path would
either have infinitely many uniform positive potential decreases, contradicting
`Φ ≥ 0`, or eventually consist only of strict domain decreases". The child relation
is well-founded, by the lexicographic measure `(⌊Φ/log(8J)⌋, s)`. -/
theorem phase_terminates (hT : T.Hyp C N K) (hN6 : 6 ≤ (N : ℝ) ^ C.γ) :
    WellFounded (fun u v => u ∈ (T.kind v).children) := by
  have hε := C.log8J_pos
  let μ : V → ℕ × ℕ := fun v => (⌊(T.state v).Φ C.A C.B / Real.log (8 * C.J)⌋₊, (T.state v).s)
  have hwf : WellFounded (InvImage (Prod.Lex (· < ·) (· < ·)) μ) :=
    InvImage.wf μ (WellFounded.prod_lex wellFounded_lt wellFounded_lt)
  refine Subrelation.wf ?_ hwf
  intro u v hu
  have hΦu : 0 ≤ (T.state u).Φ C.A C.B := PotentialState.Φ_nonneg C.A_nonneg C.B_nonneg
    (hT.nonneg u).1 (hT.nonneg u).2.1 (hT.nonneg u).2.2
  show Prod.Lex _ _ (μ u) (μ v)
  rw [Prod.lex_def]
  cases hk : T.kind v with
  | leaf => rw [hk] at hu; simp [NodeKind.children] at hu
  | charged cls =>
    -- A charged child: `Φ` drops by at least `ε`.
    left
    obtain ⟨c, hc, b, hb, hub⟩ := mem_children_charged T hk hu
    have h1 := charged_child_Φ_le C T N K hT hN6 hk hc hb hub
    have h2 := Row.log8J_le_drop C (internal_six C T N K hT hN6 (v := v) (by rw [hk]; simp))
      (hT.class_valid v cls hk c hc)
    have h3 : (T.state u).Φ C.A C.B / Real.log (8 * C.J) + 1 ≤ (T.state v).Φ C.A C.B / Real.log (8 * C.J) := by
      rw [div_add_one hε.ne', div_le_div_iff_of_pos_right hε]; linarith
    have h4 := Nat.floor_le_floor (R := ℝ) h3
    rw [Nat.floor_add_one (div_nonneg hΦu hε.le)] at h4
    show ⌊(T.state u).Φ C.A C.B / Real.log (8 * C.J)⌋₊ < ⌊(T.state v).Φ C.A C.B / Real.log (8 * C.J)⌋₊
    omega
  | orbit cs =>
    -- An orbit child: `Φ` does not increase and `s` decreases.
    rw [hk] at hu
    have h1 := orbit_child_Φ_le C T N K hT hN6 hk hu
    have h2 := (hT.orbit_pos v cs hk u hu).2
    have h4 := Nat.floor_le_floor (R := ℝ) (div_le_div_of_nonneg_right h1 hε.le)
    show ⌊(T.state u).Φ C.A C.B / Real.log (8 * C.J)⌋₊ < ⌊(T.state v).Φ C.A C.B / Real.log (8 * C.J)⌋₊ ∨
      ⌊(T.state u).Φ C.A C.B / Real.log (8 * C.J)⌋₊ = ⌊(T.state v).Φ C.A C.B / Real.log (8 * C.J)⌋₊ ∧
        (T.state u).s < (T.state v).s
    omega

/-- **Lemma 7.1** (`lem:main-phase-bound`, Weighted phase induction), for the abstract
model of one phase. With constants as in Section 7.5 and a phase size `N` above the
base size (`N^γ ≥ 6` and `N^{γD-a} ≥ 2`), the phase terminates, and every node `v`
(a transitive inherited state, or a conditional orbit forest with the original orbit's
credit) costs at most `K_N W(v)`, including its fresh oracle calls. Here
`K_N = exp(c_T (log(N+2))²)(1 + F(⌈N^γ⌉))` is the toll of `eq:main-phase-toll`. -/
theorem lem_main_phase_bound (cT : ℝ) (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n)
    (hN6 : 6 ≤ (N : ℝ) ^ C.γ) (hN2 : 2 ≤ (N : ℝ) ^ (C.γ * C.D - C.a))
    (hT : T.Hyp C N (phaseToll cT C.γ F N)) :
    WellFounded (fun u v => u ∈ (T.kind v).children) ∧
    ∀ v, T.cost v ≤ phaseToll cT C.γ F N * (T.state v).W C.A C.B C.D := by
  set K := phaseToll cT C.γ F N
  have hK : 0 ≤ K := mul_nonneg (Real.exp_pos _).le (by linarith [hF ⌈(N : ℝ) ^ C.γ⌉₊])
  have hwf := phase_terminates C T N K hT hN6
  refine ⟨hwf, fun v => hwf.induction (C := fun v => T.cost v ≤ K * (T.state v).W C.A C.B C.D)
    v ?_⟩
  intro v ih
  have hΦ0 : 0 ≤ (T.state v).Φ C.A C.B := PotentialState.Φ_nonneg C.A_nonneg C.B_nonneg
    (hT.nonneg v).1 (hT.nonneg v).2.1 (hT.nonneg v).2.2
  have hW1 := PotentialState.one_le_W (D := C.D) hΦ0
  -- The children's costs, by the induction hypothesis.
  have hchildren : (((T.kind v).children).map T.cost).sum ≤
      K * (((T.kind v).children).map fun u => (T.state u).W C.A C.B C.D).sum := by
    rw [← List.sum_map_mul_left]
    exact List.sum_le_sum (fun u hu => ih u hu)
  cases hk : T.kind v with
  | leaf =>
    -- "At a threshold leaf, `W ≥ 1` and the claimed bound follows from
    -- (main-phase-toll)."
    have := hT.leaf_cost v hk
    nlinarith
  | charged cls =>
    -- `T_N(S) ≤ K_N (N^a + Σ_j W(S_j)) ≤ K_N W(S)` by (main-charged-induction).
    have htoll := hT.toll v (by rw [hk]; simp)
    obtain ⟨h1, h2⟩ := eq_main_charged_induction C T N K hT hN6 hN2 hk
    have := mul_le_mul_of_nonneg_left h1 hK
    have := mul_le_mul_of_nonneg_left h2 hK
    nlinarith
  | orbit cs =>
    -- `W(S) - Σ_j W(S_j) ≥ N^a` by (main-orbit-slack).
    have htoll := hT.toll v (by rw [hk]; simp)
    have h1 := orbit_node_slack C T N K hT hN6 hk
    have := mul_le_mul_of_nonneg_left h1 hK
    nlinarith

end Lemma

/-! ## The phase root and a fresh phase -/

/-- The resources at a phase root, as listed in the proof of Lemma 7.1: "At a phase
root, `ρ = O(log N)`, `σ = O(log(N+2))`, `Q ≤ (log N)²`, and `h ≤ 2`". The constant
`cσ` is the one in Section 3.3 (i), `σ(G,Ω) = O(log(s+2))`. -/
structure RootBounds (cσ : ℝ) (N : ℕ) (S : PotentialState) : Prop where
  /-- an orbit of the fresh input is nonempty -/
  one_le_s : 1 ≤ S.s
  /-- a phase on `N` positions -/
  s_le_N : S.s ≤ N
  ρ_nonneg : 0 ≤ S.ρ
  /-- equation `eq:main-rho` -/
  ρ_le : S.ρ ≤ 2 * Real.logb 2 S.s
  σ_nonneg : 0 ≤ S.σ
  /-- Section 3.3 (i) -/
  σ_le : S.σ ≤ cσ * Real.log ((S.s : ℝ) + 2)
  Q_nonneg : 0 ≤ S.Q
  /-- equation `eq:main-Q` -/
  Q_le : S.Q ≤ Real.log S.s ^ 2
  /-- Section 6.1: `h ∈ {0,1,2}` -/
  h_le : S.h ≤ 2

/-- The potential at a phase root is `O((log(N+2))²)`. -/
theorem main_phase_root_potential (C : ChargingConstants) {cσ : ℝ} (hcσ : 0 ≤ cσ) :
    ∃ CΦ : ℝ, 0 ≤ CΦ ∧ ∀ (N : ℕ) (S : PotentialState), RootBounds cσ N S →
      S.Φ C.A C.B ≤ CΦ * Real.log ((N : ℝ) + 2) ^ 2 := by
  have hl2 := ChargingConstants.log_two_pos'
  refine ⟨C.A * (2 + 2 / Real.log 2 + cσ) + 2 * C.B / Real.log 2 ^ 2, by
    have := C.A_nonneg; have := C.B_nonneg; positivity, ?_⟩
  intro N S hS
  set L := Real.log ((N : ℝ) + 2)
  have hs1 : (1 : ℝ) ≤ S.s := by exact_mod_cast hS.one_le_s
  have hsN : (S.s : ℝ) ≤ N := by exact_mod_cast hS.s_le_N
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith)
  have hL0 : 0 ≤ L := hl2.le.trans hL2
  have hx0 := S.x_nonneg
  have hxL : S.x ≤ L := Real.log_le_log (by positivity) (by linarith)
  have hls0 : 0 ≤ Real.log S.s := Real.log_nonneg hs1
  have hlsL : Real.log S.s ≤ L := Real.log_le_log (by linarith) (by linarith)
  -- Each term of `Φ` is at most a constant times `L²`.
  have hρx : S.ρ * S.x ≤ 2 / Real.log 2 * L ^ 2 := by
    have h1 : S.ρ ≤ 2 / Real.log 2 * L := by
      have := hS.ρ_le
      rw [Real.logb] at this
      calc S.ρ ≤ 2 * (Real.log S.s / Real.log 2) := this
        _ ≤ 2 * (L / Real.log 2) := by gcongr
        _ = 2 / Real.log 2 * L := by ring
    calc S.ρ * S.x ≤ 2 / Real.log 2 * L * L :=
          mul_le_mul h1 hxL hx0 (by positivity)
      _ = _ := by ring
  have hσx : S.σ * S.x ≤ cσ * L ^ 2 := by
    calc S.σ * S.x ≤ cσ * S.x * L := mul_le_mul hS.σ_le hxL hx0 (mul_nonneg hcσ hx0)
      _ ≤ cσ * L * L := by gcongr
      _ = _ := by ring
  have hQ : S.Q ≤ L ^ 2 := hS.Q_le.trans (pow_le_pow_left₀ hls0 hlsL 2)
  have hx2 : S.x ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hx0 hxL 2
  have hh : (S.h : ℝ) ≤ 2 := by exact_mod_cast hS.h_le
  have hBh : C.B * S.h ≤ 2 * C.B / Real.log 2 ^ 2 * L ^ 2 := by
    have hL : 1 ≤ L ^ 2 / Real.log 2 ^ 2 := by
      rw [le_div_iff₀ (by positivity), one_mul]
      exact pow_le_pow_left₀ hl2.le hL2 2
    calc C.B * S.h ≤ C.B * 2 := mul_le_mul_of_nonneg_left hh C.B_nonneg
      _ ≤ C.B * 2 * (L ^ 2 / Real.log 2 ^ 2) := le_mul_of_one_le_right
          (by linarith [C.B_nonneg]) hL
      _ = _ := by ring
  have hsum : S.x ^ 2 + S.ρ * S.x + S.σ * S.x + S.Q ≤ (2 + 2 / Real.log 2 + cσ) * L ^ 2 := by
    linarith
  have := mul_le_mul_of_nonneg_left hsum C.A_nonneg
  unfold PotentialState.Φ
  nlinarith

/-- The proof of Lemma 7.1: "Thus `W ≤ exp(C₀ (log(N+2))²)` for a fixed `C₀`." -/
theorem main_phase_root_weight (C : ChargingConstants) {cσ : ℝ} (hcσ : 0 ≤ cσ) :
    ∃ C₀ : ℝ, ∀ (N : ℕ) (S : PotentialState), RootBounds cσ N S →
      S.W C.A C.B C.D ≤ Real.exp (C₀ * Real.log ((N : ℝ) + 2) ^ 2) := by
  obtain ⟨CΦ, _, hΦ⟩ := main_phase_root_potential C hcσ
  have hl2 := ChargingConstants.log_two_pos'
  refine ⟨C.D / Real.log 2 + CΦ, fun N S hS => ?_⟩
  set L := Real.log ((N : ℝ) + 2)
  have hsN : (S.s : ℝ) ≤ N := by exact_mod_cast hS.s_le_N
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)])
  have hpre : ((S.s : ℝ) + 2) ^ C.D ≤ Real.exp (C.D / Real.log 2 * L ^ 2) := by
    calc ((S.s : ℝ) + 2) ^ C.D ≤ ((N : ℝ) + 2) ^ C.D :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = Real.exp (C.D * L) := by
          rw [← Real.exp_log (by positivity : (0 : ℝ) < (N : ℝ) + 2), ← Real.exp_nat_mul]
      _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          have hD : (0 : ℝ) ≤ C.D := Nat.cast_nonneg _
          rw [div_mul_eq_mul_div, le_div_iff₀ hl2, pow_two, ← mul_assoc]
          have := mul_le_mul_of_nonneg_left hL2 (mul_nonneg hD (hl2.le.trans hL2))
          nlinarith
  unfold PotentialState.W
  rw [add_mul, Real.exp_add]
  exact mul_le_mul hpre (Real.exp_le_exp.mpr (hΦ N S hS)) (Real.exp_pos _).le (Real.exp_pos _).le

/-- The last claim of Lemma 7.1: "a fresh phase costs `exp(O((log N)²))(1+F(M_N))`".
A fresh (possibly intransitive) input on `N` positions initializes each original
orbit as a root, with disjoint domains; the phase costs at most its polynomial
initialization work plus the costs of the roots. -/
theorem lem_main_phase_bound_fresh (C : ChargingConstants) {cσ : ℝ} (hcσ : 0 ≤ cσ)
    (cT : ℝ) :
    ∃ C₁ : ℝ, ∀ (N : ℕ) (F : ℕ → ℝ), (∀ n, 0 ≤ F n) → 6 ≤ (N : ℝ) ^ C.γ →
      2 ≤ (N : ℝ) ^ (C.γ * C.D - C.a) →
      ∀ {V : Type} (T : PhaseTree V), T.Hyp C N (phaseToll cT C.γ F N) →
      ∀ (roots : List V) (phaseCost : ℝ),
        (∀ v ∈ roots, RootBounds cσ N (T.state v)) →
        (roots.map fun v => (T.state v).s).sum ≤ N →
        phaseCost ≤ (N : ℝ) ^ C.a * phaseToll cT C.γ F N + (roots.map T.cost).sum →
        phaseCost ≤ Real.exp (C₁ * Real.log ((N : ℝ) + 2) ^ 2) *
          (1 + F ⌈(N : ℝ) ^ C.γ⌉₊) := by
  obtain ⟨CΦ, _, hΦ⟩ := main_phase_root_potential C hcσ
  have hl2 := ChargingConstants.log_two_pos'
  refine ⟨cT + C.D / Real.log 2 + CΦ + 1 / Real.log 2, ?_⟩
  intro N F hF hN6 hN2 V T hT roots phaseCost hroots hsum hcost
  set L := Real.log ((N : ℝ) + 2)
  set K := phaseToll cT C.γ F N
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith)
  have hL0 : 0 < L := hl2.trans_le hL2
  have hK : 0 ≤ K := mul_nonneg (Real.exp_pos _).le (by linarith [hF ⌈(N : ℝ) ^ C.γ⌉₊])
  have hcostW := (lem_main_phase_bound C T N cT F hF hN6 hN2 hT).2
  -- The roots' weights: their prefactors sum to at most `(N+2)^D`.
  have hWroots : (roots.map fun v => (T.state v).W C.A C.B C.D).sum ≤
      ((N : ℝ) + 2) ^ C.D * Real.exp (CΦ * L ^ 2) := by
    calc (roots.map fun v => (T.state v).W C.A C.B C.D).sum
        = ((roots.map T.state).map fun S => S.W C.A C.B C.D).sum := by rw [List.map_map]; rfl
      _ ≤ ((roots.map T.state).map fun S => ((S.s : ℝ) + 2) ^ C.D *
            Real.exp (CΦ * L ^ 2)).sum := by
          apply List.sum_le_sum
          intro S hS
          obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hS
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hΦ N _ (hroots v hv)))
            (by positivity)
      _ = ((roots.map T.state).map fun S => ((S.s : ℝ) + 2) ^ C.D).sum *
            Real.exp (CΦ * L ^ 2) := by rw [List.sum_map_mul_right]
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          apply list_prefactor_sum_le C.three_le_D
          · intro S hS
            obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hS
            exact (hroots v hv).one_le_s
          · have h' : ((roots.map fun v => (T.state v).s).sum : ℝ) ≤ N := by
              exact_mod_cast hsum
            simpa [Nat.cast_list_sum, List.map_map] using h'
  -- The initialization work: `N^a ≤ (N+2)^D`, since `a < D`.
  have haD : C.a ≤ C.D := by
    have h := C.D_gt
    have : C.a ≤ C.a / C.γ := by
      rw [le_div_iff₀ C.γ_pos]; nlinarith [C.γ_lt_one, C.a_pos]
    linarith
  have hNa : (N : ℝ) ^ C.a ≤ ((N : ℝ) + 2) ^ C.D := by
    calc (N : ℝ) ^ C.a ≤ ((N : ℝ) + 2) ^ C.a :=
          Real.rpow_le_rpow hN0 (by linarith) C.a_pos.le
      _ ≤ ((N : ℝ) + 2) ^ (C.D : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) haD
      _ = _ := Real.rpow_natCast _ _
  have hpre : ((N : ℝ) + 2) ^ C.D ≤ Real.exp (C.D / Real.log 2 * L ^ 2) := by
    calc ((N : ℝ) + 2) ^ C.D = Real.exp (C.D * L) := by
          rw [← Real.exp_log (by positivity : (0 : ℝ) < (N : ℝ) + 2), ← Real.exp_nat_mul]
      _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          have hD : (0 : ℝ) ≤ C.D := Nat.cast_nonneg _
          rw [div_mul_eq_mul_div, le_div_iff₀ hl2, pow_two, ← mul_assoc]
          have := mul_le_mul_of_nonneg_left hL2 (mul_nonneg hD hL0.le)
          nlinarith
  have htwo : (2 : ℝ) ≤ Real.exp (1 / Real.log 2 * L ^ 2) := by
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hl2]
          nlinarith
  have hE : 1 ≤ Real.exp (CΦ * L ^ 2) := Real.one_le_exp (by positivity)
  -- Together: `N^a + Σ W ≤ (N+2)^D · 2 exp(CΦ L²)`.
  have hroot : (N : ℝ) ^ C.a + (roots.map fun v => (T.state v).W C.A C.B C.D).sum ≤
      Real.exp ((C.D / Real.log 2 + CΦ + 1 / Real.log 2) * L ^ 2) := by
    have hP0 : 0 ≤ ((N : ℝ) + 2) ^ C.D := by positivity
    calc (N : ℝ) ^ C.a + (roots.map fun v => (T.state v).W C.A C.B C.D).sum
        ≤ ((N : ℝ) + 2) ^ C.D * (2 * Real.exp (CΦ * L ^ 2)) := by nlinarith
      _ ≤ Real.exp (C.D / Real.log 2 * L ^ 2) *
            (Real.exp (1 / Real.log 2 * L ^ 2) * Real.exp (CΦ * L ^ 2)) := by
          apply mul_le_mul hpre _ (by positivity) (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have hcostroots : (roots.map T.cost).sum ≤
      K * (roots.map fun v => (T.state v).W C.A C.B C.D).sum := by
    rw [← List.sum_map_mul_left]
    exact List.sum_le_sum (fun v _ => hcostW v)
  calc phaseCost ≤ K * ((N : ℝ) ^ C.a + (roots.map fun v => (T.state v).W C.A C.B C.D).sum) := by
        nlinarith
    _ ≤ K * Real.exp ((C.D / Real.log 2 + CΦ + 1 / Real.log 2) * L ^ 2) :=
        mul_le_mul_of_nonneg_left hroot hK
    _ = _ := by
        simp only [K, phaseToll, L]
        rw [show (cT + ↑C.D / Real.log 2 + CΦ + 1 / Real.log 2) * Real.log (↑N + 2) ^ 2 =
          cT * Real.log (↑N + 2) ^ 2 +
            (↑C.D / Real.log 2 + CΦ + 1 / Real.log 2) * Real.log (↑N + 2) ^ 2 by ring,
          Real.exp_add]
        ring

/-! ## The recurrence (main-recurrence) -/

/-- The solution of equation `eq:main-recurrence`: if
`F(N) ≤ exp(C(log(N+2))²)(1 + F(⌈N^γ⌉))` above a base size, with `0 < γ < 1`, then
`F(N) ≤ exp(C'(log(N+2))²)` for all `N`. As in Section 7.4, the proof fixes
`γ < γ̂ < 1` and enlarges the base size so that
`log(⌈N^γ⌉+2) ≤ γ̂ log(N+2)`; the logarithmic contributions form a geometric series
with ratio `γ̂²`. The additive constants (the `1 +` and the values below the base
size) enlarge `C'`, as the paper says. -/
theorem main_recurrence_solution {γ C : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hC : 0 ≤ C)
    (F : ℕ → ℝ) (N₁ : ℕ)
    (hrec : ∀ N, N₁ ≤ N →
      F N ≤ Real.exp (C * Real.log ((N : ℝ) + 2) ^ 2) * (1 + F ⌈(N : ℝ) ^ γ⌉₊)) :
    ∃ C' : ℝ, ∀ N, F N ≤ Real.exp (C' * Real.log ((N : ℝ) + 2) ^ 2) := by
  set γh := (1 + γ) / 2 with hγh
  have hγh1 : γh < 1 := by rw [hγh]; linarith
  have hγh0 : 0 < γh := by rw [hγh]; linarith
  set r := γh ^ 2
  have hr1 : r < 1 := by simp only [r]; nlinarith
  -- Enlarge the base size: `n^{(1-γ)/2} ≥ 4` and `n ≥ 1`.
  have hev : ∀ᶠ n : ℕ in Filter.atTop, (4 : ℝ) ≤ (n : ℝ) ^ ((1 - γ) / 2) :=
    ((tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 4
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp hev
  set base := max N₁ (max N₂ 1)
  have hl2 := ChargingConstants.log_two_pos'
  -- The coefficient: the contraction condition and the values below the base size.
  set D := max ((C + Real.log 2) / (1 - r))
    (∑ n ∈ Finset.range base, Real.log (|F n| + 1) / Real.log 2 ^ 2)
  have hD1 : (C + Real.log 2) / (1 - r) ≤ D := le_max_left _ _
  have hD0 : 0 ≤ D := le_trans (div_nonneg (by linarith) (by linarith)) hD1
  refine ⟨D, GI.contracting_recurrence_bound F GI.logSquare (fun n => ⌈(n : ℝ) ^ γ⌉₊) base
    C D r hD0 (fun _ => sq_nonneg _) ?_ ?_ ?_⟩
  · -- `C + Dr + log 2 ≤ D`.
    have := (div_le_iff₀ (by linarith : (0 : ℝ) < 1 - r)).mp hD1
    nlinarith
  · -- Below the base size.
    intro n hn
    have hterm : Real.log (|F n| + 1) / Real.log 2 ^ 2 ≤ D := by
      refine le_trans ?_ (le_max_right _ _)
      exact Finset.single_le_sum (f := fun n => Real.log (|F n| + 1) / Real.log 2 ^ 2)
        (fun i _ => div_nonneg (Real.log_nonneg (by linarith [abs_nonneg (F i)]))
          (by positivity)) (Finset.mem_range.mpr hn)
    have hls : Real.log 2 ^ 2 ≤ GI.logSquare n := by
      unfold GI.logSquare
      exact pow_le_pow_left₀ hl2.le (Real.log_le_log (by norm_num)
        (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])) 2
    calc F n ≤ |F n| + 1 := by linarith [le_abs_self (F n)]
      _ = Real.exp (Real.log (|F n| + 1)) := (Real.exp_log (by positivity)).symm
      _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          have := mul_le_mul hterm hls (by positivity) hD0
          rwa [div_mul_cancel₀ _ (by positivity)] at this
  · -- Above the base size.
    intro n hn
    have hn1 : N₁ ≤ n := le_trans (le_max_left _ _) hn
    have hn2 : N₂ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
    have hn3 : 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
    have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn3
    have h4 := hN₂ n hn2
    have hnγ1 : (1 : ℝ) ≤ (n : ℝ) ^ γ := Real.one_le_rpow hN hγ0.le
    have hceil : (⌈(n : ℝ) ^ γ⌉₊ : ℝ) < (n : ℝ) ^ γ + 1 :=
      Nat.ceil_lt_add_one (by linarith)
    -- `⌈n^γ⌉ + 2 < n^γ + 3 ≤ 4 n^γ ≤ n^{γ̂} ≤ (n+2)^{γ̂}`.
    have hsplit : (n : ℝ) ^ γh = (n : ℝ) ^ ((1 - γ) / 2) * (n : ℝ) ^ γ := by
      rw [← Real.rpow_add (by linarith)]; congr 1; rw [hγh]; ring
    have hc1 : (⌈(n : ℝ) ^ γ⌉₊ : ℝ) + 2 ≤ (n : ℝ) ^ γh := by
      rw [hsplit]; nlinarith
    have hc2 : (n : ℝ) ^ γh ≤ ((n : ℝ) + 2) ^ γh :=
      Real.rpow_le_rpow (by linarith) (by linarith) hγh0.le
    have hc3 : (n : ℝ) ^ γh ≤ n := by
      calc (n : ℝ) ^ γh ≤ (n : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hN hγh1.le
        _ = n := Real.rpow_one _
    refine ⟨?_, ?_, ?_, hrec n hn1⟩
    · have : (⌈(n : ℝ) ^ γ⌉₊ : ℝ) < n := by linarith
      exact_mod_cast this
    · -- `log(n+2) ≥ log 3 ≥ 1`.
      unfold GI.logSquare
      have h3 : 1 ≤ Real.log ((n : ℝ) + 2) := by
        rw [Real.le_log_iff_exp_le (by positivity)]
        have := Real.exp_one_lt_d9
        linarith
      nlinarith
    · unfold GI.logSquare
      have hl0 : 0 ≤ Real.log ((⌈(n : ℝ) ^ γ⌉₊ : ℝ) + 2) := Real.log_nonneg (by
        have : (0 : ℝ) ≤ (⌈(n : ℝ) ^ γ⌉₊ : ℝ) := Nat.cast_nonneg _
        linarith)
      have hlog : Real.log ((⌈(n : ℝ) ^ γ⌉₊ : ℝ) + 2) ≤ γh * Real.log ((n : ℝ) + 2) := by
        rw [← Real.log_rpow (by positivity)]
        exact Real.log_le_log (by positivity) (hc1.trans hc2)
      have := pow_le_pow_left₀ hl0 hlog 2
      simp only [r]
      nlinarith

end GI.Paper
