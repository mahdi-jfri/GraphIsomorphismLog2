import Workspace.Algorithm.PhaseTree
import Workspace.Algorithm.DispatchInv
import Workspace.Algorithm.DispatchKeep
import Workspace.Algorithm.Counter
import Workspace.Algorithm.LabelData
import Workspace.Algorithm.CarrierSet
import Workspace.Algorithm.OrbitKeep

/-!
# Every state has a run (termination of the recursion)

`GI.Algorithm.Run` is an inductive relation, so Lemma 6.1 (`Run.exact`) is about the runs
that exist. Here we show that a run of `Solve` exists on every state of a finite position
set, once the subroutines supply their interface data.

## What is assumed

A `Supply` gives the case data of the states that the recursion reaches. These are the states
inside a phase (`N₀ < N`, `s ≤ N`) whose hierarchy satisfies the invariant `HierInv`
(`Workspace/Algorithm/HierInv.lean`: a tower of block systems of every orbit of the current
action, with upper-bound ratios and clamped bounds):

* `cont`: at a transitive `Continue` state above the threshold, off the column floor, the
  coarsest primitive quotient of the action, and the single-factor normalization for the
  case where the quotient is one alternating factor (Algorithm 5). The dispatcher
  (`PrimitiveQuotient.dispatch`, `Workspace/Algorithm/Dispatch.lean`) then decides between
  enumeration, product refinement and normalization; that these cases are exhaustive is
  Maróti's theorem (`GI.Cited.MarotiPrimitive`, a hypothesis) with `a ≥ 128`. This field is
  constructed (`Supply.ofGiant`, `Workspace/Algorithm/SupplyBuild.lean`);
* `giant`: at a transitive `GiantStep` state above the threshold, the supplied labels
  and one of the three branches: the row terminal, the column step (whose new hierarchy
  satisfies the invariant), or an aggregation round with `q ≥ q₀`. The recursive questions of
  the aggregation are asked on finite position sets.

The initial hierarchy of a fresh phase is not assumed: the hierarchy of all original orbits
(`orbitHier`, `exists_orbitHier`) is used. Every step of the recursion keeps the invariant
(`HierInv.mono`, `DispatchStep.hierInv`, `HierInv.capUpdate`), so a `Supply` only needs data on
invariant states. Before, `Supply` asked for case data on every state, and it was empty
(`Workspace/Algorithm/SupplyCheck.lean`).

The counter `h ≥ 1` at a column step is not assumed: it is proved from the invariant
`CounterInv` of the state (`column_step_counter`, Section 7.1 and Lemma A.29).

The parameters satisfy the inequalities of `Params.Terminating`, which the paper's
choices satisfy (Section 6: `1/3 < α`, `1 - α < 2α < γ < 1`; Lemma 5.1: `θ < 1`; Lemma 4.1:
`κ ≥ 5`; Lemma A.12: `β < 1`; Section 7.5 (i): `β q₀ ≥ 2`).

## The termination argument

The paper's argument is the potential decrease of Lemma 7.1 inside a phase ("an
infinite inherited path would either have infinitely many uniform positive potential
decreases, contradicting `Φ ≥ 0`, or eventually consist only of strict domain
decreases", `GI.Paper.phase_terminates`), together with the fresh-phase rule: a fresh
call has fewer than `N` positions. For the existence of a run only the order of the
resources matters, not the size of the decrease, so we use the lexicographic order of

`(N or s, [Solve], s, [transitive], σ, ρ, 3 [floor] + h, Σ c_i, [not giant])`

where the first entry is `s` for `Solve` and the phase size `N` otherwise. Each case of
Algorithms 4 and 5 decreases it:

* a fresh phase keeps the first entry and leaves `Solve`; the threshold, the row
  terminal and the configuration calls of an aggregation are fresh calls on fewer than
  `N` positions (`s ≤ N^γ`, `N^{1-α}`, `N^{2α}`);
* an orbit chain shrinks `s`;
* an enumeration child, a normalization child with an intransitive group, and an
  affected charged call with the same `s` are intransitive;
* an unaffected charged call decreases `σ` by `κ`; a product refinement decreases `ρ`;
* a floor reset clears the floor mode; the column step decreases `h`;
* a continuation of an aggregation round lowers one interval bound from at least `q`
  to `min{c, ⌊βq⌋}`;
* a transitive normalization child is a `GiantStep` with the same resources.

The free bookkeeping of a child (row record, floor mode, counter, where the recursion
does not fix them) is copied from the parent. A child on the same domain keeps it
(`State.restrict`). A child on a smaller domain keeps it when the counter invariant still
holds, and otherwise resets it to no rows and `h = 2` (`State.inherit`).

## Result

`GI.Algorithm.exists_run_solve`: for every state `S` on a finite type there is a run
`Run P .solve S none S.answer`. With `Run.exact` (Lemma 6.1) every run returns `S.answer`.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm
open scoped Pointwise

/-! ### Scripts -/

namespace Script

variable {α : Type}

theorem CallsExact.mono {p q : ∀ {Ω' C' : Type}, Mode → State Ω' C' → Prop}
    (hpq : ∀ {Ω' C' : Type} (m : Mode) (T : State Ω' C'), p m T → q m T) :
    ∀ {s : Script α}, s.CallsExact p → s.CallsExact q
  | .done _, _ => trivial
  | .ask m T _, h => ⟨hpq m T h.1, CallsExact.mono hpq h.2⟩

theorem CallsExact.and {p q : ∀ {Ω' C' : Type}, Mode → State Ω' C' → Prop} :
    ∀ {s : Script α}, s.CallsExact p → s.CallsExact q →
      s.CallsExact fun m T => p m T ∧ q m T
  | .done _, _, _ => trivial
  | .ask _ _ _, h, h' => ⟨⟨h.1, h'.1⟩, CallsExact.and h.2 h'.2⟩

end Script

/-- A script runs, with its exact value, when each of its calls along the exact answers
has a run with the exact answer. -/
theorem Exec.exists_exact {P : Params} {α : Type} :
    ∀ (s : Script α), s.CallsExact (fun m T => Nonempty (Run P m T none T.answer)) →
      Nonempty (Exec P s s.evalExact)
  | .done a, _ => ⟨Exec.done a⟩
  | .ask _ T k, h => by
    obtain ⟨⟨r⟩, hk⟩ := h
    obtain ⟨e⟩ := Exec.exists_exact (k T.answer) hk
    exact ⟨Exec.ask r e⟩

/-- A run returns the exact answer (Lemma 6.1), so it can be restated with that answer. -/
theorem Run.nonempty_answer {P : Params} {m : Mode} {Ω C : Type} {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)} (r : Run P m S L A) :
    Nonempty (Run P m S L S.answer) :=
  ⟨r.exact ▸ r⟩

/-! ### The data that the recursion needs -/

/-- The parameter inequalities used for termination. The paper's choices satisfy them:
`1/3 < α` and `1 - α < 2α < γ < 1` (Section 6, eq. `scale-constraints`; `1/3 < α` is used by
the counter at a column step, Section 6, eq. `promotion-product`), `θ < 1` (the domain fraction
of Lemma 5.1), `κ ≥ 5` (Lemma 4.1), `β < 1` (Lemma A.12), `β q₀ ≥ 2` (Section 7.5 (i),
so `q₀ ≥ 1`), and a base size `N₀ ≥ 1`. -/
structure Params.Terminating (P : Params) : Prop where
  N₀_pos : 1 ≤ P.N₀
  γ_lt : P.γ < 1
  α_pos : 0 < P.α
  third_lt_α : 1 / 3 < P.α
  two_α_lt : 2 * P.α < 1
  θ_lt : P.θ < 1
  κ_five : 5 ≤ P.κ
  β_lt : P.β < 1
  q₀_pos : 1 ≤ P.q₀

/-- The step of a transitive `Continue` state above the threshold and off the column
floor (Algorithm 5): a dispatcher reduction ("if enumeration or a product refinement
applies"), or the single-factor normalization of a primitive quotient that fails the integer
small test (`PrimitiveQuotient.SmallZ`) and is not a product with at least two coordinates. -/
inductive ContStep (P : Params) {Ω C : Type} [Finite Ω] (S : State Ω C) : Type 1
  | dispatch (I : DispatchStep P S)
  | normalize (Q : PrimitiveQuotient S) (hs : ¬ Q.SmallZ P.smallExp) (hp : ¬ Q.ProductCase)
      (h : Q.SingleFactor) (hq : P.q₀ < (Q.normalization h).q) (hkc : Q.KillsCols)
      (hkl : Q.KeepsLevels)

/-- The case data of a transitive `Continue` state above the threshold and off the
column floor: the coarsest primitive quotient of the action (Section A.5, "Selection of
the quotient and its cap"), and, when the quotient is a single factor and fails the integer
small test, the fact that the normalized degree is above `q₀` (Section A.3: "When `m ≤ q₀`, enumerate the
alternating quotient at its actual Cameron block level"). The normalization itself is the one
of the quotient (`PrimitiveQuotient.normAbove`), whose labels carry the data of the Cameron
constituent. -/
inductive ContCase (P : Params) {Ω C : Type} [Finite Ω] (S : State Ω C) : Type 1
  | quotient (Q : PrimitiveQuotient S) (hkc : Q.KillsCols) (hkl : Q.KeepsLevels)
      (hq : ∀ (_ : ¬ Q.SmallZ P.smallExp) (h : Q.SingleFactor), P.q₀ < (Q.normalization h).q)

/-- **The dispatcher** (Algorithm 5) on the case data: enumerate a small quotient, refine a
product with at least two coordinates, or normalize a single factor
(`PrimitiveQuotient.dispatch`). -/
noncomputable def ContCase.step {P : Params} {Ω C : Type} [Finite Ω] {S : State Ω C}
    (hM : GI.Cited.MarotiPrimitive) (ha : 128 ≤ P.a) (htr : S.Transitive) :
    ContCase P S → ContStep P S
  | .quotient Q hkc hkl norm =>
    match Q.dispatch hM P ha htr (Q.kernel_keeps hkc hkl) (Q.productRed_keeps P hkc hkl) with
    | .step I => .dispatch I
    | .single hs hp h => .normalize Q hs hp h (norm hs h) hkc hkl

/-- The case data of a transitive `GiantStep` state above the threshold with the supplied
labels `L` (Algorithms 4 and 5, `GiantStep(S, Γ)`: "Put `q ← |Γ|` for the supplied alternating
label set"): the row terminal, the column step (whose new hierarchy satisfies the hierarchy
invariant), or an aggregation round. The recursive questions of the aggregation are asked on
finite position sets. The data of the row terminal and of the column step are those of
Theorems A.17, A.18 and A.23 and of Lemma A.14 (`Workspace/Algorithm/RowSteps.lean`).

An aggregation round uses the interval and the constituent data that the supplied labels carry
(`hsel`, `hcon`; Section 7.2: "the selected alternating section belongs to that whole
constituent"). -/
inductive GiantCase (P : Params) {Ω C : Type} (S : State Ω C) (L : SuppliedLabels S) : Type 1
  | terminal (hrow : RowCase P.α S L.toGiantLabels) (I : RowTerminal P S L.toGiantLabels)
  | columns (hrow : RowCase P.α S L.toGiantLabels) (I : ColumnStep S L.toGiantLabels)
      (hinv : HierInv S.G S.dom I.hier')
  | aggregate (hnot : ¬ RowCase P.α S L.toGiantLabels) (I : Aggregation P S L.toGiantLabels)
      (hsel : I.sel.val = L.sel.val) (hcon : I.con = L.con)
      (fin : I.script.CallsExact fun {Ω' _} _ _ => Finite Ω')

/-- **The cap update of an aggregation round is valid** (`LiftAndContinue`: "It replaces the
selected interval bound by the minimum of its old value and `βq`"). The group of a continuation
is `π⁻¹(E₀)` with `aw(E₀) ≤ βq` (`Aggregation.overs_cap`). An element of the kernel of `π` fixes
every fine class of the selected interval (`SuppliedLabels.sel_ker`). So every alternating
section of the constituent of the selected interval is a section of `E₀`, and `⌊βq⌋` bounds it. -/
theorem Aggregation.child_hierInv {P : Params} {Ω C : Type} [Finite Ω] {S : State Ω C}
    {L : SuppliedLabels S} (I : Aggregation P S L.toGiantLabels) (hsel : I.sel.val = L.sel.val)
    (hinv : S.HierInv) {o : Perm Ω × Subgroup (Perm Ω)} (ho : o ∈ I.script.evalExact.overs) :
    HierInv o.2 S.dom (I.newHier o) := by
  obtain ⟨σ, E₀, hE, rfl⟩ := I.overs_cap o ho
  have hle := L.toGiantLabels.lift_le E₀
  have h1 : HierInv (L.toGiantLabels.lift E₀) S.dom S.hier := HierInv.mono hinv hle subset_rfl
  refine HierInv.capUpdate (P := P) (q := L.q) I.sel h1 fun a _ U hU _ t ht φ hφ hk => ?_
  have hUG : U ≤ S.G := hU.trans hle
  let p : U →* E₀ := (L.π.comp (Subgroup.inclusion hUG)).codRestrict E₀ fun u =>
    ((L.toGiantLabels.mem_lift).1 (hU u.2)).2
  refine GI.SectionCaps.quotient_degree_le hE ht p φ hφ fun u hu => ?_
  have hπ : L.π (Subgroup.inclusion hUG u) = 1 := congrArg Subtype.val hu
  have hfix := (L.sel_ker _).1 hπ
  refine hk u fun w hw => ?_
  have := hfix w hw.1
  rwa [← hsel] at this

/-- **The subroutine data**: for each state that the recursion reaches, what its case of
Algorithms 4 and 5 needs. A reached state lies inside a phase (above the base size, with at most
`N` positions) and its hierarchy satisfies the invariant `HierInv`. -/
structure Supply (P : Params) : Type 1 where
  /-- The case of a transitive `Continue` state above the threshold, off the floor. -/
  cont : ∀ {Ω C : Type} [Finite Ω] (S : State Ω C), S.HierInv → P.N₀ < S.N → S.size ≤ S.N →
    S.Transitive → (S.N : ℝ) ^ P.γ < S.size → ¬ S.FloorEntered → ContCase P S
  /-- The case of a transitive `GiantStep` state above the threshold, with supplied labels
  `L` on `q > q₀` points that carry their constituent data. -/
  giant : ∀ {Ω C : Type} [Finite Ω] (S : State Ω C), S.HierInv → P.N₀ < S.N → S.size ≤ S.N →
    S.Transitive → (S.N : ℝ) ^ P.γ < S.size → (L : SuppliedLabels S) → P.q₀ < L.q →
      GiantCase P S L

/-! ### The measure -/

section Measure

variable {Ω C : Type}

/-- `ρ` as a natural number: `Σ (2⌊log₂ d_i⌋ - 1)` over the nontrivial ratios. -/
def rhoNat (l : List (Interval Ω)) : ℕ := (l.map fun I => (GI.towerRank I.ratio).toNat).sum

/-- The sum of the interval bounds `Σ c_i`. -/
def capSum (l : List (Interval Ω)) : ℕ := (l.map Interval.cap).sum

theorem rhoNat_cast (l : List (Interval Ω)) : (rhoNat l : ℝ) = State.hierRho l := by
  unfold rhoNat State.hierRho
  induction l with
  | nil => simp
  | cons I l ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]
    congr 1
    have h := Int.toNat_of_nonneg (GI.tower_rank_nonneg I.ratio)
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h

theorem capSum_cast (l : List (Interval Ω)) :
    (capSum l : ℝ) = (l.map fun I => (I.cap : ℝ)).sum := by
  unfold capSum
  induction l with
  | nil => simp
  | cons I l ih => simp [ih]

open Classical in
/-- `1` for a transitive state, `0` otherwise. -/
noncomputable def trInd (S : State Ω C) : ℕ := if S.Transitive then 1 else 0

open Classical in
/-- `1` in fixed-floor mode, `0` otherwise. -/
noncomputable def flInd (S : State Ω C) : ℕ := if S.floor then 1 else 0

theorem trInd_le (S : State Ω C) : trInd S ≤ 1 := by unfold trInd; split_ifs <;> omega

theorem trInd_of (S : State Ω C) (h : S.Transitive) : trInd S = 1 := by simp [trInd, h]

theorem trInd_of_not (S : State Ω C) (h : ¬ S.Transitive) : trInd S = 0 := by simp [trInd, h]

/-- The first entry: `s` for `Solve`, the phase size `N` otherwise. -/
noncomputable def major : Mode → State Ω C → ℕ
  | .solve, S => S.size
  | .cont, S => S.N
  | .giant, S => S.N

/-- `1` for `Solve`. -/
def solveInd : Mode → ℕ
  | .solve => 1
  | _ => 0

/-- `0` for `GiantStep`, `1` otherwise. -/
def stageInd : Mode → ℕ
  | .giant => 0
  | _ => 1

/-- **The termination measure** of a call `m` on `S`. -/
noncomputable def measure (P : Params) (m : Mode) (S : State Ω C) :
    ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  (major m S, solveInd m, S.size, trInd S, S.sigma P.κ, rhoNat S.hier,
    3 * flInd S + S.h, capSum S.hier, stageInd m)

end Measure

/-- The lexicographic order on the measure. -/
def MLt : (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) → (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) → Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·)
    (Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))))))))

theorem MLt_wf : WellFounded MLt := by
  unfold MLt
  repeat (first | exact wellFounded_lt | apply WellFounded.prod_lex wellFounded_lt)

theorem mlt_iff (a b : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : MLt a b ↔
    a.1 < b.1 ∨ a.1 = b.1 ∧ (a.2.1 < b.2.1 ∨ a.2.1 = b.2.1 ∧ (a.2.2.1 < b.2.2.1 ∨
    a.2.2.1 = b.2.2.1 ∧ (a.2.2.2.1 < b.2.2.2.1 ∨ a.2.2.2.1 = b.2.2.2.1 ∧
    (a.2.2.2.2.1 < b.2.2.2.2.1 ∨ a.2.2.2.2.1 = b.2.2.2.2.1 ∧
    (a.2.2.2.2.2.1 < b.2.2.2.2.2.1 ∨ a.2.2.2.2.2.1 = b.2.2.2.2.2.1 ∧
    (a.2.2.2.2.2.2.1 < b.2.2.2.2.2.2.1 ∨ a.2.2.2.2.2.2.1 = b.2.2.2.2.2.2.1 ∧
    (a.2.2.2.2.2.2.2.1 < b.2.2.2.2.2.2.2.1 ∨ a.2.2.2.2.2.2.2.1 = b.2.2.2.2.2.2.2.1 ∧
    a.2.2.2.2.2.2.2.2 < b.2.2.2.2.2.2.2.2))))))) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := a
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := b
  simp only [MLt, Prod.lex_def]

/-! ### Facts used by the cases -/

section Facts

variable {P : Params} {Ω C : Type}

theorem rpow_lt_self {N : ℕ} (hN : 2 ≤ N) {e : ℝ} (he : e < 1) : (N : ℝ) ^ e < N := by
  have h1 : (1 : ℝ) < N := by exact_mod_cast hN
  calc (N : ℝ) ^ e < (N : ℝ) ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt h1 he
    _ = N := Real.rpow_one _

/-- A size at most `N^e` with `e < 1` is smaller than the phase size `N ≥ 2`. -/
theorem size_lt_of_rpow {N s : ℕ} (hN : 2 ≤ N) {e : ℝ} (he : e < 1) (hs : (s : ℝ) ≤ (N : ℝ) ^ e) :
    s < N := by
  have := hs.trans_lt (rpow_lt_self hN he)
  exact_mod_cast this

theorem size_pos_of_large {S : State Ω C} {γ : ℝ} (hs : (S.N : ℝ) ^ γ < S.size) :
    0 < S.size := by
  have h0 : (0 : ℝ) ≤ (S.N : ℝ) ^ γ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  exact_mod_cast h0.trans_lt hs

/-- On a transitive state, an orbit of a point of the domain has at least `s` points. -/
theorem size_le_orb [Finite Ω] {S : State Ω C} (htr : S.Transitive) {v : Ω} (hv : v ∈ S.dom) :
    S.size ≤ Nat.card (orb S.G v) := by
  change Nat.card S.dom ≤ _
  simp only [Nat.card_coe_set_eq]
  exact Set.ncard_le_ncard (transitive_orb_subset htr v hv) (Set.toFinite _)

/-- An intransitive finite domain that is nonempty has a largest orbit. -/
theorem exists_largestOrbit [Finite Ω] (S : State Ω C) (hne : S.dom.Nonempty) :
    ∃ D₁, S.LargestOrbit D₁ := by
  classical
  have hfin : S.dom.Finite := Set.toFinite _
  obtain ⟨a, ha, hmax⟩ := Set.exists_max_image S.dom (fun v => Nat.card (orb S.G v)) hfin hne
  exact ⟨orb S.G a, orb_subset S.dom_inv ha, ⟨a, ha, rfl⟩, fun b hb => hmax b hb⟩

/-- A cap update lowers the sum of the bounds: the selected bound `c ≥ q` becomes
`min{c, ⌊βq⌋} < q`, since `β < 1` and `q ≥ 1`. -/
theorem CapUpdate.capSum_lt {l l' : List (Interval Ω)} {q : ℕ} (h : CapUpdate P l q l')
    (hβ : P.β < 1) (hq : 1 ≤ q) : capSum l' < capSum l := by
  obtain ⟨i, hqc, -, rfl⟩ := h
  have hset := sum_map_set (fun I : Interval Ω => (I.cap : ℝ)) l i i.2
    ⟨l[i].part, l[i].ratio, min l[i].cap ⌊P.β * q⌋₊, l[i].origin⟩
  have hfl : ⌊P.β * q⌋₊ < q := by
    rw [Nat.floor_lt' (by omega)]
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith
  have hmin : min l[i].cap ⌊P.β * q⌋₊ < l[i].cap := by omega
  have hmin' : ((min l[i].cap ⌊P.β * q⌋₊ : ℕ) : ℝ) < (l[i].cap : ℝ) := by exact_mod_cast hmin
  have : (capSum (l.set i ⟨l[i].part, l[i].ratio, min l[i].cap ⌊P.β * q⌋₊, l[i].origin⟩) : ℝ) <
      capSum l := by
    rw [capSum_cast, capSum_cast]
    simp only [Fin.getElem_fin] at hset hmin' ⊢
    linarith
  exact_mod_cast this

end Facts

/-! ### Building children -/

namespace State

variable {Ω C : Type}

/-- The floor reset: the same core, hierarchy and phase, no row record, `h = 2`. -/
def floorCleared (S : State Ω C) : State Ω C :=
  ⟨S.G, S.dom, S.dom_inv, S.x, S.y, S.hier, none, false, 2, le_rfl, S.N,
    CounterInv.reset _ _ _ _,
    CarrierOK.none _ _ _⟩

end State

/-! ### Existence -/

section Exists

variable {P : Params}

/-- Unfold the measure and compare it entry by entry. -/
macro "mlt_tac" : tactic => `(tactic| (rw [mlt_iff]; simp only [measure, major, solveInd,
  stageInd, true_and, lt_self_iff_false, false_or]; omega))

/-- What a call needs: nothing for `Solve`; for `Continue`, a phase size above the base
size, a domain of at most `N` points (a phase starts on `N` positions and its domains
only shrink) and the hierarchy invariant; for `GiantStep` also a transitive group and a size
above the threshold, and labels to call it with. -/
def Good (P : Params) {Ω C : Type} : Mode → State Ω C → Prop
  | .solve, _ => True
  | .cont, S => P.N₀ < S.N ∧ S.size ≤ S.N ∧ S.HierInv
  | .giant, S => P.N₀ < S.N ∧ S.size ≤ S.N ∧ S.Transitive ∧ (S.N : ℝ) ^ P.γ < S.size ∧
      S.HierInv ∧ Nonempty {L : SuppliedLabels S // P.q₀ < L.q}

/-- What a call with the label index `L` needs (`Good`, with the labels of the call): no labels
for `Solve` and `Continue`, and for `GiantStep` supplied labels on more than `q₀` points. -/
def GoodL (P : Params) {Ω C : Type} : (m : Mode) → (S : State Ω C) →
    Option (SuppliedLabels S) → Prop
  | .solve, _, L => L = none
  | .cont, S, L => L = none ∧ P.N₀ < S.N ∧ S.size ≤ S.N ∧ S.HierInv
  | .giant, S, L => P.N₀ < S.N ∧ S.size ≤ S.N ∧ S.Transitive ∧ (S.N : ℝ) ^ P.γ < S.size ∧
      S.HierInv ∧ ∃ L' : SuppliedLabels S, L = some L' ∧ P.q₀ < L'.q

theorem exists_run_aux (hP : P.Terminating) (hM : GI.Cited.MarotiPrimitive) (ha : 128 ≤ P.a)
    (Su : Supply P) :
    ∀ k, ∀ {Ω C : Type} [Finite Ω] (m : Mode) (S : State Ω C) (L : Option (SuppliedLabels S)),
      GoodL P m S L → measure P m S = k → Nonempty (Run P m S L S.answer) := by
  intro k
  induction k using MLt_wf.induction with
  | _ k ih =>
  intro Ω C _ m S L hgood hk
  subst hk
  -- The induction hypothesis, for calls of smaller measure.
  have IH : ∀ {Ω' C' : Type} [Finite Ω'] (m' : Mode) (T : State Ω' C')
      (L' : Option (SuppliedLabels T)), GoodL P m' T L' →
      MLt (measure P m' T) (measure P m S) → Nonempty (Run P m' T L' T.answer) :=
    fun m' T L' hg hlt => ih _ hlt m' T L' hg rfl
  have hκ := hP.κ_five
  cases m with
  | solve =>
    subst hgood
    by_cases hs : S.size ≤ P.N₀
    · exact ⟨Run.direct S hs⟩
    · -- A fresh phase.
      push Not at hs
      have hne : S.dom.Nonempty := by
        have h0 : 0 < Nat.card S.dom := by change 0 < S.size; omega
        obtain ⟨⟨v, hv⟩⟩ := Nat.card_pos_iff.1 h0 |>.1
        exact ⟨v, hv⟩
      -- The hierarchy of all original orbits (Algorithm 5: "Initialize each original orbit's
      -- hierarchy and interval bounds").
      obtain ⟨M, hT, hH⟩ := exists_orbitHier S.domGroup (D := Set.univ) (fun _ _ _ => by simp) (by
        obtain ⟨v, hv⟩ := hne
        exact ⟨⟨v, hv⟩, trivial⟩)
      let S' : State S.dom C := S.freshOn (orbitHier S.domGroup M)
      have hS' : S.FreshOf S' := S.freshOn_freshOf hT hH
      have hN' : S'.N = S.size := rfl
      have hsz' : S'.size = S.size := hS'.size_eq
      obtain ⟨r⟩ := IH .cont S' none ⟨rfl, show P.N₀ < S'.N from hN' ▸ hs, by omega,
        hS'.hierInv⟩ (by
        rw [mlt_iff]
        simp only [measure, major, solveInd]
        omega)
      exact (Run.fresh hs hS' r).nonempty_answer
  | cont =>
    obtain ⟨rfl, hN, hsN, hhi⟩ := hgood
    have hN2 : 2 ≤ S.N := by have := hP.N₀_pos; omega
    by_cases hth : (S.size : ℝ) ≤ (S.N : ℝ) ^ P.γ
    · -- The threshold: a fresh call on fewer than `N` positions.
      have hlt := size_lt_of_rpow hN2 hP.γ_lt hth
      obtain ⟨r⟩ := IH .solve S none rfl (by mlt_tac)
      exact ⟨Run.threshold hth r⟩
    push Not at hth
    have hpos := size_pos_of_large hth
    by_cases htr : S.Transitive
    swap
    · -- The orbit chain.
      obtain ⟨D₁, hD₁⟩ := exists_largestOrbit S (dom_nonempty_of_large hth)
      let S₁ := S.inherit S.G D₁ hD₁.invariant S.x S.y
      have hsz₁ : S₁.size < S.size := LargestOrbit.size_lt htr hD₁ (State.inherit_dom _ _ _ _ _ _)
      have hN₁ : S₁.N = S.N := State.inherit_N _ _ _ _ _ _
      have hinv₁ : S₁.HierInv := by
        show HierInv S₁.G S₁.dom S₁.hier
        rw [State.inherit_G, State.inherit_dom, State.inherit_hier]
        exact HierInv.mono hhi le_rfl hD₁.subset
      obtain ⟨r₁⟩ := IH .cont S₁ none ⟨rfl, hN₁ ▸ hN, by omega, hinv₁⟩ (by mlt_tac)
      have hb₁ : S₁.book = S.orbitBook D₁ :=
        S.inherit_book hD₁.invariant hD₁.subset hD₁.nonempty _ _
      by_cases hA : S₁.answer = ∅
      · exact (Run.orbitStop hth htr hD₁ (S.inherit_inst _ _ _ _ _) hN₁
          (State.inherit_hier _ _ _ _ _ _) hb₁ (hA ▸ r₁)).nonempty_answer
      · obtain ⟨t, ht⟩ := Set.nonempty_iff_ne_empty.2 hA
        have hinv : Invariant (autGroup S.G D₁ hD₁.invariant S.x) (S.dom \ D₁) :=
          (S.dom_inv.diff hD₁.invariant).mono (autGroup_le _ _ _ _)
        let S₂ := S.resetChild (autGroup S.G D₁ hD₁.invariant S.x) (S.dom \ D₁) hinv S.x (S.y ∘ t)
        have hsz := orbitChain_sizes (S₁ := S₁) (S₂ := S₂) htr hD₁
          (State.inherit_dom _ _ _ _ _ _) rfl
        have hN₂ : S₂.N = S.N := rfl
        have hinv₂ : S₂.HierInv := by
          show HierInv (autGroup S.G D₁ hD₁.invariant S.x) (S.dom \ D₁) S.hier
          exact HierInv.mono hhi (autGroup_le _ _ _ _) Set.diff_subset
        obtain ⟨r₂⟩ := IH .cont S₂ none ⟨rfl, hN₂ ▸ hN, by omega, hinv₂⟩ (by mlt_tac)
        exact (Run.orbitChain hth htr hD₁ (S.inherit_inst _ _ _ _ _) hN₁
          (State.inherit_hier _ _ _ _ _ _) hb₁ r₁ t ht (S.resetChild_inst _ _ _ _ _) hN₂
          rfl rfl r₂).nonempty_answer
    have htr1 := trInd_of S htr
    by_cases hfl : S.FloorEntered
    · -- The floor reset.
      let S' : State Ω C := S.floorCleared
      have hfl1 : flInd S = 1 := by simp [flInd, hfl.1]
      have hfl0 : flInd S' = 0 := by simp [flInd, S', State.floorCleared]
      have htr' : trInd S' = 1 := trInd_of S' htr
      have hh := S.h_le
      have h1 : S'.N = S.N := rfl
      have h2 : S'.size = S.size := rfl
      have h3 : S'.sigma P.κ = S.sigma P.κ := rfl
      have h4 : rhoNat S'.hier = rhoNat S.hier := rfl
      have h5 : S'.h = 2 := rfl
      obtain ⟨r⟩ := IH .cont S' none ⟨rfl, hN, hsN, hhi⟩ (by mlt_tac)
      exact ⟨Run.floorReset (S' := S') hth htr hfl ⟨rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl r⟩
    match (Su.cont S hhi hN hsN htr hth hfl).step hM ha htr with
    | .dispatch I =>
      let child : Fin I.n → State Ω C := fun j =>
        S.restrict I.K I.K_le S.x (S.y ∘ I.τ j) I.hier'
      have hdrop : ∀ j, MLt (measure P .cont (child j)) (measure P .cont S) := by
        intro j
        have hσ : (child j).sigma P.κ ≤ S.sigma P.κ := State.sigma_le_of hκ I.K_le le_rfl
        have htrj := trInd_le (child j)
        have hsz : (child j).size = S.size := rfl
        have hNj : (child j).N = S.N := rfl
        rw [mlt_iff]
        simp only [measure, major, solveInd, stageInd, true_and, lt_self_iff_false, false_or]
        cases hkind : I.kind with
        | enumeration d =>
          have hf := I.facts
          rw [hkind] at hf
          obtain ⟨hd2, -, -, -, hdorb⟩ := hf
          -- The child is intransitive: its orbits have at most `s/d` points.
          have hnt : ¬ (child j).Transitive := by
            intro htj
            obtain ⟨v, hv⟩ := dom_nonempty_of_large hth
            have h1 := size_le_orb htj hv
            have h2 := hdorb v hv
            change S.size ≤ Nat.card (orb I.K v) at h1
            have : 2 * S.size ≤ S.size :=
              (Nat.mul_le_mul hd2 h1).trans h2
            omega
          have := trInd_of_not _ hnt
          omega
        | product r =>
          have hf := I.facts
          rw [hkind] at hf
          obtain ⟨hr2, -, -, hρ⟩ := hf
          have hρ' : rhoNat I.hier' + 1 ≤ rhoNat S.hier := by
            have h1 : (rhoNat I.hier' : ℝ) + 1 ≤ rhoNat S.hier := by
              rw [rhoNat_cast, rhoNat_cast]
              have : (2 : ℝ) ≤ r := by exact_mod_cast hr2
              linarith
            exact_mod_cast h1
          change rhoNat I.hier' + 1 ≤ rhoNat S.hier at hρ'
          have : rhoNat (child j).hier = rhoNat I.hier' := rfl
          omega
      have r : ∀ j, Run P .cont (child j) none (child j).answer :=
        fun j => Classical.choice (IH .cont (child j) none ⟨rfl, hN, hsN, I.hierInv⟩ (hdrop j))
      have hbk : ∀ j, (child j).book = S.book := fun j => by
        simp only [child, State.book, State.restrict_rows_of _ _ _ _ _ _ I.keeps,
          State.restrict_floor_of _ _ _ _ _ _ I.keeps, State.restrict_h_of _ _ _ _ _ _ I.keeps]
      exact (Run.dispatch hth htr hfl I child (fun j => ⟨rfl, rfl, rfl, rfl⟩) (fun _ => rfl)
        (fun _ => rfl) hbk _ r).nonempty_answer
    | .normalize Q hsm hp h1 hq hkc hkl =>
      let N := Q.normAbove h1 htr hq hkc hkl
      let I := N.I
      let child : Fin I.k → State Ω C := fun j => N.child j
      have hρI : rhoNat I.hier' ≤ rhoNat S.hier := by
        have h1 : (rhoNat I.hier' : ℝ) ≤ rhoNat S.hier := by
          rw [rhoNat_cast, rhoNat_cast]; exact I.rho_le
        exact_mod_cast h1
      have hdropI : rhoNat I.hier' < rhoNat S.hier ∨ capSum I.hier' ≤ capSum S.hier := by
        rcases I.drop with h | h
        · left
          have h1 : (rhoNat I.hier' : ℝ) < rhoNat S.hier := by
            rw [rhoNat_cast, rhoNat_cast]; exact h
          exact_mod_cast h1
        · exact Or.inr h
      have hσ : ∀ j, (child j).sigma P.κ ≤ S.sigma P.κ := fun j =>
        State.sigma_le_of hκ I.le le_rfl
      by_cases hT' : ∀ v ∈ S.dom, ∀ w ∈ S.dom, ∃ g ∈ I.G', g v = w
      · -- A transitive normalized group: `GiantStep` in each coset.
        have hdrop : ∀ j, MLt (measure P .giant (child j)) (measure P .cont S) := by
          intro j
          have htrj : trInd (child j) = 1 := trInd_of _ hT'
          have hσj := hσ j
          rw [mlt_iff]
          simp only [measure, major, solveInd, stageInd, true_and, lt_self_iff_false, false_or]
          have h1 : (child j).size = S.size := rfl
          have hNj : (child j).N = S.N := rfl
          have h2 : rhoNat (child j).hier = rhoNat I.hier' := rfl
          have hfl : (child j).floor = S.floor := State.restrict_floor_of _ _ _ _ _ _ N.keeps
          have h3 : flInd (child j) = flInd S := by simp only [flInd, hfl]
          have h4 : (child j).h = S.h := State.restrict_h_of _ _ _ _ _ _ N.keeps
          have h5 : capSum (child j).hier = capSum I.hier' := rfl
          omega
        have r : ∀ j, Run P .giant (child j) (some (N.childLabels j)) (child j).answer :=
          fun j => Classical.choice (IH .giant (child j) _ ⟨hN, hsN, hT', hth,
            N.tower, N.childLabels j, rfl, N.q_large⟩ (hdrop j))
        exact (Run.normalize hth htr hfl Q hsm (Q.defaultChoice h1) hq hkc hkl N rfl .giant
          (fun _ => Or.inr ⟨rfl, hT'⟩) _ r).nonempty_answer
      · -- An intransitive normalized group: the orbit-chain answers.
        have hdrop : ∀ j, MLt (measure P .cont (child j)) (measure P .cont S) := by
          intro j
          have htrj : trInd (child j) = 0 := trInd_of_not _ hT'
          rw [mlt_iff]
          simp only [measure, major, solveInd, stageInd, true_and, lt_self_iff_false, false_or]
          have h1 : (child j).size = S.size := rfl
          have hNj : (child j).N = S.N := rfl
          omega
        have r : ∀ j, Run P .cont (child j) none (child j).answer :=
          fun j => Classical.choice (IH .cont (child j) none ⟨rfl, hN, hsN, N.tower⟩ (hdrop j))
        exact (Run.normalize hth htr hfl Q hsm (Q.defaultChoice h1) hq hkc hkl N rfl .cont
          (fun _ => Or.inl ⟨rfl, hT'⟩) _ r).nonempty_answer
  | giant =>
    obtain ⟨hN, hsN, htr, hth, hhi, L, rfl, hLq⟩ := hgood
    have hN2 : 2 ≤ S.N := by have := hP.N₀_pos; omega
    have hpos := size_pos_of_large hth
    have htr1 := trInd_of S htr
    match Su.giant S hhi hN hsN htr hth L hLq with
    | .terminal hrow I =>
      -- The row terminal: fresh calls on rows of at most `N^{1-α}` positions.
      have hcalls := Script.CallsExact.and I.calls I.calls_finite
      have he := Exec.exists_exact (P := P) I.script (hcalls.mono fun m' T hT => by
        obtain ⟨⟨rfl, hsz⟩, hfinT⟩ := hT
        have hlt := size_lt_of_rpow hN2 (by linarith [hP.α_pos]) hsz
        exact IH .solve T none rfl (by mlt_tac))
      obtain ⟨e⟩ := he
      exact (Run.rowTerminal hth htr L hrow I e).nonempty_answer
    | .columns hrow I hinv' =>
      -- The column step: the same core, `h ← h - 1`. The counter stays nonnegative and the
      -- new state satisfies the counter invariant (Section 7.1, Lemma A.29) and the carrier
      -- invariant (`ColumnStep.carrierOK`).
      obtain ⟨hh1, hcnt⟩ := column_step_counter hP.third_lt_α S htr hsN L hrow I
      let S' : State Ω C := ⟨S.G, S.dom, S.dom_inv, S.x, S.y, dropTriv I.hier',
        some ⟨L.q, I.rowPart, some I.cols⟩, S.floor, S.h - 1, by have := S.h_le; omega, S.N,
        hcnt, CarrierOK.dropTriv S.dom_inv htr hinv' I.carrierOK⟩
      have hρ : rhoNat (dropTriv I.hier') ≤ rhoNat S.hier := by
        have h1 : (rhoNat (dropTriv I.hier') : ℝ) ≤ rhoNat S.hier := by
          rw [rhoNat_cast, rhoNat_cast, hierRho_dropTriv]; exact I.rho_le
        exact_mod_cast h1
      have htr' : trInd S' = 1 := trInd_of S' htr
      obtain ⟨r⟩ := IH .cont S' none ⟨rfl, hN, hsN, HierInv.dropTriv S.dom_inv hinv'⟩ (by
        rw [mlt_iff]; simp only [measure, major, solveInd, stageInd, true_and, lt_self_iff_false, false_or]
        have h1 : S'.size = S.size := rfl
        have hNj : S'.N = S.N := rfl
        have h2 : S'.sigma P.κ = S.sigma P.κ := rfl
        have h3 : flInd S' = flInd S := rfl
        have h4 : S'.h = S.h - 1 := rfl
        have h5 : rhoNat S'.hier = rhoNat (dropTriv I.hier') := rfl
        omega)
      exact ⟨Run.rowColumns (S' := S') hth htr L hrow I ⟨rfl, rfl, rfl, rfl⟩ rfl hh1 rfl rfl rfl r⟩
    | .aggregate hnot I hsel hcon hfin =>
      have hq₀ : P.q₀ ≤ L.q := hLq.le
      -- The aggregation round: its calls, then the continuations on the overcosets.
      have hcalls := Script.CallsExact.and I.calls hfin
      have he := Exec.exists_exact (P := P) I.script (hcalls.mono fun m' T hT => by
        obtain ⟨hT, hfinT⟩ := hT
        rcases hT with ⟨rfl, hsz⟩ | ⟨rfl, e, hch⟩
        · have hlt := size_lt_of_rpow hN2 hP.two_α_lt hsz
          exact IH .solve T none rfl (by mlt_tac)
        · subst e
          replace hch : ChargedCall P S T := hch
          have hTN : T.N = S.N := hch.N_eq
          have hsz : T.size ≤ S.size := size_le_of_subset hch.sub
          -- With the same size, the call is intransitive or `σ` drops by `κ`.
          have key : T.size < S.size ∨ trInd T = 0 ∨ T.sigma P.κ < S.sigma P.κ := by
            by_cases hlt : T.size < S.size
            · exact Or.inl hlt
            by_cases htrT : T.Transitive
            · right; right
              have heq : T.size = S.size := by omega
              obtain ⟨v, hv⟩ : T.dom.Nonempty := by
                have : 0 < T.size := heq ▸ hpos
                exact Set.nonempty_coe_sort.1 (Nat.card_pos_iff.1 this).1
              rcases hch.types v hv with horb | hσ
              · exfalso
                have h1 := size_le_orb htrT hv
                have h2 : (T.size : ℝ) ≤ P.θ * S.size :=
                  (by exact_mod_cast h1 : (T.size : ℝ) ≤ (Nat.card (orb T.G v) : ℝ)).trans horb
                rw [heq] at h2
                have h3 : (0 : ℝ) < S.size := by exact_mod_cast hpos
                nlinarith [hP.θ_lt]
              · rw [State.sigma_eq_point P.κ htrT hv]
                omega
            · exact Or.inr (Or.inl (trInd_of_not _ htrT))
          have htrT := trInd_le T
          have hinvT : T.HierInv := by
            show HierInv T.G T.dom T.hier
            rw [hch.hier_eq]
            exact HierInv.mono hhi hch.le hch.sub
          exact IH .cont T none ⟨rfl, show P.N₀ < T.N by omega, by omega, hinvT⟩ (by
            mlt_tac))
      obtain ⟨e⟩ := he
      let b := I.script.evalExact
      let child : Fin b.overs.length → State Ω C := fun j =>
        S.restrict (b.overs.get j).2 (I.covers.overs_le j) S.x
          (S.y ∘ (b.overs.get j).1) (I.newHier (b.overs.get j))
      have hdrop : ∀ j, MLt (measure P .cont (child j)) (measure P .giant S) := by
        intro j
        have hcu := I.capUpdate (b.overs.get j) (List.get_mem _ _)
        have hσ : (child j).sigma P.κ ≤ S.sigma P.κ :=
          State.sigma_le_of hκ (I.covers.overs_le j) le_rfl
        have hρ : rhoNat (I.newHier (b.overs.get j)) = rhoNat S.hier := by
          have h1 : (rhoNat (I.newHier (b.overs.get j)) : ℝ) = rhoNat S.hier := by
            rw [rhoNat_cast, rhoNat_cast]; exact hcu.rho_eq
          exact_mod_cast h1
        have hc := hcu.capSum_lt hP.β_lt (hP.q₀_pos.trans hq₀)
        have htrj := trInd_le (child j)
        rw [mlt_iff]
        simp only [measure, major, solveInd, stageInd, true_and, lt_self_iff_false, false_or]
        have h1 : (child j).size = S.size := rfl
        have hNj : (child j).N = S.N := rfl
        have h2 : rhoNat (child j).hier = rhoNat (I.newHier (b.overs.get j)) := rfl
        have hk := I.overs_keep (b.overs.get j) (List.get_mem _ _)
        have hfl : (child j).floor = S.floor := State.restrict_floor_of _ _ _ _ _ _ hk
        have h3 : flInd (child j) = flInd S := by simp only [flInd, hfl]
        have h4 : (child j).h = S.h := State.restrict_h_of _ _ _ _ _ _ hk
        have h5 : capSum (child j).hier = capSum (I.newHier (b.overs.get j)) := rfl
        omega
      have r : ∀ j, Run P .cont (child j) none (child j).answer :=
        fun j => Classical.choice (IH .cont (child j) none ⟨rfl, hN, hsN,
          I.child_hierInv hsel hhi (List.get_mem _ _)⟩ (hdrop j))
      have hbk : ∀ j, (child j).book = S.book := fun j => by
        have hk := I.overs_keep (b.overs.get j) (List.get_mem _ _)
        simp only [State.book, child, State.restrict_rows_of _ _ _ _ _ _ hk,
          State.restrict_floor_of _ _ _ _ _ _ hk, State.restrict_h_of _ _ _ _ _ _ hk]
      exact (Run.aggregate hth htr L hnot hq₀ I hsel hcon b e (fun j => (b.overs.get j).1)
        (fun j => ⟨1, (b.overs.get j).2.one_mem, mul_one _⟩) child (fun j => ⟨rfl, rfl, rfl, rfl⟩)
        (fun _ => rfl) (fun _ => rfl) hbk _ r).nonempty_answer

/-- **Every state has a run of `Solve`**, given the subroutine data. The run returns the
exact answer of the state. -/
theorem exists_run_solve (hP : P.Terminating) (hM : GI.Cited.MarotiPrimitive)
    (ha : 128 ≤ P.a) (Su : Supply P) {Ω C : Type} [Finite Ω]
    (S : State Ω C) : Nonempty (Run P .solve S none S.answer) :=
  exists_run_aux hP hM ha Su _ .solve S none rfl rfl

/-- **Every `Continue` state of a phase above the base size with the hierarchy invariant has a
run.** -/
theorem exists_run_cont (hP : P.Terminating) (hM : GI.Cited.MarotiPrimitive)
    (ha : 128 ≤ P.a) (Su : Supply P) {Ω C : Type} [Finite Ω]
    (S : State Ω C) (hN : P.N₀ < S.N) (hsN : S.size ≤ S.N) (hinv : S.HierInv) :
    Nonempty (Run P .cont S none S.answer) :=
  exists_run_aux hP hM ha Su _ .cont S none ⟨rfl, hN, hsN, hinv⟩ rfl

end Exists

end GI.Algorithm
