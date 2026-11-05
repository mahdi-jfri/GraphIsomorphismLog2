module

public import Workspace.Paper.TotalCost

@[expose] public section

/-!
# The number of script calls of a node

Section 7.2: "Fix an absolute exponent `a ≥ 1` bounding the polynomial numbers of local and
auxiliary calls". The per-node hypothesis `GI.Algorithm.NodeBound` of the stage 1 cost
theorems has a field `calls`: a node makes at most `N^{af}` calls from its query scripts. Here
we prove it with `af = a`, for `a ≥ 5`:

* `Script.numCalls`: the number of calls a script makes along the exact answers; a script run
  makes exactly this many calls (`Exec.calls_length`).
* **Aggregation round** (`Aggregation.numCalls_le`, `Aggregation.calls_count'`): the
  certificate phase asks only `Continue` (`certPhase_cont`), so it makes at most
  `2 binom(q, κ) s κ!` calls (`certPhase_numCont_le`); the comparison phase asks only
  `Continue` (`comparePhase_cont`), at most `4 q^{2κ} s` calls; each item asks at most three
  calls (`AuxItem.numCalls_le`). In all at most `N^a`, by `Aggregation.count_bound`.
* **Row terminal** (`RowTerminal.numCalls_eq`): the script asks the `N`-test of every ordered
  pair of the `2q` rows and the coset of every pair of a row of `x` and a row of `y`, so
  `(2q)² + q² = 5q²` calls; with `q ≤ s ≤ N` and `N ≥ 2` this is at most `N^5 ≤ N^a`.
  (Theorem A.23 counts `2m² + m ≤ 3(m+1)²` string calls, `GI.Paper.terminalStringCalls`; the
  script of the recursion asks all ordered pairs, which is the same order.)
* `Run.scriptCalls_le`: every node with `s ≤ N` that is not a `Solve` node makes at most `N^a`
  script calls, and `NodeBound'.toNodeBound`: the per-node hypothesis without the field
  `calls` gives `NodeBound` with `af = a`.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.Endpoint GI.LocalGroups
open scoped Pointwise

/-! ### Counting all calls of a script -/

namespace Script

variable {α β : Type}

/-- The number of calls that the script makes along the exact answers. -/
def numCalls : Script α → ℕ
  | done _ => 0
  | ask _ S k => 1 + (k S.answer).numCalls

theorem numCalls_bind : ∀ (s : Script α) (f : α → Script β),
    (s.bind f).numCalls = s.numCalls + (f s.evalExact).numCalls
  | .done _, _ => by simp [bind, numCalls, evalExact]
  | .ask m _ k, f => by
    simp only [bind, numCalls, evalExact]
    rw [numCalls_bind (k _) f]
    omega

theorem numCalls_seqList : ∀ (l : List (Script α)),
    (seqList l).numCalls = (l.map numCalls).sum
  | [] => rfl
  | s :: ss => by
    simp only [seqList, numCalls_bind, List.map_cons, List.sum_cons, numCalls_seqList ss]
    simp [numCalls]

/-- A script that asks only `Continue` makes `numCont` calls. -/
theorem numCalls_eq_numCont : ∀ (s : Script α), s.CallsExact (fun m _ => m = .cont) →
    s.numCalls = s.numCont
  | .done _, _ => rfl
  | .ask _ _ k, h => by
    obtain ⟨hm, hk⟩ := h
    subst hm
    simp only [numCalls, numCont, if_true]
    rw [numCalls_eq_numCont _ hk]

/-- A table asks one call per entry. -/
theorem numCalls_table {ι : Type} [DecidableEq ι] {Ω' C' : Type} (st : ι → State Ω' C') :
    ∀ l : List ι, (table st l).numCalls = l.length
  | [] => rfl
  | i :: l => by
    simp only [table, numCalls, numCalls_bind, numCalls_table st l, List.length_cons]
    omega

end Script

variable {P : Params}

/-- **A script run makes `numCalls` calls**: the answers of its calls are exact (Lemma 6.1,
`Run.exact`), so the run follows the exact answers. -/
theorem Exec.calls_length {α : Type} {s : Script α} {a : α} (e : Exec P s a) :
    e.calls.length = s.numCalls := by
  refine Exec.rec (motive_1 := fun _ {_ _} _ _ _ _ => True)
    (motive_2 := fun s _ e => e.calls.length = s.numCalls)
    (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    ?done ?ask e
  case done => intro α a; rfl
  case ask =>
    intro α Ω' C' m S k A a r e' _ ih
    have hA : A = S.answer := r.exact
    subst hA
    change (e'.calls.length + 1) = 1 + (k S.answer).numCalls
    omega

/-! ### The certificate phase asks only `Continue` -/

section Cert

/-- Every call of the lifted endpoint script (Algorithm 2) is a `Continue` call. -/
theorem endpointScriptLift_cont {Ω C C₀ : Type} [DecidableEq Ω] (S : State Ω C)
    [Fintype S.dom] {Q : Type} [Group Q] (R : CosetRepFn S.dom) {P' : Subgroup (Perm S.dom)}
    (phi : P' →* Q) (hP : P' ≤ S.domGroup) (x : S.dom → C₀) (t : ℕ) :
    (endpointScriptLift S R phi x t).CallsExact (fun m _ => m = .cont) := by
  classical
  induction t with
  | zero => trivial
  | succ t ih =>
    rw [endpointScriptLift]
    refine Script.callsExact_bind _ _ ih ?_
    rw [endpointScriptLift_evalExact S R phi hP]
    split_ifs
    · trivial
    · refine Script.callsExact_bind _ _ ?_ trivial
      unfold checkNewWindowLift
      split_ifs
      · refine Script.callsExact_bind _ _ (Script.callsExact_seqList _ fun s hs => ?_) trivial
        obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hs
        exact ⟨rfl, trivial⟩
      · trivial

/-- Every call of the certificate phase is a `Continue` call. -/
theorem certPhase_cont {Ω C : Type} [DecidableEq Ω] (S : State Ω C) [Fintype S.dom] {q : ℕ}
    (πd : S.domGroup →* alternatingGroup (Fin q)) (κ : ℕ) (O : TestSetOrder q κ)
    (R : CosetRepFn S.dom) (x y : S.dom → C) :
    (certPhase S πd κ O R x y).CallsExact (fun m _ => m = .cont) := by
  unfold certPhase
  refine Script.callsExact_seqList _ fun s hs => ?_
  obtain ⟨T, -, rfl⟩ := List.mem_map.1 hs
  refine Script.callsExact_bind _ _ (endpointScriptLift_cont S R _ Pgrp_le x _) ?_
  exact Script.callsExact_bind _ _ (endpointScriptLift_cont S R _ Pgrp_le y _) trivial

end Cert

/-! ### The aggregation round -/

namespace AuxItem

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S} {B : Set (Perm Ω)}

/-- An item makes at most three calls: at most two queries, or the three calls of Lemma A.11. -/
theorem numCalls_le (I : AuxItem P S L) (hI : I.Valid B) : I.script.numCalls ≤ 3 := by
  cases I with
  | none => simp [script, Script.numCalls]
  | overcoset => simp [script, Script.numCalls]
  | query Qs E₀ =>
    obtain ⟨-, hlen, -, -, -⟩ := hI
    simp only [script, Script.numCalls_bind, Script.numCalls_seqList, List.map_map]
    have h1 : ∀ x ∈ Qs.map (Script.numCalls ∘ AuxQuery.script), x ≤ 1 := by
      intro x hx
      obtain ⟨Q, -, rfl⟩ := List.mem_map.1 hx
      simp [AuxQuery.script, Script.numCalls]
    have h := List.sum_le_card_nsmul _ 1 h1
    rw [List.length_map, smul_eq_mul, mul_one] at h
    simp only [Script.numCalls]
    omega
  | halving H => simp [script, Halving.script, Script.numCalls]

end AuxItem

namespace Aggregation

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S} (I : Aggregation P S L)

theorem certScript_numCalls : I.certScript.numCalls = I.certScript.numCont := by
  haveI := I.fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq Ω := Classical.decEq _
  exact Script.numCalls_eq_numCont _ (certPhase_cont S I.πd P.κ I.sets I.reps _ _)

theorem itemsScript_numCalls_le : I.itemsScript.numCalls ≤ 3 * L.q ^ I.ℓ := by
  simp only [itemsScript, Script.numCalls_bind, Script.numCalls_seqList, List.map_map]
  simp only [Script.numCalls, add_zero]
  have h := List.sum_le_card_nsmul (I.tuples.map (Script.numCalls ∘ fun b => (I.items b).script))
    3 (fun x hx => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx
      exact (I.items b).numCalls_le (I.items_valid b))
  rw [List.length_map, length_tuples, smul_eq_mul] at h
  linarith

theorem compScript_numCalls : I.compScript.numCalls = I.compScript.numCont := by
  haveI := I.fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq Ω := Classical.decEq _
  exact Script.numCalls_eq_numCont _ (comparePhase_cont S I.πd P.κ I.tests I.pick _ _)

/-- **The calls of an aggregation round**: at most `2 binom(q, κ) s κ! + 4 q^{2κ} s + 3 q^ℓ`
(certificate phase, comparison phase, items). -/
theorem numCalls_le :
    I.script.numCalls ≤ 2 * L.q.choose P.κ * S.size * P.κ.factorial +
      (4 * L.q ^ (2 * P.κ) * S.size + 3 * L.q ^ I.ℓ) := by
  rw [script, Script.numCalls_bind, certScript_numCalls, Script.numCalls_bind,
    compScript_numCalls]
  exact Nat.add_le_add I.certScript_numCont_le
    (Nat.add_le_add I.compScript_numCont_le I.itemsScript_numCalls_le)

/-- **At most `N^a` calls** in an aggregation round, by the arithmetic of `count_bound`
(Section 7.2: "a ≥ 1 bounding the polynomial numbers of local and auxiliary calls"). -/
theorem calls_count' : (I.script.numCalls : ℝ) ≤ (S.N : ℝ) ^ P.a :=
  le_trans (by exact_mod_cast I.numCalls_le) I.count_bound

end Aggregation

/-! ### The row terminal -/

namespace RowTerminal

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S} (I : RowTerminal P S L)

/-- **The calls of the row terminal**: `(2q)²` `N`-tests and `q²` cosets, `5q²` in all. -/
theorem numCalls_eq : I.script.numCalls = 5 * L.q ^ 2 := by
  classical
  have h1 : I.tests.length = Fintype.card ((Fin L.q ⊕ Fin L.q) × (Fin L.q ⊕ Fin L.q)) := by
    rw [← List.toFinset_card_of_nodup I.tests_nodup, ← Finset.card_univ]
    congr 1
    exact Finset.eq_univ_iff_forall.2 fun a => List.mem_toFinset.2 (I.mem_tests a)
  have h2 : I.cosets.length = Fintype.card (Fin L.q × Fin L.q) := by
    rw [← List.toFinset_card_of_nodup I.cosets_nodup, ← Finset.card_univ]
    congr 1
    exact Finset.eq_univ_iff_forall.2 fun a => List.mem_toFinset.2 (I.mem_cosets a)
  simp only [script, Script.numCalls_bind, Script.numCalls_table, Script.numCalls, h1, h2,
    Fintype.card_prod, Fintype.card_sum, Fintype.card_fin]
  ring

/-- The row terminal has `q ≤ s`: the domain is `B × [q]` with `B` nonempty when the domain
is. -/
theorem q_le_size (I : RowTerminal P S L) (hpos : 0 < S.size) : L.q ≤ S.size := by
  have h := Nat.card_congr I.e
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := I.B), Nat.card_fin] at h
  change _ = S.size at h
  have hB : 0 < Fintype.card I.B := by
    rcases Nat.eq_zero_or_pos (Fintype.card I.B) with h0 | h0
    · rw [h0, zero_mul] at h; omega
    · exact h0
  rw [← h]
  exact Nat.le_mul_of_pos_left _ hB

end RowTerminal

/-! ### Every node -/

theorem size_pos_of_large' {Ω C : Type} {S : State Ω C} {γ : ℝ} (hs : (S.N : ℝ) ^ γ < S.size) :
    0 < S.size := by
  have h0 : (0 : ℝ) ≤ (S.N : ℝ) ^ γ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  exact_mod_cast h0.trans_lt hs

/-- A phase size `N` with `N^γ < s ≤ N` is at least two. -/
theorem two_le_N_of_large {Ω C : Type} {S : State Ω C} {γ : ℝ} (hs : (S.N : ℝ) ^ γ < S.size)
    (hsz : S.size ≤ S.N) : 2 ≤ S.N := by
  have hpos := size_pos_of_large' hs
  by_contra h
  have hN1 : S.N = 1 := by omega
  have : S.size = 1 := by omega
  rw [hN1, this] at hs
  simp at hs

/-- **Every node makes at most `N^a` script calls** (Section 7.2), for `a ≥ 5`: a node that is
not a `Solve` node, on at most `N` positions. -/
theorem Run.scriptCalls_le (ha : 5 ≤ P.a) {m : Mode} {Ω C : Type} {S : State Ω C}
    {L : Option (SuppliedLabels S)}
    {A : Set (Perm Ω)} (r : Run P m S L A) (hsz : S.size ≤ S.N) :
    (r.scriptCalls.length : ℝ) ≤ (S.N : ℝ) ^ P.a := by
  have h0 : (0 : ℝ) ≤ (S.N : ℝ) ^ P.a := Real.rpow_nonneg (Nat.cast_nonneg _) _
  cases r with
  | rowTerminal hs _ L _ I e =>
    change (e.calls.length : ℝ) ≤ _
    rw [Exec.calls_length, I.numCalls_eq]
    have hN2 := two_le_N_of_large hs hsz
    have hq : L.q ≤ S.N := (I.q_le_size (size_pos_of_large' hs)).trans hsz
    have hN2' : (2 : ℝ) ≤ S.N := by exact_mod_cast hN2
    have hqR : (L.q : ℝ) ≤ S.N := by exact_mod_cast hq
    have hq0 : (0 : ℝ) ≤ L.q := Nat.cast_nonneg _
    have h5 : (5 : ℝ) * L.q ^ 2 ≤ (S.N : ℝ) ^ (5 : ℕ) := by
      have h1 : (L.q : ℝ) ^ 2 ≤ (S.N : ℝ) ^ 2 := pow_le_pow_left₀ hq0 hqR 2
      have h2 : (5 : ℝ) ≤ (S.N : ℝ) ^ 3 := by nlinarith
      calc (5 : ℝ) * L.q ^ 2 ≤ (S.N : ℝ) ^ 3 * (S.N : ℝ) ^ 2 :=
            mul_le_mul h2 h1 (by positivity) (by positivity)
        _ = (S.N : ℝ) ^ (5 : ℕ) := by ring
    push_cast
    calc (5 : ℝ) * L.q ^ 2 ≤ (S.N : ℝ) ^ (5 : ℕ) := h5
      _ = (S.N : ℝ) ^ ((5 : ℕ) : ℝ) := by rw [Real.rpow_natCast]
      _ ≤ (S.N : ℝ) ^ P.a :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; exact ha)
  | aggregate _ _ _ _ _ I _ _ b e =>
    change (e.calls.length : ℝ) ≤ _
    rw [Exec.calls_length]
    exact I.calls_count'
  | direct => simpa [Run.scriptCalls] using h0
  | fresh => simpa [Run.scriptCalls] using h0
  | threshold => simpa [Run.scriptCalls] using h0
  | orbitStop => simpa [Run.scriptCalls] using h0
  | orbitChain => simpa [Run.scriptCalls] using h0
  | floorReset => simpa [Run.scriptCalls] using h0
  | dispatch => simpa [Run.scriptCalls] using h0
  | normalize => simpa [Run.scriptCalls] using h0
  | rowColumns => simpa [Run.scriptCalls] using h0

/-- **The per-node hypothesis without the call count** (Section 7.4): the work bounds of
`NodeBound`. The call count is proved (`Run.scriptCalls_le`). -/
structure NodeBound' (w : Node P → ℝ) (cw : ℝ) : Prop where
  nonneg : ∀ nd, 0 ≤ w nd
  work : ∀ nd : Node P, nd.m ≠ .solve → nd.S.size ≤ nd.S.N → w nd ≤ expLogSq cw nd.S.N
  solve : ∀ nd : Node P, nd.m = .solve → w nd ≤ expLogSq cw nd.S.size

/-- **`NodeBound.calls` holds with `af = a`** (for `a ≥ 5`), so the work bounds give the
per-node hypothesis `NodeBound`. -/
theorem NodeBound'.toNodeBound {w : Node P → ℝ} {cw : ℝ} (hw : NodeBound' w cw)
    (ha : 5 ≤ P.a) : NodeBound w cw P.a where
  nonneg := hw.nonneg
  work := hw.work
  solve := hw.solve
  calls nd _ hsz := nd.run.scriptCalls_le ha hsz

end GI.Algorithm
