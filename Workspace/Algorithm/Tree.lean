import Workspace.Algorithm.Correctness

/-!
# The recursion tree of a run, and the facts it gives for Lemma 7.1

A run `r : Run P m S L A` is itself the recursion tree. This file records, for each
node, what the analysis of Section 7 reads from it:

* `Run.res`: the resources `s, ρ, σ, Q, h` of the potential (Section 7.1), read from
  the state (`GI.Algorithm.State.res`);
* `Run.kind`: which case of Algorithms 4 and 5 the node is;
* `Run.children`: its immediate recursive runs, with the script runs (`Exec.calls`).

The following fields of `GI.Paper.PhaseTree.Hyp` follow from the guards of the
constructors and are proved here:

* `nonneg` (`Run.res_nonneg`): `ρ, σ, Q ≥ 0` at every node;
* `leaf_small` (`Run.leaf_small`): a threshold leaf has `s ≤ N^γ`;
* `internal_large` (`Run.internal_large`): every other `Continue` or `GiantStep`
  node has `s > N^γ`;
* `orbit_pos`, `orbit_disjoint` for the binary orbit chain
  (`Run.orbitChain_sizes`): the two children have nonempty disjoint domains that
  together make up the parent domain, so each is strictly smaller.

The remaining fields need the potential decrease of each row of the table of
Section 7.2 and the multiplicity bounds; they rest on interface data that the
abstract run does not yet carry (see the module docstring of
`Workspace/Algorithm/Procedure.lean`).
-/

namespace GI.Algorithm

open Equiv Equiv.Perm
open scoped Pointwise

variable {P : Params}

/-- A node of the recursion tree: a run of some procedure on some state. -/
structure Node (P : Params) where
  m : Mode
  Ω : Type
  C : Type
  S : State Ω C
  L : Option (SuppliedLabels S)
  A : Set (Perm Ω)
  run : Run P m S L A

/-- The cases of Algorithms 4 and 5. -/
inductive CallKind
  | direct | fresh | threshold | orbitStop | orbitChain | floorReset | dispatch
  | normalize | rowTerminal | rowColumns | aggregate
  deriving DecidableEq

/-- The case of Algorithms 4 and 5 that a run starts with. -/
def Run.kind {m : Mode} {Ω C : Type} {S : State Ω C} {L : Option (SuppliedLabels S)}
    {A : Set (Perm Ω)} :
    Run P m S L A → CallKind
  | .direct .. => .direct
  | .fresh .. => .fresh
  | .threshold .. => .threshold
  | .orbitStop .. => .orbitStop
  | .orbitChain .. => .orbitChain
  | .floorReset .. => .floorReset
  | .dispatch .. => .dispatch
  | .normalize .. => .normalize
  | .rowTerminal .. => .rowTerminal
  | .rowColumns .. => .rowColumns
  | .aggregate .. => .aggregate

/-- The resources `s, ρ, σ, Q, h` of a node, with the certificate size `κ` as the
cutoff of the symmetry measure. -/
noncomputable def Run.res {m : Mode} {Ω C : Type} {S : State Ω C} {L : Option (SuppliedLabels S)}
    {A : Set (Perm Ω)}
    (_ : Run P m S L A) : GI.Paper.PotentialState :=
  S.res P.κ

/-- The recursive runs made by a script run, in order. -/
noncomputable def Exec.calls {α : Type} {s : Script α} {a : α} (e : Exec P s a) :
    List (Node P) :=
  Exec.rec (motive_1 := fun _ _ _ _ _ _ _ => PUnit) (motive_2 := fun _ _ _ => List (Node P))
    (direct := fun _ _ => ⟨⟩)
    (fresh := fun _ _ _ _ => ⟨⟩)
    (threshold := fun _ _ _ => ⟨⟩)
    (orbitStop := fun _ _ _ _ _ _ _ _ _ => ⟨⟩)
    (orbitChain := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ⟨⟩)
    (floorReset := fun _ _ _ _ _ _ _ _ _ _ _ => ⟨⟩)
    (dispatch := fun _ _ _ _ _ _ _ _ _ _ _ _ => ⟨⟩)
    (normalize := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ⟨⟩)
    (rowTerminal := fun _ _ _ _ _ _ _ => ⟨⟩)
    (rowColumns := fun _ _ _ _ _ _ _ _ _ _ _ _ _ => ⟨⟩)
    (aggregate := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ⟨⟩)
    (done := fun _ => [])
    (ask := fun r _ _ ih => ⟨_, _, _, _, _, _, r⟩ :: ih)
    e

/-- The immediate recursive runs of a node, in the order the pseudocode makes them:
inherited `Continue` and `GiantStep` children, fresh `Solve` calls, and the runs of
its query scripts. -/
noncomputable def Run.children {m : Mode} {Ω C : Type} {S : State Ω C}
    {L : Option (SuppliedLabels S)}
    {A : Set (Perm Ω)} :
    Run P m S L A → List (Node P)
  | .direct .. => []
  | .fresh _ _ r => [⟨_, _, _, _, _, _, r⟩]
  | .threshold _ r => [⟨_, _, _, _, _, _, r⟩]
  | .orbitStop _ _ _ _ _ _ _ r₁ => [⟨_, _, _, _, _, _, r₁⟩]
  | .orbitChain _ _ _ _ _ _ _ r₁ _ _ _ _ _ _ r₂ => [⟨_, _, _, _, _, _, r₁⟩, ⟨_, _, _, _, _, _, r₂⟩]
  | .floorReset _ _ _ _ _ _ _ _ _ r => [⟨_, _, _, _, _, _, r⟩]
  | .dispatch _ _ _ _ _ _ _ _ _ _ r => List.ofFn fun j => ⟨_, _, _, _, _, _, r j⟩
  | .normalize _ _ _ _ _ _ _ _ _ _ _ _ _ _ r => List.ofFn fun j => ⟨_, _, _, _, _, _, r j⟩
  | .rowTerminal _ _ _ _ _ e => e.calls
  | .rowColumns _ _ _ _ _ _ _ _ _ _ _ r => [⟨_, _, _, _, _, _, r⟩]
  | .aggregate _ _ _ _ _ _ _ _ _ e _ _ _ _ _ _ _ _ r =>
    e.calls ++ List.ofFn fun j => ⟨_, _, _, _, _, _, r j⟩

/-- `PhaseTree.Hyp.nonneg`: `ρ, σ, Q ≥ 0` at every node. -/
theorem Run.res_nonneg {m : Mode} {Ω C : Type} {S : State Ω C} {L : Option (SuppliedLabels S)}
    {A : Set (Perm Ω)}
    (r : Run P m S L A) : 0 ≤ r.res.ρ ∧ 0 ≤ r.res.σ ∧ 0 ≤ r.res.Q :=
  S.res_nonneg P.κ

/-- `PhaseTree.Hyp.leaf_small`: a threshold leaf ("Every fresh leaf has at most `N^γ`
positions") has `s ≤ N^γ`, for the phase size `N` stored in the state. -/
theorem Run.leaf_small {m : Mode} {Ω C : Type} {S : State Ω C} {L : Option (SuppliedLabels S)}
    {A : Set (Perm Ω)}
    (r : Run P m S L A) (h : r.kind = .threshold) : (r.res.s : ℝ) ≤ (S.N : ℝ) ^ P.γ := by
  cases r with
  | threshold hs _ => exact hs
  | _ => simp [Run.kind] at h

/-- `PhaseTree.Hyp.internal_large` (eq. `main-phase-active`): every `Continue` or
`GiantStep` node other than a threshold leaf has `s > N^γ`. -/
theorem Run.internal_large {m : Mode} {Ω C : Type} {S : State Ω C} {L : Option (SuppliedLabels S)}
    {A : Set (Perm Ω)}
    (r : Run P m S L A) (hm : m ≠ .solve) (h : r.kind ≠ .threshold) :
    (S.N : ℝ) ^ P.γ < r.res.s := by
  cases r with
  | direct => exact absurd rfl hm
  | fresh => exact absurd rfl hm
  | threshold => exact absurd rfl h
  | orbitStop hs => exact hs
  | orbitChain hs => exact hs
  | floorReset hs => exact hs
  | dispatch hs => exact hs
  | normalize hs => exact hs
  | rowTerminal hs => exact hs
  | rowColumns hs => exact hs
  | aggregate hs => exact hs

/-- `PhaseTree.Hyp.orbit_pos` and `orbit_disjoint` for the orbit chain: the largest
orbit `D₁` and the rest `dom \ D₁` are nonempty, disjoint, and make up the parent
domain, so each child is strictly smaller than the parent. -/
theorem orbitChain_sizes {Ω C : Type} [Finite Ω] {S S₁ S₂ : State Ω C} {D₁ : Set Ω}
    (hint : ¬ S.Transitive) (hD₁ : S.LargestOrbit D₁) (h₁ : S₁.dom = D₁)
    (h₂ : S₂.dom = S.dom \ D₁) :
    S₁.size + S₂.size = S.size ∧ 1 ≤ S₁.size ∧ 1 ≤ S₂.size := by
  classical
  have hfin : ∀ X : Set Ω, X.Finite := fun X => Set.toFinite X
  simp only [State.size, h₁, h₂, Nat.card_coe_set_eq]
  obtain ⟨a, ha, hD⟩ := hD₁.orbit
  have haD : a ∈ D₁ := by rw [hD]; exact ⟨1, S.G.one_mem, rfl⟩
  -- The rest is nonempty: otherwise `D₁` is the whole domain and `G` is transitive.
  have hrest : (S.dom \ D₁).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty] at hne
    apply hint
    intro v hv w hw
    have hv' := hne hv
    have hw' := hne hw
    rw [hD] at hv' hw'
    obtain ⟨g, hg, rfl⟩ := hv'
    obtain ⟨k, hk, rfl⟩ := hw'
    exact ⟨k * g⁻¹, S.G.mul_mem hk (S.G.inv_mem hg), by simp⟩
  refine ⟨by rw [add_comm, Set.ncard_diff_add_ncard_of_subset hD₁.subset (hfin _)], ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.2 ((Set.ncard_pos (hfin _)).2 ⟨a, haD⟩).ne'
  · exact Nat.one_le_iff_ne_zero.2 ((Set.ncard_pos (hfin _)).2 hrest).ne'

end GI.Algorithm
