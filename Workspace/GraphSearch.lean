module

public import Workspace.Search

@[expose] public section

namespace GI

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The executable reference graph solver enumerates vertex permutations only. -/
def allGraphIsomorphisms (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] : Finset (Equiv.Perm V) :=
  Finset.univ.filter (fun p =>
    Transports (adjacencyColor G) (adjacencyColor H) (diagonal p))

theorem mem_allGraphIsomorphisms (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (p : Equiv.Perm V) :
    p ∈ allGraphIsomorphisms G H ↔ ∀ u v, G.Adj u v ↔ H.Adj (p u) (p v) := by
  simp only [allGraphIsomorphisms, Finset.mem_filter, Finset.mem_univ, true_and]
  exact graph_transport_iff G H p

def graphIsomorphic (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] : Bool :=
  decide (allGraphIsomorphisms G H).Nonempty

/-- Unconditional executable GI decidability, with no fast-runtime assertion. -/
theorem graphIsomorphic_correct (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] :
    graphIsomorphic G H = true ↔ Nonempty (G ≃g H) := by
  rw [graph_iso_iff_string_iso]
  simp [graphIsomorphic, allGraphIsomorphisms, Finset.Nonempty]

def vertexPermutations : (n : ℕ) → List (Equiv.Perm (Fin n))
  | 0 => [1]
  | n + 1 => (List.finRange (n + 1)).flatMap fun a =>
      (vertexPermutations n).map fun p => Equiv.Perm.decomposeFin.symm (a, p)

theorem vertexPermutations_complete (n : ℕ) (p : Equiv.Perm (Fin n)) :
    p ∈ vertexPermutations n := by
  induction n with
  | zero =>
    have hp : p = 1 := Subsingleton.elim _ _
    simp [vertexPermutations, hp]
  | succ n ih =>
    let parts := Equiv.Perm.decomposeFin p
    apply List.mem_flatMap.mpr
    refine ⟨parts.1, List.mem_finRange _, ?_⟩
    apply List.mem_map.mpr
    exact ⟨parts.2, ih parts.2, Equiv.symm_apply_apply _ p⟩

def graphWitnessCandidates {n : ℕ} (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj] : List (Equiv.Perm (Fin n)) :=
  (vertexPermutations n).filter fun p =>
    decide (Transports (adjacencyColor G) (adjacencyColor H) (diagonal p))

theorem mem_graphWitnessCandidates {n : ℕ} (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (p : Equiv.Perm (Fin n)) :
    p ∈ graphWitnessCandidates G H ↔
      Transports (adjacencyColor G) (adjacencyColor H) (diagonal p) := by
  simp [graphWitnessCandidates, vertexPermutations_complete]

def graphWitness {n : ℕ} (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj] : Option (Equiv.Perm (Fin n)) :=
  (graphWitnessCandidates G H).head?

theorem graphWitness_sound {n : ℕ} (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj] {p : Equiv.Perm (Fin n)}
    (hp : graphWitness G H = some p) : ∀ u v, G.Adj u v ↔ H.Adj (p u) (p v) := by
  apply (graph_transport_iff G H p).1
  apply (mem_graphWitnessCandidates G H p).1
  obtain ⟨tail, htail⟩ := List.head?_eq_some_iff.mp hp
  rw [htail]
  exact List.mem_cons_self

theorem graphWitness_none_iff {n : ℕ} (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj] :
    graphWitness G H = none ↔ ¬ Nonempty (G ≃g H) := by
  rw [graph_iso_iff_string_iso]
  simp [graphWitness, List.eq_nil_iff_forall_not_mem, mem_graphWitnessCandidates]

end GI
