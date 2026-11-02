import Workspace.GraphSearch

namespace GI
variable {V : Type*}

def graphAutomorphisms (G : SimpleGraph V) : Subgroup (Equiv.Perm V) where
  carrier := {p | ∀ u v, G.Adj u v ↔ G.Adj (p u) (p v)}
  one_mem' := fun _ _ => Iff.rfl
  mul_mem' := fun hp hq u v => (hq u v).trans (hp _ _)
  inv_mem' := by
    intro p hp u v
    simpa using (hp (p⁻¹ u) (p⁻¹ v)).symm

variable [Fintype V] [DecidableEq V]

theorem graph_generators_complete (G : SimpleGraph V) [DecidableRel G.Adj] :
    Subgroup.closure (↑(allGraphIsomorphisms G G) : Set (Equiv.Perm V)) =
      graphAutomorphisms G := by
  have he : (↑(allGraphIsomorphisms G G) : Set (Equiv.Perm V)) =
      (graphAutomorphisms G : Set (Equiv.Perm V)) := by
    ext p
    exact mem_allGraphIsomorphisms G G p
  rw [he, Subgroup.closure_eq]

/-- One returned graph isomorphism and the complete source automorphism group describe
every graph isomorphism, with the multiplication order fixed explicitly. -/
theorem graph_full_output_coset (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] {t : Equiv.Perm V}
    (ht : t ∈ allGraphIsomorphisms G H) (p : Equiv.Perm V) :
    p ∈ allGraphIsomorphisms G H ↔ ∃ a ∈ graphAutomorphisms G, p = t * a := by
  have ht' := (mem_allGraphIsomorphisms G H t).1 ht
  constructor
  · intro hp
    have hp' := (mem_allGraphIsomorphisms G H p).1 hp
    refine ⟨t⁻¹ * p, ?_, by simp⟩
    intro u v
    have hh := ht' (t⁻¹ (p u)) (t⁻¹ (p v))
    have hh' : G.Adj (t⁻¹ (p u)) (t⁻¹ (p v)) ↔ H.Adj (p u) (p v) := by
      simpa using hh
    simpa using (hp' u v).trans hh'.symm
  · rintro ⟨a, ha, rfl⟩
    apply (mem_allGraphIsomorphisms G H (t * a)).2
    intro u v
    exact (ha u v).trans (ht' (a u) (a v))

end GI
