import Workspace.Transport
import Mathlib.Combinatorics.SimpleGraph.Maps

namespace GI

variable {V : Type*}

/-- The permitted action on adjacency positions is diagonal, not all pair permutations. -/
def diagonal (p : Equiv.Perm V) : Equiv.Perm (V × V) := p.prodCongr p

def adjacencyColor (G : SimpleGraph V) [DecidableRel G.Adj] : V × V → Bool :=
  fun uv => decide (G.Adj uv.1 uv.2)

theorem graph_transport_iff (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (p : Equiv.Perm V) :
    Transports (adjacencyColor G) (adjacencyColor H) (diagonal p) ↔
      ∀ u v, G.Adj u v ↔ H.Adj (p u) (p v) := by
  constructor
  · intro h u v
    have he := h (u, v)
    change decide (H.Adj (p u) (p v)) = decide (G.Adj u v) at he
    simpa only [decide_eq_decide] using he.symm
  · intro h uv
    change decide (H.Adj (p uv.1) (p uv.2)) = decide (G.Adj uv.1 uv.2)
    simp only [decide_eq_decide]
    exact (h uv.1 uv.2).symm

/-- The exact graph-isomorphism reduction in Section 3 / Algorithm 1. -/
theorem graph_iso_iff_string_iso (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] :
    Nonempty (G ≃g H) ↔ ∃ p : Equiv.Perm V,
      Transports (adjacencyColor G) (adjacencyColor H) (diagonal p) := by
  constructor
  · rintro ⟨e⟩
    refine ⟨e.toEquiv, (graph_transport_iff G H e.toEquiv).2 ?_⟩
    intro u v
    exact e.map_rel_iff.symm
  · rintro ⟨p, hp⟩
    exact ⟨{ toEquiv := p, map_rel_iff' := fun {u v} =>
      ((graph_transport_iff G H p).1 hp u v).symm }⟩

theorem adjacency_position_count [Fintype V] :
    Fintype.card (V × V) = Fintype.card V ^ 2 := by
  simp [pow_two]

theorem diagonal_injective : Function.Injective (@diagonal V) := by
  intro p q h
  ext v
  exact congrArg Prod.fst (Equiv.congr_fun h (v, v))

end GI
