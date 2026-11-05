module

public import Workspace.StablePairRefinement
public import Workspace.GraphReduction
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Data.Bool.Basic

@[expose] public section

namespace GI.PairRefinement

variable {n : ℕ} {B : Type*} [LinearOrder B]

def jointInput (left right : (Fin n × Fin n) → B) (a : Domain n) : B :=
  if a.1 then right a.2 else left a.2

/-- Both inputs are compressed together, so unequal original colors on
opposite sides cannot collapse to the same new label. -/
def initialColors (left right : (Fin n × Fin n) → B) : Coloring n :=
  materialize (ColorCompression.compress (jointInput left right))

theorem initialize_eq_iff (left right : (Fin n × Fin n) → B) (a b : Domain n) :
    initialColors left right a = initialColors left right b ↔
      jointInput left right a = jointInput left right b := by
  rw [initialColors, materialize_eq]
  exact ColorCompression.compress_eq_iff _ a b

theorem initialize_transports_iff (left right : (Fin n × Fin n) → B)
    (p : Equiv.Perm (Fin n)) : Transports (initialColors left right) false true p ↔
      GI.Transports left right (GI.diagonal p) := by
  constructor
  · intro h uv
    exact (initialize_eq_iff left right _ _).mp (h uv.1 uv.2)
  · intro h x y
    exact (initialize_eq_iff left right _ _).mpr (h (x, y))

def refineInputs (left right : (Fin n × Fin n) → B) : Coloring n :=
  run (initialColors left right)

theorem refineInputs_coherent (left right : (Fin n × Fin n) → B) :
    Coherent (refineInputs left right) := run_coherent _

/-- Exact preservation of all vertex-permutation transporters, including
any subgroup of permitted permutations used by a caller. -/
theorem refineInputs_transports_iff (left right : (Fin n × Fin n) → B)
    (p : Equiv.Perm (Fin n)) : Transports (refineInputs left right) false true p ↔
      GI.Transports left right (GI.diagonal p) :=
  (run_transports_iff _ false true p).trans (initialize_transports_iff left right p)

theorem refineInputs_preserves_colors (left right : (Fin n × Fin n) → B)
    {a b : Domain n} (h : refineInputs left right a = refineInputs left right b) :
    jointInput left right a = jointInput left right b :=
  (initialize_eq_iff left right a b).mp (run_refines _ h)

/-- The returned colors on pairs encode exactly the original graph
isomorphisms; refinement itself is not a complete GI decision procedure. -/
theorem refined_graph_transport_iff (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (p : Equiv.Perm (Fin n)) :
    Transports (refineInputs (GI.adjacencyColor G) (GI.adjacencyColor H)) false true p ↔
      ∀ x y, G.Adj x y ↔ H.Adj (p x) (p y) :=
  (refineInputs_transports_iff _ _ p).trans (GI.graph_transport_iff G H p)

theorem refined_graph_iso_iff (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj] :
    Nonempty (G ≃g H) ↔ ∃ p : Equiv.Perm (Fin n),
      Transports (refineInputs (GI.adjacencyColor G) (GI.adjacencyColor H)) false true p := by
  rw [GI.graph_iso_iff_string_iso]
  exact exists_congr (fun p => (refineInputs_transports_iff _ _ p).symm)

/-- A transitive group of original automorphisms remains transitive on a
single diagonal color after refinement, giving homogeneity on that side. -/
theorem run_homogeneous (c : Coloring n) (side : Bool)
    (H : Subgroup (Equiv.Perm (Fin n))) [MulAction.IsPretransitive H (Fin n)]
    (preserves : ∀ h : H, Transports c side side h.val) (x y : Fin n) :
    run c (side, x, x) = run c (side, y, y) := by
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H x y
  change h.val x = y at hh
  have he := ((run_transports_iff c side side h.val).mpr (preserves h)) x x
  rw [hh] at he
  exact he.symm

end GI.PairRefinement
