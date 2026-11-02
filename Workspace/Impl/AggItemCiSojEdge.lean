import Workspace.Impl.AggItemCiSojComp
import Workspace.Lang.Lib.Orbit

/-!
# Computing the component labels with the orbit table program

An undirected color edge can exchange its two endpoints. The orbits of all these
exchanges are exactly the connected components. This lets us reuse the existing
finite orbit-table program to compute the least-component labels. The auxiliary
group is only an encoding of reachability, not a replacement for the component
partition or for a rectangle call.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm Finset
open GI.Cited (gens Val encPerms)

variable {q : ℕ}

open Classical in
/-- Exchange the endpoints of an edge, and do nothing for a nonedge. -/
noncomputable def itcsEdge (X : PairCfg q) (v : ℕ) (a b : Fin q) : Perm (Fin q) :=
  if X.edge v a b then Equiv.swap a b else 1

/-- All color-edge exchanges on the label set. -/
noncomputable def itcsEdges (X : PairCfg q) (v : ℕ) : List (Perm (Fin q)) :=
  (List.finRange q).flatMap fun a => (List.finRange q).map (itcsEdge X v a)

/-- Every actual edge exchange appears in the list. -/
theorem itcs_edge_mem {X : PairCfg q} {v : ℕ} {a b : Fin q} (hab : X.edge v a b) :
    Equiv.swap a b ∈ itcsEdges X v := by
  classical
  apply List.mem_flatMap.2
  refine ⟨a, List.mem_finRange _, List.mem_map.2 ⟨b, List.mem_finRange _, ?_⟩⟩
  simp only [itcsEdge, if_pos hab]

/-- One generator moves each point within its component. -/
theorem itcs_edge_reach (X : PairCfg q) (v : ℕ) (a b z : Fin q) :
    X.reach v z (itcsEdge X v a b z) := by
  classical
  unfold itcsEdge
  split_ifs with hab
  · by_cases hza : z = a
    · subst z
      rw [Equiv.swap_apply_left]
      exact Relation.ReflTransGen.single hab
    · by_cases hzb : z = b
      · subst z
        rw [Equiv.swap_apply_right]
        exact PairCfg.reach_symm (Relation.ReflTransGen.single hab)
      · rw [Equiv.swap_apply_of_ne_of_ne hza hzb]
        exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.refl

/-- Every generated permutation moves each point within its component. -/
theorem itcs_edges_reach {X : PairCfg q} {v : ℕ} {g : Perm (Fin q)}
    (hg : g ∈ gens (itcsEdges X v)) (a : Fin q) : X.reach v a (g a) := by
  have key : ∀ g ∈ gens (itcsEdges X v), ∀ a, X.reach v a (g a) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨a, -, hb⟩ := List.mem_flatMap.1 hg
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 hb
      exact itcs_edge_reach X v a b
    | one => intro a; exact Relation.ReflTransGen.refl
    | mul g h _ _ hg hh =>
      intro a
      exact (hh a).trans (hg (h a))
    | inv g _ hg =>
      intro a
      have h := PairCfg.reach_symm (hg (g⁻¹ a))
      simpa only [Perm.apply_inv_self] using h
  exact key g hg a

/-- A path is a sequence of edge exchanges, so it lies in one orbit. -/
theorem itcs_orbit_of_reach {X : PairCfg q} {v : ℕ} {a b : Fin q}
    (hab : X.reach v a b) : b ∈ genOrbit (itcsEdges X v) a := by
  rw [mem_genOrbit]
  induction hab with
  | refl => exact ⟨1, Subgroup.one_mem _, rfl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨g, hg, hga⟩ := ih
    exact ⟨Equiv.swap b c * g,
      Subgroup.mul_mem _ (Subgroup.subset_closure (itcs_edge_mem hbc)) hg, by
        rw [Perm.mul_apply, hga, Equiv.swap_apply_left]⟩

/-- The orbit relation of the edge exchanges is exactly the component relation. -/
theorem itcs_orbit_iff (X : PairCfg q) (v : ℕ) (a b : Fin q) :
    b ∈ genOrbit (itcsEdges X v) a ↔ X.reach v a b := by
  constructor
  · intro h
    obtain ⟨g, hg, rfl⟩ := mem_genOrbit.1 h
    exact itcs_edges_reach hg a
  · exact itcs_orbit_of_reach

/-- The orbit program's least labels are the least-component labels already used
by the imprimitive item proof. -/
theorem itcs_orbit_labels (X : PairCfg q) (v : ℕ) :
    orbitLabels (itcsEdges X v) = itcsLab X v := by
  funext a
  obtain ⟨hlt, hmem, hmin⟩ := (orbitLabels_spec (itcsEdges X v)).2 a
  apply le_antisymm
  · exact hmin _ (itcs_orbit_of_reach (PairCfg.mem_comp.1 (itcs_center_mem X v a)))
  · exact Fin.le_def.1 (itcs_center_le ((itcs_lab_eq X v a _).2
      ((itcs_orbit_iff X v a _).1 hmem)))

/-- The edge list has exactly `q²` entries. -/
theorem itcs_edges_length (X : PairCfg q) (v : ℕ) : (itcsEdges X v).length = q * q := by
  simp [itcsEdges, List.length_flatMap]

/-- The existing orbit-table program computes the exact component labels. -/
theorem itcs_component_table {Pg : Program} {fo : ℕ}
    (ho : Pg.HasAt fo (orbitFuns fo)) (X : PairCfg q) (v : ℕ) :
    FunDet Pg fo (encPerms (itcsEdges X v)) (encFun (itcsLab X v))
      (orbitK * ((q * q + 1) * (q + 1)) ^ 5) := by
  have h := orbitFuns_spec ho (itcsEdges X v)
  rwa [itcs_orbit_labels, itcs_edges_length] at h

end GI.Impl
