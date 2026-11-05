module

public import Workspace.Impl.AggItemCiSojEG
public import Workspace.Impl.AggItemCiCfgA

@[expose] public section

/-!
# Numbering the color-edge exchanges by one square index

The program scans `q²` indices, with quotient and remainder giving the two
endpoints. This is the same list of edge exchanges as the nested pair scan,
up to order, and has the same component labels.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerms gens)

variable {q : ℕ}

/-- One entry of the square-indexed list of edge exchanges. -/
noncomputable def itcsSqEdge (X : PairCfg q) (v : ℕ) (t : Fin (q * q)) : Perm (Fin q) :=
  itcsEdge X v ((itciPE q).symm t).1 ((itciPE q).symm t).2

/-- The square-indexed list seen by the table-construction program. -/
noncomputable def itcsSqEdges (X : PairCfg q) (v : ℕ) : List (Perm (Fin q)) :=
  (List.finRange (q * q)).map (itcsSqEdge X v)

/-- The two scans have exactly the same entries. -/
theorem itcs_sq_edges_mem (X : PairCfg q) (v : ℕ) (g : Perm (Fin q)) :
    g ∈ itcsSqEdges X v ↔ g ∈ itcsEdges X v := by
  constructor
  · intro h
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 h
    exact List.mem_flatMap.2 ⟨((itciPE q).symm t).1, List.mem_finRange _,
      List.mem_map.2 ⟨((itciPE q).symm t).2, List.mem_finRange _, rfl⟩⟩
  · intro h
    obtain ⟨a, -, hb⟩ := List.mem_flatMap.1 h
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hb
    exact List.mem_map.2 ⟨itciPE q (a, b), List.mem_finRange _, by
      simp only [itcsSqEdge, Equiv.symm_apply_apply]⟩

/-- Their generated groups, used only as component encodings, are equal. -/
theorem itcs_sq_edges_gens (X : PairCfg q) (v : ℕ) :
    gens (itcsSqEdges X v) = gens (itcsEdges X v) := by
  unfold gens
  congr 1
  ext g
  exact itcs_sq_edges_mem X v g

/-- The orbit program returns the same fixed component labels for the square scan. -/
theorem itcs_sq_labels (X : PairCfg q) (v : ℕ) :
    orbitLabels (itcsSqEdges X v) = itcsLab X v := by
  have horb (a b : Fin q) : b ∈ genOrbit (itcsSqEdges X v) a ↔ X.reach v a b := by
    have he := itcs_sq_edges_gens X v
    change b ∈ MulAction.orbit (gens (itcsSqEdges X v)) a ↔ _
    rw [he]
    exact itcs_orbit_iff X v a b
  funext a
  obtain ⟨hlt, hmem, hmin⟩ := (orbitLabels_spec (itcsSqEdges X v)).2 a
  apply le_antisymm
  · exact hmin _ ((horb a _).2 (PairCfg.mem_comp.1 (itcs_center_mem X v a)))
  · exact Fin.le_def.1 (itcs_center_le ((itcs_lab_eq X v a _).2 ((horb a _).1 hmem)))

/-- The length is the number of indices scanned. -/
theorem itcs_sq_length (X : PairCfg q) (v : ℕ) : (itcsSqEdges X v).length = q * q := by
  simp [itcsSqEdges]

/-- The component table from the indexed exchanges has the same polynomial cost. -/
theorem itcs_sq_table {Pg : Program} {fo : ℕ}
    (ho : Pg.HasAt fo (orbitFuns fo)) (X : PairCfg q) (v : ℕ) :
    FunDet Pg fo (encPerms (itcsSqEdges X v)) (encFun (itcsLab X v))
      (orbitK * ((q * q + 1) * (q + 1)) ^ 5) := by
  have h := orbitFuns_spec ho (itcsSqEdges X v)
  rwa [itcs_sq_labels, itcs_sq_length] at h

end GI.Impl
