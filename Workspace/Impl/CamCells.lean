import Workspace.Lang.Bridge
import Workspace.Lang.Glue
import Workspace.Cited.AlgoPermGroups

/-!
# The cells of a group encoding are at most its size

The hypothesis `hcells` of `GI.Lang.polyTimeAt_ofVal_of_lang_cells`, for `enc = encGroup`, with
`A = 1, E = 1`. The cells of `encGroup gs` are counts (at most the size), the degree `n` and its
double `2n` (at most the size, since the identity alone takes `2n + 3` cells), and points `< n`.
-/

namespace GI.Impl

open GI.Cited GI.Lang

theorem cam_mem_cellsList {a : ℕ} {vs : List Val} (h : a ∈ Val.cellsList vs) :
    ∃ v ∈ vs, a ∈ v.cells := by
  induction vs with
  | nil => simp at h
  | cons v vs ih =>
    rw [cellsList_cons, List.mem_append] at h
    rcases h with h | h
    · exact ⟨v, List.mem_cons_self .., h⟩
    · obtain ⟨w, hw, h⟩ := ih h
      exact ⟨w, List.mem_cons_of_mem _ hw, h⟩

theorem cam_encPerm_cells {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ∀ a ∈ (encPerm σ).cells, a ≤ 2 * n + 1 := by
  intro a ha
  simp only [encPerm, cells_list, List.length_map, List.length_finRange] at ha
  rw [show (List.finRange n).map (fun i => Val.nat (σ i)) =
    ((List.finRange n).map fun i => ((σ i : Fin n) : ℕ)).map Val.nat by simp,
    length_cellsList_map_nat] at ha
  simp only [List.length_map, List.length_finRange, List.cons_append, List.nil_append,
    List.mem_cons] at ha
  rcases ha with rfl | rfl | rfl | ha
  · omega
  · omega
  · omega
  obtain ⟨v, hv, ha⟩ := cam_mem_cellsList ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hv
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hb
  simp only [cells_nat, List.mem_cons, List.not_mem_nil, or_false] at ha
  have := (σ i).2
  omega

theorem cam_encPerm_size {n : ℕ} (σ : Equiv.Perm (Fin n)) : (encPerm σ).cells.length = 2 * n + 3 := by
  simp only [encPerm, cells_list, List.length_append, List.length_cons, List.length_nil]
  rw [show (List.finRange n).map (fun i => Val.nat (σ i)) =
    ((List.finRange n).map fun i => ((σ i : Fin n) : ℕ)).map Val.nat by simp,
    length_cellsList_map_nat]
  simp; omega

/-- **The cells of a group encoding are at most its size plus one.** -/
theorem cam_encGroup_cells {n : ℕ} (gs : List (Equiv.Perm (Fin n))) :
    ∀ a ∈ (encGroup gs).cells, a ≤ 1 * ((encGroup gs).size + 1) ^ 1 := by
  intro a ha
  rw [one_mul, pow_one, size_eq_length]
  set X := Val.cellsList ((1 :: gs).map encPerm) with hX
  have hlen : (encGroup gs).cells.length = 8 + X.length := by
    simp only [encGroup, encPerms, cells_list, cellsList_cons, cellsList_nil, cells_nat,
      List.length_append, List.length_cons, List.length_nil, ← hX]
    omega
  have h2n : 2 * n + 3 ≤ X.length := by
    rw [hX, List.map_cons, cellsList_cons, List.length_append, cam_encPerm_size]
    omega
  have hk : ((1 :: gs).map encPerm).length ≤ X.length := by
    rw [hX]
    exact (Nat.le_mul_of_pos_left _ (by omega)).trans (length_le_cellsList _)
  rw [hlen]
  simp only [encGroup, encPerms, cells_list, cellsList_cons, cellsList_nil, cells_nat,
    List.length_cons, List.length_nil, List.append_nil, ← hX, List.cons_append,
    List.nil_append, List.mem_cons, List.mem_append] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ha
  all_goals try omega
  · obtain ⟨v, hv, ha⟩ := cam_mem_cellsList ha
    obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hv
    have := cam_encPerm_cells σ a ha
    omega

end GI.Impl
