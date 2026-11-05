module

public import Workspace.Impl.NClEntry
public import Workspace.Impl.CamCells
public import Workspace.Proved.SSMembership

@[expose] public section

/-!
# The normal closure from membership

`normalClosure_of`: the cited membership test gives a polynomial-time algorithm for
`NormalClosureTask`. The program is `nclFuns 0 0` with the membership algorithm as primitive `0`
(`Workspace/Impl/NClProg.lean`): it adds conjugates of the kept generators by the generators of
`⟨gs, hs⟩` until no conjugate is new, keeping only generators that enlarge the group (Luks 1993,
DIMACS 11, item (3.11), p. 145; Seress, *Permutation Group Algorithms*, Section 5.1.4). The
correctness is `ncl_correct`, the cost is `nclEntry_spec`.

`GI.Proved.normalClosure` applies `normalClosure_of` to the membership algorithm.
-/

namespace GI.Impl

open GI.Cited GI.Lang Equiv

/-- The cells of a list are at most its size plus one, if this holds for its entries. -/
theorem ncl_list_cells {vs : List Val} (h : ∀ v ∈ vs, ∀ a ∈ v.cells, a ≤ v.size + 1) :
    ∀ a ∈ (Val.list vs).cells, a ≤ (Val.list vs).size + 1 := by
  intro a ha
  have hsz : (Val.list vs).size = 3 + (Val.cellsList vs).length := by
    simp [size_eq_length]; omega
  have hlen : vs.length ≤ (Val.cellsList vs).length := by
    rw [length_cellsList]
    calc vs.length = (vs.map fun _ => 1).sum := by simp
      _ ≤ (vs.map Val.size).sum := List.sum_le_sum fun v _ => by
          have := v.two_le_size; omega
  rw [hsz]
  simp only [cells_list, List.cons_append, List.nil_append, List.mem_cons] at ha
  rcases ha with rfl | rfl | rfl | ha
  · omega
  · omega
  · omega
  obtain ⟨v, hv, ha⟩ := cam_mem_cellsList ha
  have h1 := h v hv a ha
  have h2 : v.size ≤ (Val.cellsList vs).length := by
    rw [length_cellsList]
    exact List.le_sum_of_mem (List.mem_map_of_mem hv)
  omega

theorem ncl_encGroup_cells' {n : ℕ} (gs : List (Perm (Fin n))) :
    ∀ a ∈ (encGroup gs).cells, a ≤ (encGroup gs).size + 1 := by
  intro a ha; simpa using cam_encGroup_cells gs a ha

/-- The constant of the cost. -/
noncomputable def nclK (h : Membership) : ℕ :=
  6 * ((membershipPrim h).c * 400 ^ (membershipPrim h).k) + 10 ^ 9

/-- The degree of the cost. -/
noncomputable def nclD (h : Membership) : ℕ := 6 * (membershipPrim h).k + 12

theorem ncl_cost_poly (h : Membership) {n Y : ℕ} (hn : n + 1 ≤ Y) :
    6 * (Y ^ 3 * memCost h n) + 10 ^ 9 * Y ^ 12 ≤ nclK h * Y ^ nclD h := by
  have hY : 1 ≤ Y := by omega
  set c := (membershipPrim h).c
  set k := (membershipPrim h).k
  have hm : memCost h n ≤ c * 400 ^ k * Y ^ (6 * k) := by
    unfold memCost
    have : (400 * (n + 1) ^ 6) ^ k ≤ (400 * Y ^ 6) ^ k :=
      Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn 6)) k
    calc c * (400 * (n + 1) ^ 6) ^ k ≤ c * (400 * Y ^ 6) ^ k := Nat.mul_le_mul_left _ this
      _ = c * 400 ^ k * Y ^ (6 * k) := by rw [mul_pow, ← pow_mul]; ring
  have h1 : Y ^ 3 * memCost h n ≤ c * 400 ^ k * Y ^ nclD h := by
    calc Y ^ 3 * memCost h n ≤ Y ^ 3 * (c * 400 ^ k * Y ^ (6 * k)) := Nat.mul_le_mul_left _ hm
      _ = c * 400 ^ k * Y ^ (6 * k + 3) := by ring
      _ ≤ c * 400 ^ k * Y ^ nclD h :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hY (by unfold nclD; omega))
  have h2 : Y ^ 12 ≤ Y ^ nclD h := Nat.pow_le_pow_right hY (by unfold nclD; omega)
  have e : nclK h * Y ^ nclD h = 6 * (c * 400 ^ k * Y ^ nclD h) + 10 ^ 9 * Y ^ nclD h := by
    unfold nclK; ring
  rw [e]
  omega

/-- **The program.** -/
noncomputable def nclProgram (h : Membership) : Program := ⟨nclFuns 0 0, [membershipPrim h]⟩

theorem nclProgram_at (h : Membership) : NclAt (nclProgram h) 0 0 h := by
  refine nclAt_of ?_ rfl
  have hA := Program.hasAt_append [] (nclFuns 0 0) [] [membershipPrim h]
  simpa [nclProgram] using hA

/-- **The normal closure from membership.** -/
theorem normalClosure_of (h : Membership) : NormalClosure := by
  refine polyTimeAt_ofVal_of_lang_cells (nclProgram h) 0 (nclK h) (nclD h) 1 1
    (fun I => ?_) fun I => ?_
  · intro a ha
    have := ncl_list_cells (vs := [encGroup I.gs, encGroup I.hs]) (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl <;> exact ncl_encGroup_cells' _) a ha
    simpa using this
  · refine FunAll.mono (nclEntry_spec (nclProgram_at h) I.gs I.hs) fun v c hv => ⟨?_, ?_⟩
    · rw [hv.1]
      exact ⟨nclResult I.gs I.hs, rfl, (ncl_correct I.gs I.hs).1, (ncl_correct I.gs I.hs).2⟩
    · refine hv.2.trans (ncl_cost_poly h ?_)
      have := ncl_deg_lt_wt I.gs
      have := wt_le_wt_list (show encGroup I.gs ∈ [encGroup I.gs, encGroup I.hs] by simp)
      omega

end GI.Impl

namespace GI.Proved

/-- **Normal closure** (`GI.Cited.NormalClosure`), proved from the membership algorithm. This
is the one place where the membership algorithm is supplied. -/
theorem normalClosure : GI.Cited.NormalClosure := GI.Impl.normalClosure_of GI.Proved.membership

end GI.Proved
