module

public import Workspace.JohnsonForest

@[expose] public section

namespace GI.Johnson
namespace RefinementTree

variable {α : Type*} [DecidableEq α]

theorem Valid.mono_anchors {T U : Finset α} (hTU : T ⊆ U) {t : RefinementTree α}
    (h : t.Valid T) : t.Valid U := by
  induction t with
  | leaf E =>
      obtain ⟨hc, x, hx⟩ := h
      exact ⟨hc, x, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
        hTU (Finset.mem_inter.mp hx).2⟩⟩
  | shrink E t ih => exact ⟨h.1, ih h.2.1, h.2.2⟩
  | fork E t u iht ihu =>
      exact ⟨h.1, iht h.2.1, ihu h.2.2.1, h.2.2.2⟩

noncomputable def extraAllowance (C B : ℝ) (t : RefinementTree α) : ℝ :=
  (t.extraStarts.map fun (n : ℕ) => C * Real.log (n : ℝ) - B).sum

omit [DecidableEq α] in
theorem root_add_extraAllowance (C B : ℝ) (t : RefinementTree α) :
    (C * Real.log (t.region.card : ℝ) - B) + t.extraAllowance C B =
      C * t.weight - B * (t.leaves : ℝ) := by
  have h := allowance_sum C B t
  simpa only [starts, List.map_cons, List.sum_cons, extraAllowance] using h

omit [DecidableEq α] in
theorem extraAllowance_leaf (C B : ℝ) (E : Finset α) : (leaf E).extraAllowance C B = 0 := rfl

omit [DecidableEq α] in
theorem extraAllowance_shrink (C B : ℝ) (E : Finset α) (t : RefinementTree α) :
    (shrink E t).extraAllowance C B = t.extraAllowance C B := rfl

omit [DecidableEq α] in
theorem extraAllowance_fork (C B : ℝ) (E : Finset α) (t u : RefinementTree α) :
    (fork E t u).extraAllowance C B = t.extraAllowance C B +
      (C * Real.log (u.region.card : ℝ) - B) + u.extraAllowance C B := by
  simp only [extraAllowance, extraStarts, List.map_append, List.map_cons,
    List.sum_append, List.sum_cons]
  ring

omit [DecidableEq α] in
theorem startAllowance_flatMap (C B : ℝ) (ts : List (RefinementTree α)) :
    ((ts.flatMap starts).map fun (n : ℕ) => C * Real.log (n : ℝ) - B).sum =
      (ts.map fun t => (C * Real.log (t.region.card : ℝ) - B) + t.extraAllowance C B).sum := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, ih,
        starts, List.map_cons, List.sum_cons, extraAllowance]

omit [DecidableEq α] in
theorem charge_bound_of_extra {C B charge remaining : ℝ} {t : RefinementTree α}
    (hcharge : charge ≤ remaining + t.extraAllowance C B)
    (hroot : remaining ≤ C * Real.log (t.region.card : ℝ) - B) :
    charge ≤ C * t.weight - B * (t.leaves : ℝ) := by
  rw [← root_add_extraAllowance C B t]
  linarith

end RefinementTree
end GI.Johnson
