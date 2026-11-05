module

public import Workspace.Impl.LinMapEncoded

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang GI.Machine

/-- Concatenation adds the entry weights. Only the two list headers change. -/
theorem linListAppendWt (xs ys : List Val) :
    (Val.list (xs ++ ys)).wt ≤ (Val.list xs).wt + (Val.list ys).wt + 2 := by
  rw [wt_list_eq, wt_list_eq, wt_list_eq]
  simp only [List.map_append, List.sum_append, List.length_append]
  have h₁ := len_add_le_add xs.length ys.length
  have h₂ := len_add_le_add (xs.map Val.size).sum (ys.map Val.size).sum
  omega

end GI.Impl
