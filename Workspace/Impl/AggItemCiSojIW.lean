module

public import Workspace.Impl.AggItemCiSojLC

@[expose] public section

/-!
# Sizes recorded in the projection input

Degrees are stored through identity permutation tables as well as numbers. Thus
both degrees and the graph-generator count are bounded by the weight of the
stored lift context. A nonempty canonical answer similarly bounds its generator
count and its physical degree through the encoded representative and group.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup)

variable {k q : ℕ}

/-- A permutation table contains one entry for every point of its degree. -/
theorem itcs_perm_degree (p : Perm (Fin k)) : k≤(encPerm p).wt := by
  have h:=length_lt_wt_list ((List.finRange k).map fun i=>Val.nat (p i))
  rw [List.length_map,List.length_finRange] at h; exact h.le

/-- The group value records every generator, in addition to its leading identity. -/
theorem itcs_group_length (gs : List (Perm (Fin k))) : gs.length≤(encGroup gs).wt := by
  have h:=length_lt_wt_list ((1::gs).map encPerm)
  have hl : gs.length+1≤(Val.list ((1::gs).map encPerm)).wt := by
    simpa only [List.length_map,List.length_cons] using h.le
  have hm : (Val.list ((1::gs).map encPerm)).wt≤(encGroup gs).wt :=
    st_wt_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  exact (Nat.le_add_right _ _).trans (hl.trans hm)

/-- Both degrees occur as identity tables in the split context. -/
theorem itcs_split_degrees : k≤(pSplitCtx k q).wt ∧ q≤(pSplitCtx k q).wt := by
  have hi : (Val.list [encPerm (1:Perm (Fin k)),encPerm (1:Perm (Fin q))]).wt≤(pSplitCtx k q).wt :=
    st_wt_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  exact ⟨(itcs_perm_degree (1:Perm (Fin k))).trans ((st_wt_mem (List.mem_cons_self ..)).trans hi),
    (itcs_perm_degree (1:Perm (Fin q))).trans
      ((st_wt_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))).trans hi)⟩

/-- The physical degree, label degree, and generator count all fit the context's
actual input weight. No bound on a bare encoded natural is inferred. -/
theorem itcs_lift_sizes (ps : List (Perm (Fin k)×Perm (Fin q))) :
    k≤(liftLabCtx k q ps).wt ∧ q≤(liftLabCtx k q ps).wt ∧ ps.length≤(liftLabCtx k q ps).wt := by
  have hs : (pSplitCtx k q).wt≤(liftLabCtx k q ps).wt := by
    change (pSplitCtx k q).wt≤(Val.list [.nat k,encGroup (ps.map encPair),
      encGroup ((onePairs ps).map encPair),pSplitCtx k q]).wt
    exact st_wt_mem (by simp)
  have hg : (encGroup (ps.map encPair)).wt≤(liftLabCtx k q ps).wt :=
    st_wt_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hl:=itcs_group_length (ps.map encPair)
  simp only [List.length_map] at hl
  exact ⟨itcs_split_degrees.1.trans hs,itcs_split_degrees.2.trans hs,hl.trans hg⟩

end GI.Impl
