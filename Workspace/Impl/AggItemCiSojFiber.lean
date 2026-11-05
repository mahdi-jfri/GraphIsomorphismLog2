module

public import Workspace.Impl.AggItemCiSojBal
public import Workspace.Impl.AggItemCiSojTP

@[expose] public section

/-!
# Constructing the source fiber list

Filter the old label range by the diagonal-color test. The resulting increasing
list is exactly the fiber enumeration used by the model and by the pair-table
reader, so the pair scan uses the same indices as `SojChoice.imp`.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv
open GI.Cited (Val)

/-- Cost of the fiber filter, including its complete output table. -/
def itcsFiberC (q B : ℕ) : ℕ :=
  q * (30 * (itcsBalW q B + 1)) + loopModK * (q + 1) *
    (2 * itCfObjB q B + 13 * (q + 1) ^ 2 + q + 7)

/-- The diagonal-color filter computes the exact increasing fiber list. -/
theorem itcs_fiber_prog {q B : ℕ} {Pg : Program} {ff fb : ℕ}
    (hf : Pg.HasAt ff (filterFuns ff fb)) (hfb : Pg.funs[fb]? = some itcqFbT)
    (X : PairCfg q) (x₀ : Fin q) (hcol : itCfColsLe (.pair X x₀) B) :
    FunDet Pg ff (.list [rcCertIn X x₀, natList (List.range q)]) (itcqFV X) (itcsFiberC q B) := by
  have h := filter_spec hf (c := rcCertIn X x₀) (xs := (List.range q).map Val.nat)
    (q := itcqFq X) (B := fun _ => 30 * (itcsBalW q B + 1)) (fun w hw => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hw
      have hat := List.mem_range.1 ha
      have hw := itcs_bal_weight X x₀ ⟨a, hat⟩ hcol
      exact itcq_fbT_spec hfb X x₀ ⟨a, hat⟩ hw.1)
  rw [itcq_fq_filter] at h
  have hc : (rcCertIn X x₀).wt ≤ itCfObjB q B :=
    (st_wt_mem (by simp : rcCertIn X x₀ ∈ [.nat 2, rcCertIn X x₀])).trans
      (itCfOutV_wt_le hcol)
  have hr := wt_range_le q
  have hout := itcs_fv_weight X
  have hin := wt_list2_le (rcCertIn X x₀) (natList (List.range q))
  refine FunAll.mono h fun w cost ⟨hw, hcost⟩ => ?_
  have he : w = itcqFV X := hw
  refine ⟨he, ?_⟩
  rw [he] at hcost
  simp only [List.map_const', List.sum_replicate, List.length_map, List.length_range,
    smul_eq_mul] at hcost
  have harg : (Val.list [rcCertIn X x₀, natList (List.range q)]).wt + q + (itcqFV X).wt + 1 ≤
      2 * itCfObjB q B + 13 * (q + 1) ^ 2 + q + 7 := by omega
  exact hcost.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ harg) _)

/-- The fiber construction is polynomial at the round's degree and palette bound. -/
theorem itcs_fiber_pbu : PBU fun _ W _ => itcsFiberC (2 * W + 3) (2 * (2 * W + 3) ^ 64) := by
  simp only [itcsFiberC, itcsBalW, itCfObjB, loopModK]
  norm_poly

end GI.Impl
