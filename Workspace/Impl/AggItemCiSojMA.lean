import Workspace.Impl.AggItemCiSojMin

/-! # The complete check of target component sizes -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)

variable {q : ℕ}

/-- A budget for the target component check and its fiber tests. -/
def itcsMinW (q B : ℕ) : ℕ := 100 * (itCfObjB q B + (q + 1) ^ 2 + q + 10)

/-- Total cost of the finite conjunction. -/
def itcsMinC (q B : ℕ) : ℕ :=
  q * (200 * (itcsMinW q B + 1) + (countK + 1000) * (q + 1) ^ 3) +
    loopModK * (q + 1) * (itcsMinW q B + q + 4)

open Classical in
/-- The literal size predicate on encoded vertices. -/
noncomputable def itcsMinQ (Y : PairCfg q) (v : ℕ) : Val → Bool
  | .nat a => if ha : a < q then decide (⟨a, ha⟩ ∈ Y.fiber → 2 ≤ (Y.comp v ⟨a, ha⟩).card) else false
  | _ => false

open Classical in
/-- The scan checks every interior component. -/
theorem itcs_min_all (Y : PairCfg q) (v : ℕ) :
    ((List.finRange q).map (fun a => Val.nat a.val)).all (itcsMinQ Y v) =
      decide (∀ a ∈ Y.fiber, 2 ≤ (Y.comp v a).card) := by
  apply Bool.eq_iff_iff.2
  simp only [List.all_map, List.all_eq_true, List.mem_finRange, true_implies,
    Function.comp_apply, itcsMinQ, dif_pos (Fin.isLt _), decide_eq_true_eq]

open Classical in
/-- Every callback and weight premise of the target-size conjunction follows from
its palette bound and the computed least-component labels. -/
theorem itcs_min_prog {Pg : Program} {all f fb sz cnt B : ℕ}
    (ha : Pg.HasAt all (allFuns all f)) (hf : Pg.funs[f]? = some (itcsMinF fb sz))
    (hb : Pg.funs[fb]? = some itcqFbT) (hs : Pg.funs[sz]? = some (itSzB cnt))
    (hc : Pg.HasAt cnt (countFuns cnt)) (Y : PairCfg q) (y₀ : Fin q) (v : ℕ)
    (hcol : itCfColsLe (.pair Y y₀) B) :
    FunDet Pg all (.list [.list [encFun (itcsLab Y v), rcCertIn Y y₀], natList (List.range q)])
      (boolVal (decide (∀ a ∈ Y.fiber, 2 ≤ (Y.comp v a).card))) (itcsMinC q B) := by
  have hcert : (rcCertIn Y y₀).wt ≤ itCfObjB q B :=
    (st_wt_mem (by simp : rcCertIn Y y₀ ∈ [.nat 2, rcCertIn Y y₀])).trans (itCfOutV_wt_le hcol)
  have hlab := it_encFun_wt (itcsLab Y v) (fun a => (itcs_lab_lt Y v a).le)
  have hctx := wt_list2_le (encFun (itcsLab Y v)) (rcCertIn Y y₀)
  let ctx : Val := .list [encFun (itcsLab Y v), rcCertIn Y y₀]
  have hin {a : Fin q} : (Val.list [ctx, .nat a]).wt ≤ itcsMinW q B := by
    have h := wt_list2_le ctx (.nat a)
    have han := wt_nat_le (a : ℕ)
    have haq := a.isLt
    dsimp only [ctx] at h ⊢
    unfold itcsMinW
    omega
  have hfb {a : Fin q} : (Val.list [rcCertIn Y y₀, .nat a]).wt ≤ itcsMinW q B := by
    have h := wt_list2_le (rcCertIn Y y₀) (.nat a)
    have han := wt_nat_le (a : ℕ)
    have haq := a.isLt
    unfold itcsMinW
    omega
  have hsz {a : Fin q} : (Val.list [encFun (itcsLab Y v), .nat a]).wt ≤ itcsMinW q B := by
    have h := wt_list2_le (encFun (itcsLab Y v)) (.nat a)
    have han := wt_nat_le (a : ℕ)
    have haq := a.isLt
    unfold itcsMinW
    omega
  have hh := all_spec ha (c := ctx) (xs := (List.finRange q).map fun a => Val.nat a.val)
    (q := itcsMinQ Y v) (B := fun _ => 200 * (itcsMinW q B + 1) + (countK + 1000) * (q + 1) ^ 3)
    (fun a ha => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 ha
      simpa only [itcsMinQ, dif_pos i.isLt] using
        itcs_min_spec hf hb hs hc Y y₀ i v hin hfb hsz (by unfold itcsMinW; omega))
  rw [itcs_min_all Y v] at hh
  have hmain : (Val.list [ctx, .list ((List.finRange q).map fun a => Val.nat a.val)]).wt ≤ itcsMinW q B := by
    have hr := it_range_wt (q := q)
    rw [it_range_eq] at hr
    have hh := wt_list2_le ctx (.list ((List.finRange q).map fun a => Val.nat a.val))
    dsimp only [ctx] at hh ⊢
    unfold itcsMinW
    omega
  have hdet : FunDet Pg all (.list [ctx, .list ((List.finRange q).map fun a => Val.nat a.val)])
      (boolVal (decide (∀ a ∈ Y.fiber, 2 ≤ (Y.comp v a).card)))
      (q * (200 * (itcsMinW q B + 1) + (countK + 1000) * (q + 1) ^ 3) +
        loopModK * (q + 1) * ((Val.list [ctx, .list ((List.finRange q).map fun a => Val.nat a.val)]).wt + q + 4)) := by
    simpa only [List.map_map, Function.comp_def, List.map_const', List.sum_replicate,
      List.length_map, List.length_finRange] using hh
  rw [← it_range_eq] at hdet
  exact hdet.mono (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by rw [it_range_eq]; omega)) _)

/-- Polynomial round bound for the target component check. -/
theorem itcs_min_pbu : PBU fun _ W _ => itcsMinC (2 * W + 3) (2 * (2 * W + 3) ^ 64) := by
  simp only [itcsMinC, itcsMinW, itCfObjB, countK, loopModK]
  norm_poly

end GI.Impl
