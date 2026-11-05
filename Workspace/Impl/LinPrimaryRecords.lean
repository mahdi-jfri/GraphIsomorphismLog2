module

public import Workspace.Impl.LinPrimaryRecord

@[expose] public section

/-! Build all field-layer generator data from the retained full action. The
map is valid even when the action has a kernel. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linPrimaryRecordsFuns (b : ℕ) : List Expr :=
  mapFuns b (b + 3) ++ linPrimaryRecordFuns (b + 3)

theorem linPrimaryRecordsFuns_length (b : ℕ) : (linPrimaryRecordsFuns b).length = 80 := rfl

structure linPrimaryRecordsAt (P : Program) (b : ℕ) : Prop where
  map : P.HasAt b (mapFuns b (b + 3))
  record : linPrimaryRecordAt P (b + 3)

theorem linPrimaryRecordsAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linPrimaryRecordsFuns b)) : linPrimaryRecordsAt P b where
  map := h.block 0 rfl
  record := linPrimaryRecordAt_of (h.block 3 rfl)

def linPrimaryRecordsCost (W : ℕ) : ℕ := linMapBudget W (linPrimaryRecordCost (100 * (W + 1)))

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 6000 in
theorem linPrimaryRecords_spec {P : Program} {b p d : ℕ} {G : Type} [Group G]
    (h : linPrimaryRecordsAt P b) (hp : p.Prime) (ν : Fin d → ℕ) (level : ℕ)
    (ρ : G →* (linFiniteVec (linPrimaryOrders p ν) ≃+ linFiniteVec (linPrimaryOrders p ν)))
    (c : G → linFiniteVec (linPrimaryOrders p ν)) (xs : List G) :
    let m := linPrimaryOrders p ν
    let ctx := Val.list [.nat p, encFun ν, .nat level, .nat (p ^ level)]
    let records := xs.map (linFiniteAffineVal m ρ c)
    let a := Val.list [ctx, .list records]
    FunDet P b a (.list (xs.map fun g => .list
      [encModMatrix (linPrimaryFieldRep p hp.pos ν level ρ g).val,
       encVec (linPrimaryCoord p ν level (c g))])) (linPrimaryRecordsCost a.wt) := by
  let m := linPrimaryOrders p ν
  let ctx := Val.list [.nat p, encFun ν, .nat level, .nat (p ^ level)]
  let records := xs.map (linFiniteAffineVal m ρ c)
  let a := Val.list [ctx, .list records]
  let W := a.wt
  apply linMapSource_spec h.map (linFiniteAffineVal m ρ c) _ ctx xs
    (linPrimaryRecordCost (100 * (W + 1)))
  intro g hg
  have wc : ctx.wt < W := wt_le_wt_list (by simp [W, a])
  have wrs : (Val.list records).wt < W := wt_le_wt_list (by simp [W, a])
  have wr : (linFiniteAffineVal m ρ c g).wt < W :=
    (wt_le_wt_list (List.mem_map.mpr ⟨g, hg, rfl⟩)).trans wrs
  have wa : (Val.list [ctx, linFiniteAffineVal m ρ c g]).wt ≤ 100 * (W + 1) := by
    have hh := wt_list2_le ctx (linFiniteAffineVal m ρ c g)
    omega
  exact (linPrimaryRecord_spec h.record hp ν level (ρ g).toAddMonoidHom (c g)
    (encIntMatrix (linFiniteActionMatrix m ρ c g⁻¹))).mono (linPrimaryRecordCost_mono wa)

theorem linPrimaryRecordsCost_mono {W V : ℕ} (h : W ≤ V) :
    linPrimaryRecordsCost W ≤ linPrimaryRecordsCost V :=
  linMapBudget_mono h (linPrimaryRecordCost_mono (by omega))

theorem linPrimaryRecordsCost_poly : PBU (fun _ W _ => linPrimaryRecordsCost W) := by
  have hr := linPoly_subst linPrimaryRecordCost_poly (PBU.const 0)
    (PBU.smul 100 (PBU.addc PBU.W 1)) (PBU.const 0)
  exact linPoly_subst (f := fun W B _ => linMapBudget W B) (by unfold linMapBudget; norm_poly)
    PBU.W hr (PBU.const 0)

end GI.Impl
