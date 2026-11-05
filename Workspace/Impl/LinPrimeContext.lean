module

public import Workspace.Impl.LinPrimeRecord
public import Workspace.Impl.LinActionItem

@[expose] public section

/-! Reduce the retained generator dictionary and its identity record together.
The permutation cover and generator order stay in the same slots. -/
namespace GI.Impl
open GI.Cited GI.Lang

theorem linPrimeRecordCost_mono {W V : ℕ} (h : W ≤ V) :
    linPrimeRecordCost W ≤ linPrimeRecordCost V := by
  unfold linPrimeRecordCost linPrimeRecordBudget
  have hh := linPrimeMatrixReduceCost_mono (by omega : 100 * (W + 1) ≤ 100 * (V + 1)) h
  omega

def linPrimeContextF (map record : ℕ) : Expr :=
  .letE (.call map (mk2 (arg 0) (.get (arg 1) (.nat 1))))
    (.letE (.call record (mk2 (arg 0) (.get (arg 1) (.nat 2))))
      (mk3 (.get (arg 1) (.nat 0)) (.var 1) (.var 2)))

def linPrimeContextFuns (b : ℕ) : List Expr :=
  [linPrimeContextF (b + 1) (b + 4)] ++ mapFuns (b + 1) (b + 4) ++ linPrimeRecordFuns (b + 4)

theorem linPrimeContextFuns_length (b : ℕ) : (linPrimeContextFuns b).length = 30 := rfl

structure linPrimeContextAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linPrimeContextF (b + 1) (b + 4))
  map : P.HasAt (b + 1) (mapFuns (b + 1) (b + 4))
  record : linPrimeRecordAt P (b + 4)

theorem linPrimeContextAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linPrimeContextFuns b)) : linPrimeContextAt P b where
  entry := (h.block (gs := [linPrimeContextF (b + 1) (b + 4)]) 0 rfl).single
  map := h.block 1 rfl
  record := linPrimeRecordAt_of (h.block 4 rfl)

def linPrimeContextCellBudget (W : ℕ) : ℕ := linPrimeRecordCost (100 * (W + 1))
def linPrimeContextMapBudget (W : ℕ) : ℕ := linMapBudget (100 * (W + 1)) (linPrimeContextCellBudget W)
def linPrimeContextCost (W : ℕ) : ℕ :=
  100000 * (W + linPrimeContextCellBudget W + linPrimeContextMapBudget W + 1)

set_option maxHeartbeats 300000 in
set_option maxRecDepth 6000 in
theorem linPrimeContext_records_spec {P : Program} {b d p : ℕ} {G : Type} [Group G]
    (h : linPrimeContextAt P b) {m : Fin d → ℕ}
    (D : linPrimeSplitData m p) (hm : ∀ i, 0 < m i)
    (ρ : G →* (linFiniteVec m ≃+ linFiniteVec m)) (c : G → linFiniteVec m)
    (cover : Val) (xs : List G) :
    let q := linPrimaryOrders p D.exponent
    let old := Val.list [cover, .list (xs.map (linFiniteAffineVal m ρ c)), linFiniteAffineVal m ρ c 1]
    let a := Val.list [linVecVal (linFiniteModuli q), old]
    FunDet P b a (.list [cover,
      .list (xs.map (linFiniteAffineVal q (linPrimeAction D hm ρ) (fun g => linPrimeProjection D (c g)))),
      linFiniteAffineVal q (linPrimeAction D hm ρ) (fun g => linPrimeProjection D (c g)) 1])
      (linPrimeContextCost a.wt) := by
  let q := linPrimaryOrders p D.exponent
  let orders := linVecVal (linFiniteModuli q)
  let records := Val.list (xs.map (linFiniteAffineVal m ρ c))
  let ident := linFiniteAffineVal m ρ c 1
  let old := Val.list [cover, records, ident]
  let a := Val.list [orders, old]
  let W := a.wt
  let newRecord := linFiniteAffineVal q (linPrimeAction D hm ρ) (fun g => linPrimeProjection D (c g))
  let newRecords := Val.list (xs.map newRecord)
  have worders : orders.wt < W := wt_le_wt_list (by simp [a, W])
  have wold : old.wt < W := wt_le_wt_list (by simp [a, W])
  have wrecords : records.wt < old.wt := wt_le_wt_list (by simp [old])
  have wident : ident.wt < old.wt := wt_le_wt_list (by simp [old])
  have wcover : cover.wt < old.wt := wt_le_wt_list (by simp [old])
  have hs (g : G) (hg : (linFiniteAffineVal m ρ c g).wt ≤ W) :
      FunDet P (b + 4) (.list [orders, linFiniteAffineVal m ρ c g]) (newRecord g)
        (linPrimeContextCellBudget W) := by
    have hh := wt_list2_le orders (linFiniteAffineVal m ρ c g)
    have hb : (Val.list [orders, linFiniteAffineVal m ρ c g]).wt ≤ 100 * (W + 1) := by omega
    exact (linPrimeRecord_spec h.record D hm ρ c g).mono (linPrimeRecordCost_mono hb)
  have hmap := linMapSource_spec h.map (linFiniteAffineVal m ρ c) newRecord orders xs
    (linPrimeContextCellBudget W) (fun g hg => hs g (by
      have hh : (linFiniteAffineVal m ρ c g).wt < records.wt :=
        wt_le_wt_list (List.mem_map.mpr ⟨g, hg, rfl⟩)
      omega))
  have wmaparg : (Val.list [orders, records]).wt ≤ 100 * (W + 1) := by
    have hh := wt_list2_le orders records
    omega
  have hmap' := hmap.mono (show linMapBudget (Val.list [orders, records]).wt
    (linPrimeContextCellBudget W) ≤ linPrimeContextMapBudget W by
      simp only [linPrimeContextMapBudget, linMapBudget]
      gcongr)
  have hi := hs 1 (show ident.wt ≤ W by omega)
  have wnrecords : newRecords.wt ≤ linPrimeContextMapBudget W := hmap'.wt_lt.le
  have wnident : (newRecord 1).wt ≤ linPrimeContextCellBudget W := hi.wt_lt.le
  have dq := Det.arg' (P := P) (vs := [orders, old]) (rest := []) (j := 0) rfl
  have do' := Det.arg' (P := P) (vs := [orders, old]) (rest := []) (j := 1) rfl
  have dm := Det.call (Det.mk2 dq (Det.get' do' (Det.nat 1) rfl)) hmap'
  have dq' := Det.arg' (P := P) (vs := [orders, old]) (rest := [newRecords]) (j := 0) rfl
  have do'' := Det.arg' (P := P) (vs := [orders, old]) (rest := [newRecords]) (j := 1) rfl
  have di := Det.call (Det.mk2 dq' (Det.get' do'' (Det.nat 2) rfl)) hi
  have dout := Det.mk3
    (Det.get' (Det.arg' (P := P) (vs := [orders, old]) (rest := [newRecords, newRecord 1]) (j := 1) rfl)
      (Det.nat 0) rfl)
    (Det.var' (P := P) (env := [a, newRecords, newRecord 1]) (i := 1) rfl)
    (Det.var' (P := P) (env := [a, newRecords, newRecord 1]) (i := 2) rfl)
  apply FunDet.intro h.entry
  refine (Det.letE dm (Det.letE di dout)).mono ?_
  have wo := wt_list3_le cover newRecords (newRecord 1)
  have wa := wt_list2_le orders records
  have wi := wt_list2_le orders ident
  change _ ≤ linPrimeContextCost W
  unfold linPrimeContextCost
  dsimp only [W, a, old, records, ident, newRecords, newRecord, linPrimeContextMapBudget,
    linPrimeContextCellBudget] at *
  omega

theorem linPrimeContext_spec {P : Program} {b d p n : ℕ}
    (h : linPrimeContextAt P b) (gs : List (Equiv.Perm (Fin n))) {m : Fin d → ℕ}
    (D : linPrimeSplitData m p) (hm : ∀ i, 0 < m i)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m) :
    let a := Val.list [linVecVal (linFiniteModuli (linPrimaryOrders p D.exponent)), linActionContext gs m ρ c]
    FunDet P b a (linActionContext gs (linPrimaryOrders p D.exponent)
      (linPrimeAction D hm ρ) (fun g => linPrimeProjection D (c g))) (linPrimeContextCost a.wt) :=
  linPrimeContext_records_spec h D hm ρ c (encGroup gs) (linActionGens gs)

theorem linPrimeContextCost_poly : PBU (fun _ W _ => linPrimeContextCost W) := by
  unfold linPrimeContextCost linPrimeContextMapBudget linPrimeContextCellBudget linMapBudget
    linPrimeRecordCost linPrimeRecordBudget linFiniteMatrixReduceCost linFiniteMatrixReduceStepCost
    linFiniteMatrixReduceAcc linFiniteMatrixReduceRowBudget linConstRemCost linMapBudget
    linScalarRemCost linVectorAccWt linIntBinaryCost linIntCoreBudget linIntPartsCost linIntCodecCost
  norm_poly

end GI.Impl
