module

public import Workspace.Impl.LinRecenterContext
public import Workspace.Impl.LinMapSource

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang
set_option maxRecDepth 16000

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
theorem linRecenterContext_spec {P : Program} {b d : ℕ} {G : Type} [Group G]
    (h : linRecenterContextAt P b) (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (ρ : G →* (linFiniteVec m ≃+ linFiniteVec m)) (c : G → linFiniteVec m)
    (hc : ∀ g k, c (g * k) = ρ g (c k) + c g)
    (cover unused : Val) (w : linFiniteVec m) (g : G) (xs : List G) :
    let a := Val.list [cover, linVecVal (fun i => (m i : ℤ)),
      .list ((g :: xs).map (linPlainAffineVal m ρ c)), unused, linVecVal (fun i => ((w i).val : ℤ))]
    FunDet P b a (.list [cover,
      .list ((g :: xs).map (linFiniteAffineVal m ρ (linFiniteRecenter ρ c w))),
      linFiniteAffineVal m ρ (linFiniteRecenter ρ c w) 1]) (linRecenterContextCost a.wt) := by
  let orders := linVecVal (fun i => (m i : ℤ))
  let wv := linVecVal (fun i => ((w i).val : ℤ))
  let raw := Val.list ((g :: xs).map (linPlainAffineVal m ρ c))
  let a := Val.list [cover, orders, raw, unused, wv]
  let W := a.wt
  let ctx := Val.list [orders, wv]
  let c' := linFiniteRecenter ρ c w
  let recordVal := linFiniteAffineVal m ρ c'
  let records := Val.list ((g :: xs).map recordVal)
  have wo : orders.wt < W := wt_le_wt_list (by simp [a, W])
  have ww : wv.wt < W := wt_le_wt_list (by simp [a, W])
  have wr : raw.wt < W := wt_le_wt_list (by simp [a, W])
  have wc : cover.wt < W := wt_le_wt_list (by simp [a, W])
  have wctx : ctx.wt ≤ 10 * (W + 1) := by
    have hh := wt_list2_le orders wv
    dsimp only [ctx]
    omega
  have hd : d ≤ W := by
    have hh := length_lt_wt_list ((List.finRange d).map fun i => encInt (m i : ℤ))
    simp only [List.length_map, List.length_finRange] at hh
    change d < orders.wt at hh
    omega
  have hcell (k : G) (hk : k ∈ g :: xs) :
      FunDet P (b + 4) (.list [ctx, linPlainAffineVal m ρ c k]) (recordVal k)
        (linRecenterRecordCost (100 * (W + 1))) := by
    have wk : (linPlainAffineVal m ρ c k).wt < raw.wt := wt_le_wt_list (List.mem_map.mpr ⟨k, hk, rfl⟩)
    have hh := wt_list2_le ctx (linPlainAffineVal m ρ c k)
    have hb : (Val.list [ctx, linPlainAffineVal m ρ c k]).wt ≤ 100 * (W + 1) := by omega
    exact (linRecenterRecord_spec h.record m hm ρ c w k).mono (linRecenterRecordCost_mono hb)
  have hmap := linMapSource_spec h.map (linPlainAffineVal m ρ c) recordVal ctx (g :: xs) _ hcell
  have wmaparg : (Val.list [ctx, raw]).wt ≤ 100 * (W + 1) := by
    have hh := wt_list2_le ctx raw
    omega
  have hmap' := hmap.mono (linMapBudget_mono wmaparg le_rfl)
  have wrecords : records.wt ≤ linRecenterContextMapBudget W := hmap'.wt_lt.le
  have wfirst : (recordVal g).wt < records.wt := wt_le_wt_list (by simp [records])
  have hcp := linFiniteRecenter_cocycle ρ c hc w
  have hprod0 := linFiniteActionMul_uniform m ρ c' h.mul hm hcp g g⁻¹
  simp only [mul_inv_cancel] at hprod0
  have hb := (linPoly_source_bound linFiniteActionOpCost_poly).choose_spec.choose_spec d orders.wt W hd wo.le
  have hprod := hprod0.mono hb
  have wid : (recordVal 1).wt ≤ linRecenterContextIdBudget W := hprod.wt_lt.le
  have wmod : (linVecVal (linFiniteModuli m)).wt < (recordVal g).wt :=
    wt_le_wt_list (by simp [recordVal, linFiniteAffineVal])
  have wfor : (encIntMatrix (linFiniteActionMatrix m ρ c' g)).wt < (recordVal g).wt :=
    wt_le_wt_list (by simp [recordVal, linFiniteAffineVal])
  have wback : (encIntMatrix (linFiniteActionMatrix m ρ c' g⁻¹)).wt < (recordVal g).wt :=
    wt_le_wt_list (by simp [recordVal, linFiniteAffineVal])
  have winv : (recordVal g⁻¹).wt ≤ 100 * (linRecenterContextMapBudget W + 1) := by
    have hh := wt_list3_le (linVecVal (linFiniteModuli m))
      (encIntMatrix (linFiniteActionMatrix m ρ c' g⁻¹)) (encIntMatrix (linFiniteActionMatrix m ρ c' g))
    dsimp only [recordVal]
    rw [linFiniteAffineVal_inv]
    omega
  have darg (rest : List Val) (j : ℕ) {v : Val}
      (hj : ([cover, orders, raw, unused, wv] : List Val)[j]? = some v) :=
    Det.arg' (P := P) (vs := [cover, orders, raw, unused, wv]) (rest := rest) (j := j) hj
  have dm := Det.call (Det.mk2 (Det.mk2 (darg [] 1 rfl) (darg [] 4 rfl)) (darg [] 2 rfl)) hmap'
  have df := Det.get' (Det.var' (P := P) (env := [a, records]) (i := 1) rfl) (Det.nat 0) rfl
  have di0 := Det.mk3 (Det.get' df (Det.nat 0) rfl)
    (Det.get' df (Det.nat 2) rfl) (Det.get' df (Det.nat 1) rfl)
  have hinv := linFiniteAffineVal_inv m ρ c' g
  rw [← hinv] at di0
  have di := Det.call (Det.mk2 df di0) hprod
  have dout := Det.mk3 (darg [records, recordVal 1] 0 rfl)
    (Det.var' (P := P) (env := [a, records, recordVal 1]) (i := 1) rfl)
    (Det.var' (P := P) (env := [a, records, recordVal 1]) (i := 2) rfl)
  apply FunDet.intro h.entry
  refine (Det.letE dm (Det.letE di dout)).mono ?_
  have wiMap := wt_list2_le ctx raw
  have wiCtx := wt_list2_le orders wv
  have wiProd := wt_list2_le (recordVal g) (recordVal g⁻¹)
  have wout := wt_list3_le cover records (recordVal 1)
  change _ ≤ linRecenterContextCost W
  unfold linRecenterContextCost
  dsimp only [W, a, ctx, raw, records, recordVal, c', orders, wv, linRecenterContextMapBudget,
    linRecenterContextIdBudget, linRecenterContextIdCoefficient, linRecenterContextIdDegree] at *
  omega

theorem linRecenterContextCost_mono {W V : ℕ} (h : W ≤ V) :
    linRecenterContextCost W ≤ linRecenterContextCost V := by
  have hm : linRecenterContextMapBudget W ≤ linRecenterContextMapBudget V :=
    linMapBudget_mono (by omega) (linRecenterRecordCost_mono (by omega))
  have hi : linRecenterContextIdBudget W ≤ linRecenterContextIdBudget V := by
    unfold linRecenterContextIdBudget
    gcongr
  unfold linRecenterContextCost
  omega

set_option maxRecDepth 16000 in
theorem linRecenterContextCost_poly : PBU (fun _ W _ => linRecenterContextCost W) := by
  have hc := linPoly_subst linRecenterRecordCost_poly (PBU.const 0)
    (PBU.smul 100 (PBU.addc PBU.W 1)) (PBU.const 0)
  have ha : PBU (fun _ W _ => 100 * (W + 1)) := PBU.smul 100 (PBU.addc PBU.W 1)
  have hm : PBU (fun _ W _ => linRecenterContextMapBudget W) := by
    simpa only [linRecenterContextMapBudget, linMapBudget, Nat.mul_assoc] using
      PBU.smul 10000 (PBU.mul (PBU.pow (PBU.addc ha 1) 2) (PBU.addc (PBU.add hc ha) 1))
  have hi : PBU (fun _ W _ => linRecenterContextIdBudget W) :=
    PBU.smul _ (PBU.pow (PBU.addc PBU.W 1) _)
  exact PBU.smul 1000000 (PBU.addc (PBU.add (PBU.add PBU.W hm) hi) 1)

end GI.Impl
