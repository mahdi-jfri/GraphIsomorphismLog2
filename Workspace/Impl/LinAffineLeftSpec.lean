import Workspace.Impl.LinAffineLeft

namespace GI.Impl
open GI.Cited GI.Lang

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 8000 in
theorem linAffineLeft_spec {P : Program} {b n : ℕ} (h : linAffineLeftAt P b)
    (gs : List (Equiv.Perm (Fin n))) (r : Equiv.Perm (Fin n)) :
    let a := Val.list [encGroup gs, encPerm r]
    FunDet P b a (.list [encPerm r, encGroup (linConjugateGenerators gs r)])
      (linAffineLeftCost a.wt) := by
  let a := Val.list [encGroup gs, encPerm r]
  let W := a.wt
  let ri := encPerm r⁻¹
  let raw := Val.list (gs.map encPerm)
  let ctx := Val.list [ri, encPerm r]
  let newgs := linConjugateGenerators gs r
  let newraw := Val.list (newgs.map encPerm)
  have wg : (encGroup gs).wt < W := wt_le_wt_list (by simp [a, W])
  have wr : (encPerm r).wt < W := wt_le_wt_list (by simp [a, W])
  have wfull : (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt := wt_le_wt_list (by simp [encGroup])
  have wraw : raw.wt ≤ (Val.list ((1 :: gs).map encPerm)).wt :=
    wt_list_sublist (List.sublist_cons_self _ _)
  have hn : n ≤ W := by
    have hh := S_le_wt_encGroup gs
    have hm : n + 1 ≤ (gs.length + 2) * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hlen : gs.length ≤ W := by
    have hh := length_lt_wt_list ((1 :: gs).map encPerm)
    simp only [List.length_map, List.length_cons] at hh
    omega
  have hi := (inv_spec h.inv r).mono (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 4))
  have wri : ri.wt ≤ linAffineLeftInvBudget W := hi.wt_lt.le
  have ht := (GI.Lang.tail_spec h.tail (encPerm (1 : Equiv.Perm (Fin n))) (gs.map encPerm)).mono (show
    loopModK * ((gs.map encPerm).length + 1) *
      (3 * (Val.list (encPerm (1 : Equiv.Perm (Fin n)) :: gs.map encPerm)).wt + 1) ≤ linAffineLeftTailBudget W by
    have hh : (Val.list (encPerm (1 : Equiv.Perm (Fin n)) :: gs.map encPerm)).wt ≤ W := by
      simpa only [List.map_cons] using wfull.le.trans wg.le
    unfold linAffineLeftTailBudget
    simp only [List.length_map]
    gcongr)
  have wctx : ctx.wt ≤ 10 * (W + linAffineLeftInvBudget W + 1) := by
    have hh := wt_list2_le ri (encPerm r)
    dsimp only [ctx]
    omega
  have hc (g : Equiv.Perm (Fin n)) (hg : g ∈ gs) :
      FunDet P (b + 19) (.list [ctx, encPerm g]) (encPerm (r⁻¹ * g * r))
        (linConjugateCellCost (linAffineLeftMapArg W) W) := by
    have wx : (encPerm g).wt < raw.wt := wt_le_wt_list (List.mem_map.mpr ⟨g, hg, rfl⟩)
    have hh := wt_list2_le ctx (encPerm g)
    have hb : (Val.list [ctx, encPerm g]).wt ≤ linAffineLeftMapArg W := by
      unfold linAffineLeftMapArg
      omega
    exact (linConjugateCell_spec h.cell h.compose r⁻¹ g r).mono (linConjugateCellCost_mono hb hn)
  have hm := linMapSource_spec h.map encPerm (fun g => encPerm (r⁻¹ * g * r)) ctx gs _ hc
  have hnew : Val.list (gs.map fun g => encPerm (r⁻¹ * g * r)) = newraw := by
    simp only [newraw, newgs, linConjugateGenerators, List.map_map, Function.comp_def]
  rw [hnew] at hm
  have wma : (Val.list [ctx, raw]).wt ≤ linAffineLeftMapArg W := by
    have hh := wt_list2_le ctx raw
    unfold linAffineLeftMapArg
    omega
  have hmap := hm.mono (show linMapBudget (Val.list [ctx, raw]).wt
      (linConjugateCellCost (linAffineLeftMapArg W) W) ≤ linAffineLeftMapBudget W by
    simp only [linAffineLeftMapBudget, linMapBudget]
    gcongr)
  have wnraw : newraw.wt ≤ linAffineLeftMapBudget W := hmap.wt_lt.le
  have hgroup := (mkGroup_spec h.group newgs).mono (show
    mkGroupK * ((newgs.length + 2) * (n + 1)) ^ 3 ≤ linAffineLeftGroupBudget W by
    simp only [newgs, linConjugateGenerators_length]
    unfold linAffineLeftGroupBudget
    gcongr)
  have wngroup : (encGroup newgs).wt ≤ linAffineLeftGroupBudget W := hgroup.wt_lt.le
  have darg (rest : List Val) (j : ℕ) {v : Val} (hj : ([encGroup gs, encPerm r] : List Val)[j]? = some v) :=
    Det.arg' (P := P) (vs := [encGroup gs, encPerm r]) (rest := rest) (j := j) hj
  have di := Det.call (darg [] 1 rfl) hi
  have dt := Det.call (Det.get' (darg [ri] 0 rfl) (Det.nat 1) rfl) ht
  have dm := Det.call (Det.mk2 (Det.mk2
    (Det.var' (P := P) (env := [a, ri, raw]) (i := 1) rfl) (darg [ri, raw] 1 rfl))
    (Det.var' (P := P) (env := [a, ri, raw]) (i := 2) rfl)) hmap
  have dg := Det.call (Det.mk2 (Det.get' (darg [ri, raw, newraw] 0 rfl) (Det.nat 0) rfl)
    (Det.var' (P := P) (env := [a, ri, raw, newraw]) (i := 3) rfl)) hgroup
  have dout := Det.mk2 (darg [ri, raw, newraw, encGroup newgs] 1 rfl)
    (Det.var' (P := P) (env := [a, ri, raw, newraw, encGroup newgs]) (i := 4) rfl)
  apply FunDet.intro h.entry
  refine (Det.letE di (Det.letE dt (Det.letE dm (Det.letE dg dout)))).mono ?_
  have wn := wt_nat_le n
  have wargm := wt_list2_le ctx raw
  have wargg := wt_list2_le (.nat n) newraw
  have wout := wt_list2_le (encPerm r) (encGroup newgs)
  change _ ≤ linAffineLeftCost W
  unfold linAffineLeftCost
  dsimp only [a, W, ri, raw, ctx, newraw, newgs, linAffineLeftInvBudget, linAffineLeftTailBudget,
    linAffineLeftMapBudget, linAffineLeftGroupBudget, encGroup] at *
  simp only [List.map_cons] at *
  omega

theorem linAffineLeftCost_poly : PBU (fun _ W _ => linAffineLeftCost W) := by
  simp only [linAffineLeftCost, linAffineLeftInvBudget, linAffineLeftTailBudget,
    linAffineLeftMapBudget, linAffineLeftMapArg, linAffineLeftGroupBudget, linMapBudget, linConjugateCellCost]
  norm_poly

end GI.Impl
