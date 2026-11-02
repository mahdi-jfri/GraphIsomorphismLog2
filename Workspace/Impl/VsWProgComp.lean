import Workspace.Impl.VsWProgImg
import Workspace.Proved.VsWFrameMath

/-!
# The complement as a program

* `vsWCompFuns b` (45 functions), `vsWComp_spec`: on `[p, vsWVs ws', vsWVs ws]` the complement
  `vsWVs (vsWComp p ws' ws)`. Meaning: `GI.Proved.vsWFrame_sup`, `GI.Proved.vsWFrame_indep`.
-/

namespace GI.Impl

open GI.Lang GI.Cited

/-- Cost of a map: `n` items of cost `B`, argument and result of weight at most `W`. -/
theorem vsW_mapCost {N n B W c k : ℕ} (hn : n ≤ N) (hB : B ≤ c * (N + 1) ^ k)
    (hW : W + 1 ≤ c * (N + 1) ^ k) :
    n * B + mapK * (n + 1) * (W + 1) ≤ 1001 * c * (N + 1) ^ (k + 1) := by
  have hK : mapK = 1000 := rfl
  have e : (N + 1) ^ (k + 1) = (N + 1) * (N + 1) ^ k := by ring
  have h1 : n * B ≤ (N + 1) * (c * (N + 1) ^ k) := Nat.mul_le_mul (by omega) hB
  have h2 : mapK * (n + 1) * (W + 1) ≤ 1000 * (N + 1) * (c * (N + 1) ^ k) := by
    rw [hK]; exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hW
  have e2 : 1000 * (N + 1) * (c * (N + 1) ^ k) = 1000 * ((N + 1) * (c * (N + 1) ^ k)) := by ring
  have e3 : 1001 * c * (N + 1) ^ (k + 1) = 1001 * ((N + 1) * (c * (N + 1) ^ k)) := by rw [e]; ring
  omega

/-- The default row. -/
def vsWRow0 : VsRow := ⟨0, [], []⟩

theorem vsW_range_drop {α : Type} (l : List α) (m : ℕ) (d : α) :
    (List.range (l.length - m)).map (fun i => l.getD (m + i) d) = l.drop m := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_drop]
  rw [List.getD_eq_getElem]

/-- One entry of the complement, on `[[rows, m], i]`: the main part of row `m + i`. -/
def vsWDropItemF : Expr :=
  .get (.get (.get (arg 0) (.nat 0)) (.arith .add (.get (arg 0) (.nat 1)) (arg 1))) (.nat 1)

theorem vsWDropItem_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some vsWDropItemF)
    {R : List VsRow} {m i W : ℕ} (hi : m + i < R.length)
    (hW : (Val.list [.list (R.map VsRow.val), .nat m]).wt ≤ W) (hiW : i ≤ W) :
    FunDet P f (.list [.list [.list (R.map VsRow.val), .nat m], .nat i])
      (natList (R.getD (m + i) vsWRow0).x) (40 * W + 200) := by
  set c := Val.list [.list (R.map VsRow.val), .nat m]
  have a0 := Det.arg' (P := P) (rest := []) (vs := [c, .nat i]) (j := 0) rfl
  have a1 := Det.arg' (P := P) (rest := []) (vs := [c, .nat i]) (j := 1) rfl
  have g0 := Det.get' a0 (Det.nat 0) (show [Val.list (R.map VsRow.val), .nat m][0]? = some _ from rfl)
  have g1 := Det.get' a0 (Det.nat 1) (show [Val.list (R.map VsRow.val), .nat m][1]? = some _ from rfl)
  have dad := Det.arith' g1 a1 (op := .add) rfl
  have hv : (R.map VsRow.val)[m + i]? = some (R.getD (m + i) vsWRow0).val := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hi, List.getD_eq_getElem _ _ hi]; rfl
  have dr := Det.get' g0 dad hv
  have dx := Det.get' dr (Det.nat 1) (show [Val.nat (R.getD (m + i) vsWRow0).j,
    natList (R.getD (m + i) vsWRow0).x, natList (R.getD (m + i) vsWRow0).t][1]? = some _ from rfl)
  refine FunDet.intro hf (dx.mono ?_)
  have w1 : (R.getD (m + i) vsWRow0).val.wt < (Val.list (R.map VsRow.val)).wt :=
    wt_le_wt_list (by rw [List.getD_eq_getElem _ _ hi]; exact List.mem_map_of_mem (List.getElem_mem hi))
  have w2 : (natList (R.getD (m + i) vsWRow0).x).wt < (R.getD (m + i) vsWRow0).val.wt :=
    wt_le_wt_list (by simp)
  have w3 : (Val.list (R.map VsRow.val)).wt < c.wt := wt_le_wt_list (by simp)
  have w4 : (Val.nat m).wt < c.wt := wt_le_wt_list (by simp)
  have wm := wt_nat_le m
  have w5 := wt_list2_le c (.nat i)
  have wi := wt_nat_le i
  have hRl := length_lt_wt_list (R.map VsRow.val)
  rw [List.length_map] at hRl
  have hadd : GI.Machine.BinOp.add.eval m i = m + i := rfl
  omega

/-- The complement, on `[p, ws', ws]`. -/
def vsWCompF (rows app mp rng : ℕ) : Expr :=
  .letE (.call rows (mk2 (arg 0) (.call app (mk2 (arg 1) (arg 2)))))
    (.letE (.length (.call rows (mk2 (arg 0) (arg 1))))
      (.call mp (mk2 (mk2 (.var 1) (.var 2)) (.call rng (.arith .sub (.length (.var 1)) (.var 2))))))

/-- The complement program at base `b` (45 functions). -/
def vsWCompFuns (b : ℕ) : List Expr :=
  [vsWCompF (b + 1) (b + 35) (b + 38) (b + 42)] ++ vsWRowsFuns (b + 1) ++ appendFuns (b + 35) ++
    mapFuns (b + 38) (b + 41) ++ [vsWDropItemF] ++ rangeFuns (b + 42)

theorem vsWCompFuns_length (b : ℕ) : (vsWCompFuns b).length = 45 := rfl

theorem vsWRows_length_le {p N d : ℕ} (hp : 0 < p) (hpN : p ≤ N) (hdN : d ≤ N)
    {us : List (List ℕ)} (hus : GI.Proved.VsWFit p d us) : (vsWRows p us).length ≤ us.length :=
  (vsWRows_fits hp hpN hdN hus).nrows

/-- **The complement program.** -/
theorem vsWComp_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsWCompFuns b)) {p N d : ℕ}
    (hp : 0 < p) (hpN : p ≤ N) (hdN : d ≤ N) {ws' ws : List (List ℕ)}
    (h' : GI.Proved.VsWFit p d ws') (hw : GI.Proved.VsWFit p d ws)
    (hl : ws'.length + ws.length ≤ N) :
    FunDet P b (.list [.nat p, vsWVs ws', vsWVs ws]) (vsWVs (vsWComp p ws' ws))
      (10 ^ 8 * (N + 1) ^ 5) := by
  have h0 : P.funs[b]? = some (vsWCompF (b + 1) (b + 35) (b + 38) (b + 42)) :=
    h.get (j := 0) (by simp [vsWCompFuns])
  have hr : P.HasAt (b + 1) (vsWRowsFuns (b + 1)) := h.block 1 rfl
  have ha : P.HasAt (b + 35) (appendFuns (b + 35)) := h.block 35 rfl
  have hm : P.HasAt (b + 38) (mapFuns (b + 38) (b + 41)) := h.block 38 rfl
  have hit : P.funs[b + 41]? = some vsWDropItemF := h.get (j := 41) (by rw [vsWCompFuns_length]; omega)
  have hrg : P.HasAt (b + 42) (rangeFuns (b + 42)) := h.block 42 rfl
  set X := Val.list [.nat p, vsWVs ws', vsWVs ws]
  have hfa : GI.Proved.VsWFit p d (ws' ++ ws) := GI.Proved.vsWFit_append h' hw
  set R := vsWRows p (ws' ++ ws)
  set m := (vsWRows p ws').length
  have hRl : R.length ≤ ws'.length + ws.length := by
    have := vsWRows_length_le hp hpN hdN hfa; simpa using this
  have hml : m ≤ ws'.length := vsWRows_length_le hp hpN hdN h'
  -- the first `let`: the rows of `ws' ++ ws`
  have a0 := Det.arg' (P := P) (rest := []) (vs := [Val.nat p, vsWVs ws', vsWVs ws]) (j := 0) rfl
  have a1 := Det.arg' (P := P) (rest := []) (vs := [Val.nat p, vsWVs ws', vsWVs ws]) (j := 1) rfl
  have a2 := Det.arg' (P := P) (rest := []) (vs := [Val.nat p, vsWVs ws', vsWVs ws]) (j := 2) rfl
  have wws' := wt_vsWVs_le (VsWFit.bnd h' hpN hdN) (show ws'.length ≤ N + 1 by omega)
  have wws := wt_vsWVs_le (VsWFit.bnd hw hpN hdN) (show ws.length ≤ N + 1 by omega)
  have wwa := wt_vsWVs_le (VsWFit.bnd hfa hpN hdN) (show (ws' ++ ws).length ≤ N + 1 by simp; omega)
  have eapp : Val.list (ws'.map natList ++ ws.map natList) = vsWVs (ws' ++ ws) := by
    simp [vsWVs]
  have q0 : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q4 : (N + 1) ^ 4 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have kapp : loopModK * ((ws.map natList).length + 1) *
      ((Val.list [.list (ws'.map natList), .list (ws.map natList)]).wt + (ws.map natList).length +
        (Val.list (ws'.map natList ++ ws.map natList)).wt + 1) ≤ 10 ^ 5 * (N + 1) ^ 4 := by
    have hK : loopModK = 1000 := rfl
    have w2 := wt_list2_le (.list (ws'.map natList)) (.list (ws.map natList))
    have e1 : (vsWVs ws').wt = (Val.list (ws'.map natList)).wt := rfl
    have e2 : (vsWVs ws).wt = (Val.list (ws.map natList)).wt := rfl
    rw [eapp, hK, List.length_map]
    calc 1000 * (ws.length + 1) * ((Val.list [.list (ws'.map natList), .list (ws.map natList)]).wt +
          ws.length + (vsWVs (ws' ++ ws)).wt + 1)
        ≤ 1000 * (N + 1) * (100 * (N + 1) ^ 3) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      _ = 10 ^ 5 * (N + 1) ^ 4 := by ring
  have dap := Det.call (Det.mk2 a1 a2) ((append_spec ha (ws'.map natList) (ws.map natList)).mono
    fun w c hw => ⟨hw.1, hw.2.trans (hw.1 ▸ kapp)⟩)
  rw [eapp] at dap
  have hl' : (ws' ++ ws).length ≤ N := by simp; omega
  have dR := Det.call (Det.mk2 a0 dap) (vsWRows_spec hr hp hpN hdN hfa hl')
  set RV := Val.list (R.map VsRow.val)
  -- the second `let`: the number of rows of `ws'`
  have b0 := Det.arg' (P := P) (rest := [RV]) (vs := [Val.nat p, vsWVs ws', vsWVs ws]) (j := 0) rfl
  have b1 := Det.arg' (P := P) (rest := [RV]) (vs := [Val.nat p, vsWVs ws', vsWVs ws]) (j := 1) rfl
  have dR' := Det.length (Det.call (Det.mk2 b0 b1) (vsWRows_spec hr hp hpN hdN h' (by omega)))
  rw [List.length_map] at dR'
  -- the body
  have v1 : Det P [X, RV, .nat m] (.var 1) RV _ := Det.var' rfl
  have v2 : Det P [X, RV, .nat m] (.var 2) (.nat m) _ := Det.var' rfl
  have dl := Det.length v1
  rw [List.length_map] at dl
  have dsub := Det.arith' dl v2 (op := .sub) rfl
  have krg : loopModK * (R.length - m + 1) * ((Val.nat (R.length - m)).wt + (R.length - m) +
      (natList (List.range (R.length - m))).wt + 1) ≤ 10 ^ 4 * (N + 1) ^ 3 := by
    have hK : loopModK = 1000 := rfl
    have wrg := wt_natList_le_sq (B := N) (xs := List.range (R.length - m)) (fun y hy => by
      simp at hy; omega) (by simp; omega)
    have := wt_nat_le (R.length - m)
    rw [hK]
    calc 1000 * (R.length - m + 1) * ((Val.nat (R.length - m)).wt + (R.length - m) +
          (natList (List.range (R.length - m))).wt + 1)
        ≤ 1000 * (N + 1) * (10 * (N + 1) ^ 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      _ = 10 ^ 4 * (N + 1) ^ 3 := by ring
  have drg := Det.call dsub ((range_spec hrg (R.length - m)).mono fun w c hw =>
    ⟨hw.1, hw.2.trans (hw.1 ▸ krg)⟩)
  have eN : natList (List.range (R.length - m)) = .list ((List.range (R.length - m)).map Val.nat) :=
    rfl
  rw [eN] at drg
  have hfit := vsWRows_fits hp hpN hdN hfa
  have wR : RV.wt ≤ 81 * (N + 1) ^ 3 + 4 := wt_vsRows_le hfit.rows (by
    have := hfit.nrows; simp at this; omega)
  have wC : (Val.list [RV, .nat m]).wt ≤ 200 * (N + 1) ^ 3 := by
    have := wt_list2_le RV (.nat m)
    have := wt_nat_le m
    omega
  have dmap := vsQ_map hm (List.range (R.length - m)) Val.nat
    (fun i => natList (R.getD (m + i) vsWRow0).x) valNat_injective (c := .list [RV, .nat m])
    fun i hi => vsWDropItem_spec hit (by simp at hi; omega) wC (by simp at hi; omega)
  have e1 : (List.range (R.length - m)).map (fun i => natList (R.getD (m + i) vsWRow0).x) =
      (vsWComp p ws' ws).map natList := by
    rw [vsWComp, List.map_map, ← vsW_range_drop R m vsWRow0, List.map_map]; rfl
  rw [e1] at dmap
  have dbody := Det.call (Det.mk2 (Det.mk2 v1 v2) drg) dmap
  refine FunDet.intro h0 ((Det.letE dR (Det.letE dR' dbody)).mono ?_)
  have hcf := GI.Proved.vsWComp_fit hp h' hw
  have hcl : (vsWComp p ws' ws).length = R.length - m := by simp [vsWComp, R, m]
  have wcomp := wt_vsWVs_le (VsWFit.bnd hcf hpN hdN) (show (vsWComp p ws' ws).length ≤ N + 1 by
    omega)
  have wrg := wt_natList_le_sq (B := N) (xs := List.range (R.length - m)) (fun y hy => by
    simp at hy; omega) (by simp; omega)
  rw [eN] at wrg
  have wc2 := wt_list2_le (.list [RV, .nat m]) (.list ((List.range (R.length - m)).map Val.nat))
  have eC : (vsWVs (vsWComp p ws' ws)).wt = (Val.list ((vsWComp p ws' ws).map natList)).wt := rfl
  have kmap := vsW_mapCost (N := N) (n := (List.range (R.length - m)).length)
    (B := 40 * (200 * (N + 1) ^ 3) + 200) (c := 10 ^ 4) (k := 3)
    (W := (Val.list [.list [RV, .nat m], .list ((List.range (R.length - m)).map Val.nat)]).wt +
      (Val.list ((vsWComp p ws' ws).map natList)).wt) (by simp; omega) (by omega) (by omega)
  have e5 : (N + 1) ^ (3 + 1) = (N + 1) ^ 4 := rfl
  rw [e5] at kmap
  have wp := wt_nat_le p
  have wm := wt_nat_le m
  have wsub := wt_nat_le (R.length - m)
  have hsub : GI.Machine.BinOp.sub.eval R.length m = R.length - m := rfl
  have wX := wt_list3_le (.nat p) (vsWVs ws') (vsWVs ws)
  have eX : X.wt = (Val.list [.nat p, vsWVs ws', vsWVs ws]).wt := rfl
  have w2a := wt_list2_le (vsWVs ws') (vsWVs ws)
  have e1' : (vsWVs ws').wt = (Val.list (ws'.map natList)).wt := rfl
  have e2' : (vsWVs ws).wt = (Val.list (ws.map natList)).wt := rfl
  have w2b := wt_list2_le (.nat p) (vsWVs (ws' ++ ws))
  have w2c := wt_list2_le (.nat p) (vsWVs ws')
  have hfit' := vsWRows_fits hp hpN hdN h'
  have wR' := wt_vsRows_le hfit'.rows (show (vsInsertAll p (vsWPairs ws')).1.length ≤ N + 1 by
    have := hfit'.nrows; omega)
  have eR' : vsWRows p ws' = (vsInsertAll p (vsWPairs ws')).1 := rfl
  rw [← eR'] at wR'
  have hlR' := length_lt_wt_list ((vsWRows p ws').map VsRow.val)
  rw [List.length_map] at hlR'
  have wRm := wt_list2_le RV (.nat m)
  have wc3 := wt_list2_le (.list [RV, .nat m]) (.list ((List.range (R.length - m)).map Val.nat))
  omega

end GI.Impl
