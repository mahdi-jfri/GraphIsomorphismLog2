module

public import Workspace.Impl.LinWreathCopy

@[expose] public section

/-! Construct the complete two-copy covering permutation list. -/
namespace GI.Impl
open GI.Cited GI.Lang Equiv

def linWreathPermF (left right swap append : ℕ) : Expr :=
  .letE (.call left (.var 0))
    (.letE (.call right (.var 0))
      (.letE (.call swap (.length (arg 0)))
        (.letE (.call append (mk2 (.var 1) (.var 2))) (.snoc (.var 4) (.var 3)))))

def linWreathPermFuns (b : ℕ) : List Expr :=
  [linWreathPermF (b + 3) (b + 6) (b + 17) (b + 25),
    linWreathCopyF (b + 9) true, linWreathCopyF (b + 9) false] ++
    mapFuns (b + 3) (b + 1) ++ mapFuns (b + 6) (b + 2) ++
    linSumPermFuns (b + 9) ++ linSwapPermFuns (b + 17) ++ appendFuns (b + 25)

theorem linWreathPermFuns_length (b : ℕ) : (linWreathPermFuns b).length = 28 := rfl

structure linWreathPermAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linWreathPermF (b + 3) (b + 6) (b + 17) (b + 25))
  left : P.funs[b + 1]? = some (linWreathCopyF (b + 9) true)
  right : P.funs[b + 2]? = some (linWreathCopyF (b + 9) false)
  mapLeft : P.HasAt (b + 3) (mapFuns (b + 3) (b + 1))
  mapRight : P.HasAt (b + 6) (mapFuns (b + 6) (b + 2))
  sum : P.HasAt (b + 9) (linSumPermFuns (b + 9))
  swap : P.HasAt (b + 17) (linSwapPermFuns (b + 17))
  append : P.HasAt (b + 25) (appendFuns (b + 25))

theorem linWreathPermAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linWreathPermFuns b)) : linWreathPermAt P b where
  entry := (h.block (gs := [linWreathPermF (b + 3) (b + 6) (b + 17) (b + 25)]) 0 rfl).single
  left := (h.block (gs := [linWreathCopyF (b + 9) true]) 1 rfl).single
  right := (h.block (gs := [linWreathCopyF (b + 9) false]) 2 rfl).single
  mapLeft := h.block 3 rfl
  mapRight := h.block 6 rfl
  sum := h.block 9 rfl
  swap := h.block 17 rfl
  append := h.block 25 rfl

def linWreathPermMapCost (W : ℕ) : ℕ := linMapBudget W (linWreathCopyCost (100 * (W + 1)))
def linWreathPermWt (W n : ℕ) : ℕ := 100 * (W + 1) * (n + 1) ^ 2

def linWreathPermAppendCost (W n : ℕ) : ℕ :=
  10000 * (W + 1) * (linWreathPermMapCost W + linWreathPermWt W n + W + 1)
def linWreathPermCost (W n : ℕ) : ℕ :=
  100000 * (W + linWreathPermMapCost W + linSwapPermCost n +
    linWreathPermAppendCost W n + linWreathPermWt W n + 1)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 6000 in
theorem linWreathPerm_spec {P : Program} {b n : ℕ} (h : linWreathPermAt P b)
    (gs : List (Perm (Fin n))) :
    FunDet P b (.list [encPerm (1 : Perm (Fin n)), .list (gs.map encPerm)])
      (.list ((linWreathCoverGenerators gs).map encPerm))
      (linWreathPermCost (Val.list [encPerm (1 : Perm (Fin n)), .list (gs.map encPerm)]).wt n) := by
  let a := Val.list [encPerm (1 : Perm (Fin n)), .list (gs.map encPerm)]
  let W := a.wt
  let ls := gs.map (fun g => sumToFin (Equiv.sumCongr g (1 : Perm (Fin n))))
  let rs := gs.map (fun g => sumToFin (Equiv.sumCongr (1 : Perm (Fin n)) g))
  have wid : (encPerm (1 : Perm (Fin n))).wt < W := wt_le_wt_list (by simp [W, a])
  have wgs : (Val.list (gs.map encPerm)).wt < W := wt_le_wt_list (by simp [W, a])
  have hn : n ≤ W := by
    have hh := length_lt_wt_list ((List.finRange n).map fun i => Val.nat ((1 : Perm (Fin n)) i))
    simp only [List.length_map, List.length_finRange] at hh
    change n < (encPerm (1 : Perm (Fin n))).wt at hh
    omega
  have len : gs.length ≤ W := by
    have hh := length_lt_wt_list (gs.map encPerm)
    simp only [List.length_map] at hh
    omega
  have wpoint (g : Perm (Fin n)) (hg : g ∈ gs) :
      (Val.list [encPerm (1 : Perm (Fin n)), encPerm g]).wt ≤ 100 * (W + 1) := by
    have hh := wt_list2_le (encPerm (1 : Perm (Fin n))) (encPerm g)
    have hw : (encPerm g).wt < (Val.list (gs.map encPerm)).wt := wt_le_wt_list (List.mem_map.mpr ⟨g, hg, rfl⟩)
    omega
  have hl := linMapEncoded_spec h.mapLeft encPerm encPerm_injective
    (fun g => encPerm (sumToFin (Equiv.sumCongr g (1 : Perm (Fin n))))) (encPerm (1 : Perm (Fin n))) gs
    (linWreathCopyCost (100 * (W + 1))) (fun g hg =>
      (linWreathCopy_spec true h.left h.sum g).mono (linWreathCopyCost_mono (wpoint g hg)))
  have hr := linMapEncoded_spec h.mapRight encPerm encPerm_injective
    (fun g => encPerm (sumToFin (Equiv.sumCongr (1 : Perm (Fin n)) g))) (encPerm (1 : Perm (Fin n))) gs
    (linWreathCopyCost (100 * (W + 1))) (fun g hg =>
      (linWreathCopy_spec false h.right h.sum g).mono (linWreathCopyCost_mono (wpoint g hg)))
  have hl' : FunDet P (b + 3) a (.list (ls.map encPerm)) (linWreathPermMapCost W) := by
    simpa only [a, ls, linWreathPermMapCost, List.map_map, Function.comp_def] using hl
  have hr' : FunDet P (b + 6) a (.list (rs.map encPerm)) (linWreathPermMapCost W) := by
    simpa only [a, rs, linWreathPermMapCost, List.map_map, Function.comp_def] using hr
  have wl := hl'.wt_lt.le
  have wr := hr'.wt_lt.le
  have wp : (Val.list ((ls ++ rs).map encPerm)).wt ≤ linWreathPermWt W n := by
    have hh := linWtList (vs := (ls ++ rs).map encPerm) (B := 16 * (n + 1) ^ 2) (by
      intro v hv
      obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hv
      exact wt_encPerm_sum_le σ)
    simp only [ls, rs, List.length_map, List.length_append] at hh
    unfold linWreathPermWt
    nlinarith [Nat.mul_le_mul_right (16 * (n + 1) ^ 2) len,
      Nat.le_self_pow (by decide : 2 ≠ 0) (n + 1)]
  have wi := wt_list2_le (.list (ls.map encPerm)) (.list (rs.map encPerm))
  have ha := linAppend_det h.append (ls.map encPerm) (rs.map encPerm)
  have ha' : FunDet P (b + 25)
      (.list [.list (ls.map encPerm), .list (rs.map encPerm)])
      (.list ((ls ++ rs).map encPerm)) (linWreathPermAppendCost W n) := by
    refine FunAll.mono ha fun v cost hv => ⟨by simpa using hv.1, ?_⟩
    have hc := hv.2
    simp only [List.length_map, rs, List.length_map] at hc
    have wp' : (Val.list (ls.map encPerm ++ rs.map encPerm)).wt ≤ linWreathPermWt W n := by
      simpa using wp
    change cost ≤ linWreathPermAppendCost W n
    unfold linWreathPermAppendCost
    simp only [loopModK] at hc
    have hw : (Val.list [.list (ls.map encPerm), .list (rs.map encPerm)]).wt + gs.length +
        (Val.list (ls.map encPerm ++ rs.map encPerm)).wt + 1 ≤
        10 * (linWreathPermMapCost W + linWreathPermWt W n + W + 1) := by omega
    exact hc.trans (by nlinarith [Nat.mul_le_mul (by omega : 1000 * (gs.length + 1) ≤ 1000 * (W + 1)) hw])
  have hs := linSwapPerm_spec h.swap n
  have ws := hs.wt_lt.le
  have d₀ := Det.var' (P := P) (env := [a]) (i := 0) rfl
  have dl := Det.call d₀ hl'
  have dr := Det.call (Det.var' (P := P) (env := [a, .list (ls.map encPerm)]) (i := 0) rfl) hr'
  have dn := Det.length (Det.arg' (P := P)
    (vs := [encPerm (1 : Perm (Fin n)), .list (gs.map encPerm)])
    (rest := [.list (ls.map encPerm), .list (rs.map encPerm)]) (j := 0) rfl)
  simp only [List.length_map, List.length_finRange] at dn
  have ds := Det.call dn hs
  have dap := Det.call (Det.mk2
    (Det.var' (P := P) (env := [a, .list (ls.map encPerm), .list (rs.map encPerm), encPerm (linSwapPerm n)]) (i := 1) rfl)
    (Det.var' (P := P) (env := [a, .list (ls.map encPerm), .list (rs.map encPerm), encPerm (linSwapPerm n)]) (i := 2) rfl)) ha'
  have dout := Det.snoc
    (Det.var' (P := P) (env := [a, .list (ls.map encPerm), .list (rs.map encPerm),
      encPerm (linSwapPerm n), .list ((ls ++ rs).map encPerm)]) (i := 4) rfl)
    (Det.var' (P := P) (env := [a, .list (ls.map encPerm), .list (rs.map encPerm),
      encPerm (linSwapPerm n), .list ((ls ++ rs).map encPerm)]) (i := 3) rfl)
  have he : (linWreathCoverGenerators gs).map encPerm =
      (ls ++ rs).map encPerm ++ [encPerm (linSwapPerm n)] := by
    rw [linWreathCoverGenerators_formula]
    simp only [ls, rs, List.map_append, List.map_cons, List.map_nil]
  have wout := wt_list_snoc_le ((ls ++ rs).map encPerm) (encPerm (linSwapPerm n))
  rw [he]
  apply FunDet.intro h.entry
  refine (Det.letE dl (Det.letE dr (Det.letE ds (Det.letE dap dout)))).mono ?_
  have wmk := wt_list2_le (.list (ls.map encPerm)) (.list (rs.map encPerm))
  change _ ≤ linWreathPermCost W n
  dsimp only [linWreathPermCost]
  dsimp only [a, W, ls, rs, encPerm] at *
  omega

theorem linWreathPermCost_poly : PBU (fun n W _ => linWreathPermCost W n) := by
  simp only [linWreathPermCost, linWreathPermMapCost, linWreathPermAppendCost, linWreathPermWt,
    linWreathCopyCost, linSumPermCost, linSumPermMapBudget, linSumPermAppendBudget,
    linSwapPermCost, linSwapPermRangeBudget, linSwapPermMapBudget, linMapBudget]
  norm_poly

end GI.Impl
