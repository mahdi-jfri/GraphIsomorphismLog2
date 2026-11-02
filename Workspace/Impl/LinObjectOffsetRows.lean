import Workspace.Impl.LinObjectOffsetWindow
import Workspace.Impl.LinObjectLocalRelations

namespace GI.Impl
open GI.Cited GI.Lang

def linObjectOffsetRowsItemF (window : ℕ) : Expr :=
  .call window (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (arg 1))

def linObjectOffsetRowsFuns (b : ℕ) : List Expr :=
  mapFuns b (b + 3) ++ [linObjectOffsetRowsItemF (b + 4)] ++ linObjectOffsetWindowFuns (b + 4)

theorem linObjectOffsetRowsFuns_length (b : ℕ) : (linObjectOffsetRowsFuns b).length = 14 := rfl

def linObjectOffsetRowsItemCost (W : ℕ) : ℕ :=
  100000 * (W + linObjectOffsetWindowCost (100 * (W + 1)) + 1)

def linObjectOffsetRowsCost (W : ℕ) : ℕ :=
  linMapBudget W (linObjectOffsetRowsItemCost (100 * (W + 1)))

theorem linObjectOffsetWindowCost_mono {W V : ℕ} (h : W ≤ V) :
    linObjectOffsetWindowCost W ≤ linObjectOffsetWindowCost V := by
  unfold linObjectOffsetWindowCost linObjectOffsetRowCost linListPickCost linSliceCost
  gcongr

theorem linObjectOffsetRowsItemCost_mono {W V : ℕ} (h : W ≤ V) :
    linObjectOffsetRowsItemCost W ≤ linObjectOffsetRowsItemCost V := by
  unfold linObjectOffsetRowsItemCost
  have hh := linObjectOffsetWindowCost_mono (show 100 * (W + 1) ≤ 100 * (V + 1) by omega)
  omega

theorem linObjectOffsetRowsCost_poly : PBU (fun _ W _ => linObjectOffsetRowsCost W) := by
  unfold linObjectOffsetRowsCost linObjectOffsetRowsItemCost linObjectOffsetWindowCost
    linObjectOffsetRowCost linListPickCost linSliceCost linMapBudget
  norm_poly

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 3000 in
theorem linObjectOffsetRowsItem_spec {P : Program} {b n offset count : ℕ}
    (h : P.HasAt b (linObjectOffsetRowsFuns b)) (xs : List Val)
    (hsafe : offset + count ≤ xs.length) (R : Equiv.Perm (Fin n) → Prop)
    (hxs : ∀ v ∈ (xs.drop offset).take count,
      v = .list [] ∨ ∃ (a : Equiv.Perm (Fin n)) (gs : List (Equiv.Perm (Fin n))),
        v = .list [encPerm a, encGroup gs] ∧ R a)
    (hex : ∃ v ∈ (xs.drop offset).take count, v ≠ .list []) :
    let a := Val.list [.list [.nat offset, .nat count], .list xs]
    FunAll P (b + 3) a (fun out cost => (∃ a, out = encPerm a ∧ R a) ∧
      cost ≤ linObjectOffsetRowsItemCost a.wt) := by
  let ctx := Val.list [.nat offset, .nat count]
  let a := Val.list [ctx, .list xs]
  let W := a.wt
  have wc : ctx.wt < W := wt_le_wt_list (by simp [a, W])
  have wx : (Val.list xs).wt < W := wt_le_wt_list (by simp [a, W])
  have wo : (Val.nat offset).wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have wn : (Val.nat count).wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have hh := wt_list3_le (.nat offset) (.nat count) (.list xs)
  have hw : (Val.list [.nat offset, .nat count, .list xs]).wt ≤ 100 * (W + 1) := by omega
  have hs : FunAll P (b + 4) (.list [.nat offset, .nat count, .list xs])
      (fun out cost => (∃ a, out = encPerm a ∧ R a) ∧
        cost ≤ linObjectOffsetWindowCost (100 * (W + 1))) :=
    (linObjectOffsetWindow_spec (h.block 4 rfl) xs hsafe R hxs hex).mono fun out cost ho =>
      ⟨ho.1, ho.2.trans (linObjectOffsetWindowCost_mono hw)⟩
  have dc := Det.arg' (P := P) (vs := [ctx, .list xs]) (rest := []) (j := 0) rfl
  have dx := Det.arg' (P := P) (vs := [ctx, .list xs]) (rest := []) (j := 1) rfl
  have da := Det.mk3 (Det.get' dc (Det.nat 0) rfl) (Det.get' dc (Det.nat 1) rfl) dx
  apply FunAll.intro (h.block (gs := [linObjectOffsetRowsItemF (b + 4)]) 3 rfl).single
  apply EvalAll.call_funAll da
  intro v ca hv
  obtain ⟨rfl, hca⟩ := hv
  refine hs.wt_lt.mono fun out cost ho => ⟨ho.1.1, ?_⟩
  have hc := ho.1.2
  have wout := ho.2
  change _ ≤ linObjectOffsetRowsItemCost W
  unfold linObjectOffsetRowsItemCost
  dsimp only [ctx, a, W] at *
  omega

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 3000 in
theorem linObjectOffsetRows_spec {P : Program} {b n offset count : ℕ}
    (h : P.HasAt b (linObjectOffsetRowsFuns b)) (rows : List (List Val))
    (R : List Val → Equiv.Perm (Fin n) → Prop)
    (hsafe : ∀ xs ∈ rows, offset + count ≤ xs.length)
    (hxs : ∀ xs ∈ rows, ∀ v ∈ (xs.drop offset).take count,
      v = .list [] ∨ ∃ (a : Equiv.Perm (Fin n)) (gs : List (Equiv.Perm (Fin n))),
        v = .list [encPerm a, encGroup gs] ∧ R xs a)
    (hex : ∀ xs ∈ rows, ∃ v ∈ (xs.drop offset).take count, v ≠ .list []) :
    let a := Val.list [.list [.nat offset, .nat count], .list (rows.map Val.list)]
    FunAll P b a (fun out cost =>
      (∃ gs : List (Equiv.Perm (Fin n)), out = .list (gs.map encPerm) ∧ List.Forall₂ R rows gs) ∧
      cost ≤ linObjectOffsetRowsCost a.wt) := by
  let ctx := Val.list [.nat offset, .nat count]
  let a := Val.list [ctx, .list (rows.map Val.list)]
  let W := a.wt
  have wc : ctx.wt < W := wt_le_wt_list (by simp [a, W])
  have wr : (Val.list (rows.map Val.list)).wt < W := wt_le_wt_list (by simp [a, W])
  have hs : ∀ xs ∈ rows, FunAll P (b + 3) (.list [ctx, .list xs])
      (fun out cost => (∃ g, out = encPerm g ∧ R xs g) ∧
        cost ≤ linObjectOffsetRowsItemCost (100 * (W + 1))) := by
    intro xs hrow
    have wx : (Val.list xs).wt < (Val.list (rows.map Val.list)).wt :=
      wt_le_wt_list (List.mem_map.mpr ⟨xs, hrow, rfl⟩)
    have hh := wt_list2_le ctx (.list xs)
    exact (linObjectOffsetRowsItem_spec h xs (hsafe xs hrow) (R xs) (hxs xs hrow) (hex xs hrow)).mono
      fun out cost ho => ⟨ho.1, ho.2.trans (linObjectOffsetRowsItemCost_mono (by
        change (Val.list [ctx, .list xs]).wt ≤ 100 * (W + 1)
        omega))⟩
  refine (linMapAll_spec (h.block 0 rfl) Val.list (fun _ _ hh => Val.list.inj hh)
    (fun xs out => ∃ g, out = encPerm g ∧ R xs g) ctx rows
    (linObjectOffsetRowsItemCost (100 * (W + 1))) hs).mono fun out cost ho => ?_
  obtain ⟨⟨ws, rfl, hws⟩, hc⟩ := ho
  obtain ⟨gs, rfl, hgs⟩ := linForall₂_encoded encPerm R hws
  exact ⟨⟨gs, rfl, hgs⟩, hc⟩

end GI.Impl
