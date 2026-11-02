import Workspace.Impl.LinObjectOffsetRow
import Workspace.Impl.LinSlice

namespace GI.Impl
open GI.Cited GI.Lang

def linObjectOffsetWindowF (slice row : ℕ) : Expr :=
  .letE (.call slice (.var 0)) (.call row (.var 1))

def linObjectOffsetWindowFuns (b : ℕ) : List Expr :=
  [linObjectOffsetWindowF (b + 1) (b + 4)] ++ linSliceFuns (b + 1) ++ linObjectOffsetRowFuns (b + 4)

theorem linObjectOffsetWindowFuns_length (b : ℕ) : (linObjectOffsetWindowFuns b).length = 10 := rfl

def linObjectOffsetWindowCost (W : ℕ) : ℕ :=
  100000 * (W + linSliceCost W + linObjectOffsetRowCost (linSliceCost W) + 1)

theorem linObjectOffsetWindowCost_poly : PBU (fun _ W _ => linObjectOffsetWindowCost W) := by
  unfold linObjectOffsetWindowCost linObjectOffsetRowCost linListPickCost linSliceCost
  norm_poly

theorem linObjectOffsetRowCost_mono {W V : ℕ} (h : W ≤ V) :
    linObjectOffsetRowCost W ≤ linObjectOffsetRowCost V := by
  unfold linObjectOffsetRowCost linListPickCost
  gcongr

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 3000 in
theorem linObjectOffsetWindow_spec {P : Program} {b n offset count : ℕ}
    (h : P.HasAt b (linObjectOffsetWindowFuns b)) (xs : List Val)
    (hsafe : offset + count ≤ xs.length) (R : Equiv.Perm (Fin n) → Prop)
    (hxs : ∀ v ∈ (xs.drop offset).take count,
      v = .list [] ∨ ∃ (a : Equiv.Perm (Fin n)) (gs : List (Equiv.Perm (Fin n))),
        v = .list [encPerm a, encGroup gs] ∧ R a)
    (hex : ∃ v ∈ (xs.drop offset).take count, v ≠ .list []) :
    let a := Val.list [.nat offset, .nat count, .list xs]
    FunAll P b a (fun out cost => (∃ a, out = encPerm a ∧ R a) ∧
      cost ≤ linObjectOffsetWindowCost a.wt) := by
  let a := Val.list [.nat offset, .nat count, .list xs]
  let cut := (xs.drop offset).take count
  let W := a.wt
  have hs := linSlice_spec (h.block 1 rfl) xs offset count hsafe
  have wc : (Val.list cut).wt ≤ linSliceCost W := hs.wt_lt.le
  have hr : FunAll P (b + 4) (.list cut) (fun out cost =>
      (∃ a, out = encPerm a ∧ R a) ∧ cost ≤ linObjectOffsetRowCost (linSliceCost W)) :=
    (linObjectOffsetRow_spec (h.block 4 rfl) cut R hxs hex).mono fun out cost ho =>
      ⟨ho.1, ho.2.trans (linObjectOffsetRowCost_mono wc)⟩
  have ds := Det.call (Det.var' (P := P) (env := [a]) (i := 0) rfl) hs
  apply FunAll.intro (h.block (gs := [linObjectOffsetWindowF (b + 1) (b + 4)]) 0 rfl).single
  apply EvalAll.letE ds
  intro v ca hv
  obtain ⟨rfl, hca⟩ := hv
  apply EvalAll.call_funAll (Det.var' (P := P) (env := [a, .list cut]) (i := 1) rfl)
  intro v cb hv
  obtain ⟨rfl, hcb⟩ := hv
  refine hr.wt_lt.mono fun out cost ho => ⟨ho.1.1, ?_⟩
  have hc := ho.1.2
  have hw := ho.2
  change _ ≤ linObjectOffsetWindowCost W
  unfold linObjectOffsetWindowCost
  dsimp only [a, W, cut] at *
  omega

end GI.Impl
