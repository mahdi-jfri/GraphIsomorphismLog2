module

public import Workspace.Impl.LinWreathChoice
public import Workspace.Impl.GenNormGlue

@[expose] public section

/-! The primitive returns raw generators. Add their group header before
scanning, without assuming a different output format for the cited task. -/
namespace GI.Impl
open GI.Cited GI.Lang Equiv

def linWreathChoiceGensF (group choice : ℕ) : Expr :=
  .letE (.call group (mk2 (.arith .add (arg 0) (arg 0)) (arg 1)))
    (.call choice (mk2 (arg 0) (.var 1)))

def linWreathChoiceGensFuns (b : ℕ) : List Expr :=
  [linWreathChoiceGensF (b + 1) (b + 8)] ++ mkGroupFuns (b + 1) ++ linWreathChoiceFuns (b + 8)

theorem linWreathChoiceGensFuns_length (b : ℕ) : (linWreathChoiceGensFuns b).length = 23 := rfl

structure linWreathChoiceGensAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linWreathChoiceGensF (b + 1) (b + 8))
  group : P.HasAt (b + 1) (mkGroupFuns (b + 1))
  choice : linWreathChoiceAt P (b + 8)

theorem linWreathChoiceGensAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linWreathChoiceGensFuns b)) : linWreathChoiceGensAt P b where
  entry := (h.block (gs := [linWreathChoiceGensF (b + 1) (b + 8)]) 0 rfl).single
  group := h.block 1 rfl
  choice := linWreathChoiceAt_of (h.block 8 rfl)

def linWreathChoiceGensGroupCost (n : ℕ) : ℕ := mkGroupK * (((n + n) ^ 2 + 2) * (n + n + 1)) ^ 3

def linWreathChoiceGensArg (W n : ℕ) : ℕ := 100 * (W + n + linWreathChoiceGensGroupCost n + 1)

def linWreathChoiceGensCost (W n : ℕ) : ℕ :=
  100000 * (W + n + linWreathChoiceGensGroupCost n + linWreathChoiceCost (linWreathChoiceGensArg W n) + 1)

theorem linWreathChoiceCost_mono {W V : ℕ} (h : W ≤ V) :
    linWreathChoiceCost W ≤ linWreathChoiceCost V := by
  simp only [linWreathChoiceCost, linWreathChoiceFindCost, linWreathChoiceExtractCost,
    linWreathExtractCost, linTabulateCost, linTabulateRangeCost, linMapBudget]
  gcongr

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 4000 in
theorem linWreathChoiceGens_spec {P : Program} {b : ℕ} (h : linWreathChoiceGensAt P b)
    (I : VecStabInst) [NeZero I.n] (w : Fin I.d → ZMod I.p)
    (hs : List (Perm (Fin (I.n + I.n)))) (hlen : hs.length ≤ (I.n + I.n) ^ 2)
    (hhs : gens hs = vecStabSub (linWreathVecInst I w)) :
    FunAll P b (.list [.nat I.n, .list (hs.map encPerm)]) (fun out cost =>
      linWreathChoiceOut I w out ∧
        cost ≤ linWreathChoiceGensCost (Val.list [.nat I.n, .list (hs.map encPerm)]).wt I.n) := by
  let a := Val.list [.nat I.n, .list (hs.map encPerm)]
  let W := a.wt
  let gv := encGroup hs
  have hgroup := (mkGroup_spec h.group hs).mono (c' := linWreathChoiceGensGroupCost I.n) (by
    unfold linWreathChoiceGensGroupCost
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul_right _ (Nat.add_le_add_right hlen 2)) 3))
  have wg := hgroup.wt_lt.le
  have wn := wt_nat_le I.n
  have wi := wt_list2_le (.nat I.n) gv
  have warg : (Val.list [.nat I.n, gv]).wt ≤ linWreathChoiceGensArg W I.n := by
    unfold linWreathChoiceGensArg
    change gv.wt ≤ linWreathChoiceGensGroupCost I.n at wg
    omega
  have hc : FunAll P (b + 8) (.list [.nat I.n, gv]) (fun out cost =>
      linWreathChoiceOut I w out ∧ cost ≤ linWreathChoiceCost (linWreathChoiceGensArg W I.n)) := by
    exact FunAll.mono (linWreathChoice_spec h.choice I w hs hhs) fun out cost ho =>
      ⟨ho.1, ho.2.trans (linWreathChoiceCost_mono warg)⟩
  have dn := Det.arg' (P := P) (vs := [.nat I.n, .list (hs.map encPerm)]) (rest := []) (j := 0) rfl
  have ds := Det.arg' (P := P) (vs := [.nat I.n, .list (hs.map encPerm)]) (rest := []) (j := 1) rfl
  have dg := Det.call (Det.mk2 (Det.arith (op := .add) dn dn) ds) hgroup
  have dn' := Det.arg' (P := P) (vs := [.nat I.n, .list (hs.map encPerm)]) (rest := [gv]) (j := 0) rfl
  have dc := normBound_call (Det.mk2 dn' (Det.var' (P := P) (env := [a, gv]) (i := 1) rfl)) hc
  apply FunAll.intro h.entry
  apply EvalAll.letE dg
  intro v cg hg
  obtain ⟨rfl, hcg⟩ := hg
  refine dc.mono fun out cost ho => ⟨ho.1, ?_⟩
  have hcost := ho.2.2
  have wout := ho.2.1
  have wraw : (Val.list (hs.map encPerm)).wt < W := wt_le_wt_list (by simp [W, a])
  have wnarg : (Val.nat I.n).wt < W := wt_le_wt_list (by simp [W, a])
  have wadd := wt_nat_le (I.n + I.n)
  have wgarg := wt_list2_le (.nat (I.n + I.n)) (.list (hs.map encPerm))
  change _ ≤ linWreathChoiceGensCost W I.n
  dsimp only [linWreathChoiceGensCost]
  dsimp only [a, W, gv] at *
  simp only [GI.Machine.BinOp.eval_add] at *
  omega

theorem linWreathChoiceGensCost_poly : PBU (fun n W _ => linWreathChoiceGensCost W n) := by
  simp only [linWreathChoiceGensCost, linWreathChoiceGensGroupCost, linWreathChoiceGensArg,
    mkGroupK, linWreathChoiceCost, linWreathChoiceFindCost, linWreathChoiceExtractCost,
    linWreathExtractCost, linTabulateCost, linTabulateRangeCost, linMapBudget]
  norm_poly

end GI.Impl
