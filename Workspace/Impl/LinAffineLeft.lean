import Workspace.Impl.LinAffineCoset
import Workspace.Impl.LinMapSource
import Workspace.Impl.GenNormGlue
import Workspace.Lang.Prims.BlockHom

namespace GI.Impl
open GI.Cited GI.Lang

def linConjugateCellF (compose : ℕ) : Expr :=
  .letE (.call compose (mk2 (.get (arg 0) (.nat 0)) (arg 1)))
    (.call compose (mk2 (.var 1) (.get (arg 0) (.nat 1))))

def linConjugateCellCost (W n : ℕ) : ℕ := 100000 * (W + permK * (n + 1) ^ 3 + 1)

set_option maxHeartbeats 1000000 in
theorem linConjugateCell_spec {P : Program} {f compose n : ℕ}
    (hf : P.funs[f]? = some (linConjugateCellF compose))
    (hc : P.HasAt compose (composeFuns compose)) (l g r : Equiv.Perm (Fin n)) :
    let a := Val.list [.list [encPerm l, encPerm r], encPerm g]
    FunDet P f a (encPerm (l * g * r)) (linConjugateCellCost a.wt n) := by
  let ctx := Val.list [encPerm l, encPerm r]
  let a := Val.list [ctx, encPerm g]
  let W := a.wt
  let u := encPerm (l * g)
  have h1 := compose_spec hc l g
  have h2 := compose_spec hc (l * g) r
  have wctx : ctx.wt < W := wt_le_wt_list (by simp [a, W])
  have wg : (encPerm g).wt < W := wt_le_wt_list (by simp [a, W])
  have wl : (encPerm l).wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have wr : (encPerm r).wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have wu := h1.wt_lt.le
  have wo := h2.wt_lt.le
  have dc := Det.arg' (P := P) (vs := [ctx, encPerm g]) (rest := []) (j := 0) rfl
  have dg := Det.arg' (P := P) (vs := [ctx, encPerm g]) (rest := []) (j := 1) rfl
  have d1 := Det.call (Det.mk2 (Det.get' dc (Det.nat 0) rfl) dg) h1
  have dc' := Det.arg' (P := P) (vs := [ctx, encPerm g]) (rest := [u]) (j := 0) rfl
  have d2 := Det.call (Det.mk2 (Det.var' (P := P) (env := [a, u]) (i := 1) rfl)
    (Det.get' dc' (Det.nat 1) rfl)) h2
  apply FunDet.intro hf
  refine (Det.letE d1 d2).mono ?_
  have wi1 := wt_list2_le (encPerm l) (encPerm g)
  have wi2 := wt_list2_le u (encPerm r)
  change _ ≤ linConjugateCellCost W n
  unfold linConjugateCellCost
  dsimp only [a, W, ctx, u] at *
  omega

theorem linConjugateCellCost_mono {W V n k : ℕ} (hW : W ≤ V) (hn : n ≤ k) :
    linConjugateCellCost W n ≤ linConjugateCellCost V k := by
  unfold linConjugateCellCost
  gcongr

def linAffineLeftF (inv tail map group : ℕ) : Expr :=
  .letE (.call inv (arg 1))
    (.letE (.call tail (.get (arg 0) (.nat 1)))
      (.letE (.call map (mk2 (mk2 (.var 1) (arg 1)) (.var 2)))
        (.letE (.call group (mk2 (.get (arg 0) (.nat 0)) (.var 3))) (mk2 (arg 1) (.var 4)))))

def linAffineLeftFuns (b : ℕ) : List Expr :=
  [linAffineLeftF (b + 1) (b + 13) (b + 16) (b + 24)] ++ invFuns (b + 1) ++
    tailFuns (b + 13) ++ mapFuns (b + 16) (b + 19) ++ [linConjugateCellF (b + 20)] ++
    composeFuns (b + 20) ++ mkGroupFuns (b + 24)

theorem linAffineLeftFuns_length (b : ℕ) : (linAffineLeftFuns b).length = 31 := rfl

structure linAffineLeftAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linAffineLeftF (b + 1) (b + 13) (b + 16) (b + 24))
  inv : P.HasAt (b + 1) (invFuns (b + 1))
  tail : P.HasAt (b + 13) (tailFuns (b + 13))
  map : P.HasAt (b + 16) (mapFuns (b + 16) (b + 19))
  cell : P.funs[b + 19]? = some (linConjugateCellF (b + 20))
  compose : P.HasAt (b + 20) (composeFuns (b + 20))
  group : P.HasAt (b + 24) (mkGroupFuns (b + 24))

theorem linAffineLeftAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linAffineLeftFuns b)) : linAffineLeftAt P b where
  entry := (h.block (gs := [linAffineLeftF (b + 1) (b + 13) (b + 16) (b + 24)]) 0 rfl).single
  inv := h.block 1 rfl
  tail := h.block 13 rfl
  map := h.block 16 rfl
  cell := (h.block (gs := [linConjugateCellF (b + 20)]) 19 rfl).single
  compose := h.block 20 rfl
  group := h.block 24 rfl

def linAffineLeftInvBudget (W : ℕ) : ℕ := invK * (W + 1) ^ 4
def linAffineLeftTailBudget (W : ℕ) : ℕ := loopModK * (W + 1) * (3 * W + 1)
def linAffineLeftMapArg (W : ℕ) : ℕ := 100 * (W + linAffineLeftInvBudget W + 1)
def linAffineLeftMapBudget (W : ℕ) : ℕ :=
  linMapBudget (linAffineLeftMapArg W) (linConjugateCellCost (linAffineLeftMapArg W) W)
def linAffineLeftGroupBudget (W : ℕ) : ℕ := mkGroupK * ((W + 2) * (W + 1)) ^ 3
def linAffineLeftCost (W : ℕ) : ℕ := 100000 * (W + linAffineLeftInvBudget W + linAffineLeftTailBudget W +
  linAffineLeftMapBudget W + linAffineLeftGroupBudget W + 1)

end GI.Impl
