import Workspace.Impl.LinWreathPerm
import Workspace.Impl.LinWreathTaskData
import Workspace.Lang.Prims.Ops

/-! Build the complete input of the two-copy vector task. -/
namespace GI.Impl
open GI.Cited GI.Lang

private def linWreathSource (i : ℕ) : Expr := .get (arg 0) (.nat i)
private def linWreathSourceN : Expr := .get (linWreathSource 0) (.nat 0)
private def linWreathSourcePerms : Expr := .get (linWreathSource 0) (.nat 1)

def linWreathInputF (tail perms group matrices append : ℕ) : Expr :=
  .letE (.call tail linWreathSourcePerms)
    (.letE (.call perms (mk2 (.get linWreathSourcePerms (.nat 0)) (.var 1)))
      (.letE (.call group (mk2 (.arith .add linWreathSourceN linWreathSourceN) (.var 2)))
        (.letE (.call matrices (mk2 (linWreathSource 2) (.length (linWreathSource 3))))
          (.letE (.call append (mk2 (linWreathSource 3) (arg 1)))
            (mk4 (.var 3) (linWreathSource 1) (.var 4) (.var 5))))))

def linWreathInputFuns (b : ℕ) : List Expr :=
  [linWreathInputF (b + 1) (b + 4) (b + 32) (b + 39) (b + 68)] ++
    linTailFuns (b + 1) ++ linWreathPermFuns (b + 4) ++ mkGroupFuns (b + 32) ++
    linWreathMatricesFuns (b + 39) ++ appendFuns (b + 68)

theorem linWreathInputFuns_length (b : ℕ) : (linWreathInputFuns b).length = 71 := rfl

structure linWreathInputAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linWreathInputF (b + 1) (b + 4) (b + 32) (b + 39) (b + 68))
  tail : P.HasAt (b + 1) (linTailFuns (b + 1))
  perms : linWreathPermAt P (b + 4)
  group : P.HasAt (b + 32) (mkGroupFuns (b + 32))
  matrices : linWreathMatricesAt P (b + 39)
  append : P.HasAt (b + 68) (appendFuns (b + 68))

theorem linWreathInputAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linWreathInputFuns b)) : linWreathInputAt P b where
  entry := (h.block (gs := [linWreathInputF (b + 1) (b + 4) (b + 32) (b + 39) (b + 68)]) 0 rfl).single
  tail := h.block 1 rfl
  perms := linWreathPermAt_of (h.block 4 rfl)
  group := h.block 32 rfl
  matrices := linWreathMatricesAt_of (h.block 39 rfl)
  append := h.block 68 rfl

/-- These accessors only select old source fields, so later `let` bindings do
not change their meaning. -/
theorem linWreathSource_det {P : Program} {rest : List Val} {vs : List Val} {i : ℕ} {v w : Val}
    (hi : vs[i]? = some w) :
    Det P (.list [.list vs, v] :: rest) (linWreathSource i) w
      (2 * (Val.list [.list vs, v]).wt + 5 + (i + 3) + w.wt + 1) := by
  exact Det.get' (Det.arg' (P := P) (vs := [.list vs, v]) (rest := rest) (j := 0) rfl) (Det.nat i) hi

end GI.Impl
