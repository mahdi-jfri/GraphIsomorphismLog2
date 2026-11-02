import Workspace.Impl.LinRecenterRecord
import Workspace.Impl.LinFiniteActionProg

namespace GI.Impl
open GI.Cited GI.Lang

def linRecenterContextF (map mul : ℕ) : Expr :=
  .letE (.call map (mk2 (mk2 (arg 1) (arg 4)) (arg 2)))
    (.letE (.call mul (mk2 (.get (.var 1) (.nat 0))
      (mk3 (.get (.get (.var 1) (.nat 0)) (.nat 0))
        (.get (.get (.var 1) (.nat 0)) (.nat 2)) (.get (.get (.var 1) (.nat 0)) (.nat 1)))))
      (mk3 (arg 0) (.var 1) (.var 2)))

def linRecenterContextFuns (b : ℕ) : List Expr :=
  [linRecenterContextF (b + 1) (b + 65)] ++ mapFuns (b + 1) (b + 4) ++
    linRecenterRecordFuns (b + 4) ++ linFinitePairFuns (b + 65)

theorem linRecenterContextFuns_length (b : ℕ) : (linRecenterContextFuns b).length = 125 := rfl

structure linRecenterContextAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linRecenterContextF (b + 1) (b + 65))
  map : P.HasAt (b + 1) (mapFuns (b + 1) (b + 4))
  record : linRecenterRecordAt P (b + 4)
  mul : linFinitePairAt P (b + 65)

theorem linRecenterContextAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linRecenterContextFuns b)) : linRecenterContextAt P b where
  entry := (h.block (gs := [linRecenterContextF (b + 1) (b + 65)]) 0 rfl).single
  map := h.block 1 rfl
  record := linRecenterRecordAt_of (h.block 4 rfl)
  mul := linFinitePairAt_of (h.block 65 rfl)

def linRecenterContextMapBudget (W : ℕ) : ℕ :=
  linMapBudget (100 * (W + 1)) (linRecenterRecordCost (100 * (W + 1)))
noncomputable def linRecenterContextIdCoefficient : ℕ :=
  (linPoly_source_bound linFiniteActionOpCost_poly).choose
noncomputable def linRecenterContextIdDegree : ℕ :=
  (linPoly_source_bound linFiniteActionOpCost_poly).choose_spec.choose
noncomputable def linRecenterContextIdBudget (W : ℕ) : ℕ :=
  linRecenterContextIdCoefficient * (W + 1) ^ linRecenterContextIdDegree
noncomputable def linRecenterContextCost (W : ℕ) : ℕ :=
  1000000 * (W + linRecenterContextMapBudget W + linRecenterContextIdBudget W + 1)

end GI.Impl
