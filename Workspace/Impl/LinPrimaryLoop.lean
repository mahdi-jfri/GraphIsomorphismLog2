module

public import Workspace.Impl.LinPrimaryStepSpec
public import Workspace.Impl.LinPrimaryTerminal

@[expose] public section

/-! Bounded primary filtration. A failed accumulator is propagated; otherwise
the current triple is expanded to the complete iteration input. -/
namespace GI.Impl
open GI.Cited GI.Lang
set_option maxRecDepth 32000

def linPrimaryLoopStepF (step : ℕ) : Expr :=
  .ite (.length (arg 2))
    (.call step (.snoc (.snoc (mk4 (.get (arg 2) (.nat 0)) (.get (arg 2) (.nat 1))
      (.get (arg 2) (.nat 2)) (.get (arg 0) (.nat 3))) (.get (arg 0) (.nat 4))) (arg 1)))
    .nil

def linPrimaryLoopFuns (b jm jv : ℕ) : List Expr :=
  loopFuns b (.call (b + 3) (arg 4)) (mk3 (arg 0) (arg 1) (arg 2)) (linPrimaryLoopStepF (b + 8)) ++
    maxFuns (b + 3) ++ linPrimaryStepFuns (b + 8) jm jv

theorem linPrimaryLoopFuns_length (b jm jv : ℕ) : (linPrimaryLoopFuns b jm jv).length = 437 := by
  simp only [linPrimaryLoopFuns, List.length_append, linPrimaryStepFuns_length]
  rfl

structure linPrimaryLoopAt (P : Program) (b jm jv : ℕ)
    (hm : ConstructiveMembership) (hv : VectorStabilizer) : Prop where
  loop : P.HasAt b (loopFuns b (.call (b + 3) (arg 4))
    (mk3 (arg 0) (arg 1) (arg 2)) (linPrimaryLoopStepF (b + 8)))
  max : P.HasAt (b + 3) (maxFuns (b + 3))
  step : linPrimaryStepAt P (b + 8) jm jv hm hv

set_option maxHeartbeats 4000000 in
theorem linPrimaryLoopAt_of (hm : ConstructiveMembership) (hv : VectorStabilizer)
    {P : Program} {b jm jv : ℕ} (h : P.HasAt b (linPrimaryLoopFuns b jm jv))
    (hjm : P.prims[jm]? = some (linMembershipPrim hm))
    (hjv : P.prims[jv]? = some (vectorStabilizerPrim hv)) : linPrimaryLoopAt P b jm jv hm hv where
  loop := h.block 0 rfl
  max := h.block 3 rfl
  step := linPrimaryStepAt_of hm hv (h.block 8 rfl) hjm hjv

end GI.Impl
