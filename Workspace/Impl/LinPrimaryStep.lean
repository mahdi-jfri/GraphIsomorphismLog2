module

public import Workspace.Impl.LinPrimaryTransportNext
public import Workspace.Impl.LinAffineRestrict
public import Workspace.Impl.LinFinitePointApply

@[expose] public section

/-! One primary iteration: solve the field layer, apply the chosen full action,
restrict the cover and its full dictionary, and accumulate the representative.
The state is [full context, full point, representative, p, exponents, level]. -/
namespace GI.Impl
open GI.Cited GI.Lang
set_option maxRecDepth 24000

def linPrimaryStepTailF (item point restrict compose : ℕ) : Expr :=
  .letE (.call item (mk2 (arg 0) (.get (.var 2) (.nat 0))))
    (.letE (.call point (mk2 (.var 3) (arg 1)))
      (.letE (.call restrict (mk2 (arg 0) (.get (.var 2) (.nat 1))))
        (.letE (.call compose (mk2 (.get (.var 2) (.nat 0)) (arg 2)))
          (mk3 (.var 5) (.var 4) (.var 6)))))

def linPrimaryStepLayerArgE : Expr :=
  mk2 (.snoc (.snoc (mk4 (.get (arg 0) (.nat 0)) (arg 3) (arg 4) (arg 5))
    (.get (arg 0) (.nat 1))) (arg 1)) (.var 1)

def linPrimaryStepF (replicate layer item point restrict compose : ℕ) : Expr :=
  .letE (.call replicate (mk2 (.length (arg 4)) (.nat 0)))
    (.letE (.call layer linPrimaryStepLayerArgE)
      (.ite (.length (.var 2)) (linPrimaryStepTailF item point restrict compose) .nil))

def linPrimaryStepFuns (b jm jv : ℕ) : List Expr :=
  [linPrimaryStepF (b + 1) (b + 4) (b + 233) (b + 300) (b + 347) (b + 425)] ++
    replicateFuns (b + 1) ++ linPrimaryTransportFuns (b + 4) jv ++
    linActionItemFuns (b + 233) jm ++ linFinitePointApplyFuns (b + 300) ++
    linAffineRestrictFuns (b + 347) jm ++ composeFuns (b + 425)

theorem linPrimaryStepFuns_length (b jm jv : ℕ) : (linPrimaryStepFuns b jm jv).length = 429 := by
  simp only [linPrimaryStepFuns, List.length_append, List.length_singleton,
    linPrimaryTransportFuns_length, linActionItemFuns_length, linFinitePointApplyFuns_length,
    linAffineRestrictFuns_length]
  rfl

structure linPrimaryStepAt (P : Program) (b jm jv : ℕ)
    (hm : ConstructiveMembership) (hv : VectorStabilizer) : Prop where
  entry : P.funs[b]? = some (linPrimaryStepF (b + 1) (b + 4) (b + 233) (b + 300) (b + 347) (b + 425))
  replicate : P.HasAt (b + 1) (replicateFuns (b + 1))
  layer : linPrimaryTransportAt P (b + 4) jv hv
  item : linActionItemAt P (b + 233) jm hm
  point : linFinitePointApplyAt P (b + 300)
  restrict : linAffineRestrictAt P (b + 347) jm hm
  compose : P.HasAt (b + 425) (composeFuns (b + 425))

set_option maxHeartbeats 3000000 in
theorem linPrimaryStepAt_of (hm : ConstructiveMembership) (hv : VectorStabilizer)
    {P : Program} {b jm jv : ℕ} (hp : P.HasAt b (linPrimaryStepFuns b jm jv))
    (hjm : P.prims[jm]? = some (linMembershipPrim hm))
    (hjv : P.prims[jv]? = some (vectorStabilizerPrim hv)) : linPrimaryStepAt P b jm jv hm hv where
  entry := (hp.block (gs := [linPrimaryStepF (b + 1) (b + 4) (b + 233) (b + 300) (b + 347) (b + 425)]) 0 rfl).single
  replicate := hp.block 1 rfl
  layer := linPrimaryTransportAt_of hv (hp.block 4 rfl) hjv
  item := linActionItemAt_of (hp.block 233 rfl) hjm
  point := linFinitePointApplyAt_of (hp.block 300 rfl)
  restrict := linAffineRestrictAt_of hm (hp.block 347 rfl) hjm
  compose := hp.block 425 rfl

end GI.Impl
