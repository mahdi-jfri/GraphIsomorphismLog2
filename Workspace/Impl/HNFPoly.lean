import Workspace.Impl.HNFMain
import Workspace.Impl.PolyBd

/-!
# The cost of the Hermite program is polynomial

`hnfMainCost W` is built from `+`, `*`, `^` with constant exponents and numerals, so it has a
uniform polynomial bound (`GI.Impl.PBU`). The tactic `hnf_norm_poly` is a copy of `norm_poly`
(`Impl/GenNormPoly.lean`), kept here to avoid importing that file's dependencies.
-/

namespace GI.Impl
open GI.Lang

open Lean Meta Elab Tactic in
private partial def hnfPolyProof (vs : Array Lean.Expr) (b : Lean.Expr) : MetaM Lean.Expr := do
  let b := b.consumeMData
  if let .letE _ _ v body _ := b then
    return ← hnfPolyProof vs (body.instantiate1 v)
  if b == vs[0]! then return mkConst ``PBU.k
  if b == vs[1]! then return mkConst ``PBU.W
  if b == vs[2]! then return mkConst ``PBU.B
  if !(b.find? (fun e => vs.contains e)).isSome then
    return ← mkAppM ``PBU.const #[b]
  let args := b.getAppArgs
  let fn := b.getAppFn.constName?
  if fn == some ``HAdd.hAdd || fn == some ``Nat.add then
    return ← mkAppM ``PBU.add #[← hnfPolyProof vs args[args.size - 2]!,
      ← hnfPolyProof vs args[args.size - 1]!]
  if fn == some ``HMul.hMul || fn == some ``Nat.mul then
    return ← mkAppM ``PBU.mul #[← hnfPolyProof vs args[args.size - 2]!,
      ← hnfPolyProof vs args[args.size - 1]!]
  if fn == some ``HPow.hPow || fn == some ``Nat.pow then
    return ← mkAppM ``PBU.pow #[← hnfPolyProof vs args[args.size - 2]!, args[args.size - 1]!]
  throwError "hnf_norm_poly: unsupported term: {b}"

open Lean Meta Elab Tactic in
elab "hnf_norm_poly" : tactic => do
  let g ← getMainGoal
  let target ← g.getType
  let f := target.getAppArgs[0]!
  let pr ← lambdaTelescope f fun vs b => hnfPolyProof vs b
  g.assign pr
  replaceMainGoal []

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem hnfMainCost_poly : PBU (fun _ W _ => hnfMainCost W) := by
  simp only [hnfMainCost, hnfXW, hnfL, hnfBarCost, hnfBarStepCost, hnfPivCost, hnfTabCost,
    hnfTabRowCost, linTabulateCost, linTabulateRangeCost, linMapBudget, hnfUpdCellCost,
    linIntBinaryCost, linIntCoreBudget, linIntPartsCost, linIntCodecCost, hnfNumsCost,
    hnfMatAbsCost, hnfRowAbsCost, hnfAbsStepCost, hnfPowCost, hnfComplCost, hnfComplTestCost,
    countK, hnfBigCellCost, hnfModCost, hnfColCost, hnfFoldCost, hnfFoldStepCost,
    hnfEucStepCost, hnfRedCost, hnfRedCellCost, hnfSingleCost, hnfMapRedCost, hnfRowRedCost,
    hnfUCellCost, hnfHCellCost]
  hnf_norm_poly

end GI.Impl
