module

public import Workspace.Impl.GenNormBudget
meta import Lean

@[expose] public section

namespace GI.Impl
open GI.Lang
open GI.Cited (Preimage PointwiseStab Membership)

open Lean Meta Elab Tactic in
private meta partial def normPolyProof (vs : Array Lean.Expr) (b : Lean.Expr) : MetaM Lean.Expr := do
  let b := b.consumeMData
  if let .letE _ _ v body _ := b then
    return ← normPolyProof vs (body.instantiate1 v)
  if b == vs[0]! then return mkConst ``PBU.k
  if b == vs[1]! then return mkConst ``PBU.W
  if b == vs[2]! then return mkConst ``PBU.B
  if !(b.find? (fun e => vs.contains e)).isSome then
    return ← mkAppM ``PBU.const #[b]
  let args := b.getAppArgs
  let fn := b.getAppFn.constName?
  if fn == some ``HAdd.hAdd || fn == some ``Nat.add then
    return ← mkAppM ``PBU.add #[← normPolyProof vs args[args.size - 2]!,
      ← normPolyProof vs args[args.size - 1]!]
  if fn == some ``HMul.hMul || fn == some ``Nat.mul then
    return ← mkAppM ``PBU.mul #[← normPolyProof vs args[args.size - 2]!,
      ← normPolyProof vs args[args.size - 1]!]
  if fn == some ``HPow.hPow || fn == some ``Nat.pow then
    return ← mkAppM ``PBU.pow #[← normPolyProof vs args[args.size - 2]!, args[args.size - 1]!]
  throwError "normalization polynomial has an unsupported term: {b}"

open Lean Meta Elab Tactic in
elab "norm_poly" : tactic => do
  let g ← getMainGoal
  let target ← g.getType
  let f := target.getAppArgs[0]!
  let pr ← lambdaTelescope f fun vs b => normPolyProof vs b
  g.assign pr
  replaceMainGoal []

/-- The common growth bound is polynomial. Cited primitive costs enter through their
fixed constants and exponents. -/
theorem normGrow_poly (hp : Preimage) (hst : PointwiseStab) (hm : Membership) :
    PBU (fun T _ _ => normGrow hp hst hm T) := by
  unfold normGrow normStageBudget normArgBudget normParentListCost normAltCost
    normGraphCost normRawReduceCost normCosetsCost normOutsideCost normBlockMapCost
    normOrbitCost cycGensCost Prim.boundSize groupW
  norm_poly

/-- Substituting a polynomial into a unary polynomial preserves a uniform bound. -/
theorem normPoly_comp {f : ℕ → ℕ} {g : ℕ → ℕ → ℕ → ℕ}
    (hf : PBU (fun k _ _ => f k)) (hg : PBU g) :
    PBU (fun k W B => f (g k W B)) := by
  obtain ⟨C, D, h⟩ := hf
  refine (PBU.smul C (PBU.pow (PBU.addc hg 2) D)).mono ?_
  intro k W B
  simpa only [PB, Nat.zero_add] using h (g k W B) 0 0

/-- Any fixed number of preparation stages has polynomial own cost. -/
theorem normGrow_iter_poly (hp : Preimage) (hst : PointwiseStab) (hm : Membership)
    (i : ℕ) {g : ℕ → ℕ → ℕ → ℕ} (hg : PBU g) :
    PBU (fun k W B => (normGrow hp hst hm)^[i] (g k W B)) := by
  induction i with
  | zero => exact hg
  | succ i ih =>
    simpa only [Function.iterate_succ_apply'] using normPoly_comp (normGrow_poly hp hst hm) ih

/-- A polynomial bound for preparation, using the degree bound `m ≤ n + 2`. -/
theorem normPrepCost_poly (hp : Preimage) (hst : PointwiseStab) (hm : Membership) :
    PBU (fun n W _ => normPrepCost hp hst hm n (n + 2) W) := by
  exact PBU.smul 100 (normGrow_iter_poly hp hst hm 15
    (PBU.addc (PBU.add (PBU.add PBU.W PBU.k) (PBU.addc PBU.k 2)) 100))

end GI.Impl
