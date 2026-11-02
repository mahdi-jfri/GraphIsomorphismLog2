import Workspace.Impl.LinPrimeContext
import Workspace.Impl.LinPrimePoint
import Workspace.Impl.LinTrialPrepare
import Workspace.Impl.LinPrimaryLoopInput

/-! Construct one complete primary-loop input from retained mixed-order data. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linPrimePrepareF (trial context point : ℕ) : Expr :=
  .letE (.call trial (mk2 (arg 3) (arg 4)))
    (.letE (.snoc (.get (.var 1) (.nat 1)) linIntZeroE)
      (.letE (.call context (mk2 (.var 2) (arg 0)))
        (.letE (.call point (mk2 (arg 1) (.var 2)))
          (.snoc (mk4 (.var 3) (.var 4) (arg 2) (arg 3)) (.get (.var 1) (.nat 0))))))

def linPrimePrepareFuns (b : ℕ) : List Expr :=
  [linPrimePrepareF (b + 1) (b + 36) (b + 66)] ++
    linTrialPrepareFuns (b + 1) ++ linPrimeContextFuns (b + 36) ++ linPrimePointFuns (b + 66)

theorem linPrimePrepareFuns_length (b : ℕ) : (linPrimePrepareFuns b).length = 87 := rfl

structure linPrimePrepareAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linPrimePrepareF (b + 1) (b + 36) (b + 66))
  trial : linTrialPrepareAt P (b + 1)
  context : linPrimeContextAt P (b + 36)
  point : P.HasAt (b + 66) (linPrimePointFuns (b + 66))

theorem linPrimePrepareAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linPrimePrepareFuns b)) : linPrimePrepareAt P b where
  entry := (h.block (gs := [linPrimePrepareF (b + 1) (b + 36) (b + 66)]) 0 rfl).single
  trial := linTrialPrepareAt_of (h.block 1 rfl)
  context := linPrimeContextAt_of (h.block 36 rfl)
  point := h.block 66 rfl

noncomputable def linPrimePrepareInputVal {n d : ℕ} (gs : List (Equiv.Perm (Fin n)))
    (m : Fin d → ℕ) (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m))
    (c : gens gs → linFiniteVec m) (x : linFiniteVec m) (r : Equiv.Perm (Fin n)) (p : ℕ) : Val :=
  .list [linActionContext gs m ρ c, linFinitePointVal m x, encPerm r,
    .nat p, linVecVal (fun i => (m i : ℤ))]

def linPrimePrepareTrialBudget (W : ℕ) : ℕ := linTrialPrepareCost (100 * (W + 1))
def linPrimePrepareSubArg (W : ℕ) : ℕ := 1000 * (W + linPrimePrepareTrialBudget W + 1)
def linPrimePrepareContextBudget (W : ℕ) : ℕ := linPrimeContextCost (linPrimePrepareSubArg W)
def linPrimePreparePointBudget (W : ℕ) : ℕ := linPrimePointCost (linPrimePrepareSubArg W)
def linPrimePrepareCost (W : ℕ) : ℕ := 1000000 * (W + linPrimePrepareTrialBudget W +
  linPrimePrepareContextBudget W + linPrimePreparePointBudget W + 1)

end GI.Impl
