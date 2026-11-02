import Workspace.Lang.Prims.LinNormal

/-! Function-index specifications for the normal-form calls in A.20.
Each program consists of one primitive call. The bounds include the input and output
weights charged by GI.Lang. The task exponents and running-time constants come only
from the explicit cited hypotheses. -/
namespace GI.Impl
open GI.Cited GI.Lang

/-- A Hermite call at primitive index j. -/
def linHermiteF (j : ℕ) : Expr := primF j

noncomputable def linHermiteCost (h : HermiteFullRank) (I : FullRankInst) : ℕ :=
  (linHermitePrim h).bound (fullRankInput I) + (fullRankInput I).wt +
    linHermiteWt (linHermiteDegree h) I + 2

/-- A function-index spec with all Hermite multipliers and their bit bounds. -/
theorem linHermite_spec (h : HermiteFullRank) {P : Program} {f j : ℕ}
    (hf : P.funs[f]? = some (linHermiteF j))
    (hj : P.prims[j]? = some (linHermitePrim h)) (I : FullRankInst) :
    FunAll P f (fullRankInput I) (fun w cost =>
      linHermiteOut (linHermiteDegree h) I w ∧ cost ≤ linHermiteCost h I) := by
  refine (FunAll.prim_spec hf hj (linHermitePrim_spec h I)).mono fun w cost hw => ?_
  exact ⟨hw.1, by have := linHermiteOut_wt hw.1; unfold linHermiteCost; omega⟩

/-- A Smith call at primitive index j. -/
def linSmithF (j : ℕ) : Expr := primF j

noncomputable def linSmithCost (h : SmithNonsingular) (I : NonsingularInst) : ℕ :=
  (linSmithPrim h).bound (nonsingularInput I) + (nonsingularInput I).wt +
    linSmithWt (linSmithDegree h) I + 2

/-- Smith is called on a square nonsingular block, with explicit output-writing cost. -/
theorem linSmith_spec (h : SmithNonsingular) {P : Program} {f j : ℕ}
    (hf : P.funs[f]? = some (linSmithF j))
    (hj : P.prims[j]? = some (linSmithPrim h)) (I : NonsingularInst) :
    FunAll P f (nonsingularInput I) (fun w cost =>
      linSmithOut (linSmithDegree h) I w ∧ cost ≤ linSmithCost h I) := by
  refine (FunAll.prim_spec hf hj (linSmithPrim_spec h I)).mono fun w cost hw => ?_
  exact ⟨hw.1, by have := linSmithOut_wt hw.1; unfold linSmithCost; omega⟩

end GI.Impl
