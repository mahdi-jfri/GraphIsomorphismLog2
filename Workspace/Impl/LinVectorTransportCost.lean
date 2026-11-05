module

public import Workspace.Impl.LinVectorTargetCall
public import Workspace.Impl.LinFiniteActionCost

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

noncomputable def linVectorTransportChoiceArg (h : VectorStabilizer) (W : ℕ) : ℕ :=
  100 * (W + linWreathStabCost h W + 1)
noncomputable def linVectorTransportChoiceBudget (h : VectorStabilizer) (W : ℕ) : ℕ :=
  linWreathChoiceGensCost (linVectorTransportChoiceArg h W) W
noncomputable def linVectorTransportCost (h : VectorStabilizer) (W : ℕ) : ℕ :=
  100000 * (W + linWreathStabCost h W + linVectorTransportChoiceBudget h W + linVectorTargetCost h W + 1)

theorem linWreathChoiceGensCost_mono {W V n m : ℕ} (hW : W ≤ V) (hn : n ≤ m) :
    linWreathChoiceGensCost W n ≤ linWreathChoiceGensCost V m := by
  simp only [linWreathChoiceGensCost, linWreathChoiceGensGroupCost, linWreathChoiceGensArg,
    mkGroupK, linWreathChoiceCost, linWreathChoiceFindCost, linWreathChoiceExtractCost,
    linWreathExtractCost, linTabulateCost, linTabulateRangeCost, linMapBudget]
  gcongr

theorem linVectorTransportCost_poly (h : VectorStabilizer) :
    PBU (fun _ W _ => linVectorTransportCost h W) := by
  have hs := linWreathStabCost_poly h
  have ha : PBU (fun _ W _ => linVectorTransportChoiceArg h W) :=
    PBU.smul 100 (PBU.addc (PBU.add PBU.W hs) 1)
  have hc : PBU (fun _ W _ => linVectorTransportChoiceBudget h W) :=
    linPoly_subst linWreathChoiceGensCost_poly PBU.W ha (PBU.const 0)
  exact PBU.smul 100000 (PBU.addc (PBU.add (PBU.add (PBU.add PBU.W hs) hc)
    (linVectorTargetCost_poly h)) 1)

end GI.Impl
