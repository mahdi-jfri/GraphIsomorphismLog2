module

public import Workspace.Impl.LinObjectMatrixSpec
public import Workspace.Impl.LinObjectFrameActions

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

theorem linObjectMatrixSeed_zero (d : ℕ) :
    (linVecVal (0 : Fin d → ℤ)).wt ≤ 100 * (d + 1) := by
  have hz : (encInt 0).wt = 15 := rfl
  have hh := linWtList (vs := (List.finRange d).map fun _ => encInt 0) (B := 15) (by simp [hz])
  simp only [List.length_map,List.length_finRange] at hh
  change (Val.list ((List.finRange d).map fun _ => encInt 0)).wt ≤ _
  omega

theorem linObjectMatrixSeed_basis {d : ℕ} (j : Fin d) :
    (linVecVal (Pi.single j (1 : ℤ))).wt ≤ 100 * (d + 1) := by
  classical
  have hi (i : Fin d) : (encInt ((Pi.single j (1 : ℤ) : Fin d → ℤ) i)).wt ≤ 21 := by
    by_cases he : i = j
    · subst i; simp only [Pi.single_eq_same]; decide
    · simp only [Pi.single_eq_of_ne he]; decide
  have hh := linWtList (vs := (List.finRange d).map fun i => encInt ((Pi.single j (1 : ℤ) : Fin d → ℤ) i))
    (B := 21) (by intro v hv; obtain ⟨i,hi',rfl⟩ := List.mem_map.mp hv; exact hi i)
  simp only [List.length_map,List.length_finRange] at hh
  change (Val.list ((List.finRange d).map fun i => encInt ((Pi.single j (1 : ℤ) : Fin d → ℤ) i))).wt ≤ _
  omega

noncomputable def linObjectMatrixEvalArg (W : ℕ) : ℕ := 10000 * (W + 1) ^ 2
noncomputable def linObjectMatrixEvalBudget (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (hh : HermiteFullRank) (W : ℕ) : ℕ :=
  linPolyEnvelope (linObjectEvalCost_poly hs hm hc hh) (linObjectMatrixEvalArg W)
noncomputable def linObjectMatrixActualSource (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (hh : HermiteFullRank) (W : ℕ) : ℕ :=
  100 * (W + linObjectMatrixEvalBudget hs hm hc hh W + 1) ^ 2
noncomputable def linObjectMatrixActualCost (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (hh : HermiteFullRank) (W : ℕ) : ℕ :=
  linObjectMatrixCost (linObjectMatrixActualSource hs hm hc hh W)

theorem linObjectMatrixActualCost_poly (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (hh : HermiteFullRank) :
    PBU (fun _ W _ => linObjectMatrixActualCost hs hm hc hh W) := by
  unfold linObjectMatrixActualCost linObjectMatrixCost linObjectMatrixEntryBound
    linObjectMatrixTransposeBudget linObjectMatrixTransposeArg linObjectMatrixMapBudget linObjectMatrixMapArg
    linObjectMatrixRangeBudget linObjectMatrixColumnBudget linObjectMatrixColumnCost linObjectMatrixColumnBound
    linObjectMatrixColumnSource linObjectMatrixBasisBudget linObjectMatrixDiffBudget
    linObjectMatrixActualSource linObjectMatrixEvalBudget linObjectMatrixEvalArg linPolyEnvelope
  norm_poly

end GI.Impl
