import Workspace.Impl.LinWreathGroup
import Workspace.Impl.LinSumPerm
import Workspace.Impl.LinSwapPerm

/-! The numbered cover generators as explicit disjoint permutation tables. -/
namespace GI.Impl
open GI.Cited Equiv

@[simp] theorem linWreathCover_first {n : ℕ} (gs : List (Perm (Fin n))) (h : gens gs) :
    linWreathFinCover (gens gs) (linWreathSingle 1 h) = sumToFin (Equiv.sumCongr h.val 1) := by
  apply Equiv.ext
  intro i
  induction i using Fin.addCases with
  | left i =>
    rw [(linWreathFinCover_single_one h i).1]
    simp [sumToFin]
    rfl
  | right i =>
    rw [(linWreathFinCover_single_one h i).2]
    change i.natAdd n = finSumFinEquiv ((Equiv.sumCongr h.val 1)
      (finSumFinEquiv.symm (i.natAdd n)))
    rw [finSumFinEquiv_symm_apply_natAdd]
    rfl

@[simp] theorem linWreathCover_second {n : ℕ} (gs : List (Perm (Fin n))) (h : gens gs) :
    linWreathFinCover (gens gs) (linWreathSingle linTwoSwap h) = sumToFin (Equiv.sumCongr 1 h.val) := by
  apply Equiv.ext
  intro i
  induction i using Fin.addCases with
  | left i =>
    rw [(linWreathFinCover_single_swap h i).1]
    simp [sumToFin]
  | right i =>
    rw [(linWreathFinCover_single_swap h i).2]
    change (h • i).natAdd n = finSumFinEquiv ((Equiv.sumCongr 1 h.val)
      (finSumFinEquiv.symm (i.natAdd n)))
    rw [finSumFinEquiv_symm_apply_natAdd]
    rfl

@[simp] theorem linWreathCover_copySwap {n : ℕ} (gs : List (Perm (Fin n))) :
    linWreathFinCover (gens gs) linWreathSwap = linSwapPerm n := by
  apply Equiv.ext
  intro i
  induction i using Fin.addCases with
  | left i => rw [(linWreathFinCover_swap i).1, linSwapPerm_left]
  | right i => rw [(linWreathFinCover_swap i).2, linSwapPerm_right]

/-- This is the list built by the permutation-table program. -/
theorem linWreathCoverGenerators_formula {n : ℕ} (gs : List (Perm (Fin n))) :
    linWreathCoverGenerators gs =
      gs.map (fun g => sumToFin (Equiv.sumCongr g 1)) ++
      gs.map (fun g => sumToFin (Equiv.sumCongr 1 g)) ++ [linSwapPerm n] := by
  unfold linWreathCoverGenerators linWreathGenerators linWreathSubgens
  simp only [List.map_append, List.map_map, List.map_cons, List.map_nil,
    linWreathCover_copySwap]
  have hfirst : gs.map (fun x => linWreathFinCover (gens gs)
      (linWreathSingle 1 (linIntoSubgroup (gens gs) x))) =
      gs.map (fun g => sumToFin (Equiv.sumCongr g 1)) := by
    apply List.map_congr_left
    intro g hg
    rw [linWreathCover_first]
    have hv := linIntoSubgroup_val (gens gs) g (show g ∈ gens gs from Subgroup.subset_closure hg)
    change (linIntoSubgroup (gens gs) g).val = g at hv
    rw [hv]
  have hsecond : gs.map (fun x => linWreathFinCover (gens gs)
      (linWreathSingle linTwoSwap (linIntoSubgroup (gens gs) x))) =
      gs.map (fun g => sumToFin (Equiv.sumCongr 1 g)) := by
    apply List.map_congr_left
    intro g hg
    rw [linWreathCover_second]
    have hv := linIntoSubgroup_val (gens gs) g (show g ∈ gens gs from Subgroup.subset_closure hg)
    change (linIntoSubgroup (gens gs) g).val = g at hv
    rw [hv]
  simpa only [Function.comp_def] using congrArg₂ (fun x y => x ++ y ++ [linSwapPerm n]) hfirst hsecond

end GI.Impl
