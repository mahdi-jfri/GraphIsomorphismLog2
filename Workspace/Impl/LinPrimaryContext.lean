module

public import Workspace.Impl.LinPrimaryInstance
public import Workspace.Impl.LinActionItem

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

theorem linPrimaryGeneratorList_eq {n : ℕ} (gs : List (Equiv.Perm (Fin n))) :
    linPrimaryGeneratorList gs = linActionGens gs := by
  unfold linPrimaryGeneratorList linActionGens
  calc _ = gs.attach.map (fun x => linIntoSubgroup (gens gs) x.val) := by
          apply List.map_congr_left
          intro x _
          apply Subtype.ext
          exact (linIntoSubgroup_val (gens gs) x.val (Subgroup.subset_closure x.property)).symm
    _ = _ := List.attach_map_val (l := gs) (f := linIntoSubgroup (gens gs))

theorem linPrimaryInput_context {n p d : ℕ} (gs : List (Equiv.Perm (Fin n)))
    (ν : Fin d → ℕ) (level : ℕ)
    (ρ : gens gs →* (linFiniteVec (linPrimaryOrders p ν) ≃+ linFiniteVec (linPrimaryOrders p ν)))
    (c : gens gs → linFiniteVec (linPrimaryOrders p ν)) (x : linFiniteVec (linPrimaryOrders p ν)) :
    linPrimaryInputVal gs ν level ρ c x =
      .list [encGroup gs, .nat p, encFun ν, .nat level,
        linGroupSlpTable (linFiniteAffineVal (linPrimaryOrders p ν) ρ c) (linActionGens gs),
        linFinitePointVal (linPrimaryOrders p ν) x] := by
  simp only [linPrimaryInputVal, linPrimaryGeneratorList_eq, linGroupSlpTable]

end GI.Impl
