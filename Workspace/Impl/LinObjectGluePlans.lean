module

public import Workspace.Impl.LinObjectReadPlan
public import Workspace.Impl.LinPolyEnvelope

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

def linObjectGlueCtxPlan : linObjectReadPlan := .list
  [.read 0 [2],.read 0 [1],.read 1 [0,0],.read 1 [4,1],.read 1 [4,0]]
def linObjectGlueDataPlan : linObjectReadPlan := .list [.read 0 [2],.read 0 [1],.read 0 [3],.read 0 [4]]
def linObjectGluePiecesPlan : linObjectReadPlan := .list [.read 0 [2],.read 0 [1],.read 0 [3]]
def linObjectGlueConjugatePlan : linObjectReadPlan := .list [.read 0 [5],.read 0 [6]]
def linObjectGlueCoordinatePlan : linObjectReadPlan := .list [linObjectGlueCtxPlan,.read 2 [0],.read 0 [6]]
def linObjectGlueZeroPlan : linObjectReadPlan := .list [.length (.read 1 [4,0]),.list [.nat 0,.nil]]
def linObjectGlueAffinePlan : linObjectReadPlan := .list [linObjectGlueCtxPlan,.read 3 [1],.read 5 [],.read 4 []]
def linObjectGlueComposePlan : linObjectReadPlan := .list [.read 0 [6],.read 6 [0]]
def linObjectGlueCorrectPlan : linObjectReadPlan := .list
  [.read 0 [2],.read 0 [1],.read 1 [0,0],.read 1 [2],.read 2 [0],.read 7 []]
def linObjectGlueStabilizerPlan : linObjectReadPlan := .list
  [.list [.read 0 [2],.read 0 [1],.read 1 [0,0],.read 1 [2]],.read 1 [0,1],.read 6 [1,1]]
def linObjectGlueOutPlan : linObjectReadPlan := .list [.read 8 [],.read 9 []]
def linObjectGlueTestPlan : linObjectReadPlan := .length (.read 6 [])

def linObjectGluePlans : List linObjectReadPlan := [linObjectGlueDataPlan,linObjectGluePiecesPlan,
  linObjectGlueConjugatePlan,linObjectGlueCoordinatePlan,linObjectGlueZeroPlan,linObjectGlueAffinePlan,
  linObjectGlueComposePlan,linObjectGlueCorrectPlan,linObjectGlueStabilizerPlan,linObjectGlueOutPlan,linObjectGlueTestPlan]

def linObjectGlueArgBudget (C : ℕ) : ℕ := (linObjectGluePlans.map (linObjectPlanBudget · C)).sum+1

theorem linObjectGlueArgBudget_poly : PBU (fun _ C _ => linObjectGlueArgBudget C) :=
  PBU.addc (linObjectPlanListBudget_poly linObjectGluePlans) 1

theorem linObjectGluePlan_det {P : Program} {env : List Val} {C : ℕ} (h : normEnvBound C env)
    (plan : linObjectReadPlan) (hp : plan ∈ linObjectGluePlans) {v : Val}
    (hv : plan.value env = some v) : Det P env plan.expr v (linObjectGlueArgBudget C) := by
  have hh : linObjectPlanBudget plan C ≤ (linObjectGluePlans.map (linObjectPlanBudget · C)).sum :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.mpr ⟨plan,hp,rfl⟩)
  exact (linObjectReadPlan_det h plan hv).mono (hh.trans (Nat.le_add_right _ _))

theorem linObjectGluePlanBudget_le (plan : linObjectReadPlan) (C : ℕ) (hp : plan ∈ linObjectGluePlans) :
    linObjectPlanBudget plan C ≤ linObjectGlueArgBudget C := by
  have hh : linObjectPlanBudget plan C ≤ (linObjectGluePlans.map (linObjectPlanBudget · C)).sum :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.mpr ⟨plan,hp,rfl⟩)
  exact hh.trans (Nat.le_add_right _ _)

end GI.Impl
