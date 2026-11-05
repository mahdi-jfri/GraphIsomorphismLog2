module

public import Workspace.Impl.LinObjectGlueCore

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

noncomputable def linObjectGlueAllCost (hs : SolvableCosetIntersection) (hm : Membership)
    (ho : GroupOrder) (hc : ConstructiveMembership) (hh : HermiteFullRank)
    (hn : SmithNonsingular) (hv : VectorStabilizer) (n W M : ℕ) : ℕ :=
  linObjectDataCost hs hm ho hc hh hn W + linObjectPiecesCost hs hm n M W +
  linObjectSourceCoordinateCost hs hm hc W + linObjectCallerCost hs hm hc hh hv W +
  linObjectCorrectOneCost hs hm hc hh W + linObjectStabilizerCost hs hm hc hh W +
  linAffineLeftCost W + permK*(n+1)^3 + 100000*(M+1)^2

theorem linObjectGlueAllCost_poly (hs : SolvableCosetIntersection) (hm : Membership)
    (ho : GroupOrder) (hc : ConstructiveMembership) (hh : HermiteFullRank)
    (hn : SmithNonsingular) (hv : VectorStabilizer) : PBU (linObjectGlueAllCost hs hm ho hc hh hn hv) := by
  have hp : PBU (fun n W M => linObjectPiecesCost hs hm n M W) :=
    linPoly_subst (linObjectPiecesCost_poly hs hm) PBU.k PBU.B PBU.W
  have hz : PBU (fun _ _ M => 100000*(M+1)^2) := PBU.smul 100000 (PBU.pow (PBU.addc PBU.B 1) 2)
  have hcP : PBU (fun n _ _ => permK*(n+1)^3) := PBU.smul permK (PBU.pow PBU.k1 3)
  exact PBU.add (PBU.add (PBU.add (PBU.add (PBU.add (PBU.add (PBU.add (PBU.add
    (linObjectDataCost_poly hs hm ho hc hh hn) hp) (linObjectSourceCoordinateCost_poly hs hm hc))
    (linObjectCallerCost_poly hs hm hc hh hv)) (linObjectCorrectOneCost_poly hs hm hc hh))
    (linObjectStabilizerCost_poly hs hm hc hh)) linAffineLeftCost_poly) hcP) hz

noncomputable def linObjectGlueEnvelope (hs : SolvableCosetIntersection) (hm : Membership)
    (ho : GroupOrder) (hc : ConstructiveMembership) (hh : HermiteFullRank)
    (hn : SmithNonsingular) (hv : VectorStabilizer) (W : ℕ) : ℕ :=
  linPolyEnvelope (linObjectGlueAllCost_poly hs hm ho hc hh hn hv) (linObjectGlueArgBudget W+W+100)

noncomputable def linObjectGlueGrow (hs : SolvableCosetIntersection) (hm : Membership)
    (ho : GroupOrder) (hc : ConstructiveMembership) (hh : HermiteFullRank)
    (hn : SmithNonsingular) (hv : VectorStabilizer) (W : ℕ) : ℕ :=
  100*(W+linObjectGlueArgBudget W+linObjectGlueEnvelope hs hm ho hc hh hn hv W+1)^2

theorem linObjectGlueGrow_poly (hs : SolvableCosetIntersection) (hm : Membership)
    (ho : GroupOrder) (hc : ConstructiveMembership) (hh : HermiteFullRank)
    (hn : SmithNonsingular) (hv : VectorStabilizer) : PBU (fun _ W _ => linObjectGlueGrow hs hm ho hc hh hn hv W) := by
  have harg := PBU.addc (PBU.add linObjectGlueArgBudget_poly PBU.W) 100
  have he := linPoly_subst (linPolyEnvelope_poly (linObjectGlueAllCost_poly hs hm ho hc hh hn hv))
    (PBU.const 0) harg (PBU.const 0)
  exact PBU.smul 100 (PBU.pow (PBU.addc (PBU.add (PBU.add PBU.W linObjectGlueArgBudget_poly) he) 1) 2)

theorem linObjectGlueGrow_le (hs : SolvableCosetIntersection) (hm : Membership)
    (ho : GroupOrder) (hc : ConstructiveMembership) (hh : HermiteFullRank)
    (hn : SmithNonsingular) (hv : VectorStabilizer) (W : ℕ) : W ≤ linObjectGlueGrow hs hm ho hc hh hn hv W := by
  have hp : W+linObjectGlueArgBudget W+linObjectGlueEnvelope hs hm ho hc hh hn hv W+1 ≤
      (W+linObjectGlueArgBudget W+linObjectGlueEnvelope hs hm ho hc hh hn hv W+1)^2 := Nat.le_self_pow (by decide) _
  unfold linObjectGlueGrow
  omega

theorem linObjectGlueGrow_bound (hs : SolvableCosetIntersection) (hm : Membership)
    (ho : GroupOrder) (hc : ConstructiveMembership) (hh : HermiteFullRank)
    (hn : SmithNonsingular) (hv : VectorStabilizer) {n S M W : ℕ}
    (hnW : n ≤ W) (hS : S ≤ linObjectGlueArgBudget W) (hM : M ≤ W) :
    linObjectGlueAllCost hs hm ho hc hh hn hv n S M ≤ linObjectGlueGrow hs hm ho hc hh hn hv W := by
  have he : linObjectGlueAllCost hs hm ho hc hh hn hv n S M ≤ linObjectGlueEnvelope hs hm ho hc hh hn hv W :=
    linPolyEnvelope_bound (linObjectGlueAllCost_poly hs hm ho hc hh hn hv) (by omega) (by omega) (by omega)
  have hp : W+linObjectGlueArgBudget W+linObjectGlueEnvelope hs hm ho hc hh hn hv W+1 ≤
      (W+linObjectGlueArgBudget W+linObjectGlueEnvelope hs hm ho hc hh hn hv W+1)^2 := Nat.le_self_pow (by decide) _
  unfold linObjectGlueGrow
  omega

theorem linObjectInflationary_iter_le (f : ℕ → ℕ) (hf : ∀ n,n ≤ f n) (W : ℕ) {i j : ℕ}
    (hij : i ≤ j) : f^[i] W ≤ f^[j] W := by
  induction j with
  | zero =>
    have hi : i = 0 := by omega
    subst i
    exact le_rfl
  | succ j ih =>
    by_cases hi : i ≤ j
    · rw [Function.iterate_succ_apply']
      exact (ih hi).trans (hf _)
    · have hi' : i = j+1 := by omega
      subst i
      exact le_rfl

theorem linObjectGlueIter_poly (hs : SolvableCosetIntersection) (hm : Membership)
    (ho : GroupOrder) (hc : ConstructiveMembership) (hh : HermiteFullRank)
    (hn : SmithNonsingular) (hv : VectorStabilizer) (i : ℕ) :
    PBU (fun _ W _ => (linObjectGlueGrow hs hm ho hc hh hn hv)^[i] W) := by
  induction i with
  | zero => exact PBU.W
  | succ i ih =>
    simpa only [Function.iterate_succ_apply'] using
      linPoly_subst (linObjectGlueGrow_poly hs hm ho hc hh hn hv) (PBU.const 0) ih (PBU.const 0)

noncomputable def linObjectGlueCoreCost (hs : SolvableCosetIntersection) (hm : Membership)
    (ho : GroupOrder) (hc : ConstructiveMembership) (hh : HermiteFullRank)
    (hn : SmithNonsingular) (hv : VectorStabilizer) (W : ℕ) : ℕ :=
  let C := (linObjectGlueGrow hs hm ho hc hh hn hv)^[10] W
  100*(linObjectGlueArgBudget C+2*C+100)*3^20

theorem linObjectGlueCoreCost_poly (hs : SolvableCosetIntersection) (hm : Membership)
    (ho : GroupOrder) (hc : ConstructiveMembership) (hh : HermiteFullRank)
    (hn : SmithNonsingular) (hv : VectorStabilizer) : PBU (fun _ W _ => linObjectGlueCoreCost hs hm ho hc hh hn hv W) := by
  have hi := linObjectGlueIter_poly hs hm ho hc hh hn hv 10
  have ha := linPoly_subst linObjectGlueArgBudget_poly (PBU.const 0) hi (PBU.const 0)
  exact PBU.mul (PBU.smul 100 (PBU.addc (PBU.add ha (PBU.smul 2 hi)) 100)) (PBU.const (3^20))

end GI.Impl
