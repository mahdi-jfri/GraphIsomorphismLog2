module

public import Workspace.Impl.LinObjectCallSteps
public import Workspace.Impl.LinObjectGlueProblem
public import Workspace.Impl.LinObjectGlueAffineSpec
public import Workspace.Impl.LinObjectGlueCoordinateSpec

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset
open scoped IsMulCommutative

variable {n : ℕ} (I : linObjectGlueProblem n)
variable [((gens I.ns).subgroupOf (gens I.as)).Normal]
variable [IsMulCommutative ((gens I.as) ⧸ (gens I.ns).subgroupOf (gens I.as))]

noncomputable def linObjectGlueProblem.affineSet (F : linObjectGlueFrame I.as I.ns I.Y) : Set (Equiv.Perm (Fin n)) :=
  let hπ : Function.Surjective (linObjectCanonicalProjection I.as I.ns) := QuotientGroup.mk'_surjective _
  let hker := linObjectCanonical_ker_local I.as I.ns I.Y I.fixY
  let hn := I.normalA.mono I.cover_H
  tmGLAffTrans I.coverGenerators (F.rep (gens I.coverGenerators) hn I.cover_conf hπ hker)
    (F.cocycle (gens I.coverGenerators) hn I.cover_conf hπ hker) 0 (F.point (tmGlMs I.X ↼ I.τ))

noncomputable def linObjectGlueProblem.sourcePieces (xv : Val) : Val :=
  .list [.list ((tmRiPcsO (gens I.as) I.X).map tmGlObjsVal),xv]

noncomputable def linObjectGlueProblem.prefixValues (F : linObjectGlueFrame I.as I.ns I.Y) (xv : Val) : List Val :=
  [I.value,F.value,I.sourcePieces xv,.list [encPerm I.τ,encGroup I.coverGenerators],
    linFiniteIntVecVal (tmGLQMod F.D) (F.point (tmGlMs I.X ↼ I.τ)),
    linVecVal (0 : Fin (I.as.length*(tmRiPcsO (gens I.as) I.Y).length) → ℤ)]

def linObjectGluePrefixInv (i : ℕ) (env : List Val) : Prop :=
  match i with
  | 0 => env = [I.value]
  | 1 => ∃ F : linObjectGlueFrame I.as I.ns I.Y,env = [I.value,F.value]
  | 2 | 3 | 4 | 5 => ∃ (F : linObjectGlueFrame I.as I.ns I.Y) (xv : Val),env = (I.prefixValues F xv).take (i+1)
  | 6 => ∃ (F : linObjectGlueFrame I.as I.ns I.Y) (xv u : Val),env = I.prefixValues F xv++[u] ∧
      CosetC n u (I.affineSet F)
  | _ => False

def linObjectGluePrefixSteps (data pieces conjugate coordinate zero affine : ℕ) : List (ℕ × linObjectReadPlan) :=
  [(data,linObjectGlueDataPlan),(pieces,linObjectGluePiecesPlan),(conjugate,linObjectGlueConjugatePlan),
    (coordinate,linObjectGlueCoordinatePlan),(zero,linObjectGlueZeroPlan),(affine,linObjectGlueAffinePlan)]

def linObjectGlueSuffixSteps (compose correct stabilizer : ℕ) : List (ℕ × linObjectReadPlan) :=
  [(compose,linObjectGlueComposePlan),(correct,linObjectGlueCorrectPlan),(stabilizer,linObjectGlueStabilizerPlan)]

theorem linObjectGlueCoreF_steps (data pieces coordinate affine correct stabilizer compose zero conjugate : ℕ) :
    linObjectGlueCoreF data pieces coordinate affine correct stabilizer compose zero conjugate =
      linObjectCallStepsE (linObjectGluePrefixSteps data pieces conjugate coordinate zero affine)
        (.ite linObjectGlueTestPlan.expr
          (linObjectCallStepsE (linObjectGlueSuffixSteps compose correct stabilizer) linObjectGlueOutPlan.expr) .nil) := rfl

end GI.Impl
