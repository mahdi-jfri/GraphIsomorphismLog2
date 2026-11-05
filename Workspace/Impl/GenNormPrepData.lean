module

public import Workspace.Impl.GenNormStage
public import Workspace.Impl.GenNormNumbering
public import Workspace.Impl.GenNormSel
public import Workspace.Impl.GenNormFiber
public import Workspace.Impl.GenNormCall

@[expose] public section

/-! # The data passed from preparation to the recursive normalization calls -/
namespace GI.Impl
open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encKSetTuples Preimage PointwiseStab Membership)

/-- Use the installed pairing loop without repeating its eleven code indices. -/
theorem normPairAt.spec {Pg : Program} (o : normPairAt Pg)
    {Ω C : Type} {S : State Ω C} {n m k : ℕ} (en : Ω ≃ Fin n) (Q : PrimitiveQuotient S)
    (e : Fin Q.d ≃ (Fin 1 → Product.KSet m k)) (hS : Q.ProductStructure m k 1 e)
    (num : Fin n → ℕ) (reps : List ℕ) (hd : normBlockData en Q num reps)
    (gs : List (Perm (Fin n))) (hgs : ∀ a ∈ gs, (toFin en).symm a ∈ S.G) :
    FunDet Pg o.map (.list [.list [encFun num, natList reps, encKSetTuples e,
      encPerm (1 : Perm (Fin Q.d)), encPerm (1 : Perm (Fin m))], .list (gs.map encPerm)])
      (.list ((gs.map (normPairOf en Q e hS)).map pairV))
      (normParentListCost n m gs.length (Val.list [encFun num, natList reps, encKSetTuples e,
        encPerm (1 : Perm (Fin Q.d)), encPerm (1 : Perm (Fin m))]).wt) :=
  normParentList_spec o.hmap o.hparent o.hact o.hgather o.hrecover o.hpoint o.hfilter
    o.hcand o.hall o.htest o.hmem en Q e hS num reps hd.1 hd.2.1 hd.2.2.1
      hd.2.2.2.1 hd.2.2.2.2 gs hgs

/-- The runtime tail input retains the original canonical state, the normalized group and
hierarchy, the exact supplied labels, one orbit-test bit, and the computed coset list. -/
def normPrepared {Ω C : Type} [Finite Ω] {S : State Ω C} {n m k : ℕ} (en : Ω ≃ Fin n)
    (Q : PrimitiveQuotient S) (htr : S.Transitive)
    (e : Fin Q.d ≃ (Fin 1 → Product.KSet m k)) (hS : Q.ProductStructure m k 1 e)
    (hq : P₀.q₀ < m) (hkc : Q.KillsCols) (hkl : Q.KeepsLevels)
    (sv hv : Val) (out : Val) : Prop :=
  ∃ (D : normCosetData Q e hS) (gv lv : Val) (b : Bool) (ts : List (Perm (Fin n))),
    let N := Q.normAboveOf D.choice htr hq hkc hkl
    out = .list [.list [sv, gv, hv, lv, boolVal b], .list (ts.map encPerm)] ∧
      GroupValC n gv (groupFin en N.I.G') ∧
      (∀ j, LabValStd en (N.child j) lv (N.childLabels j)) ∧
      ts.length = N.I.k ∧ (∀ j : Fin N.I.k, N.I.τ j = (toFin en).symm (ts.getD j 1)) ∧
      (∀ j, (normMode b = .cont ∧ ¬ (N.child j).Transitive) ∨
        (normMode b = .giant ∧ (N.child j).Transitive))

end GI.Impl
