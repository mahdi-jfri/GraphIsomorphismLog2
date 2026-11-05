module

public import Workspace.Assembly.FinalOpen
public import Workspace.Proved.SNFFinal
public import Workspace.Proved.VectorStabilizer
public import Workspace.Proved.KRef
public import Workspace.Proved.JohnFinal
public import Workspace.Proved.NClDerived
public import Workspace.Proved.NClPreimage
public import Workspace.Proved.MBlk
public import Workspace.Proved.NInt
public import Workspace.Proved.HNFFinal
public import Workspace.Proved.SSMembership
public import Workspace.Proved.SSGroupOrder
public import Workspace.Proved.SSPointwiseStab
public import Workspace.Proved.SSConstructiveMembership
public import Workspace.Proved.SCosFinal

@[expose] public section

/-!
# Stage 2 from the two program contracts

`final_modulo_contracts` is `final_modulo_open` with each of its cited algorithm tasks
supplied by its proof in `Workspace/Proved/`. Its only hypotheses are the two program contracts: the object glue and the first-rectangle item.

`cProg` and `cIface` are `finProg` and `finIface` at these proofs, so that the statement can be
read.
-/

namespace GI.Assembly

open GI.Algorithm GI.Lang GI.Paper GI.Impl

/-- The final program at these proofs, with the object glue `gObjF` and the
first-rectangle item `sojF` as its two remaining parts. -/
noncomputable abbrev cProg (gObjF sojF : List Expr) : Program :=
  finProg GI.Proved.pointwiseStab GI.Proved.membership GI.Proved.preimage GI.Proved.normalizedFactor GI.Proved.minimalBlocks GI.Proved.groupOrder
    GI.Proved.johnsonIdentification GI.Proved.derivedSubgroup
    GI.Proved.normalizedIntersection GI.Proved.normalClosure GI.Proved.solvableCosetIntersection
    GI.Proved.hermiteFullRank GI.Proved.smithNonsingular GI.Proved.constructiveMembership GI.Proved.vectorStabilizer GI.Proved.karyRefinement64
    GI.Proved.karyRefinement2 gObjF sojF

/-- The interface of the first-rectangle contract at these proofs. `Kj Dj` are the
constants of the join program, `Kg Dg` those of the object glue, and `Xs` the weight bound of
the first-rectangle item. -/
noncomputable abbrev cIface (Kj Dj Kg Dg : ℕ) (Xs : ℕ → ℕ) : Iface :=
  finIface GI.Proved.pointwiseStab GI.Proved.membership GI.Proved.preimage GI.Proved.normalizedFactor GI.Proved.minimalBlocks GI.Proved.groupOrder
    GI.Proved.johnsonIdentification GI.Proved.derivedSubgroup
    GI.Proved.normalizedIntersection GI.Proved.normalClosure GI.Proved.solvableCosetIntersection
    GI.Proved.hermiteFullRank GI.Proved.smithNonsingular GI.Proved.constructiveMembership GI.Proved.vectorStabilizer GI.Proved.karyRefinement64
    GI.Proved.karyRefinement2 Kj Dj Kg Dg Xs

/-- **Stage 2 from the two program contracts.**

Every cited algorithm task is a proved theorem. The hypotheses are the two program
contracts:
* the object glue `gObjF`, with its length bound `hgo` and its contract `hgl`
  (`TermGlueObjSpec` at constants `Kg Dg`);
* the first-rectangle item `sojF`, with its length bound `hsojF`, its contract `hsoj`
  (`ItciSojSpec` for all join constants `Kj Dj`) and the polynomial bound `hXs` on its weight
  bound `Xs`. -/
theorem final_modulo_contracts
    (gObjF : List Expr) (hgo : gObjF.length ≤ flcLabOff - flcRecOff - tmRiGlueOff)
    (sojF : List Expr) (hsojF : sojF.length ≤ 99000)
    {Kg Dg : ℕ} (Xs : ℕ → ℕ)
    (hgl : Iface.TermGlueObjSpec (cProg gObjF sojF) Kg Dg (flcRecIdx + tmRiGlueOff))
    (hsoj : ∀ Kj Dj : ℕ, ItciSojSpec (cIface Kj Dj Kg Dg Xs) (cProg gObjF sojF)
      asmF (fitC23Idx + 101000) (fitC23Idx + 101001) (fitC23Idx + 101002) Xs)
    (hXs : PBU fun _ W _ => Xs W) :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime :=
  final_modulo_open GI.Proved.pointwiseStab GI.Proved.membership GI.Proved.preimage GI.Proved.normalizedFactor GI.Proved.minimalBlocks GI.Proved.groupOrder
    GI.Proved.johnsonIdentification GI.Proved.derivedSubgroup
    GI.Proved.normalizedIntersection GI.Proved.normalClosure GI.Proved.solvableCosetIntersection
    GI.Proved.hermiteFullRank GI.Proved.smithNonsingular GI.Proved.constructiveMembership GI.Proved.vectorStabilizer GI.Proved.karyRefinement64
    GI.Proved.karyRefinement2 gObjF hgo sojF hsojF Xs hgl hsoj hXs

end GI.Assembly
