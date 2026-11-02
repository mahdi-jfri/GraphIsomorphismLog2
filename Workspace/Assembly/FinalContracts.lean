import Workspace.Assembly.FinalOpen
import Workspace.Axioms.AlgoPermGroups
import Workspace.Proved.SNFFinal
import Workspace.Proved.VectorStabilizer
import Workspace.Proved.KRef
import Workspace.Proved.JohnFinal
import Workspace.Proved.NClDerived
import Workspace.Proved.NClPreimage
import Workspace.Proved.MBlk
import Workspace.Proved.NInt
import Workspace.Proved.HNFFinal
import Workspace.Proved.SSMembership
import Workspace.Proved.SSGroupOrder
import Workspace.Proved.SSPointwiseStab
import Workspace.Proved.SSConstructiveMembership
import Workspace.Proved.SCosFinal

/-!
# Stage 2 from the two program contracts

`final_modulo_contracts` is `final_modulo_open` with each of its 21 cited algorithm tasks
supplied by its proof in `Workspace/Proved/` or, for four of them, by an axiom of
`Workspace/Axioms/AlgoPermGroups.lean`. Its only hypotheses are the two program contracts: the object glue and the first-rectangle item.

`cProg` and `cIface` are `finProg` and `finIface` at these axioms, so that the statement can be
read.
-/

namespace GI.Assembly

open GI.Algorithm GI.Lang GI.Paper GI.Impl GI.Axioms

/-- The final program at these proofs and axioms, with the object glue `gObjF` and the
first-rectangle item `sojF` as its two remaining parts. -/
noncomputable abbrev cProg (gObjF sojF : List Expr) : Program :=
  finProg GI.Proved.pointwiseStab GI.Proved.membership GI.Proved.preimage GI.Proved.normalizedFactor GI.Proved.minimalBlocks GI.Proved.groupOrder
    GI.Proved.johnsonIdentification chiefSeriesAlgo GI.Proved.derivedSubgroup quotientCentralizer
    GI.Proved.normalizedIntersection sylowAlgo sylowConjugate GI.Proved.normalClosure GI.Proved.solvableCosetIntersection
    GI.Proved.hermiteFullRank GI.Proved.smithNonsingular GI.Proved.constructiveMembership GI.Proved.vectorStabilizer GI.Proved.karyRefinement64
    GI.Proved.karyRefinement2 gObjF sojF

/-- The interface of the first-rectangle contract at these proofs and axioms. `Kj Dj` are the
constants of the join program, `Kg Dg` those of the object glue, and `Xs` the weight bound of
the first-rectangle item. -/
noncomputable abbrev cIface (Kj Dj Kg Dg : ℕ) (Xs : ℕ → ℕ) : Iface :=
  finIface GI.Proved.pointwiseStab GI.Proved.membership GI.Proved.preimage GI.Proved.normalizedFactor GI.Proved.minimalBlocks GI.Proved.groupOrder
    GI.Proved.johnsonIdentification chiefSeriesAlgo GI.Proved.derivedSubgroup quotientCentralizer
    GI.Proved.normalizedIntersection sylowAlgo sylowConjugate GI.Proved.normalClosure GI.Proved.solvableCosetIntersection
    GI.Proved.hermiteFullRank GI.Proved.smithNonsingular GI.Proved.constructiveMembership GI.Proved.vectorStabilizer GI.Proved.karyRefinement64
    GI.Proved.karyRefinement2 Kj Dj Kg Dg Xs

/-- **Stage 2 from the two program contracts.**

Every cited algorithm task is a proved theorem or an axiom. The hypotheses are the two program
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
    GI.Proved.johnsonIdentification chiefSeriesAlgo GI.Proved.derivedSubgroup quotientCentralizer
    GI.Proved.normalizedIntersection sylowAlgo sylowConjugate GI.Proved.normalClosure GI.Proved.solvableCosetIntersection
    GI.Proved.hermiteFullRank GI.Proved.smithNonsingular GI.Proved.constructiveMembership GI.Proved.vectorStabilizer GI.Proved.karyRefinement64
    GI.Proved.karyRefinement2 gObjF hgo sojF hsojF Xs hgl hsoj hXs

end GI.Assembly
