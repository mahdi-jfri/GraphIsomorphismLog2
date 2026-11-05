module

public import Workspace.Assembly.Items6Req
public import Workspace.Impl.CamFinal
public import Workspace.Proved.GMPTransitive
public import Workspace.Proved.SolvGMP
public import Workspace.Proved.DixonPrimitive
public import Workspace.Proved.KCRefinement
public import Workspace.Proved.DesignLemma
public import Workspace.Cited.Facts

@[expose] public section

/-!
# Stage 2 from the cited tasks and the two program contracts

`final_modulo_open` is `final_modulo_items6` with three changes.
* The cited `KaryCoherentRefinement`, `DesignLemma`, `GMPAbelianFactors`,
  `GMPTransitiveNonabelian` and `DixonDerivedLength` are
  proved in Lean (`Workspace/Proved/`).
* `CameronRecognition` is derived by `cameronRecognition_of_johnson` from Maróti's theorem
  (`marotiPrimitive`) and the cited algorithm tasks `GroupOrder`
  and `JohnsonIdentification`.
* The free list of extra primitives is empty: `ext''' := []`.

The final program and the interface of the first-rectangle contract are named `finProg` and
`finIface`, so that the two program contracts can be read.
-/

namespace GI.Assembly

open GI.Algorithm GI.Lang GI.Paper GI.Impl
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership MinimalBlocks GroupOrder
  CameronRecognition DerivedSubgroup NormalizedIntersection
  NormalClosure SolvableCosetIntersection HermiteFullRank
  SmithNonsingular ConstructiveMembership VectorStabilizer KaryRefinement JohnsonIdentification)

/-- The Cameron recognition algorithm, built from Maróti's theorem and the cited tasks
(`cameronRecognition_of_johnson`). -/
noncomputable abbrev finCam (hj : JohnsonIdentification) (hO : GroupOrder) :
    CameronRecognition :=
  cameronRecognition_of_johnson GI.Cited.marotiPrimitive hj hO

/-- The extra primitives of the final program: those of the linear-algebra layer, those of the
aggregation layer, and the `2`-ary refinement. -/
noncomputable abbrev finExt (hs : SolvableCosetIntersection) (hh : HermiteFullRank)
    (hn : SmithNonsingular) (hcmb : ConstructiveMembership) (hv : VectorStabilizer)
    (hk : KaryRefinement P₀.κ) (h2 : KaryRefinement 2) : List Prim :=
  linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ [karyRefinementPrim h2])

/-- The final program, with the object glue `gObjF` and the first-rectangle item `sojF` as its
two remaining parts. -/
noncomputable abbrev finProg
    (hst : PointwiseStab) (hm : Membership) (hpre : Preimage)
    (hfac : NormalizedFactor) (hmb : MinimalBlocks) (hO : GroupOrder)
    (hj : JohnsonIdentification) (hder : DerivedSubgroup)
    (hni : NormalizedIntersection)
    (hnc : NormalClosure) (hs : SolvableCosetIntersection)
    (hh : HermiteFullRank) (hn : SmithNonsingular) (hcmb : ConstructiveMembership)
    (hv : VectorStabilizer) (hk : KaryRefinement P₀.κ) (h2 : KaryRefinement 2)
    (gObjF sojF : List Expr) : Program :=
  fagProg hst hm hpre hfac hmb hO (finCam hj hO) hder hni hnc
    (finExt hs hh hn hcmb hv hk h2) (tmRiRecF flcRecIdx 14 8 1 gObjF)
    (tmGLPLabF (tmGLNeConc (flcLabIdx + 1) flSupIdx)) tmJFinF fcrE fcmE fitE fcrF fcmF
    (fitF itHvHvIF (fc23F fc23ObF (fc10PrF sojF)) (rcRepF fitRpIdx))

/-- The interface of the first-rectangle contract in the final program. `Kj Dj` are the
constants of the join program, `Kg Dg` those of the object glue, and `Xs` the weight bound of
the first-rectangle item. -/
noncomputable abbrev finIface
    (hst : PointwiseStab) (hm : Membership) (hpre : Preimage)
    (hfac : NormalizedFactor) (hmb : MinimalBlocks) (hO : GroupOrder)
    (hj : JohnsonIdentification) (hder : DerivedSubgroup)
    (hni : NormalizedIntersection)
    (hnc : NormalClosure) (hs : SolvableCosetIntersection)
    (hh : HermiteFullRank) (hn : SmithNonsingular) (hcmb : ConstructiveMembership)
    (hv : VectorStabilizer) (hk : KaryRefinement P₀.κ) (h2 : KaryRefinement 2)
    (Kj Dj Kg Dg : ℕ) (Xs : ℕ → ℕ) : Iface :=
  fagIface hst hm hpre hfac hmb hO (finCam hj hO) hder hni hnc
    (3 * items6K hst hm hfac hO hh hn hcmb hv hni hnc + 100)
    (items6D hst hm hfac hO hh hn hcmb hv hni hnc + 1)
    Kj Dj (fglRecK hs hder hm Kg Dg) (fglRecD hs hder hm Kg Dg)
    (fagX hpre (cpCertX hst hpre hm) (cmRunX hst hpre hm)
      (fitXi hk hst hO (itHvXh hfac hst) (fc23X h2 (itCfObjCo hst) (itCfObjDo hst) (fc10Xp Xs))))

/-- **Stage 2 from the cited algorithm tasks and the two program contracts.**

`CameronRecognition` is derived from Maróti's theorem (`finCam`). The hypotheses are of two kinds.

*Cited algorithm tasks*, each supplied in `Assembly/FinalContracts.lean` by a proved
theorem: `hst` (PointwiseStab), `hm`
(Membership), `hpre` (Preimage), `hfac` (NormalizedFactor), `hmb` (MinimalBlocks), `hO`
(GroupOrder), `hj` (JohnsonIdentification), `hder` (DerivedSubgroup),
`hni` (NormalizedIntersection),
`hnc` (NormalClosure), `hs` (SolvableCosetIntersection), `hh`
(HermiteFullRank), `hn` (SmithNonsingular), `hcmb` (ConstructiveMembership), `hv`
(VectorStabilizer), `hk` (`KaryRefinement P₀.κ`) and `h2` (`KaryRefinement 2`).

*Program contracts*:
* the object glue `gObjF`, with its length bound `hgo` and its contract `hgl`
  (`TermGlueObjSpec` at constants `Kg Dg`), proved in `Assembly/Main.lean`;
* the first-rectangle item `sojF`, with its length bound `hsojF`, its contract `hsoj`
  (`ItciSojSpec` for all join constants `Kj Dj`) and the polynomial bound `hXs` on its weight
  bound `Xs`, proved in `Assembly/FinalGlue.lean`. -/
theorem final_modulo_open (hst : PointwiseStab) (hm : Membership) (hpre : Preimage)
    (hfac : NormalizedFactor) (hmb : MinimalBlocks) (hO : GroupOrder)
    (hj : JohnsonIdentification) (hder : DerivedSubgroup)
    (hni : NormalizedIntersection)
    (hnc : NormalClosure) (hs : SolvableCosetIntersection)
    (hh : HermiteFullRank) (hn : SmithNonsingular) (hcmb : ConstructiveMembership)
    (hv : VectorStabilizer) (hk : KaryRefinement P₀.κ) (h2 : KaryRefinement 2)
    (gObjF : List Expr) (hgo : gObjF.length ≤ flcLabOff - flcRecOff - tmRiGlueOff)
    (sojF : List Expr) (hsojF : sojF.length ≤ 99000)
    {Kg Dg : ℕ} (Xs : ℕ → ℕ)
    (hgl : Iface.TermGlueObjSpec
      (finProg hst hm hpre hfac hmb hO hj hder hni hnc hs hh hn hcmb hv hk h2
        gObjF sojF) Kg Dg (flcRecIdx + tmRiGlueOff))
    (hsoj : ∀ Kj Dj : ℕ, ItciSojSpec
      (finIface hst hm hpre hfac hmb hO hj hder hni hnc hs hh hn hcmb hv hk h2
        Kj Dj Kg Dg Xs)
      (finProg hst hm hpre hfac hmb hO hj hder hni hnc hs hh hn hcmb hv hk h2
        gObjF sojF)
      asmF (fitC23Idx + 101000) (fitC23Idx + 101001) (fitC23Idx + 101002) Xs)
    (hXs : PBU fun _ W _ => Xs W) :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime :=
  final_modulo_items6 hst hm hpre hfac hmb hO (finCam hj hO)
    GI.Proved.gmpAbelianFactors GI.Proved.gmpTransitiveNonabelian hder
    hni hnc hs hh hn hcmb hv GI.Proved.dixonDerivedLength
    GI.Proved.karyCoherentRefinement GI.Proved.designLemma hk h2
    [] gObjF hgo sojF hsojF Xs hgl hsoj hXs

end GI.Assembly
