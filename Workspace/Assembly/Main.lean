module

public import Workspace.Assembly.FinalGlue
public import Workspace.Impl.LinObjectGlueUniform

@[expose] public section

/-!
# Theorem 1.1: graph isomorphism in quasipolynomial time

This is the last step of the chain of reductions. `final_modulo_glueObj`
(`Workspace/Assembly/FinalGlue.lean`) proves the statement from one remaining part, the object glue:
a list of functions placed at `flcRecIdx + tmRiGlueOff`, with a length bound and the contract
`TermGlueObjSpec`. Here we plug in the concrete object glue `GI.Impl.gObjF` of
`Workspace/Impl/LinObjectGlue.lean`. Its contract is `linObjectGlue_iface_fixed_of`.

That theorem needs the list to sit at its base and eight primitives at given indices. In the
final program the cited primitives sit at these indices (all checked by `rfl`):
* `Membership` at `1`, `GroupOrder` at `5`, `DerivedSubgroup` at `8`;
* the block `linA20Extra` at `14`: `SolvableCosetIntersection` at `14`, Hermite at `15`,
  Smith at `16`, constructive membership at `17`, `VectorStabilizer` at `18`.

The statement is `GI.Statement.GraphIsomorphismInQuasipolynomialTime`
(`Workspace/Statement/Main.lean`).
-/

open GI.Algorithm GI.Lang GI.Paper GI.Impl GI.Assembly

/-- The object glue list of the final program: `gObjF` at `flcRecIdx + tmRiGlueOff`, with the
primitive indices of the final program. -/
noncomputable abbrev GI.Assembly.mainGObjF : List Expr :=
  GI.Impl.gObjF (flcRecIdx + tmRiGlueOff) 14 8 1 5 17 15 16 18

theorem GI.Assembly.mainGObjF_fits :
    mainGObjF.length ≤ flcLabOff - flcRecOff - tmRiGlueOff := by
  rw [mainGObjF, gObjF_length]; unfold flcLabOff flcRecOff tmRiGlueOff; omega

/-- The object glue list sits at `flcRecIdx + tmRiGlueOff` in the final program. -/
theorem GI.Assembly.mainGObjF_hasAt :
    (cProg mainGObjF fc11SojF).HasAt (flcRecIdx + tmRiGlueOff) mainGObjF := by
  have hF : FlcFits (tmRiRecF flcRecIdx 14 8 1 mainGObjF)
      (tmGLPLabF (tmGLNeConc (flcLabIdx + 1) flSupIdx)) tmJFinF :=
    ⟨tmRi_recF_fits mainGObjF_fits, tmGLPLabF_fits items6_neF_room, tmJFinF_fits⟩
  have hg : gsGen.length ≤ asmSlot := by rw [length_gsGen]; unfold asmSlot; omega
  exact (tmRi_recF_hasAt (flc_hasAt hg hF).2.1).2

/-- **Theorem 1.1.** Graph isomorphism is decidable in quasipolynomial time, in the model of
`Workspace/Statement/Main.lean`. -/
theorem GI.Assembly.graphIsomorphismInQuasipolynomialTime :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime :=
  final_modulo_glueObj mainGObjF mainGObjF_fits
    (linObjectGlue_iface_fixed_of GI.Proved.solvableCosetIntersection GI.Proved.derivedSubgroup GI.Proved.membership
      GI.Proved.groupOrder GI.Proved.constructiveMembership GI.Proved.hermiteFullRank GI.Proved.smithNonsingular GI.Proved.vectorStabilizer
      mainGObjF_hasAt rfl rfl rfl rfl rfl rfl rfl rfl)
