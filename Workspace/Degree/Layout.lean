module

public import Workspace.Assembly.Main
public import Workspace.Degree.Root
public import Workspace.Degree.AggD
public import Workspace.Degree.RoundOK

@[expose] public section

/-!
# The program of the degree algorithm

The program `degProg h E D` extends the final program of the general algorithm
(`cProg mainGObjF fc11SojF`). It is again an `asmProg`, so that the placement lemmas of the general
algorithm (`asm_block`, `gs_blk`, `as_blk`, `fag_hasAt_parts`) apply to it. Only two things change:

* the list of the aggregation round gets the new functions `degFuns jr E D` at `dgb 0 = 5·10⁶`,
  after padding;
* the primitive table gets the recognition primitive at its end, at index `degJr`.

The new functions are the ones that call `contD` or `giantD`, and the new programs of Section 8 of
the paper: `contD`, the orbit chain, the reset, `transD`, the case decision, the branches, and the
root. They reuse every other block of the general algorithm at its place. `degF` is the triple of
the three procedures: the general solver at `0`, `contD` at `dgb 0` and `giantD` at `dgb 20`.

`cProg_sub_degProg`: the final program is a prefix of `degProg`, so every contract of the general
algorithm holds in `degProg` (`Program.Sub`).
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly GI.Impl GI.Lang
open GI.Cited (Val)

set_option maxRecDepth 100000

/-! ### The parts of the final program -/

/-- The extra primitives of the final program (after the first four). -/
noncomputable abbrev cExt : List Prim :=
  gsExtra GI.Proved.minimalBlocks GI.Proved.groupOrder
      (finCam GI.Proved.johnsonIdentification GI.Proved.groupOrder) ++
    (flRadExtra GI.Proved.derivedSubgroup GI.Proved.normalizedIntersection ++
      (flSupExtra GI.Proved.normalClosure ++
        finExt GI.Proved.solvableCosetIntersection GI.Proved.hermiteFullRank
          GI.Proved.smithNonsingular GI.Proved.constructiveMembership GI.Proved.vectorStabilizer
          GI.Proved.karyRefinement64 GI.Proved.karyRefinement2))

/-- The list of the row step of the final program. -/
noncomputable abbrev cRow : List Expr :=
  rlRow flRad (flCos (flcCos (tmRiRecF flcRecIdx 14 8 1 mainGObjF)
    (tmGLPLabF (tmGLNeConc (flcLabIdx + 1) flSupIdx)) tmJFinF))

/-- The list of the aggregation round of the final program. -/
noncomputable abbrev cAgg : List Expr :=
  fagAgg fcrE fcmE fitE fcrF fcmF (fitF itHvHvIF (fc23F fc23ObF (fc10PrF fc11SojF)) (rcRepF fitRpIdx))

theorem cProg_eq : cProg mainGObjF fc11SojF =
    asmProg GI.Proved.pointwiseStab GI.Proved.membership GI.Proved.preimage
      GI.Proved.normalizedFactor cExt gsGen cRow cAgg := rfl

theorem length_cAgg : cAgg.length ≤ 2000000 := by
  have hit := fit_fits (rcR_fits itHvHvIF_fits (fc23_fits fc23ObF_length (fc10PrF_fits fc11SojF_length)))
  simp only [cAgg, fagAgg, length_asAgg, fagRest, List.length_append,
    length_asmPad length_fagRd_le, length_asmPad fcr_fits, length_asmPad fcm_fits]
  unfold fitRoom fagItOff fagCmOff fagCrOff at *
  omega

/-! ### The new functions -/

/-- The index of the new function `i`. -/
def dgb (i : ℕ) : ℕ := 5000000 + i

/-- The three procedures of the degree algorithm. -/
def degF : Funs := ⟨0, dgb 0, dgb 20⟩

/-- **The single new functions**, at `dgb 0, …, dgb 41`. -/
noncomputable def degSingles (jr D : ℕ) : List Expr :=
  [contE 99 (dgb 100) 143 342 P₀.N₀ 0 (dgb 1) (dgb 2),
    orbitBody degF 143 320 338 273,
    resetBody 9 (dgb 110) (dgb 3) 289,
    transE (gsb 1) 5 (dgb 4) (dgb 5),
    caseDE (dgb 120) jr D,
    branchE (dgb 6) (dgb 7) (dgb 8),
    enumF (gsb 119) (gsb 154) (dgb 9),
    prodDE (gsb 10) (gsb 417) (gsb 119) (gsb 426) (gsb 429) (gsb 21) (gsb 22) (dgb 9) 5,
    normGateE 0 (dgb 10),
    tailF (dgb 140) (gsb 206) (gsb 200),
    -- 10
    gsNormE (dgb 11),
    normStepF (gsb 28) (dgb 12),
    tailF (dgb 150) (gsb 206) (gsb 200),
    enumChildF degF (gsb 103),
    normChildF degF (gsb 103),
    rhoStep (dgb 160),
    resetIntBody (112 + 18) (112 + 9),
    .nil, .nil, .nil,
    -- 20: the round
    aggBodyE (asb 1) (dgb 21) (dgb 22) (dgb 23) (dgb 170) (asb 5),
    cpCertE (dgb 24) (fagCrIdx + 2),
    cmSetF (fagCmIdx + 100) (dgb 25) (fagCmIdx + 10),
    itSItemsF (fagItIdx + 0) (dgb 26),
    runBody degF (dgb 24) (fagCrIdx + 1),
    runBody degF (dgb 25) (fagCmIdx + 1),
    itSRunF (fagItIdx + 2) (fagItIdx + 29) (dgb 27),
    runBody degF (dgb 27) (fagItIdx + 32),
    .nil, .nil,
    -- 30
    lcChildF degF (asb 50) (asb 100) (asb 7) (asb 120) (asb 8),
    .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil,
    -- 40: the root
    rootTopBody 0 (dgb 41) P₀.N₀ (.nat D),
    rootFreshBody 9 (dgb 0) 289 (.nat D)]

theorem length_degSingles (jr D : ℕ) : (degSingles jr D).length = 42 := rfl

/-- **The new functions**: the singles at `dgb 0`, then the blocks at `dgb 100` (the fold of `ρ`),
`dgb 110` (the map of the reset), `dgb 120` (the test of a quotient), `dgb 140` and `dgb 150` (the
maps of the two tails), `dgb 160` (`log₂`) and `dgb 170` (the map of the children of the round). -/
noncomputable def degFuns (jr E D : ℕ) : List Expr :=
  asmPad 100 (degSingles jr D) ++ asmPad 10 (foldlFuns (dgb 100) (dgb 15)) ++
    asmPad 10 (mapFuns (dgb 110) (dgb 16)) ++ asmPad 20 (degTestFuns (dgb 120) E) ++
    asmPad 10 (mapFuns (dgb 140) (dgb 13)) ++ asmPad 10 (mapFuns (dgb 150) (dgb 14)) ++
    asmPad 10 (log2Funs (dgb 160)) ++ mapFuns (dgb 170) (dgb 30)

/-- The index of the recognition primitive. -/
noncomputable def degJr : ℕ := asmPrimBase + cExt.length

/-- **The program of the degree algorithm**, for the recognition `h`, the exponent `E` of the test
and the degree `D`. -/
noncomputable abbrev degProg (h : JohnsonRecognition) (E D : ℕ) : Program :=
  asmProg GI.Proved.pointwiseStab GI.Proved.membership GI.Proved.preimage
    GI.Proved.normalizedFactor (cExt ++ [recognitionPrim h]) gsGen cRow
    (asmPad 2000000 cAgg ++ degFuns degJr E D)

variable {h : JohnsonRecognition} {E D : ℕ}

/-- **The final program is a prefix of `degProg`.** -/
theorem cProg_sub_degProg : (cProg mainGObjF fc11SojF).Sub (degProg h E D) := by
  rw [cProg_eq]
  refine ⟨⟨List.replicate (2000000 - cAgg.length) .nil ++ degFuns degJr E D, ?_⟩,
    ⟨[recognitionPrim h], ?_⟩⟩
  · simp only [degProg, asmProg, asmPad, List.append_assoc]
  · simp only [degProg, asmProg, List.append_assoc]

/-! ### Where the functions sit -/

theorem cFlcFits : FlcFits (tmRiRecF flcRecIdx 14 8 1 mainGObjF)
    (tmGLPLabF (tmGLNeConc (flcLabIdx + 1) flSupIdx)) tmJFinF :=
  ⟨tmRi_recF_fits mainGObjF_fits, tmGLPLabF_fits items6_neF_room, tmJFinF_fits⟩

theorem dp_hasAt_gen : (degProg h E D).HasAt asmGenBase gsGen :=
  asmProg_hasAt_gen (by rw [length_gsGen]; unfold asmSlot; omega)

theorem dp_hasAt_agg' : (degProg h E D).HasAt asmAggBase (asmPad 2000000 cAgg ++ degFuns degJr E D) :=
  asmProg_hasAt_agg (by rw [length_gsGen]; unfold asmSlot; omega) (fag_row_le cFlcFits)

/-- The list of the round of the general algorithm sits at `asmAggBase`. -/
theorem dp_hasAt_agg : (degProg h E D).HasAt asmAggBase cAgg := dp_hasAt_agg'.left.left

/-- The new functions sit at `dgb 0`. -/
theorem dp_hasAt_deg : (degProg h E D).HasAt (dgb 0) (degFuns degJr E D) := by
  have h2 := dp_hasAt_agg' (h := h) (E := E) (D := D)
  have := h2.right
  rwa [length_asmPad length_cAgg] at this

theorem dg_blk {gs : List Expr} (i : ℕ) (hg : ((degFuns degJr E D).drop i).take gs.length = gs) :
    (degProg h E D).HasAt (dgb i) gs := by
  have := (dp_hasAt_deg (h := h)).block i hg
  simpa [dgb, Nat.add_assoc] using this

theorem dg_one {e : Expr} (i : ℕ) (hg : ((degFuns degJr E D).drop i).take 1 = [e]) :
    (degProg h E D).funs[dgb i]? = some e :=
  (dg_blk (gs := [e]) i hg).single

theorem dp_prim_recog : (degProg h E D).prims[degJr]? = some (recognitionPrim h) := by
  rw [degJr, asmProg_prim_extra]
  simp

end GI.Degree
