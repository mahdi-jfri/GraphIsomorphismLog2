import Workspace.Impl.TermRecInd
import Workspace.Impl.LayoutAsm

/-!
# T5, the layout of the A.20 recursion with its glue program

The recursion `tmRiFuns` calls a glue program for one profile class (`TermGlueObjSpec`). This
file puts both in one list, for the slot that the final assembly keeps for the recursion:

* `tmRiRecF b jsci jder jmem gObjF` is `tmRiFuns` at `b`, padded to `tmRiGlueOff = 1000`
  functions, followed by the glue program `gObjF`. So the glue program sits at `b + 1000`.
* `tmRi_recSpecAt`: if a program holds this list at `b`, the three cited primitives at
  `jsci, jder, jmem`, and the glue meets `TermGlueObjSpec` at `b + 1000`, then the program
  meets `TermRecSpec` at `b`. The constants `K, D` depend only on the cited algorithms and on
  the glue's constants.
-/

namespace GI.Impl

open GI.Lang
open GI.Cited (SolvableCosetIntersection DerivedSubgroup Membership)

/-- The offset of the glue program inside the list of the recursion. -/
def tmRiGlueOff : ℕ := 1000

/-- **The list of the recursion**: `tmRiFuns` at `b`, padded to `tmRiGlueOff` functions, then the
glue program `gObjF`, which the recursion calls at `b + tmRiGlueOff`. -/
def tmRiRecF (b jsci jder jmem : ℕ) (gObjF : List Expr) : List Expr :=
  asmPad tmRiGlueOff (tmRiFuns b jsci jder jmem (b + tmRiGlueOff)) ++ gObjF

theorem tmRi_funs_le (b jsci jder jmem gObj : ℕ) :
    (tmRiFuns b jsci jder jmem gObj).length ≤ tmRiGlueOff := by
  rw [length_tmRiFuns]; unfold tmRiGlueOff; omega

theorem length_tmRiRecF (b jsci jder jmem : ℕ) (gObjF : List Expr) :
    (tmRiRecF b jsci jder jmem gObjF).length = tmRiGlueOff + gObjF.length := by
  simp only [tmRiRecF, List.length_append, length_asmPad (tmRi_funs_le _ _ _ _ _)]

/-- The two parts of the list of the recursion. -/
theorem tmRi_recF_hasAt {P : Program} {b jsci jder jmem : ℕ} {gObjF : List Expr}
    (h : P.HasAt b (tmRiRecF b jsci jder jmem gObjF)) :
    P.HasAt b (tmRiFuns b jsci jder jmem (b + tmRiGlueOff)) ∧
      P.HasAt (b + tmRiGlueOff) gObjF := by
  refine ⟨(show P.HasAt b (tmRiFuns b jsci jder jmem (b + tmRiGlueOff) ++ _) from h.left).left,
    ?_⟩
  simpa [length_asmPad (tmRi_funs_le _ _ _ _ _)] using h.right

/-- **`TermRecSpec` at `b` from the list `tmRiRecF` at `b`**, the primitives, and the glue spec at
`b + tmRiGlueOff`. -/
theorem tmRi_recSpecAt (hsci : SolvableCosetIntersection) (hder : DerivedSubgroup)
    (hmem : Membership) (Kg Dg : ℕ) :
    ∃ K D : ℕ, ∀ {P : Program} {b jsci jder jmem : ℕ} {gObjF : List Expr},
      P.HasAt b (tmRiRecF b jsci jder jmem gObjF) →
      P.prims[jsci]? = some (solvableCosetIntersectionPrim hsci) →
      P.prims[jder]? = some (derivedSubgroupPrim hder) →
      P.prims[jmem]? = some (membershipPrim hmem) →
      Iface.TermGlueObjSpec P Kg Dg (b + tmRiGlueOff) →
      Iface.TermRecSpec P K D b := by
  obtain ⟨K, D, h⟩ := tmRi_termRecSpec hsci hder hmem Kg Dg
  exact ⟨K, D, fun hf hs hd hm hg => h ⟨(tmRi_recF_hasAt hf).1, hs, hd, hm⟩ hg⟩

end GI.Impl
