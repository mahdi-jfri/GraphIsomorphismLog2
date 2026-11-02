import Workspace.Impl.FinLayoutC23

/-! # Cases 2b/3 in their final slot

The fixed block has 32 functions. The object stage starts at offset 1000
and the pair stage at offset 100000. Padding preserves these indices.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang
open GI.Cited (KaryRefinement)

/-- The list installed at `fitC23Idx`. -/
noncomputable def fc23F (cfObF cfPrF : List Expr) : List Expr :=
  asmPad 1000 (fc23Conc fitC23Idx fagItIdx) ++ (asmPad 99000 cfObF ++ cfPrF)

/-- The two remaining stages fit in the Case 2b/3 slot. -/
theorem fc23_fits {cfObF cfPrF : List Expr}
    (ho : cfObF.length ≤ 99000) (hp : cfPrF.length ≤ 100000) :
    (fc23F cfObF cfPrF).length ≤ fitRpOff - fitC23Off := by
  have hc : (fc23Conc fitC23Idx fagItIdx).length ≤ 1000 := by rw [fc23_length]; decide
  simp only [fc23F, List.length_append, length_asmPad hc, length_asmPad ho]
  change 1000 + (99000 + cfPrF.length) ≤ 200000
  exact Nat.add_le_add_left (Nat.add_le_add_left hp 99000) 1000

/-- Each stage keeps its advertised base after padding. -/
theorem fc23_parts {P : Program} {cfObF cfPrF : List Expr}
    (ho : cfObF.length ≤ 99000) (h : P.HasAt fitC23Idx (fc23F cfObF cfPrF)) :
    fc23At P fitC23Idx fagItIdx ∧ P.HasAt (fitC23Idx + 1000) cfObF ∧
      P.HasAt (fitC23Idx + 100000) cfPrF := by
  have hc : (fc23Conc fitC23Idx fagItIdx).length ≤ 1000 := by rw [fc23_length]; decide
  unfold fc23F at h
  have ht : P.HasAt (fitC23Idx + 1000) (asmPad 99000 cfObF ++ cfPrF) := by
    simpa only [length_asmPad hc] using h.right
  have hp : P.HasAt (fitC23Idx + 100000) cfPrF := by
    simpa only [length_asmPad ho, Nat.add_assoc] using ht.right
  exact ⟨fc23_at h.left.left, ht.left.left, hp⟩

/-- The concrete Case 2b/3 list meets the case contract for every interface. -/
theorem fc23_caseOK_final (I : Iface) {P : Program} {F : Funs}
    {cfObF cfPrF : List Expr} (ho : cfObF.length ≤ 99000)
    (h : P.HasAt fitC23Idx (fc23F cfObF cfPrF)) (hA : FitAt P fagItIdx)
    (h2 : KaryRefinement 2) (hj : P.prims[20]? = some (karyRefinementPrim h2))
    {Co Do : ℕ} {Xp : ℕ → ℕ}
    (hobj : ItCfObjSpec P (fitC23Idx + 1000) (fitC23Idx + 1001) (fitC23Idx + 1002) Co Do)
    (hpair : ItciPairSpec I P F (fitC23Idx + 100000) (fitC23Idx + 100001)
      (fitC23Idx + 100002) Xp) :
    ItSCaseOK I P F (fun a => a = .twoB ∨ a = .three) fitC23Idx (fitC23Idx + 1)
      (fc23X h2 Co Do Xp) :=
  fc23_caseOK I (fc23_parts ho h).1 hA h2 hj hobj hpair

end GI.Impl
