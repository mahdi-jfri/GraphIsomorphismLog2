module

public import Workspace.Impl.GMPReps
public import Workspace.Impl.PolyBd

@[expose] public section

namespace GI.Impl

open GI.Lang GI.Cited

/-- Coset enumeration costs a fixed polynomial in the input weight and
the number of cosets. This includes the cost of all membership tests. -/
theorem gmpRepsCost_poly (hm : Membership) :
    PBU (fun q W _ => gmpRepsCost hm W q) := by
  have hY : PBU (fun _ W _ => gmpRepsWeight W) :=
    PBU.smul 100 ((PBU.W.addc 1).pow 4)
  have hL : PBU (fun q _ _ => q + 2) := PBU.k.addc 2
  have hp : PBU (fun _ W _ => tmRpPredC hm (gmpRepsWeight W)) :=
    (hY.smul (10 ^ 6)).add
      ((((hY.smul 20).addc 2).pow (membershipPrim hm).k).smul (membershipPrim hm).c)
  have ht : PBU (fun q W _ => tmRpTestC hm (gmpRepsWeight W) (q + 2)) :=
    (hL.mul hp).add (((hL.mul hL).mul hY).smul (10 ^ 8))
  have hr : PBU (fun q W _ => tmRpRoundC hm (gmpRepsWeight W) (q + 2)) :=
    (hY.mul ht).add ((hY.mul (hL.mul hY)).smul (10 ^ 7))
  have hw := PBU.smul tmRpWK (((hY.add PBU.k).add ((hL.mul hY).smul 10)).addc 10)
  exact ((PBU.k.addc 1).mul (hr.add hw)).add ((hL.mul hY).smul 10000)

/-- A two-variable form convenient for the chief-factor degree bound. -/
theorem gmpRepsCost_le (hm : Membership) :
    ∃ C D : ℕ, ∀ W q : ℕ, gmpRepsCost hm W q ≤ C * (W + q + 2) ^ D := by
  obtain ⟨C, D, h⟩ := gmpRepsCost_poly hm
  exact ⟨C, D, fun W q => by simpa only [PB, Nat.add_zero] using h q W 0⟩

end GI.Impl
