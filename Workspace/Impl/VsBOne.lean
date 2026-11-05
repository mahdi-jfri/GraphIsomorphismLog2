module

public import Workspace.Impl.VsBFld

@[expose] public section

/-!
# The bases `D = 0` and `D = 1`

* `vsB_ans_D0`: when `D = 0` the answer is `(1, hs)`.
* `vsB_orb_D1`: when `D = 1` the orbit of `0` has at most `p` points, so the small orbit
  program `vsBOrb_spec` applies with `B = p`.
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- With no local coordinates, every element of `H` is a solution. -/
theorem vsB_ans_D0 {s : VsQSt I} (hs : VsQStOK s) (hD : vsQD s = 0) :
    VsQAnsOK hs.prob (some (1, s.hs)) := by
  have hsub : Subsingleton (Fin (vsQD s) → ZMod I.p) := by
    rw [hD]; infer_instance
  exact vsB0_ans_all hs (fun _ _ => Subsingleton.elim _ _) (Subsingleton.elim _ _)

/-- With one local coordinate, every orbit has at most `p` points. -/
theorem vsB_orb_D1 {s : VsQSt I} (hD : vsQD s = 1) :
    (vsQOrb (vsBAlpha s) (1 :: s.hs) 0).ncard ≤ I.p := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  calc (vsQOrb (vsBAlpha s) (1 :: s.hs) 0).ncard ≤ (Set.univ : Set (Fin (vsQD s) → ZMod I.p)).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _)
    _ = I.p := by
        rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin, hD,
          pow_one]

end GI.Impl
