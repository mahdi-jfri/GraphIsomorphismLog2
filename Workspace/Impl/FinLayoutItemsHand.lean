module

public import Workspace.Impl.AggCmpRun
public import Workspace.Impl.AggItemOKHand

@[expose] public section

/-!
# The comparison phase hands over `ItHandB`

The items need the lengths of the graph pairs `ps, fx, fy` of the hand-over to be bounded
(`ItHandB`, `AggItemStepSpec.lean`). So the hand-over `asHandImpl` of the final program uses
`ItHandB` for the items. `cm_asCompOK` (`AggCmpRun.lean`) asks that `ItHand` imply the relation
of the items, which is false for this hand-over. `fitm_cmAsCompOKB` is the same result for a hand-over whose
relation of the items contains `ItHandB`: it is `cm_runOK` followed by `itS_asCompOK_of_runB`
in place of `asCompOK_of_run`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val PointwiseStab Preimage Membership)

/-- **`AsCompOK` for the comparison program**, for any hand-over whose relation `comp` gives
`CmHand` and whose relation `items` contains `ItHandB`. -/
theorem fitm_cmAsCompOKB (I : Iface) (Pg : Program) (F : Funs) (hst : PointwiseStab)
    (hpre : Preimage) (hm : Membership) (H : AsHand)
    {fm b d stp tb jm jp : ℕ} (hset : CmSetAt Pg F hst hm fm b d stp tb jm jp)
    (hc : ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C)
      (L : SuppliedLabels S) Cs st, H.comp e c S L Cs st → CmHand e c S L Cs st)
    (hi : ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C)
      (L : SuppliedLabels S) Cs st, ItHandB e c S L Cs st → H.items e c S L Cs st) :
    AsCompOK I Pg F H (cmRunX hst hpre hm) fm :=
  itS_asCompOK_of_runB I Pg F H _ fm hc hi (cm_runOK I Pg F hst hpre hm hset)

end GI.Impl
