module

public import Workspace.Impl.AggItemCiSojQueryWt

@[expose] public section

/-! # Paid raw graph-pair bytes in a rectangle representation -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang
open GI.Cited (Val)

/-- The graph-pair generator bytes are the first stored representation field. -/
theorem itcs_frame_pairs_weight {Ω C : Type} {k : ℕ} {e : Ω ≃ Fin k}
    {S : State Ω C} {L : GiantLabels S} (F : itcsQFrame e S L) {n : ℕ}
    (h : (rcRepVal e F.rep F.hs).wt≤n) : (Val.list (F.hs.map pairV)).wt≤n :=
  (st_wt_mem (List.mem_cons_self ..)).trans h

end GI.Impl
