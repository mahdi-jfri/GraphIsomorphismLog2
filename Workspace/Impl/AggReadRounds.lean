module

public import Workspace.Impl.AggSpecDefs
public import Workspace.Paper.MainTheoremCarrier
public import Workspace.Assembly.AggParams

@[expose] public section

/-!
# The reading: the start set of rounds is nonempty

The certificate phase starts from the set `asRounds L` of all rounds of the supplied labels
(`CpHand`, `Workspace/Impl/AggCertHand.lean`), and its hand-over asks that this set is nonempty.
The paper builds one round from the labels: the data of Section 7 (`Aggregation.ofLabels`,
`Workspace/Paper/MainTheoremCarrier.lean`). It needs the hierarchy invariant, the size and
transitivity conditions of a `GiantStep` call, `q > q₀`, the parameter conditions
`Params.Aggregates` and three cited results. A call of the round (`AsCall`) gives all of these
except the cited results; `Params.Aggregates P₀` is `P₀_aggregates`, which takes one more cited
result. The round built in this way has the selected interval and the constituent of the labels,
so it lies in `asRounds L` (`rd_asRounds_nonempty`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang

variable {I : Iface} {Pg : Program} {F : Funs} {Ω C : Type} {k : ℕ}

/-- **The start set of rounds is nonempty.** The round of `Aggregation.ofLabels` (Section 7) is
built from the facts of the call `AsCall` and the cited results; it has the selected interval
and the constituent of the labels. -/
theorem rd_asRounds_nonempty
    (hK : GI.Cited.KaryCoherentRefinement)
    (hD : GI.Cited.DesignLemma) {e : Ω ≃ Fin k} {c : C → ℕ} {S : State Ω C} {sv lv : GI.Cited.Val}
    {L : SuppliedLabels S} (h : AsCall I Pg F e c S sv lv L) : (asRounds L).Nonempty := by
  haveI : Finite Ω := Finite.of_equiv _ e.symm
  obtain ⟨hN, hsN, htr, -, hinv, -⟩ := h.good
  exact ⟨Aggregation.ofLabels L hinv hN hsN htr h.q₀ P₀_aggregates hK hD h.hnot,
    rfl, rfl⟩

end GI.Impl
