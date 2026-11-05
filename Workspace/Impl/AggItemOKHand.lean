module

public import Workspace.Impl.AggItemStepSpec
public import Workspace.Impl.AggCmpPhase

@[expose] public section

/-!
# The hand-over to the items with length bounds

The items need the lengths of the graph pairs `ps, fx, fy` of the hand-over to be at most
`(k + q)²` (`ItHandB`), so that the start state weighs at most a polynomial in the input weight.
The comparison phase hands them over with these bounds (`CmHand` has them), so `asCompOK_of_run`
holds as well with `ItHandB` in place of `ItHand`: `itS_asCompOK_of_runB`.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)

variable {Ω C : Type} {k : ℕ}

/-- **`AsCompOK` from the comparison program, with `ItHandB`.** As `asCompOK_of_run`, with the
hand-over relation `ItHandB` after the phase. -/
theorem itS_asCompOK_of_runB (I : Iface) (Pg : Program) (F : Funs) (H : AsHand) (X : ℕ → ℕ)
    (fm : ℕ)
    (hc : ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C)
      (L : SuppliedLabels S) Cs st, H.comp e c S L Cs st → CmHand e c S L Cs st)
    (hi : ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C)
      (L : SuppliedLabels S) Cs st, ItHandB e c S L Cs st → H.items e c S L Cs st)
    (hrun : CmRunOK I Pg F X fm) : AsCompOK I Pg F H X fm := by
  intro Ω C k e c S sv' lv L hcall Cs st hst
  obtain ⟨hsub, Ag₀, hAg₀, hcl, sv, ps, fx, fy, logs, rfl, hcan, hps, hfx, hfy, hl1, hl2, hl3,
    hlogs⟩ := hc e c S L Cs st hst
  refine (hrun e c S sv' lv L hcall Cs Ag₀ hAg₀ hsub hcl sv ps fx fy logs hcan hps hfx hfy hl1 hl2
    hl3 hlogs).mono ?_
  rintro w cost ⟨O, Ag, hAg, a, ex, rfl, hcost, hw⟩
  have hCs := hAg.1
  obtain ⟨-, hcert, htests, -⟩ := hAg
  refine ⟨Ag, hCs, a, ex, hi e c S L _ _ ⟨fun Ag' h => hsub h.1, Ag, ⟨hCs, rfl⟩,
    fun Ag' h' h1 h2 => ⟨hcl Ag' h' (h1.trans hcert), h2⟩, sv, ps, fx, fy, O, ?_, hcan, hps, ?_, ?_,
    hl1, hl2, hl3⟩, hcost, hw⟩
  · rw [← htests]
    exact cm_out_eq ex sv ps fx fy
  · rwa [cm_certLift_eq (hsub hCs) (hsub hAg₀)]
  · rwa [cm_certLift_eq (hsub hCs) (hsub hAg₀)]

end GI.Impl
