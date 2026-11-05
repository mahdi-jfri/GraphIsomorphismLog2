module

public import Workspace.Impl.AggItemCiPair

@[expose] public section

/-!
# A trampoline for the init program of `sojItem`

The pair part needs its init program at a fixed index (offset 0 of the pair room), and the init
program of `sojItem` sits inside its own sub-list. The trampoline `fc10TrF f` at offset 0 only
calls `f` on its input. A call adds the cost of reading the input and the weight of the result,
so the contract `ItciSojSpec` moves to the trampoline with a larger bound `fc10TrX Xs`
(`fc10_sojSpec_tr`). The start and step fields do not change, but the larger bound also raises
the call budget `f`, so the item-state relation becomes `itciR R` ("at most `f` more calls").
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv
open GI.Cited (Val)

variable {Ω C : Type} {k : ℕ}

/-- **The trampoline**: call `f` on the input. -/
def fc10TrF (f : ℕ) : Expr := .call f (.var 0)

/-- The bound of `sojItem` behind the trampoline. -/
def fc10TrX (Xs : ℕ → ℕ) (W : ℕ) : ℕ := itSVB W + 2 * Xs W + 2

/-- **One context**: the obligations at `fi'` give those at the trampoline `fi`, when the kept
input weighs at most `V`. -/
theorem fc10_sojAt_tr {Pg : Program} {R : ItCfIRel} {fi fi' fs fk : ℕ} {e : Ω ≃ Fin k}
    {c : C → ℕ} {S : State Ω C} {L : SuppliedLabels S} {K : ItSCtx k S L} {B V : ℕ}
    (hf : Pg.funs[fi]? = some (fc10TrF fi')) (hv : K.v.wt ≤ V)
    (h : ItciSojAt Pg R fi' fs fk e c S L K B) :
    ItciSojAt Pg (itciR R) fi fs fk e c S L K (V + 2 * B + 2) := by
  have hB : B ≤ V + 2 * B + 2 := by omega
  refine ⟨?_, h.ne, fun w E hw => (h.wtK w E hw).trans hB, ?_, ?_, ?_, ?_⟩
  · refine FunAll.intro hf (EvalAll.call_funAll
      (Ra := fun v ca => v = K.v ∧ ca = K.v.wt + 1) (.var (by simp) ⟨rfl, rfl⟩) ?_)
    rintro v ca ⟨rfl, rfl⟩
    refine h.init.mono fun w cb ⟨E, hE, hcb⟩ => ⟨E, hE, ?_⟩
    have := h.wtK w E hE
    omega
  · intro b X x₀ Y y₀ w E ho hq hK
    exact (h.start b X x₀ Y y₀ w E ho hq hK).mono fun w' c' ⟨hc', hp⟩ =>
      ⟨hc'.trans hB, itci_post_mono hp hB hB⟩
  · rintro b oX oY ist E sb f ⟨f', -, hR⟩
    exact (h.wtR b oX oY ist E sb f' hR).trans hB
  · rintro b oX oY ist E sb f ⟨f', hf', hR⟩
    exact (h.step b oX oY ist E sb f' hR).mono fun w' c' ⟨hc', hp⟩ =>
      ⟨hc'.trans hB, itci_post_mono hp hf' hB⟩
  · intro b oX oY ho
    obtain ⟨h1, h2⟩ := h.objW b oX oY ho
    exact ⟨fun X x₀ hX => (h1 X x₀ hX).trans hB, fun Y y₀ hY => (h2 Y y₀ hY).trans hB⟩

/-- **The contract of `sojItem` behind the trampoline**: `ItciSojSpec` at `fi'` gives it at the
trampoline `fi` with the bound `fc10TrX Xs`. The kept input weighs at most `itSVB` (`itS_vW`). -/
theorem fc10_sojSpec_tr (I : Iface) {Pg : Program} {F : Funs} {fi fi' fs fk : ℕ} {Xs : ℕ → ℕ}
    (hf : Pg.funs[fi]? = some (fc10TrF fi')) (h : ItciSojSpec I Pg F fi' fs fk Xs) :
    ItciSojSpec I Pg F fi fs fk (fc10TrX Xs) := by
  obtain ⟨R, hR⟩ := h
  exact ⟨itciR R, fun {Ω C k} e c S sv lv L hc K hK hcase =>
    fc10_sojAt_tr hf (itS_vW I Pg F hc hK) (hR e c S sv lv L hc K hK hcase)⟩

/-- The bound behind the trampoline is polynomial when `Xs` is. -/
theorem fc10TrX_pbu {Xs : ℕ → ℕ} (hs : PBU fun _ W _ => Xs W) :
    PBU fun _ W _ => fc10TrX Xs W := by
  have hp : PBU fun _ W _ => itSVB W := by
    simp only [itSVB, cmOutB, cmPb, cmNb]
    norm_poly
  exact PBU.addc (PBU.add hp (PBU.smul 2 hs)) 2

end GI.Impl
