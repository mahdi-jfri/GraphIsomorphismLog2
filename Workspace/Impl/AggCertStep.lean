module

public import Workspace.Impl.AggCache
public import Workspace.Impl.AggWin

@[expose] public section

/-!
# The certificate phase as a script with choices: one step

The script runner with choices (`Iface.run_specC`) asks of the step function, at a program state
standing for a set `Ss` of candidate scripts, either the result of a finished candidate or one
call that a nonempty part of the candidates asks, with the continuations of that part as the next
set (`StepPostC`). In the certificate phase the candidates differ only in the coset
representatives `R : CosetRepFn S.dom`. This file gives the form of the candidate sets and the
one step of the phase at the level of scripts; a program meets it by computing the values that
the step names.

* `Cands rec`: the representatives that agree with a record `rec` of the program's choices. It is
  nonempty for a good cache (`CacheOK.cands_nonempty`) and shrinks as the record grows.
* `stepPostC_ask`, `stepPostC_done`: `StepPostC` for a candidate set `F '' C` when every
  candidate in `C` asks the same call (or all are finished with the same result).
* `cert_roundStart`: at the start of a round with a nonempty increment, every candidate that
  agrees with a record holding the representatives `l` of `(A, ker)` continues with the window
  calls of `l` (`winCont`); so all of them ask the window call of the first element of `l`
  (`winCont_cons`).

The rest of the phase moves through the normal forms of `Workspace/Impl/ScriptCont.lean`:
`epFrom_succ_bind_empty` (a round with an empty increment), `winCont_cons` (the next window
call), `winCont_nil` (the new stage, `pairGens_newStage`), `certFrom_cons` and `certFrom_nil`
(the next string and the next test set).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open GI.Cited (Val)
open scoped Pointwise

/-! ### Candidate sets -/

section Cands

variable {V : Type}

/-- The coset representatives that agree with a record of choices. -/
def Cands (rec : List ((Subgroup (Perm V) × Subgroup (Perm V)) × List (Perm V))) :
    Set (CosetRepFn V) :=
  {R | ∀ p ∈ rec, R.reps p.1.1 p.1.2 = p.2}

/-- A consistent and allowed record has a candidate. -/
theorem cands_nonempty (R₀ : CosetRepFn V)
    {rec : List ((Subgroup (Perm V) × Subgroup (Perm V)) × List (Perm V))}
    (hok : RecordOK rec) (hQ : ∀ p ∈ rec, RepsOK p.1 p.2) : (Cands rec).Nonempty :=
  ⟨CosetRepFn.ofRecord R₀ rec hok hQ, fun _ hp => CosetRepFn.ofRecord_reps R₀ rec hok hQ hp⟩

/-- A longer record has fewer candidates. -/
theorem cands_cons {rec : List ((Subgroup (Perm V) × Subgroup (Perm V)) × List (Perm V))}
    (p : (Subgroup (Perm V) × Subgroup (Perm V)) × List (Perm V)) :
    Cands (p :: rec) ⊆ Cands rec := fun _ hR q hq => hR q (List.mem_cons_of_mem _ hq)

/-- A candidate of a record gives the recorded representatives. -/
theorem cands_reps {rec : List ((Subgroup (Perm V) × Subgroup (Perm V)) × List (Perm V))}
    {R : CosetRepFn V} (hR : R ∈ Cands rec) {A N : Subgroup (Perm V)} {l : List (Perm V)}
    (h : ((A, N), l) ∈ rec) : R.reps A N = l :=
  hR _ h

end Cands

theorem CacheOK.cands_nonempty {k : ℕ} {Ω C : Type} {e : Ω ≃ Fin k} {S : State Ω C}
    {L : GiantLabels S} {c : List (CacheEntry k L.q)}
    {rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))}
    (hc : CacheOK e S L c rec) (R₀ : CosetRepFn S.dom) : (Cands rec).Nonempty :=
  _root_.GI.Impl.cands_nonempty R₀ hc.2.1 hc.2.2

/-! ### One step for a family of candidates -/

section Step

variable {μ : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ} {α : Type} {Out : α → Val → Prop}
  {Rep : Val → Set (Script α) → ℕ → Prop}

/-- **One call for a family of candidates.** If every candidate `F R` (`R ∈ C`, a nonempty set)
asks `Continue` on the same state `T` with continuation `kf R`, then the call
`[1, 1, arg, kst]` with a canonical `arg` of `T` meets `StepPostC`, provided every canonical
answer `u` gives a program state of the continuations `kf R T.answer`. -/
theorem stepPostC_ask {ι : Type} {C : Set ι} (hC : C.Nonempty) (F : ι → Script α)
    {Ω' C' : Type} (T : State Ω' C') (kf : ι → Set (Perm Ω') → Script α)
    (hF : ∀ R ∈ C, F R = Script.ask .cont T (kf R)) {f : ℕ} (hf : 0 < f) {k' : ℕ}
    (e' : Ω' ≃ Fin k') (c' : C' → ℕ) (hc' : Function.Injective c') {arg kst : Val}
    (hcan : Canon e' c' arg T) (hg : Good P₀ .cont T) (hlt : MLt (measure P₀ .cont T) μ)
    (hrep : ∀ u, AnsC e' u T.answer → Rep (.list [kst, u]) ((fun R => kf R T.answer) '' C) (f - 1)) :
    Iface.StepPostC μ Out Rep (F '' C) f (.list [.nat 1, .nat (modeCode .cont), arg, kst]) := by
  refine Or.inr ⟨hf, .cont, Ω', C', T, k', e', c', arg, kst, kf '' C, hc', Or.inr rfl, rfl, hcan,
    hg, hlt, hC.image _, ?_, fun u hu => ?_⟩
  · rintro _ ⟨R, hR, rfl⟩
    exact ⟨R, hR, hF R hR⟩
  · rw [Set.image_image]
    exact hrep u hu

/-- **A finished family.** If some candidate is finished with result `a`, the output
`[0, out]` with `Out a out` meets `StepPostC`. -/
theorem stepPostC_done {ι : Type} {C : Set ι} (F : ι → Script α) {R : ι} (hR : R ∈ C) {a : α}
    (hF : F R = Script.done a) {f : ℕ} {out : Val} (hout : Out a out) :
    Iface.StepPostC μ Out Rep (F '' C) f (.list [.nat 0, out]) :=
  Or.inl ⟨a, out, rfl, hout, ⟨R, hR, hF⟩⟩

end Step

/-! ### The start of a round -/

section Round

variable {Ω C C₀ : Type} [DecidableEq Ω] (S : State Ω C) [Fintype S.dom]
  {Q : Type} [Group Q] {P' : Subgroup (Perm S.dom)} (phi : P' →* Q) (z : S.dom → C₀)

/-- **The start of a round, for the candidates of a record.** If the increment of the stage
`AW` is nonempty and the record holds the representatives `l` of `(A, ker)`, every candidate of
the record starts the round with the window calls of `l`. -/
theorem cert_roundStart {β : Type}
    {rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))}
    {R : CosetRepFn S.dom} (hR : R ∈ Cands rec) (AW : Subgroup (Perm S.dom) × Finset S.dom)
    (m : ℕ) (K : Subgroup (Perm S.dom) × Finset S.dom → Script β)
    (h : increment phi AW.1 AW.2 ≠ ∅)
    (hV : GI.Algorithm.Invariant (kernelIn phi AW.1) (increment phi AW.1 AW.2 : Set S.dom))
    {l : List (Perm S.dom)} (hl : ((AW.1, kernelIn phi AW.1), l) ∈ rec) :
    (epFrom S R phi z AW (m + 1)).bind K =
      winCont S R phi z AW.1 AW.2 (increment phi AW.1 AW.2) hV l [] m K := by
  rw [epFrom_succ_bind_window S R phi z AW m K h hV, cands_reps hR hl]

/-- **The first window call of a round.** -/
theorem cert_firstCall {β : Type}
    {rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))}
    {R : CosetRepFn S.dom} (hR : R ∈ Cands rec) (AW : Subgroup (Perm S.dom) × Finset S.dom)
    (m : ℕ) (K : Subgroup (Perm S.dom) × Finset S.dom → Script β)
    (h : increment phi AW.1 AW.2 ≠ ∅)
    (hV : GI.Algorithm.Invariant (kernelIn phi AW.1) (increment phi AW.1 AW.2 : Set S.dom))
    {τ : Perm S.dom} {τs : List (Perm S.dom)}
    (hl : ((AW.1, kernelIn phi AW.1), τ :: τs) ∈ rec) :
    (epFrom S R phi z AW (m + 1)).bind K =
      Script.ask .cont (windowCall S (kernelIn phi AW.1) (increment phi AW.1 AW.2) hV z τ)
        fun B => winCont S R phi z AW.1 AW.2 (increment phi AW.1 AW.2) hV τs [winVal S τ B] m K := by
  rw [cert_roundStart S phi z hR AW m K h hV hl, winCont_cons]
  rfl

end Round

end GI.Impl
