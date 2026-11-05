module

public import Workspace.Algorithm.Aggregation

@[expose] public section

/-!
# The rest of a script, after some of its calls

The script runner with choices (`Iface.run_specC`, `Workspace/Impl/ScriptRun.lean`) asks the
step function to say which script its program state stands for, at every point of the run. A
step of the certificate phase is in the middle of a nested script: inside the `j`-th window
call of a round of the endpoint loop for one string of one test set, followed by the rest of the
round's script. This file gives the normal forms of these remaining scripts and the equations
that move from one to the next.

* `scr_bind_assoc`, `scr_bind_done`: `Script.bind` is associative, with `done` as unit.
* `scr_seqList_cons`: running a list of scripts is running the first one, then the rest.
* `epStep`, `epFrom`: one round of Algorithm 2 with lifted calls, and `m` rounds from a stage.
  `endpointScriptLift_eq_epFrom`: the loop `endpointScriptLift` is `epFrom` from the first stage.
  So the rest of the loop after some rounds is `(epFrom AW m).bind K`, a right-nested form.
* `winCont`: inside a round, after the window calls of the first representatives, the rest is
  the window calls of the other representatives (`List.drop`), then the closure and the remaining
  rounds. `epFrom_succ_bind` and `winCont_cons` say how each form unfolds into its next call.
* `certPhase_bind`: the certificate phase, followed by any continuation, starts with the endpoint
  loop of the first string of the first test set.
-/

namespace GI.Impl

open GI.Algorithm GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open scoped Pointwise

/-! ### Binds -/

section Bind

variable {α β γ : Type}

theorem scr_done_bind (a : α) (f : α → Script β) : (Script.done a).bind f = f a := rfl

theorem scr_ask_bind {Ω' C' : Type} (m : Mode) (T : State Ω' C') (k : Set (Perm Ω') → Script α)
    (f : α → Script β) : (Script.ask m T k).bind f = Script.ask m T fun A => (k A).bind f := rfl

/-- **`bind` is associative.** -/
theorem scr_bind_assoc (s : Script α) (f : α → Script β) (g : β → Script γ) :
    (s.bind f).bind g = s.bind fun a => (f a).bind g := by
  induction s with
  | done a => rfl
  | ask m T k ih =>
    show Script.ask m T (fun A => ((k A).bind f).bind g) = Script.ask m T fun A => (k A).bind _
    congr 1
    funext A
    exact ih A

/-- `done` is a right unit of `bind`. -/
theorem scr_bind_done (s : Script α) : s.bind Script.done = s := by
  induction s with
  | done a => rfl
  | ask m T k ih =>
    show Script.ask m T (fun A => (k A).bind Script.done) = _
    congr 1
    funext A
    exact ih A

/-- Binds with pointwise equal continuations are equal. -/
theorem scr_bind_congr (s : Script α) {f g : α → Script β} (h : ∀ a, f a = g a) :
    s.bind f = s.bind g := by
  rw [funext h]

/-- **Running a list of scripts**: the first script, then the others. -/
theorem scr_seqList_cons (s : Script α) (l : List (Script α)) (f : List α → Script β) :
    (Script.seqList (s :: l)).bind f =
      s.bind fun a => (Script.seqList l).bind fun as => f (a :: as) := by
  show ((s.bind fun a => (Script.seqList l).bind fun as => Script.done (a :: as)).bind f) = _
  rw [scr_bind_assoc]
  refine scr_bind_congr s fun a => ?_
  rw [scr_bind_assoc]
  rfl

theorem scr_seqList_nil (f : List α → Script β) :
    (Script.seqList ([] : List (Script α))).bind f = f [] := rfl

/-- **A list of single calls**: running `call (W τ)` for every `τ` and collecting `val τ B`
asks `W τ` for the first `τ` and continues with the others. -/
theorem scr_seqList_calls {ι Ω' C' : Type} (W : ι → State Ω' C') (val : ι → Set (Perm Ω') → α)
    (τ : ι) (τs : List ι) (f : List α → Script β) :
    (Script.seqList ((τ :: τs).map fun τ =>
        (Script.call .cont (W τ)).bind fun B => Script.done (val τ B))).bind f =
      Script.ask .cont (W τ) fun B =>
        (Script.seqList (τs.map fun τ =>
          (Script.call .cont (W τ)).bind fun B => Script.done (val τ B))).bind
          fun as => f (val τ B :: as) := by
  rw [List.map_cons, scr_seqList_cons]
  rfl

end Bind

/-! ### The endpoint loop in right-nested form -/

section Endpoint

variable {Ω C C₀ : Type} [DecidableEq Ω] (S : State Ω C) [Fintype S.dom]
  {Q : Type} [Group Q] {P' : Subgroup (Perm S.dom)} (R : CosetRepFn S.dom) (phi : P' →* Q)
  (x : S.dom → C₀)

/-- **One round of Algorithm 2** with lifted calls, from the stage `AW = (A_t, W_t)`. -/
noncomputable def epStep (AW : Subgroup (Perm S.dom) × Finset S.dom) :
    Script (Subgroup (Perm S.dom) × Finset S.dom) := by
  classical
  exact if increment phi AW.1 AW.2 = ∅ then Script.done AW
    else (checkNewWindowLift S R AW.1 (kernelIn phi AW.1) (increment phi AW.1 AW.2) x).bind
      fun B => Script.done (Subgroup.closure B, AW.2 ∪ increment phi AW.1 AW.2)

theorem endpointScriptLift_succ (t : ℕ) :
    endpointScriptLift S R phi x (t + 1) = (endpointScriptLift S R phi x t).bind (epStep S R phi x) :=
  rfl

/-- **`m` rounds of Algorithm 2** from the stage `AW`, nested to the right. -/
noncomputable def epFrom (AW : Subgroup (Perm S.dom) × Finset S.dom) :
    ℕ → Script (Subgroup (Perm S.dom) × Finset S.dom)
  | 0 => Script.done AW
  | m + 1 => (epStep S R phi x AW).bind fun AW' => epFrom AW' m

theorem epFrom_zero (AW : Subgroup (Perm S.dom) × Finset S.dom) :
    epFrom S R phi x AW 0 = Script.done AW := rfl

theorem epFrom_succ (AW : Subgroup (Perm S.dom) × Finset S.dom) (m : ℕ) :
    epFrom S R phi x AW (m + 1) = (epStep S R phi x AW).bind fun AW' => epFrom S R phi x AW' m :=
  rfl

/-- One more round at the end is one more round at the front. -/
theorem epFrom_bind_step (m : ℕ) : ∀ AW : Subgroup (Perm S.dom) × Finset S.dom,
    (epFrom S R phi x AW m).bind (epStep S R phi x) = epFrom S R phi x AW (m + 1) := by
  induction m with
  | zero =>
    intro AW
    rw [epFrom_zero, scr_done_bind, epFrom_succ]
    simp only [epFrom_zero]
    exact (scr_bind_done _).symm
  | succ m ih =>
    intro AW
    rw [epFrom_succ, scr_bind_assoc, epFrom_succ]
    exact scr_bind_congr _ fun AW' => ih AW'

/-- **The endpoint loop is `epFrom` from the first stage** `(P', ∅)`. -/
theorem endpointScriptLift_eq_epFrom (t : ℕ) :
    endpointScriptLift S R phi x t = epFrom S R phi x (P', ∅) t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [endpointScriptLift_succ, ih, epFrom_bind_step]

/-- The window value of one representative `τ`: the translate of the restricted answer. -/
def winVal (τ : Perm S.dom) (B : Set (Perm Ω)) : Set (Perm S.dom) := τ • restrictAns S B

/-- **The rest of a round** after the window calls of some representatives: the window calls of
the representatives `τs` still to come, with the translated answers `acc` collected so far, then
the new stage and the other `m` rounds, then `K`. -/
noncomputable def winCont {β : Type} (A : Subgroup (Perm S.dom)) (W V : Finset S.dom)
    (hV : GI.Algorithm.Invariant (kernelIn phi A) (V : Set S.dom)) (τs : List (Perm S.dom))
    (acc : List (Set (Perm S.dom))) (m : ℕ)
    (K : Subgroup (Perm S.dom) × Finset S.dom → Script β) : Script β :=
  (Script.seqList (τs.map fun τ =>
      (Script.call .cont (windowCall S (kernelIn phi A) V hV x τ)).bind
        fun B => Script.done (winVal S τ B))).bind fun l =>
    (epFrom S R phi x (Subgroup.closure (⋃ s ∈ acc ++ l, s), W ∪ V) m).bind K

/-- **A round with an empty increment** changes nothing. -/
theorem epFrom_succ_bind_empty {β : Type} (AW : Subgroup (Perm S.dom) × Finset S.dom) (m : ℕ)
    (K : Subgroup (Perm S.dom) × Finset S.dom → Script β)
    (h : increment phi AW.1 AW.2 = ∅) :
    (epFrom S R phi x AW (m + 1)).bind K = (epFrom S R phi x AW m).bind K := by
  classical
  rw [epFrom_succ, scr_bind_assoc]
  unfold epStep
  simp only [h, if_true]
  rfl

/-- **A round with a nonempty increment** starts with the window calls of all representatives of
the kernel in `A`. -/
theorem epFrom_succ_bind_window {β : Type} (AW : Subgroup (Perm S.dom) × Finset S.dom) (m : ℕ)
    (K : Subgroup (Perm S.dom) × Finset S.dom → Script β)
    (h : increment phi AW.1 AW.2 ≠ ∅)
    (hV : GI.Algorithm.Invariant (kernelIn phi AW.1) (increment phi AW.1 AW.2 : Set S.dom)) :
    (epFrom S R phi x AW (m + 1)).bind K =
      winCont S R phi x AW.1 AW.2 (increment phi AW.1 AW.2) hV (R.reps AW.1 (kernelIn phi AW.1))
        [] m K := by
  classical
  rw [epFrom_succ, scr_bind_assoc]
  unfold epStep
  simp only [h, if_false]
  unfold checkNewWindowLift
  rw [dif_pos hV]
  unfold winCont
  simp only [scr_bind_assoc, scr_done_bind, List.nil_append]
  rfl

/-- **The next window call** of a round: the call on the first remaining representative; its
answer is added to the collected ones. -/
theorem winCont_cons {β : Type} (A : Subgroup (Perm S.dom)) (W V : Finset S.dom)
    (hV : GI.Algorithm.Invariant (kernelIn phi A) (V : Set S.dom)) (τ : Perm S.dom)
    (τs : List (Perm S.dom)) (acc : List (Set (Perm S.dom))) (m : ℕ)
    (K : Subgroup (Perm S.dom) × Finset S.dom → Script β) :
    winCont S R phi x A W V hV (τ :: τs) acc m K =
      Script.ask .cont (windowCall S (kernelIn phi A) V hV x τ) fun B =>
        winCont S R phi x A W V hV τs (acc ++ [winVal S τ B]) m K := by
  unfold winCont
  rw [scr_seqList_calls]
  congr 1
  funext B
  refine scr_bind_congr _ fun l => ?_
  simp

/-- **The end of a round**: after the last window call, the new stage is the closure of the
collected answers. -/
theorem winCont_nil {β : Type} (A : Subgroup (Perm S.dom)) (W V : Finset S.dom)
    (hV : GI.Algorithm.Invariant (kernelIn phi A) (V : Set S.dom))
    (acc : List (Set (Perm S.dom))) (m : ℕ)
    (K : Subgroup (Perm S.dom) × Finset S.dom → Script β) :
    winCont S R phi x A W V hV [] acc m K =
      (epFrom S R phi x (Subgroup.closure (⋃ s ∈ acc, s), W ∪ V) m).bind K := by
  unfold winCont
  simp only [List.map_nil, scr_seqList_nil, List.append_nil]

/-- **The rest of a round after `j` window calls**: the representatives after the first `j`
(`List.drop`). -/
theorem winCont_drop {β : Type} (A : Subgroup (Perm S.dom)) (W V : Finset S.dom)
    (hV : GI.Algorithm.Invariant (kernelIn phi A) (V : Set S.dom)) (τs : List (Perm S.dom))
    (acc : List (Set (Perm S.dom))) (m j : ℕ) (hj : j < τs.length)
    (K : Subgroup (Perm S.dom) × Finset S.dom → Script β) :
    winCont S R phi x A W V hV (τs.drop j) acc m K =
      Script.ask .cont (windowCall S (kernelIn phi A) V hV x (τs[j]'hj)) fun B =>
        winCont S R phi x A W V hV (τs.drop (j + 1)) (acc ++ [winVal S (τs[j]'hj) B]) m K := by
  rw [List.drop_eq_getElem_cons hj, winCont_cons]

end Endpoint

/-! ### The certificate phase -/

section Phase

variable {Ω C : Type} [DecidableEq Ω] (S : State Ω C) [Fintype S.dom] {q : ℕ}
  (πd : S.domGroup →* alternatingGroup (Fin q)) (R : CosetRepFn S.dom)

/-- **The certificate phase of the test sets `Ts`**, followed by `K`: the endpoint loops of `x`
and of `y` for the first test set, then the others. -/
noncomputable def certFrom {β : Type} (x y : S.dom → C) (Ts : List (Finset (Fin q)))
    (K : List (StagePair S) → Script β) : Script β :=
  (Script.seqList (Ts.map fun T =>
    (endpointScriptLift S R (phiT S.domGroup πd T) x (Fintype.card S.dom)).bind fun a =>
      (endpointScriptLift S R (phiT S.domGroup πd T) y (Fintype.card S.dom)).bind fun b =>
        Script.done (a, b))).bind K

theorem certPhase_bind {β : Type} (κ : ℕ) (O : TestSetOrder q κ) (x y : S.dom → C)
    (K : List (StagePair S) → Script β) :
    (certPhase S πd κ O R x y).bind K = certFrom S πd R x y O.sets K := rfl

/-- **The next test set**: the loop of `x` from the first stage, then the loop of `y`, then the
other test sets, with the pair of final stages added in front of their results. -/
theorem certFrom_cons {β : Type} (x y : S.dom → C) (T : Finset (Fin q))
    (Ts : List (Finset (Fin q))) (K : List (StagePair S) → Script β) :
    certFrom S πd R x y (T :: Ts) K =
      (epFrom S R (phiT S.domGroup πd T) x (Pgrp S.domGroup πd T, ∅)
          (Fintype.card S.dom)).bind fun a =>
        (epFrom S R (phiT S.domGroup πd T) y (Pgrp S.domGroup πd T, ∅)
            (Fintype.card S.dom)).bind fun b =>
          certFrom S πd R x y Ts fun ps => K ((a, b) :: ps) := by
  unfold certFrom
  rw [List.map_cons, scr_seqList_cons, scr_bind_assoc]
  rw [endpointScriptLift_eq_epFrom, endpointScriptLift_eq_epFrom]
  refine scr_bind_congr _ fun a => ?_
  rw [scr_bind_assoc]
  rfl

theorem certFrom_nil {β : Type} (x y : S.dom → C) (K : List (StagePair S) → Script β) :
    certFrom S πd R x y [] K = K [] := rfl

end Phase

end GI.Impl
