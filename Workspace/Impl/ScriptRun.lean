import Workspace.Impl.Cases

/-!
# Running a query script

Several steps of the recursion first ask recursive questions and then compute their answer
from the replies: the certificate phase and the ordered comparisons of an aggregation round
ask `Continue` on kernel orbits, the auxiliary reduction asks `Continue` or `Solve`, and the row
terminal asks `Solve`. In the model each of them is a query script (`GI.Algorithm.Script`),
and a run of the step holds a run of its script (`GI.Algorithm.Exec`): every question is
answered by a recursive run.

This file gives one program that runs any such script, and its specification.

## The program

The program keeps a value `st`, the *program state* of the script. A step function `stp`
(any user function) reads `st` and returns either

* `[0, out]`: the script is finished, and `out` is its result; or
* `[1, code, arg, kst]`: the script asks procedure `code` (`0` for `Solve`, `1` for `Continue`)
  on the state value `arg`, and `kst` is what the step function keeps for later.

The driver (`runBody`) then calls the procedure on `arg`, gets the answer `u`, and runs again on
`[kst, u]`. So the step function computes the next question from the answers so far.

## The specification

A relation `Rep st s` says that the program state `st` stands for the script `s`. The step
function meets `StepOK` if on every `st` with `Rep st s` it returns, at cost at most `B`,

* for a finished script `done a`: `[0, out]` with `Out a out`;
* for a script `ask m T k`: `[1, code m, arg, kst]` with a canonical value `arg` of `T`
  (`Canon`), where `m` is `Solve` or `Continue`, the call is allowed by the induction hypothesis
  (`Good` and smaller in the measure), and for every canonical answer `u` of the exact answer
  `A` of `T`, `Rep [kst, u] (k A)`.

The exact answer is all a step function needs to know about a reply: every run returns the
exact answer (`Run.exact`).

`run_spec`: then every evaluation of the driver on a program state of `s` returns `out` with
`Out a out` for a run `ex : Exec P₀ s a` of the script whose questions are the calls that the
driver made, at a cost of at most `(n + 1) runK (B + 1)` plus, for each call, the total cost of
its run and its setup charge (`Iface.charge`). Here `n` is the number of calls. This is the form
that `Iface.childCost` asks of the script calls of a step (`Run.children` lists `Exec.calls`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val)
open scoped Pointwise

/-- The number of a procedure in the questions of a script: `0` for `Solve`, `1` for
`Continue`. -/
def modeCode : Mode → ℕ
  | .solve => 0
  | .cont => 1
  | .giant => 2

/-- **The body of the driver** with index `d`, step function `stp` and the procedures `F`.
The environment grows as `[st, w, u]`. -/
def runBody (F : Funs) (d stp : ℕ) : Expr :=
  .letE (.call stp (.var 0))
    (.ite (.get (.var 1) (.nat 0))
      (.letE (.ite (.get (.var 1) (.nat 1)) (.call F.cont (.get (.var 1) (.nat 2)))
          (.call F.solve (.get (.var 1) (.nat 2))))
        (.call d (mk2 (.get (.var 1) (.nat 3)) (.var 2))))
      (.get (.var 1) (.nat 1)))

/-- The cost constant of one round of the driver. -/
def runK : ℕ := 40

namespace Iface

variable (I : Iface) (Pg : Program) (F : Funs)

/-- **What one step of a script must return** (see the module docstring). `μ` bounds the
measure of the calls (the measure of the calling node). -/
def StepPost (μ : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) {α : Type} (Out : α → Val → Prop)
    (Rep : Val → Script α → Prop) : Script α → Val → Prop
  | .done a, w => ∃ out, w = .list [.nat 0, out] ∧ Out a out
  | .ask (Ω' := Ω') (C' := C') m T k, w => ∃ (k' : ℕ) (e' : Ω' ≃ Fin k') (c' : C' → ℕ)
      (arg kst : Val), Function.Injective c' ∧ (m = .solve ∨ m = .cont) ∧
      w = .list [.nat 1, .nat (modeCode m), arg, kst] ∧ Canon e' c' arg T ∧ Good P₀ m T ∧
      MLt (measure P₀ m T) μ ∧ ∀ u, AnsC e' u T.answer → Rep (.list [kst, u]) (k T.answer)

/-- **The step function of a script**: on every program state of a script it returns what
`StepPost` asks, at cost at most `B`. Every program state has weight at most `B`. -/
structure StepOK (stp : ℕ) (μ : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) {α : Type}
    (Out : α → Val → Prop) (Rep : Val → Script α → Prop) (B : ℕ) : Prop where
  step : ∀ st s, Rep st s → FunAll Pg stp st (fun w c => c ≤ B ∧ StepPost μ Out Rep s w)
  wt : ∀ st s, Rep st s → st.wt ≤ B

/-- The induction hypothesis for the calls below `μ`. -/
def IHBelow (μ : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : Prop :=
  ∀ (m' : Mode) {Ω' C' : Type} (T : State Ω' C'), Good P₀ m' T → MLt (measure P₀ m' T) μ →
    I.CallOK Pg F m' T

/-- The induction hypothesis of a step gives `IHBelow` at the measure of its node. -/
theorem IH.below {m : Mode} {Ω C : Type} {S : State Ω C} (h : I.IH Pg F m S) :
    I.IHBelow Pg F (measure P₀ m S) := fun m' _ _ T hg hlt => h m' T hg hlt

/-- The cost of the calls of a script run: for each call, the total cost of its run and its
setup charge. -/
noncomputable def execCost {α : Type} {s : Script α} {a : α} (ex : Exec P₀ s a) : ℝ :=
  (ex.calls.map fun nd => nd.run.total I.work + I.charge nd).sum

theorem execCost_done {α : Type} (a : α) : I.execCost (Exec.done (P := P₀) a) = 0 := by
  simp [execCost, Exec.calls]

theorem calls_ask {α : Type} {Ω' C' : Type} {m : Mode} {T : State Ω' C'}
    {k : Set (Perm Ω') → Script α} {A : Set (Perm Ω')} {a : α}
    (r : Run P₀ m T none A) (ex : Exec P₀ (k A) a) :
    (Exec.ask r ex).calls = ⟨m, Ω', C', T, none, A, r⟩ :: ex.calls := rfl

theorem execCost_ask {α : Type} {Ω' C' : Type} {m : Mode} {T : State Ω' C'}
    {k : Set (Perm Ω') → Script α} {A : Set (Perm Ω')} {a : α}
    (r : Run P₀ m T none A) (ex : Exec P₀ (k A) a) :
    I.execCost (Exec.ask r ex) =
      r.total I.work + I.charge ⟨m, Ω', C', T, none, A, r⟩ + I.execCost ex := by
  simp only [execCost, calls_ask, List.map_cons, List.sum_cons]

/-- A call of `Solve` or `Continue` on a canonical value costs at most the total cost of its run
plus its setup charge. -/
theorem call_cost {m : Mode} {Ω' C' : Type} {T : State Ω' C'} {k' : ℕ} {e' : Ω' ≃ Fin k'}
    {c' : C' → ℕ} {arg : Val} (hm : m = .solve ∨ m = .cont) (hcan : Canon e' c' arg T)
    {A : Set (Perm Ω')} (r : Run P₀ m T none A) {cost : ℕ}
    (hc : (cost : ℝ) ≤ r.total I.work + I.excess m arg) :
    (cost : ℝ) ≤ r.total I.work + I.charge ⟨m, Ω', C', T, none, A, r⟩ := by
  rcases hm with rfl | rfl
  · simp only [excess, if_true] at hc
    simp only [charge, if_true]
    have hw : (arg.wt : ℝ) ≤ stateW (Nat.card Ω') T := by
      rw [card_eq e']; exact_mod_cast hcan.wt_le
    have hp : ((arg.wt : ℝ) + 1) ^ I.d₀ ≤ ((stateW (Nat.card Ω') T : ℝ) + 1) ^ I.d₀ :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    have hK : (0 : ℝ) ≤ I.K₀ := Nat.cast_nonneg _
    nlinarith
  · simpa [excess, charge] using hc

/-- **The call of the driver.** In the environment `[st, w]` with `w = [1, code m, arg, kst]`,
the driver calls the procedure `m` on `arg`. Its answer is a canonical answer of a run on `T`,
which returns the exact answer. -/
theorem call_step {μ : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ} (ih : I.IHBelow Pg F μ)
    {m : Mode} {Ω' C' : Type} {T : State Ω' C'} {k' : ℕ} {e' : Ω' ≃ Fin k'} {c' : C' → ℕ}
    (hc' : Function.Injective c') {arg kst st : Val} (hm : m = .solve ∨ m = .cont)
    (hcan : Canon e' c' arg T) (hg : Good P₀ m T) (hlt : MLt (measure P₀ m T) μ) :
    EvalAll Pg [st, .list [.nat 1, .nat (modeCode m), arg, kst]]
      (.ite (.get (.var 1) (.nat 1)) (.call F.cont (.get (.var 1) (.nat 2)))
        (.call F.solve (.get (.var 1) (.nat 2))))
      (fun u cu => ∃ (r : Run P₀ m T none T.answer) (cb : ℕ), AnsC e' u T.answer ∧
        (cb : ℝ) ≤ r.total I.work + I.charge ⟨m, Ω', C', T, none, T.answer, r⟩ ∧
        cu ≤ 3 * (Val.list [.nat 1, .nat (modeCode m), arg, kst]).wt + 30 + cb + 2 * u.wt) := by
  set w := Val.list [.nat 1, .nat (modeCode m), arg, kst] with hw
  have hcall := ih m T hg hlt k' e' c' hc' arg (by
    rcases hm with rfl | rfl
    · exact hcan.stateVal
    · exact hcan)
  have hcode : (Val.nat (modeCode m)).wt ≤ 3 := by
    rcases hm with rfl | rfl <;> simp [modeCode, wt_nat, GI.Machine.len_zero]
  have warg : arg.wt < w.wt := wt_le_wt_list (by simp)
  have dc := Det.get' (Det.var' (P := Pg) (env := [st, w]) (i := 1) (v := w) rfl) (Det.nat 1)
    (v := .nat (modeCode m)) rfl
  have da := Det.get' (Det.var' (P := Pg) (env := [st, w]) (i := 1) (v := w) rfl) (Det.nat 2)
    (v := arg) rfl
  -- The call of the procedure `f` on `arg`.
  have key : ∀ f, F.get m = f → EvalAll Pg [st, w] (.call f (.get (.var 1) (.nat 2)))
      (fun u cu => ∃ (r : Run P₀ m T none T.answer) (cb : ℕ), AnsC e' u T.answer ∧
        (cb : ℝ) ≤ r.total I.work + I.charge ⟨m, Ω', C', T, none, T.answer, r⟩ ∧
        cu ≤ w.wt + arg.wt + 8 + cb + u.wt) := by
    intro f hf
    subst hf
    refine EvalAll.call_funAll da fun v ca h => ?_
    obtain ⟨rfl, hca⟩ := h
    refine hcall.mono fun u cb ⟨A, L, r, hL, hA, hcb⟩ => ?_
    have hL' : L = none := by
      rcases hm with rfl | rfl <;> exact hL
    subst hL'
    have hAe := r.exact
    subst hAe
    exact ⟨r, cb, hA, I.call_cost hm hcan r hcb, by omega⟩
  refine EvalAll.ite dc (fun _ _ h => ⟨_, h.1⟩) fun x cc hx => ?_
  obtain ⟨hx, hcc⟩ := hx
  cases hx
  have hcc' : cc ≤ w.wt + 10 := by
    have := wt_nat_le 1; omega
  rcases hm with rfl | rfl
  · simp only [modeCode, if_true]
    refine (key F.solve rfl).mono fun u cu ⟨r, cb, hA, hcb, hcu⟩ => ⟨r, cb, hA, hcb, by omega⟩
  · simp only [modeCode, one_ne_zero, if_false]
    refine (key F.cont rfl).mono fun u cu ⟨r, cb, hA, hcb, hcu⟩ => ⟨r, cb, hA, hcb, by omega⟩

/-- **The script runner meets its specification.** If the step function meets `StepOK` and the
induction hypothesis holds below `μ`, then on every program state `st` of a script `s` every
evaluation of the driver returns the result `out` of a run `ex` of `s` (`Out a out`), whose calls
are the calls the driver made, at a cost of at most `(n + 1) runK (B + 1)` plus the cost of the
calls (`execCost`), where `n` is the number of calls. -/
theorem run_spec {d stp : ℕ} (hd : Pg.funs[d]? = some (runBody F d stp))
    {μ : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ} {α : Type} {Out : α → Val → Prop}
    {Rep : Val → Script α → Prop} {B : ℕ} (hs : StepOK Pg stp μ Out Rep B)
    (ih : I.IHBelow Pg F μ) :
    ∀ (s : Script α) (st : Val), Rep st s →
      FunAll Pg d st (fun out cost => ∃ (a : α) (ex : Exec P₀ s a), Out a out ∧ out.wt ≤ B ∧
        (cost : ℝ) ≤ ((ex.calls.length : ℝ) + 1) * (runK * ((B : ℝ) + 1)) + I.execCost ex) := by
  intro s
  induction s with
  | done a =>
    intro st hst
    have hwst := hs.wt st _ hst
    refine FunAll.intro hd ?_
    unfold runBody
    refine EvalAll.letE (Ra := fun w cw => cw ≤ st.wt + 2 * B + 2 ∧ w.wt < B ∧
        StepPost μ Out Rep (.done a) w)
      (EvalAll.call_funAll (Det.var' (P := Pg) (env := [st]) (i := 0) rfl) fun v ca h => ?_) ?_
    · obtain ⟨rfl, hca⟩ := h
      exact (hs.step _ _ hst).wt_lt.mono fun w c ⟨⟨hc, hp⟩, hwc⟩ => ⟨by omega, by omega, hp⟩
    rintro w cw ⟨hcw, hww, out, rfl, hout⟩
    have wout : out.wt < (Val.list [.nat 0, out]).wt := wt_le_wt_list (by simp)
    have dc := Det.get' (Det.var' (P := Pg) (env := [st, .list [.nat 0, out]]) (i := 1)
      (v := .list [.nat 0, out]) rfl) (Det.nat 0) (v := .nat 0) rfl
    have de := Det.get' (Det.var' (P := Pg) (env := [st, .list [.nat 0, out]]) (i := 1)
      (v := .list [.nat 0, out]) rfl) (Det.nat 1) (v := out) rfl
    refine (Det.ite_zero dc de).post fun c' hc' => ⟨a, Exec.done a, hout, by omega, ?_⟩
    rw [execCost_done]
    simp only [Exec.calls, List.length_nil, CharP.cast_eq_zero, zero_add, one_mul, add_zero]
    have h0 : (Val.nat 0).wt ≤ 3 := by simp [wt_nat, GI.Machine.len_zero]
    have hn : cw + c' + out.wt + 1 ≤ runK * (B + 1) := by
      simp only [runK]; omega
    exact_mod_cast hn
  | ask m T k ihk =>
    intro st hst
    have hwst := hs.wt st _ hst
    refine FunAll.intro hd ?_
    unfold runBody
    refine EvalAll.letE (Ra := fun w cw => cw ≤ st.wt + 2 * B + 2 ∧ w.wt < B ∧
        StepPost μ Out Rep (.ask m T k) w)
      (EvalAll.call_funAll (Det.var' (P := Pg) (env := [st]) (i := 0) rfl) fun v ca h => ?_) ?_
    · obtain ⟨rfl, hca⟩ := h
      exact (hs.step _ _ hst).wt_lt.mono fun w c ⟨⟨hc, hp⟩, hwc⟩ => ⟨by omega, by omega, hp⟩
    rintro w cw ⟨hcw, hww, k', e', c', arg, kst, hc', hm, rfl, hcan, hg, hlt, hrep⟩
    set w := Val.list [.nat 1, .nat (modeCode m), arg, kst] with hw
    have dc := Det.get' (Det.var' (P := Pg) (env := [st, w]) (i := 1) (v := w) rfl) (Det.nat 0)
      (v := .nat 1) rfl
    refine EvalAll.ite dc (fun _ _ h => ⟨_, h.1⟩) fun x cc hx => ?_
    obtain ⟨hx, hcc⟩ := hx
    cases hx
    simp only [one_ne_zero, if_false]
    have hcc' : cc ≤ w.wt + 10 := by have := wt_nat_le 1; have := wt_nat_le 0; omega
    refine EvalAll.letE (I.call_step Pg F ih hc' (st := st) hm hcan hg hlt) fun u cu hu => ?_
    obtain ⟨r, cb, hA, hcb, hcu⟩ := hu
    have hrep' := hrep u hA
    have hwku := hs.wt _ _ hrep'
    have wkst : kst.wt < (Val.list [kst, u]).wt := wt_le_wt_list (by simp)
    have wu : u.wt < (Val.list [kst, u]).wt := wt_le_wt_list (by simp)
    have dk := Det.get' (Det.var' (P := Pg) (env := [st, w, u]) (i := 1) (v := w) rfl) (Det.nat 3)
      (v := kst) rfl
    have du := Det.var' (P := Pg) (env := [st, w, u]) (i := 2) (v := u) rfl
    refine EvalAll.call_funAll (Det.mk2 dk du) fun v ca h => ?_
    obtain ⟨rfl, hca⟩ := h
    refine (ihk T.answer _ hrep').mono fun out cr ⟨a, ex, hout, hwo, hcr⟩ => ?_
    refine ⟨a, Exec.ask r ex, hout, hwo, ?_⟩
    rw [execCost_ask, calls_ask, List.length_cons]
    have hwi : w.wt = (Val.list [.nat 1, .nat (modeCode m), arg, kst]).wt := rfl
    have hn : cw + (cc + (cu + (ca + cr + out.wt + 1) + out.wt + 1) + out.wt + 1) + out.wt + 1 ≤
        runK * (B + 1) + cb + cr := by
      simp only [runK]; omega
    have hn' : ((cw + (cc + (cu + (ca + cr + out.wt + 1) + out.wt + 1) + out.wt + 1) + out.wt + 1 : ℕ) : ℝ) ≤
        (runK : ℝ) * ((B : ℝ) + 1) + cb + cr := by exact_mod_cast hn
    push_cast at hn' ⊢
    nlinarith

/-! ### Scripts with choices

The script of a step often depends on choices that the program makes as it goes: coset
representatives, the order of calls, a numbering of classes (`Aggregation.reps`, `pick`, `num`,
`src`, …). In the model these are fields fixed before the script runs, but a program computes
them along the way, with primitives whose outputs are relational. So the program cannot follow
one script fixed in advance. Instead it follows a *set* of candidate scripts, those whose choices
agree with the choices made so far, and narrows it at every step. At the end, one candidate is
the script that was run.

`Rep st Ss f`: the program state `st` stands for every script in the set `Ss`, and at most `f`
more calls are made. A step either finishes (`done a` is a candidate), or asks one call that all
the candidates of a nonempty subset `{ask m T k | k ∈ Ks}` ask, and continues with the set of
their continuations at the exact answer. -/

/-- **What one step of a script with choices must return.** -/
def StepPostC (μ : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) {α : Type} (Out : α → Val → Prop)
    (Rep : Val → Set (Script α) → ℕ → Prop) (Ss : Set (Script α)) (f : ℕ) (w : Val) : Prop :=
  (∃ a out, w = .list [.nat 0, out] ∧ Out a out ∧ Script.done a ∈ Ss) ∨
  (0 < f ∧ ∃ (m : Mode) (Ω' C' : Type) (T : State Ω' C') (k' : ℕ) (e' : Ω' ≃ Fin k')
    (c' : C' → ℕ) (arg kst : Val) (Ks : Set (Set (Perm Ω') → Script α)),
    Function.Injective c' ∧ (m = .solve ∨ m = .cont) ∧
    w = .list [.nat 1, .nat (modeCode m), arg, kst] ∧ Canon e' c' arg T ∧ Good P₀ m T ∧
    MLt (measure P₀ m T) μ ∧ Ks.Nonempty ∧ (∀ k ∈ Ks, Script.ask m T k ∈ Ss) ∧
    ∀ u, AnsC e' u T.answer → Rep (.list [kst, u]) ((fun k => k T.answer) '' Ks) (f - 1))

/-- **The step function of a script with choices**: on every program state it returns what
`StepPostC` asks, at cost at most `B`; every program state has weight at most `B`. -/
structure StepOKC (stp : ℕ) (μ : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) {α : Type}
    (Out : α → Val → Prop) (Rep : Val → Set (Script α) → ℕ → Prop) (B : ℕ) : Prop where
  step : ∀ st Ss f, Rep st Ss f →
    FunAll Pg stp st (fun w c => c ≤ B ∧ StepPostC μ Out Rep Ss f w)
  wt : ∀ st Ss f, Rep st Ss f → st.wt ≤ B

/-- **The script runner with choices.** On a program state of a set `Ss` of candidate scripts
with at most `f` more calls, every evaluation of the driver returns the result `out` of a run
`ex` of one of the candidates, with at most `f` calls, at a cost of at most
`(n + 1) runK (B + 1)` plus the cost of the calls, where `n` is the number of calls. -/
theorem run_specC {d stp : ℕ} (hd : Pg.funs[d]? = some (runBody F d stp))
    {μ : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ} {α : Type} {Out : α → Val → Prop}
    {Rep : Val → Set (Script α) → ℕ → Prop} {B : ℕ} (hs : StepOKC Pg stp μ Out Rep B)
    (ih : I.IHBelow Pg F μ) :
    ∀ (f : ℕ) (st : Val) (Ss : Set (Script α)), Rep st Ss f →
      FunAll Pg d st (fun out cost => ∃ s ∈ Ss, ∃ (a : α) (ex : Exec P₀ s a), Out a out ∧
        out.wt ≤ B ∧ ex.calls.length ≤ f ∧
        (cost : ℝ) ≤ ((ex.calls.length : ℝ) + 1) * (runK * ((B : ℝ) + 1)) + I.execCost ex) := by
  intro f
  induction f using Nat.strong_induction_on with
  | _ f ihf =>
  intro st Ss hst
  have hwst := hs.wt st _ _ hst
  refine FunAll.intro hd ?_
  unfold runBody
  refine EvalAll.letE (Ra := fun w cw => cw ≤ st.wt + 2 * B + 2 ∧ w.wt < B ∧
      StepPostC μ Out Rep Ss f w)
    (EvalAll.call_funAll (Det.var' (P := Pg) (env := [st]) (i := 0) rfl) fun v ca h => ?_) ?_
  · obtain ⟨rfl, hca⟩ := h
    exact (hs.step _ _ _ hst).wt_lt.mono fun w c ⟨⟨hc, hp⟩, hwc⟩ => ⟨by omega, by omega, hp⟩
  rintro w cw ⟨hcw, hww, ⟨a, out, rfl, hout, hmem⟩ | ⟨hf, m, Ω', C', T, k', e', c', arg, kst, Ks,
    hc', hm, rfl, hcan, hg, hlt, hKs, hKS, hrep⟩⟩
  · -- The script is finished.
    have wout : out.wt < (Val.list [.nat 0, out]).wt := wt_le_wt_list (by simp)
    have dc := Det.get' (Det.var' (P := Pg) (env := [st, .list [.nat 0, out]]) (i := 1)
      (v := .list [.nat 0, out]) rfl) (Det.nat 0) (v := .nat 0) rfl
    have de := Det.get' (Det.var' (P := Pg) (env := [st, .list [.nat 0, out]]) (i := 1)
      (v := .list [.nat 0, out]) rfl) (Det.nat 1) (v := out) rfl
    refine (Det.ite_zero dc de).post fun c' hc' =>
      ⟨_, hmem, a, Exec.done a, hout, by omega, by simp [Exec.calls], ?_⟩
    rw [execCost_done]
    simp only [Exec.calls, List.length_nil, CharP.cast_eq_zero, zero_add, one_mul, add_zero]
    have h0 : (Val.nat 0).wt ≤ 3 := by simp [wt_nat, GI.Machine.len_zero]
    have hn : cw + c' + out.wt + 1 ≤ runK * (B + 1) := by
      simp only [runK]; omega
    exact_mod_cast hn
  · -- The script asks a call.
    set w := Val.list [.nat 1, .nat (modeCode m), arg, kst] with hw
    have dc := Det.get' (Det.var' (P := Pg) (env := [st, w]) (i := 1) (v := w) rfl) (Det.nat 0)
      (v := .nat 1) rfl
    refine EvalAll.ite dc (fun _ _ h => ⟨_, h.1⟩) fun x cc hx => ?_
    obtain ⟨hx, hcc⟩ := hx
    cases hx
    simp only [one_ne_zero, if_false]
    have hcc' : cc ≤ w.wt + 10 := by have := wt_nat_le 1; have := wt_nat_le 0; omega
    refine EvalAll.letE (I.call_step Pg F ih hc' (st := st) hm hcan hg hlt) fun u cu hu => ?_
    obtain ⟨r, cb, hA, hcb, hcu⟩ := hu
    have hrep' := hrep u hA
    have hwku := hs.wt _ _ _ hrep'
    have wkst : kst.wt < (Val.list [kst, u]).wt := wt_le_wt_list (by simp)
    have wu : u.wt < (Val.list [kst, u]).wt := wt_le_wt_list (by simp)
    have dk := Det.get' (Det.var' (P := Pg) (env := [st, w, u]) (i := 1) (v := w) rfl) (Det.nat 3)
      (v := kst) rfl
    have du := Det.var' (P := Pg) (env := [st, w, u]) (i := 2) (v := u) rfl
    refine EvalAll.call_funAll (Det.mk2 dk du) fun v ca h => ?_
    obtain ⟨rfl, hca⟩ := h
    refine (ihf (f - 1) (by omega) _ _ hrep').mono
      fun out cr ⟨s', hs', a, ex, hout, hwo, hlen, hcr⟩ => ?_
    obtain ⟨kk, hkk, rfl⟩ := hs'
    refine ⟨_, hKS kk hkk, a, Exec.ask r ex, hout, hwo, ?_, ?_⟩
    · rw [calls_ask, List.length_cons]; omega
    rw [execCost_ask, calls_ask, List.length_cons]
    have hwi : w.wt = (Val.list [.nat 1, .nat (modeCode m), arg, kst]).wt := rfl
    have hn : cw + (cc + (cu + (ca + cr + out.wt + 1) + out.wt + 1) + out.wt + 1) + out.wt + 1 ≤
        runK * (B + 1) + cb + cr := by
      simp only [runK]; omega
    have hn' : ((cw + (cc + (cu + (ca + cr + out.wt + 1) + out.wt + 1) + out.wt + 1) + out.wt + 1 :
        ℕ) : ℝ) ≤ (runK : ℝ) * ((B : ℝ) + 1) + cb + cr := by exact_mod_cast hn
    push_cast at hn' ⊢
    nlinarith

/-- **The children of an aggregation round** (`Run.aggregate`): the calls of its script and the
continuations on the overcosets. The continuations are `Continue` calls, which pay no setup. -/
theorem childCost_aggregate {Ω C : Type} {S : State Ω C}
    (hs : (S.N : ℝ) ^ P₀.γ < S.size) (htr : S.Transitive)
    (L : SuppliedLabels S) (hnot : ¬ RowCase P₀.α S L.toGiantLabels) (hq₀ : P₀.q₀ ≤ L.q)
    (Ag : Aggregation P₀ S L.toGiantLabels) (hsel : Ag.sel.val = L.sel.val) (hcon : Ag.con = L.con)
    (b : Branches Ω) (e : Exec P₀ Ag.script b)
    (τ : Fin b.overs.length → Perm Ω)
    (hτ : ∀ j, τ j ∈ (b.overs.get j).1 • ((b.overs.get j).2 : Set (Perm Ω)))
    (child : Fin b.overs.length → State Ω C)
    (hchild : ∀ j, (child j).Inst (b.overs.get j).2 S.dom S.x (S.y ∘ τ j))
    (hN : ∀ j, (child j).N = S.N) (hhier : ∀ j, (child j).hier = Ag.newHier (b.overs.get j))
    (hbk : ∀ j, (child j).book = S.book)
    (A : Fin b.overs.length → Set (Perm Ω)) (r : ∀ j, Run P₀ .cont (child j) none (A j)) :
    I.childCost (Run.aggregate hs htr L hnot hq₀ Ag hsel hcon b e τ hτ child hchild hN hhier hbk
      A r) = I.execCost e + ((List.ofFn fun j => (r j).total I.work)).sum := by
  simp only [childCost, Run.children, List.map_append, List.sum_append, execCost, List.map_ofFn]
  congr 2
  exact List.ofFn_inj.2 (funext fun j => by simp [charge])

end Iface

end GI.Impl
