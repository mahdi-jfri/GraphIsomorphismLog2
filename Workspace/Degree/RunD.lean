module

public import Workspace.Impl.ScriptRun
public import Workspace.Paper.ScriptCalls

@[expose] public section

/-!
# The script runner of the degree algorithm

`run_specC` of the general algorithm builds a run `Exec` of a script out of the runs of its calls.
In the degree algorithm a call only returns its exact answer at a known cost, so the runner keeps
the script and adds up the costs. `DX s a` says that `a` is the result of the script `s` when each
call returns its exact answer. It stands for `Exec P₀ s a`. For a table `J` of costs,
`Script.cost J s` stands for `execCost`, and `Script.numCalls` for the number of calls.
-/

namespace GI.Algorithm

/-- A table of costs for the calls of a script. -/
abbrev CostT := ∀ {Ω C : Type}, Mode → State Ω C → ℝ


variable {α β : Type}

namespace Script

/-- The cost of the calls of a script along the exact answers. -/
noncomputable def cost (J : CostT) : Script α → ℝ
  | done _ => 0
  | ask m T k => J m T + cost J (k T.answer)

theorem cost_bind (J : CostT) : ∀ (s : Script α) (f : α → Script β),
    (s.bind f).cost J = s.cost J + (f s.evalExact).cost J
  | done _, _ => by simp [bind, cost, evalExact]
  | ask m T k, f => by
    simp only [bind, cost, evalExact]
    rw [cost_bind J (k T.answer) f]
    ring

end Script

end GI.Algorithm

namespace GI.Degree

open GI.Algorithm GI.Assembly GI.Impl GI.Lang Equiv
open GI.Cited (Val)

/-- `a` is the result of `s`, when each call returns its exact answer. -/
structure DX {α : Type} (s : Script α) (a : α) : Prop where
  exact : s.evalExact = a

/-- The number of calls of a script with result `a`. -/
noncomputable def DX.n {α : Type} {s : Script α} {a : α} (_ : DX s a) : ℕ := s.numCalls

/-- The cost of the calls of a script with result `a`. -/
noncomputable def DX.cost {α : Type} {s : Script α} {a : α} (_ : DX s a) (J : CostT) : ℝ := s.cost J

/-- Moving along an equation of scripts keeps the number of calls and their cost. -/
theorem DX.cast {α : Type} {s s' : Script α} (h : s = s') {a : α} (ex : DX s a) :
    ∃ ex' : DX s' a, ex'.n = ex.n ∧ ∀ J, ex'.cost J = ex.cost J := by
  subst h; exact ⟨ex, rfl, fun _ => rfl⟩

/-- The calls below `μ` with the property `Pr` return their exact answers, at the costs of `J`. -/
def DIH (Pg : Program) (F : Funs) (J : CostT) (Pr : ∀ {Ω' C' : Type}, Mode → State Ω' C' → Prop)
    (μ : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : Prop :=
  ∀ (m : Mode) {Ω C : Type} (T : State Ω C), (m = .solve ∨ m = .cont) → Good P₀ m T →
    MLt (measure P₀ m T) μ → Pr m T → ∀ (k : ℕ) (e : Ω ≃ Fin k) (c : C → ℕ), Function.Injective c →
      ∀ arg : Val, Canon e c arg T →
        FunAll Pg (F.get m) arg fun u cost => AnsC e u T.answer ∧ (cost : ℝ) ≤ J m T

variable {Pg : Program} {F : Funs} {J : CostT}

/-- One call of the driver. As `call_step` of the general algorithm. -/
theorem call_stepD {μ : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ}
    {Pr : ∀ {Ω' C' : Type}, Mode → State Ω' C' → Prop} (ih : DIH Pg F J Pr μ)
    {m : Mode} {Ω' C' : Type} {T : State Ω' C'} {k' : ℕ} {e' : Ω' ≃ Fin k'} {c' : C' → ℕ}
    (hc' : Function.Injective c') {arg kst st : Val} (hm : m = .solve ∨ m = .cont)
    (hcan : Canon e' c' arg T) (hg : Good P₀ m T) (hlt : MLt (measure P₀ m T) μ) (hp : Pr m T) :
    EvalAll Pg [st, .list [.nat 1, .nat (modeCode m), arg, kst]]
      (.ite (.get (.var 1) (.nat 1)) (.call F.cont (.get (.var 1) (.nat 2)))
        (.call F.solve (.get (.var 1) (.nat 2))))
      (fun u cu => ∃ cb : ℕ, AnsC e' u T.answer ∧ (cb : ℝ) ≤ J m T ∧
        cu ≤ 3 * (Val.list [.nat 1, .nat (modeCode m), arg, kst]).wt + 30 + cb + 2 * u.wt) := by
  set w := Val.list [.nat 1, .nat (modeCode m), arg, kst] with hw
  have hcall := ih m T hm hg hlt hp k' e' c' hc' arg hcan
  have hcode : (Val.nat (modeCode m)).wt ≤ 3 := by
    rcases hm with rfl | rfl <;> simp [modeCode, wt_nat, GI.Machine.len_zero]
  have warg : arg.wt < w.wt := wt_le_wt_list (by simp)
  have dc := Det.get' (Det.var' (P := Pg) (env := [st, w]) (i := 1) (v := w) rfl) (Det.nat 1)
    (v := .nat (modeCode m)) rfl
  have da := Det.get' (Det.var' (P := Pg) (env := [st, w]) (i := 1) (v := w) rfl) (Det.nat 2)
    (v := arg) rfl
  have key : ∀ f, F.get m = f → EvalAll Pg [st, w] (.call f (.get (.var 1) (.nat 2)))
      (fun u cu => ∃ cb : ℕ, AnsC e' u T.answer ∧ (cb : ℝ) ≤ J m T ∧
        cu ≤ w.wt + arg.wt + 8 + cb + u.wt) := by
    intro f hf
    subst hf
    refine EvalAll.call_funAll da fun v ca h => ?_
    obtain ⟨rfl, hca⟩ := h
    exact hcall.mono fun u cb ⟨hA, hcb⟩ => ⟨cb, hA, hcb, by omega⟩
  refine EvalAll.ite dc (fun _ _ h => ⟨_, h.1⟩) fun x cc hx => ?_
  obtain ⟨hx, hcc⟩ := hx
  cases hx
  have hcc' : cc ≤ w.wt + 10 := by
    have := wt_nat_le 1; omega
  rcases hm with rfl | rfl
  · simp only [modeCode, if_true]
    refine (key F.solve rfl).mono fun u cu ⟨cb, hA, hcb, hcu⟩ => ⟨cb, hA, hcb, by omega⟩
  · simp only [modeCode, one_ne_zero, if_false]
    refine (key F.cont rfl).mono fun u cu ⟨cb, hA, hcb, hcu⟩ => ⟨cb, hA, hcb, by omega⟩

/-- **The script runner with choices.** As `run_specC` of the general algorithm: on a program state
of a set `Ss` of candidate scripts with at most `f` more calls, every evaluation of the driver
returns the result of one of the candidates, with at most `f` calls, at a cost of at most
`(n + 1) runK (B + 1)` plus the cost of the calls. -/
theorem run_specCD {d stp : ℕ} (hd : Pg.funs[d]? = some (runBody F d stp))
    {μ : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ} {α : Type} {Out : α → Val → Prop}
    {Rep : Val → Set (Script α) → ℕ → Prop} {B : ℕ} (hs : Iface.StepOKC Pg stp μ Out Rep B)
    {Pr : ∀ {Ω' C' : Type}, Mode → State Ω' C' → Prop} (ih : DIH Pg F J Pr μ) :
    ∀ (f : ℕ) (st : Val) (Ss : Set (Script α)), Rep st Ss f → (∀ s ∈ Ss, s.CallsExact Pr) →
      FunAll Pg d st (fun out cost => ∃ s ∈ Ss, ∃ (a : α) (_ : DX s a), Out a out ∧
        out.wt ≤ B ∧ s.numCalls ≤ f ∧
        (cost : ℝ) ≤ ((s.numCalls : ℝ) + 1) * (runK * ((B : ℝ) + 1)) + s.cost J) := by
  intro f
  induction f using Nat.strong_induction_on with
  | _ f ihf =>
  intro st Ss hst hPr
  have hwst := hs.wt st _ _ hst
  refine FunAll.intro hd ?_
  unfold runBody
  refine EvalAll.letE (Ra := fun w cw => cw ≤ st.wt + 2 * B + 2 ∧ w.wt < B ∧
      Iface.StepPostC μ Out Rep Ss f w)
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
      ⟨_, hmem, a, ⟨rfl⟩, hout, by omega, by simp [Script.numCalls], ?_⟩
    simp only [Script.numCalls, Script.cost, CharP.cast_eq_zero, zero_add, one_mul, add_zero]
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
    obtain ⟨k₀, hk₀⟩ := hKs
    have hp₀ : Pr m T := (hPr _ (hKS k₀ hk₀)).1
    refine EvalAll.letE (call_stepD ih hc' (st := st) hm hcan hg hlt hp₀) fun u cu hu => ?_
    obtain ⟨cb, hA, hcb, hcu⟩ := hu
    have hrep' := hrep u hA
    have hwku := hs.wt _ _ _ hrep'
    have wkst : kst.wt < (Val.list [kst, u]).wt := wt_le_wt_list (by simp)
    have wu : u.wt < (Val.list [kst, u]).wt := wt_le_wt_list (by simp)
    have dk := Det.get' (Det.var' (P := Pg) (env := [st, w, u]) (i := 1) (v := w) rfl) (Det.nat 3)
      (v := kst) rfl
    have du := Det.var' (P := Pg) (env := [st, w, u]) (i := 2) (v := u) rfl
    refine EvalAll.call_funAll (Det.mk2 dk du) fun v ca h => ?_
    obtain ⟨rfl, hca⟩ := h
    refine (ihf (f - 1) (by omega) _ _ hrep' ?_).mono ?_
    · rintro _ ⟨kk, hkk, rfl⟩
      exact (hPr _ (hKS kk hkk)).2
    rintro out cr ⟨s', hs', a, ex, hout, hwo, hlen, hcr⟩
    obtain ⟨kk, hkk, rfl⟩ := hs'
    beta_reduce at hlen hcr
    have hex : (kk T.answer).evalExact = a := ex.exact
    refine ⟨_, hKS kk hkk, a, ⟨hex⟩, hout, hwo, ?_, ?_⟩
    · simp only [Script.numCalls]; omega
    simp only [Script.numCalls, Script.cost]
    have hwi : w.wt = (Val.list [.nat 1, .nat (modeCode m), arg, kst]).wt := rfl
    have hn : cw + (cc + (cu + (ca + cr + out.wt + 1) + out.wt + 1) + out.wt + 1) + out.wt + 1 ≤
        runK * (B + 1) + cb + cr := by
      simp only [runK]; omega
    have hn' : ((cw + (cc + (cu + (ca + cr + out.wt + 1) + out.wt + 1) + out.wt + 1) + out.wt + 1 :
        ℕ) : ℝ) ≤ (runK : ℝ) * ((B : ℝ) + 1) + cb + cr := by exact_mod_cast hn
    push_cast at hn' ⊢
    nlinarith

end GI.Degree
