module

public import Workspace.Assembly.Stage2
public import Workspace.Assembly.Params

@[expose] public section

/-!
# The general solver, as a function of a program

The degree-sensitive algorithm calls the general solver `fs` of the final program.

* `total_le_any`: the stage 1 bound holds at `P₀` on every state of a finite type. The root of the
  run plays no part, and no `Supply` or Maróti's theorem is used.
* `GeneralSolver Pg fs`: on every value of a state, `fs` returns a canonical value of the exact
  answer, at cost `exp(c log²(s + 2)) + K (wt v + 1)^d`. Here `s` is the size of the active domain.
* `GeneralSolver.of_sub`: the contract moves to every extension of the program.
* `Solved.generalSolver`: a solved program meets the contract at `asmF.solve`.
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly GI.Lang GI.Paper GI.Impl Equiv Equiv.Perm
open GI.Cited (Val)

/-- **The stage 1 bound on every state.** -/
theorem total_le_any {w : Node P₀ → ℝ} {cw : ℝ} (hw : NodeBound' w cw) (hcw : 0 ≤ cw) :
    ∃ C' : ℝ, ∀ {Ω C : Type} [Finite Ω] (S : State Ω C) {A : Set (Perm Ω)}
      (r : Run P₀ .solve S none A),
      r.total w ≤ Real.exp (C' * Real.log ((S.size : ℝ) + 2) ^ 2) := by
  obtain ⟨hP, ha128, hκ, hc, hαγ, hbase, ha, -⟩ := P₀_hyps
  obtain ⟨cσ, hcσ, hok⟩ := Run.rootsOK_all hκ
  have h5 : (5 : ℝ) ≤ P₀.a := by linarith
  obtain ⟨C', h⟩ := main_recurrence_solved hP hc hαγ hbase hcσ (hw.toNodeBound h5) hcw
    (by linarith) ha
  exact ⟨C', fun S A r => (total_le_worstCost (h S.size).1 r le_rfl (hok r)).trans (h S.size).2⟩

/-- **The contract of the general solver at function `fs`.** The constants do not depend on the
state. -/
def GeneralSolver (Pg : Program) (fs : ℕ) : Prop :=
  ∃ (a : ℝ) (K d : ℕ), 0 ≤ a ∧ ∀ {Ω C : Type} (S : State Ω C) (k : ℕ) (e : Ω ≃ Fin k) (c : C → ℕ),
    Function.Injective c → ∀ v : Val, StateVal e c v S →
      FunAll Pg fs v fun u cost => AnsC e u S.answer ∧
        (cost : ℝ) ≤ Real.exp (a * Real.log ((S.size : ℝ) + 2) ^ 2) + K * ((v.wt : ℝ) + 1) ^ d

theorem GeneralSolver.of_sub {Pg Pg' : Program} {fs : ℕ} (hs : Pg.Sub Pg')
    (h : GeneralSolver Pg fs) : GeneralSolver Pg' fs := by
  obtain ⟨a, K, d, ha, h⟩ := h
  exact ⟨a, K, d, ha, fun S k e c hc v hv => (h S k e c hc v hv).of_sub hs⟩

/-- **A solved program holds the general solver at `asmF.solve`.** -/
theorem Solved.generalSolver {Pg : Program} (h : Solved Pg) : GeneralSolver Pg asmF.solve := by
  obtain ⟨R, L, fm, hF, hL, -, hR⟩ := h
  obtain ⟨cw, hcw, hw⟩ := R.iface.workBound (R.workReq hR)
  obtain ⟨a, ha⟩ := total_le_any hw hcw
  refine ⟨max a 0, R.iface.K₀, R.iface.d₀, le_max_right _ _, ?_⟩
  intro Ω C S k e c hc v hv
  haveI : Finite Ω := Finite.of_equiv _ e.symm
  have hall := R.iface.callOK_all Pg L.F (Iface.Layout.modeOK R.iface Pg hL) .solve S trivial k e c
    hc v hv
  rw [hF] at hall
  refine hall.mono ?_
  rintro u cost ⟨A, L', r, hL', hA, hcost⟩
  have hL'' : L' = none := hL'
  subst hL''
  have hAe : A = S.answer := r.exact
  subst hAe
  refine ⟨hA, ?_⟩
  simp only [Iface.excess, if_true] at hcost
  refine hcost.trans (add_le_add ((ha S r).trans (Real.exp_le_exp.2 ?_)) le_rfl)
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)

end GI.Degree
