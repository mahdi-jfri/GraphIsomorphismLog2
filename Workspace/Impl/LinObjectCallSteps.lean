import Workspace.Impl.LinObjectReadPlan

namespace GI.Impl
open GI.Cited GI.Lang

def linObjectCallStepsE : List (ℕ × linObjectReadPlan) → Expr → Expr
  | [],tail => tail
  | (f,p)::steps,tail => .letE (.call f p.expr) (linObjectCallStepsE steps tail)

set_option maxHeartbeats 400000 in
/-- Compose a fixed sequence of proved calls while retaining the entire
store as an invariant. Every intermediate value is bounded by its call cost. -/
theorem linObjectCallSteps_spec {P : Program} {C A T : ℕ}
    (steps : List (ℕ × linObjectReadPlan)) (tail : Expr) (I : ℕ → List Val → Prop) (R : Val → Prop)
    (harg : ∀ fp ∈ steps,linObjectPlanBudget fp.2 C ≤ A)
    (hstep : ∀ i f p,steps[i]? = some (f,p) → ∀ env,I i env → normEnvBound C env →
      ∃ input,p.value env = some input ∧
        FunAll P f input (fun out cost => I (i+1) (env++[out]) ∧ cost ≤ C))
    (htail : ∀ env,I steps.length env → normEnvBound C env →
      EvalAll P env tail (fun out cost => R out ∧ cost ≤ T))
    (env : List Val) (hi : I 0 env) (hw : normEnvBound C env) :
    EvalAll P env (linObjectCallStepsE steps tail)
      (fun out cost => R out ∧ cost ≤ (A+2*C+T+5)*3^steps.length) := by
  induction steps generalizing I env with
  | nil =>
    exact (htail env hi hw).mono fun out cost hout => ⟨hout.1,by simp only [List.length_nil,pow_zero,mul_one]; omega⟩
  | cons fp steps ih =>
    obtain ⟨f,p⟩ := fp
    obtain ⟨input,hread,hcall⟩ := hstep 0 f p rfl env hi hw
    have da := (linObjectReadPlan_det (P:=P) hw p hread).mono (harg (f,p) (by simp))
    apply EvalAll.letE (normBound_call da hcall)
    intro v cv hv
    obtain ⟨hi1,wv,hcv⟩ := hv
    have hw1 : normEnvBound C (env++[v]) := normEnvBound_snoc hw le_rfl wv
    have harg' : ∀ fp ∈ steps,linObjectPlanBudget fp.2 C ≤ A := fun fp hfp => harg fp (by simp [hfp])
    have hstep' : ∀ i f p,steps[i]? = some (f,p) → ∀ env,I (i+1) env → normEnvBound C env →
        ∃ input,p.value env = some input ∧
          FunAll P f input (fun out cost => I (i+1+1) (env++[out]) ∧ cost ≤ C) := by
      intro i f p hp env hI hW
      exact hstep (i+1) f p (by simpa using hp) env hI hW
    have htail' : ∀ env,I (steps.length+1) env → normEnvBound C env →
        EvalAll P env tail (fun out cost => R out ∧ cost ≤ T) := by
      intro env hI hW
      exact htail env hI hW
    have hr := ih (fun i env => I (i+1) env) harg' hstep' htail' (env++[v]) hi1 hw1
    refine hr.wt_lt.mono fun out cost hout => ⟨hout.1.1,?_⟩
    simp only [List.length_cons,pow_succ]
    have hc := hout.1.2
    have wo := hout.2
    have hp : 1 ≤ 3^steps.length := Nat.one_le_pow _ _ (by decide)
    nlinarith

end GI.Impl
