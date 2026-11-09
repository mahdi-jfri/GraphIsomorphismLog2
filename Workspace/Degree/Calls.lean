module

public import Workspace.Degree.Budget

@[expose] public section

/-!
# The bound on every call

`calls_bound`: with the code in place, every good call returns the exact answer within
`bound (K K₁ L) L`, where `L = logD D` and `K₁ = 16 M (1 + solveB)`. Here `M` is the polynomial of
`budgets` in the root's bound `Nm`, and `solveB` pays the calls of a round to the general solver.
The constants depend on the primitives, the solver and `E` only.
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly GI.Impl GI.Lang Equiv Equiv.Perm Real
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership GroupOrder MinimalBlocks)

theorem ContBudget.mono {X : Ctx} {hst : PointwiseStab} {hpre : Preimage}
    {hfac : NormalizedFactor} {Kg dg : ℕ} {K K' : ℝ} (h : ContBudget X hst hpre hfac Kg dg K)
    (hK : K ≤ K') : ContBudget X hst hpre hfac Kg dg K' :=
  ⟨fun k N W a b c => (h.base k N W a b c).trans hK, fun k N W a b c => (h.orbit k N W a b c).trans hK,
    fun k N W a b c => (h.reset k N W a b c).trans hK⟩

theorem cBeta_P₀ : 0 < GI.Paper.cBeta P₀.β := by
  unfold GI.Paper.cBeta
  exact Real.log_pos (by norm_num [P₀])

/-- The size of the own budget of `contD`. -/
noncomputable def ownK (Cm em : ℕ) (a : ℝ) (Kg dg D n : ℕ) : ℝ :=
  16 * (budM Cm em n : ℝ) * (1 + solveB a Kg dg D)

/-- **Every good call meets its bound.** -/
theorem calls_bound (hst : PointwiseStab) (hpre : Preimage) (hfac : NormalizedFactor)
    (hmb : MinimalBlocks) (hO : GroupOrder) (h : JohnsonRecognition) (hp : Preimage)
    (hm : Membership) {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hA : AltAt c₁ c₂ P₀.q₀)
    (Kg dg : ℕ) {a : ℝ} (ha : 0 ≤ a) {Xw : ℕ → ℕ} (hXw : PBU fun _ W _ => Xw W) :
    ∃ (ks : Cst) (Cm em : ℕ), ks.a = a ∧ 1 ≤ Cm ∧
      ∀ (X : Ctx) (F₀ F : Funs) (fs : ℕ) (cd : ContCode X F) (_ : ResetCode X cd.frs hst hpre hfac)
        (ht : TransCode X F hmb hO h hp hst hm) (gc : GiantCode X F₀ F hpre hfac hm (abKrC hst) Xw),
        GenSolverAt X.Pg fs a Kg dg → cd.fs = fs → ht.fs = fs → gc.fs = fs → ht.E = caseE c₁ c₂ P₀.q₀ → 6 ≤ X.D → X.D ≤ X.Nm →
        (∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (S : State Ω C) (lv : Val)
          (L : SuppliedLabels S), LabValStd e S lv L → X.I.LabVal e S lv L) →
        (∀ k N, labWStd k N ≤ X.I.labW k N) →
        ∀ c : Child, X.Good c → X.Spec c (ks.bound (ks.K (ownK Cm em a Kg dg X.D X.Nm)
          (logD X.D)) (logD X.D) c) := by
  set E := caseE c₁ c₂ P₀.q₀
  obtain ⟨Cm, em, p, hp1, hCm1, hb⟩ := budgets hst hpre hfac hmb hO h hp hm E Kg dg hXw
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  obtain ⟨ks, hka, hkE, hkP, hkCm, hkam, hkCo, hkao, hkc₀, hkδ⟩ :=
    exists_cst (a := a) (cE := 3 * (p : ℝ) * ((E : ℝ) + 1)) (cP := 2 * (p : ℝ))
      (Cm := 4 * (P₀.κ.factorial : ℝ) + 11) (am := 2 * (P₀.κ : ℝ)) (Co := 2)
      (ao := (P₀.κ : ℝ) + 1) (c₀ := cZero) (δ := GI.Paper.cBeta P₀.β) ha (by positivity)
      (by positivity) (by positivity) (by norm_num) cZero_pos cBeta_P₀
  refine ⟨ks, Cm, em, hka, hCm1, fun X F₀ F fs cd rc ht gc hsol hf₁ hf₂ hf₃ hE hD6 hDn hlab hlabW
    => ?_⟩
  subst hka
  obtain ⟨cb, tb, gb⟩ := hb X hDn
  have hs := solveB_nn ks.a Kg dg X.D
  have hM := (Nat.cast_nonneg (budM Cm em X.Nm) : (0 : ℝ) ≤ _)
  have hMs := mul_nonneg hM hs
  have hK : 0 ≤ ownK Cm em ks.a Kg dg X.D X.Nm := by unfold ownK; positivity
  have hown : ownK Cm em ks.a Kg dg X.D X.Nm = 16 * (budM Cm em X.Nm : ℝ) +
      16 * ((budM Cm em X.Nm : ℝ) * solveB ks.a Kg dg X.D) := by unfold ownK; ring
  have hsol' : GenSolverAt X.Pg fs ks.a Kg dg := hsol
  have ops := ops_of (ks := ks) (K₁ := ownK Cm em ks.a Kg dg X.D X.Nm) cd rc ht gc hsol' hf₁ hf₂ hf₃
    (cb.mono (by rw [hown]; linarith)) (hE ▸ tb) (gb ks.a) (by rw [hown]; linarith)
    (by rw [hown]; linarith) hc₁ hc₂ hA hE hD6 (by rw [hkE, hE]) hkP hkc₀ hkδ hkCm hkam hkCo
    hkao hlab hlabW
  exact spine X ks hK (by omega) ops

end GI.Degree
