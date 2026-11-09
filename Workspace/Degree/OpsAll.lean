module

public import Workspace.Degree.OpsGiant
public import Workspace.Degree.OpsTrans

@[expose] public section

/-!
# All the operations

`ops_of` gives `Ops` (`Degree/Spine.lean`) from the code of the four new functions, the general
solver, and the polynomial budgets. With `spine`, this proves the bound on every call
(`spine_of`).
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly GI.Impl GI.Lang Equiv Equiv.Perm Real
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership GroupOrder MinimalBlocks)

/-- **The general solver** at `f`, with the cost bound of `GeneralSolver`. -/
def GenSolverAt (Pg : Program) (f : ℕ) (a : ℝ) (Kg dg : ℕ) : Prop :=
  ∀ {Ω C : Type} (S : State Ω C) (k : ℕ) (e : Ω ≃ Fin k) (c : C → ℕ),
    Function.Injective c → ∀ v : Val, StateVal e c v S →
      FunAll Pg f v fun u cost => AnsC e u S.answer ∧
        (cost : ℝ) ≤ exp (a * Real.log ((S.size : ℝ) + 2) ^ 2) + Kg * ((v.wt : ℝ) + 1) ^ dg

/-- **The polynomial bounds of `contD`.** -/
structure ContBudget (X : Ctx) (hst : PointwiseStab) (hpre : Preimage) (hfac : NormalizedFactor)
    (Kg dg : ℕ) (K₁ : ℝ) : Prop where
  base : ∀ k N W, k ≤ X.Nm → N ≤ X.Nm → W ≤ X.W₀ →
    (contPart k N W : ℝ) + Kg * ((W : ℝ) + 1) ^ dg ≤ K₁
  orbit : ∀ k N W, k ≤ X.Nm → N ≤ X.Nm → W ≤ X.W₀ →
    (contPart k N W : ℝ) + (orbK * (X.W₀ + ansW k + 1) ^ 15 : ℕ) ≤ K₁
  reset : ∀ k N W, k ≤ X.Nm → N ≤ X.Nm → W ≤ X.W₀ →
    (contPart k N W : ℝ) + (resetOwn (pointwiseStabPrim hst) (preimagePrim hpre)
      (normalizedFactorPrim hfac) (W + 1) : ℕ) ≤ K₁

variable {X : Ctx} {ks : Cst}

theorem Ctx.Runs.mono_own {Ω C : Type} {f : ℕ} {m : Mode} {T : State Ω C}
    {μ : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ} {own own' : ℝ} {Sh : List Child → Prop}
    (h : X.Runs f m T μ own Sh) (hle : own ≤ own') : X.Runs f m T μ own' Sh :=
  fun B hB k e cc hcc v hv => (h B hB k e cc hcc v hv).mono fun _ _ ⟨ha, cs, hs, hc⟩ =>
    ⟨ha, cs, hs, by linarith⟩

/-- **The operations**, from the code and the budgets. -/
theorem ops_of {F₀ F : Funs} {hst : PointwiseStab} {hpre : Preimage} {hfac : NormalizedFactor}
    {hmb : MinimalBlocks} {hO : GroupOrder} {h : JohnsonRecognition} {hp : Preimage}
    {hm : Membership} {krC Xw : ℕ → ℕ} {fs Kg dg p : ℕ} {K₁ K₂ K₃ : ℝ}
    (cd : ContCode X F) (rc : ResetCode X cd.frs hst hpre hfac)
    (ht : TransCode X F hmb hO h hp hst hm) (gc : GiantCode X F₀ F hpre hfac hm krC Xw)
    (hsol : GenSolverAt X.Pg fs ks.a Kg dg) (hf₁ : cd.fs = fs) (hf₂ : ht.fs = fs) (hf₃ : gc.fs = fs)
    (cb : ContBudget X hst hpre hfac Kg dg K₁)
    (tb : TransBudget X hmb hO h hp hst hm ht.E Kg dg p K₂)
    (gb : GiantBudget X hpre hfac hm krC Xw ks.a Kg dg K₃)
    (hK₂ : K₂ + K₂ + K₂ + K₂ ≤ K₁) (hK₃ : K₃ + K₃ ≤ K₁)
    {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hA : AltAt c₁ c₂ P₀.q₀)
    (hE : ht.E = caseE c₁ c₂ P₀.q₀) (hD6 : 6 ≤ X.D)
    (hcE : ks.cE = 3 * (p : ℝ) * ((ht.E : ℝ) + 1)) (hcP : ks.cP = 2 * (p : ℝ))
    (hc₀ : ks.c₀ = cZero) (hδ : ks.δ = GI.Paper.cBeta P₀.β)
    (hCm : ks.Cm = 4 * (P₀.κ.factorial : ℝ) + 11) (ham : ks.am = 2 * (P₀.κ : ℝ)) (hCo : ks.Co = 2)
    (hao : ks.ao = (P₀.κ : ℝ) + 1)
    (hlab : ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (S : State Ω C) (lv : Val)
      (L : SuppliedLabels S), LabValStd e S lv L → X.I.LabVal e S lv L)
    (hlabW : ∀ k N, labWStd k N ≤ X.I.labW k N) :
    Ops X ks K₁ where
  base T hd hs := ops_base cd (fun S k e c hc v hv => hf₁ ▸ hsol S k e c hc v hv) cb.base T hd hs
  orbit T hd hs ht' := ops_orbit cd cb.orbit T hd hs ht'
  reset T hd hs ht' := ops_reset cd rc cb.reset T hd hs ht'
  trans R hd htr h2 hNs B hB k e cc hcc v hv :=
    (ops_trans ht hc₁ hc₂ hA hE hD6 tb (fun S k e c hc v hv => hf₂ ▸ hsol S k e c hc v hv) hcE hcP
      hc₀.le hlab hlabW R hd htr h2 hNs B hB k e cc hcc v hv).mono fun _ _ ⟨ha, ho⟩ =>
      ⟨ha, TransOut_le hK₂ ho⟩
  giant T hd hg := (ops_giant gc gb (fun S k e c hc v hv => hf₃ ▸ hsol S k e c hc v hv) hc₀ hδ hCm
    ham hCo hao T hd hg).mono_own hK₃

end GI.Degree
