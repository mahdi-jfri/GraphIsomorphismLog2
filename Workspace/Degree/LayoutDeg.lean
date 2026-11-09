module

public import Workspace.Degree.LayoutGiant
public import Workspace.Degree.PrimitiveBound

@[expose] public section

/-!
# The code of the degree algorithm in `degProg`

`dp_degCode D` gives `DegCode` for `degProg h dpE D`. All constants are fixed before `D`:

* `pc₁, pc₂` are the constants of Lemma 8.2 of the paper at `P₀.q₀` (`primitiveAlternatives`), and
  the test of the case decision uses the exponent `dpE = caseE pc₁ pc₂ P₀.q₀`;
* `sa, sK, sd` are the constants of the general solver of the final program of the general
  algorithm;
* `dpXw` is the phase bound of the round (`Degree/LayoutGiant.lean`).

So `degree_root` applies to every `degProg h dpE D` with the same constants (`dp_root`).
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly GI.Impl GI.Lang
open GI.Cited (Val)

set_option maxRecDepth 100000

/-! ### The constants -/

/-- The constant `c₁` of Lemma 8.2 of the paper. -/
noncomputable def pc₁ : ℝ := Classical.choose primitiveAlternatives

theorem pc₁_nonneg : 0 ≤ pc₁ := (Classical.choose_spec primitiveAlternatives).1

/-- The constant `c₂` of Lemma 8.2 of the paper, at `P₀.q₀`. -/
noncomputable def pc₂ : ℝ := Classical.choose ((Classical.choose_spec primitiveAlternatives).2 P₀.q₀)

theorem pc₂_nonneg : 0 ≤ pc₂ :=
  (Classical.choose_spec ((Classical.choose_spec primitiveAlternatives).2 P₀.q₀)).1

theorem pc_altAt : AltAt pc₁ pc₂ P₀.q₀ :=
  (Classical.choose_spec ((Classical.choose_spec primitiveAlternatives).2 P₀.q₀)).2

/-- The exponent of the test of the case decision. -/
noncomputable def dpE : ℕ := caseE pc₁ pc₂ P₀.q₀

theorem cGen : GeneralSolver (cProg mainGObjF fc11SojF) asmF.solve :=
  Solved.generalSolver finalProg_solved

/-- The constant `a` of the general solver. -/
noncomputable def sa : ℝ := Classical.choose cGen

/-- The constant `K` of the general solver. -/
noncomputable def sK : ℕ := Classical.choose (Classical.choose_spec cGen)

/-- The exponent of the general solver. -/
noncomputable def sd : ℕ := Classical.choose (Classical.choose_spec (Classical.choose_spec cGen))

theorem sa_nonneg : 0 ≤ sa :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec cGen))).1

theorem dp_solver {h : JohnsonRecognition} {D : ℕ} : GenSolverAt (degProg h dpE D) 0 sa sK sd :=
  fun S k e c hc v hv =>
    ((Classical.choose_spec (Classical.choose_spec (Classical.choose_spec cGen))).2 S k e c hc v
      hv).of_sub cProg_sub_degProg

/-! ### The code -/

/-- **The code of the degree algorithm** in `degProg h dpE D`. -/
noncomputable def dp_degCode (h : JohnsonRecognition) (D : ℕ) :
    DegCode (degProg h dpE D) D GI.Proved.pointwiseStab GI.Proved.preimage
      GI.Proved.normalizedFactor GI.Proved.minimalBlocks GI.Proved.groupOrder h GI.Proved.preimage
      GI.Proved.membership pc₁ pc₂ dpXw sa sK sd where
  I := mI
  contD := dgb 0
  transD := dgb 3
  giantD := dgb 20
  F₀ := asmF
  F := degF
  fs := 0
  cd Nm := dp_contCode mI Nm
  rc Nm := dp_resetCode mI Nm
  ht Nm := dp_transCode mI Nm
  gc Nm := dp_giantCode Nm
  solver := dp_solver
  hf₁ _ := rfl
  hf₂ _ := rfl
  hf₃ _ := rfl
  hE _ := rfl
  hlab _ _ _ _ hl := hl
  hlabW _ _ := le_rfl
  root := dp_rootCode
  root_fs := rfl
  root_cont := rfl

/-- **The root of `degProg`**, with constants that do not depend on `D`. -/
theorem dp_root (h : JohnsonRecognition) :
    ∃ (C : ℝ) (K m : ℕ), 0 ≤ C ∧ ∀ D : ℕ, 6 ≤ D →
      ∀ {Ω C' : Type} [Finite Ω] (S : State Ω C') (k : ℕ) (e : Ω ≃ Fin k) (c : C' → ℕ),
        Function.Injective c → GammaHat D S.G → S.size = k → ∀ v : Val, StateVal e c v S →
        FunAll (degProg h dpE D) (dgb 40) v fun u cost => AnsC e u S.answer ∧
          (cost : ℝ) ≤ Real.exp (C * Real.log ((k : ℝ) + 2) * Real.log ((D : ℝ) + 2)) * K *
            ((v.wt : ℝ) + 1) ^ m := by
  obtain ⟨C, K, m, hC, hr⟩ := degree_root GI.Proved.pointwiseStab GI.Proved.preimage
    GI.Proved.normalizedFactor GI.Proved.minimalBlocks GI.Proved.groupOrder h GI.Proved.preimage
    GI.Proved.membership pc₁_nonneg pc₂_nonneg pc_altAt sK sd sa_nonneg dpXw_pbu
  exact ⟨C, K, m, hC, fun D hD => hr _ D (dp_degCode h D) hD⟩

end GI.Degree
