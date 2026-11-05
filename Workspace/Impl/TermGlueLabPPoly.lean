module

public import Workspace.Impl.TermGlueLabPCMat
public import Workspace.Impl.TermGlueLabPInv

@[expose] public section

/-!
# Polynomial bounds of the step 5 programs

The cost bounds of the transpose, matrix, vector, inverse, coordinate-matrix and
coordinate-sum programs are polynomial (`PBU`, proved by `norm_poly` after unfolding to
termlin's explicit cost formulas). The second argument is the input weight `W`, the first is
the matrix size `t` where the bound uses it.
-/

namespace GI.Impl

open GI.Lang

theorem tmGLPTrC_poly : PBU (fun t W _ => tmGLPTrC W t t) := by
  unfold tmGLPTrC tmGLPTrColC tmGLPColW
  dsimp only [linColumnCost, linVectorAccWt]
  norm_poly

/-- **Substitution**: a polynomial bound composed with a polynomial in the weight slot. -/
theorem tmGLP_pbu_subst {f g : ℕ → ℕ → ℕ → ℕ} (hf : PBU f) (hg : PBU g) :
    PBU (fun k W B => f k (g k W B) B) := by
  obtain ⟨C, D, hC⟩ := hf
  have h : PBU fun k W B => C * (g k W B + B + k + 2) ^ D :=
    PBU.smul C (PBU.pow (PBU.addc (PBU.add (PBU.add hg PBU.B) PBU.k) 2) D)
  exact h.mono fun k W B => hC k (g k W B) B

/-- `2 (X + f) + 6`-type weights. -/
theorem tmGLP_pbu_lin {f : ℕ → ℕ → ℕ → ℕ} (hf : PBU f) (a b c : ℕ) :
    PBU (fun k W B => a * (W + f k W B) + b * W + c) :=
  PBU.addc (PBU.add (PBU.smul a (PBU.add PBU.W hf)) (PBU.smul b PBU.W)) c

theorem tmGLPMatC1_poly : PBU (fun t W _ => tmGLPMatC1 W t) :=
  tmGLP_pbu_subst (f := fun n W _ => linMatrixMulCost W n n n) linDenseMulCost_poly
    (g := fun _ W _ => 2 * (2 * (W + W) + 6 + W) + 6) (by norm_poly)

theorem tmGLPMatC2_poly : PBU (fun t W _ => tmGLPMatC2 W t) := by
  have hg : PBU (fun t W _ => 2 * (2 * (W + tmGLPMatC1 W t) + 6 + W) + 6) :=
    (tmGLP_pbu_lin tmGLPMatC1_poly 4 2 18).mono fun _ _ _ => by omega
  exact tmGLP_pbu_subst (f := fun n W _ => linMatrixMulCost W n n n) linDenseMulCost_poly hg

theorem tmGLPMatC3_poly : PBU (fun t W _ => tmGLPMatC3 W t) := by
  have hg : PBU (fun t W _ => 2 * (W + tmGLPMatC2 W t) + 6) :=
    (tmGLP_pbu_lin tmGLPMatC2_poly 2 0 6).mono fun _ _ _ => by omega
  exact tmGLP_pbu_subst (f := fun t W _ => tmGLPTrC W t t) tmGLPTrC_poly hg

theorem tmGLPMatC4_poly : PBU (fun t W _ => tmGLPMatC4 W t) := by
  have hg : PBU (fun t W _ => 2 * (W + tmGLPMatC3 W t) + 6) :=
    (tmGLP_pbu_lin tmGLPMatC3_poly 2 0 6).mono fun _ _ _ => by omega
  exact tmGLP_pbu_subst (f := fun r W _ => linFiniteMatrixReduceCost W r)
    linFiniteMatrixReduceCost_poly hg

theorem tmGLPMatC_poly : PBU (fun t W _ => tmGLPMatC W t) := by
  have h := PBU.addc (PBU.add (PBU.add (PBU.add (PBU.add (PBU.add (PBU.smul 1000 (PBU.addc PBU.W 1))
    (PBU.smul 2 tmGLPMatC1_poly)) (PBU.smul 2 tmGLPMatC2_poly)) (PBU.smul 2 tmGLPMatC3_poly))
    (PBU.smul 2 tmGLPMatC4_poly))
    (PBU.smul 100 (PBU.add (PBU.add tmGLPMatC1_poly tmGLPMatC2_poly) tmGLPMatC3_poly))) 100
  exact h.mono fun _ _ _ => le_of_eq rfl

theorem tmGLP_mul1_poly : PBU (fun t W _ => linMatrixMulCost W 1 t t) := by
  dsimp only [linMatrixMulCost, linMatrixMulRowCost, linRowMulCost, linRowMulStepCost,
    linRowMulEntryWt, linRowMulDotIn, linRowMulColWt, linRowMulColIn, linColumnCost,
    linDotLoopCost, linDotStepCost, linDotProductWt, linDotAccWt, linVectorAccWt,
    linIntBinaryCost, linIntCoreBudget, linIntPartsCost, linIntCodecCost]
  norm_poly

theorem tmGLP_tr1_poly : PBU (fun t W _ => tmGLPTrC W 1 t) := by
  unfold tmGLPTrC tmGLPTrColC tmGLPColW
  dsimp only [linColumnCost, linVectorAccWt]
  norm_poly

theorem tmGLP_col_poly : PBU (fun t W _ => linColumnCost W t) := by
  dsimp only [linColumnCost, linVectorAccWt]
  norm_poly

theorem tmGLPVecC1_poly : PBU (fun t W _ => tmGLPVecC1 W t) :=
  tmGLP_pbu_subst (f := fun t W _ => linMatrixMulCost W 1 t t) tmGLP_mul1_poly
    (g := fun _ W _ => 2 * (2 * (W + W) + 6 + (2 * W + 6)) + 6) (by norm_poly)

theorem tmGLPVecC2_poly : PBU (fun t W _ => tmGLPVecC2 W t) := by
  have hg : PBU (fun t W _ => 2 * (W + tmGLPVecC1 W t) + 6) :=
    (tmGLP_pbu_lin tmGLPVecC1_poly 2 0 6).mono fun _ _ _ => by omega
  exact tmGLP_pbu_subst (f := fun t W _ => tmGLPTrC W 1 t) tmGLP_tr1_poly hg

theorem tmGLPVecC3_poly : PBU (fun t W _ => tmGLPVecC3 W t) := by
  have hg : PBU (fun t W _ => 2 * (W + tmGLPVecC2 W t) + 6) :=
    (tmGLP_pbu_lin tmGLPVecC2_poly 2 0 6).mono fun _ _ _ => by omega
  exact tmGLP_pbu_subst (f := fun r W _ => linFiniteMatrixReduceCost W r)
    linFiniteMatrixReduceCost_poly hg

theorem tmGLPVecC4_poly : PBU (fun t W _ => tmGLPVecC4 W t) := by
  have hg : PBU (fun t W _ => 2 * (3 + tmGLPVecC3 W t) + 6) :=
    (PBU.addc (PBU.smul 2 (PBU.addc tmGLPVecC3_poly 3)) 6).mono fun _ _ _ => by omega
  exact tmGLP_pbu_subst (f := fun t W _ => linColumnCost W t) tmGLP_col_poly hg

theorem tmGLPVecC_poly : PBU (fun t W _ => tmGLPVecC W t) := by
  have h := PBU.addc (PBU.add (PBU.add (PBU.add (PBU.add (PBU.add (PBU.smul 1000 (PBU.addc PBU.W 1))
    (PBU.smul 2 tmGLPVecC1_poly)) (PBU.smul 2 tmGLPVecC2_poly)) (PBU.smul 2 tmGLPVecC3_poly))
    (PBU.smul 2 tmGLPVecC4_poly))
    (PBU.smul 100 (PBU.add (PBU.add tmGLPVecC1_poly tmGLPVecC2_poly) tmGLPVecC3_poly))) 100
  exact h.mono fun _ _ _ => le_of_eq rfl

theorem tmGLPInvC_poly (hH : GI.Cited.HermiteFullRank) : PBU (fun _ W _ => tmGLPInvC hH W) := by
  unfold tmGLPInvC tmGLQHW linRowSolverHermiteBudget linMatrixWt Prim.boundSize
  norm_poly

/-- With `linElementBudget hm W ≤ Ce (W + 2)^De`, the coordinate costs are polynomial. -/
theorem tmGLPCMatC_poly (Ce De : ℕ) : PBU (fun _ W _ => tmGLPCMatC Ce De W) := by
  unfold tmGLPCMatC tmGLPCL tmGLPBud tmGLPColW linTailCost
  norm_poly

theorem tmGLPCSumC_poly (Ce De : ℕ) : PBU (fun _ W _ => tmGLPCSumC Ce De W) := by
  unfold tmGLPCSumC tmGLPVB tmGLPMacc tmGLPBud
  dsimp only [linVectorBinaryCost, linVectorAccWt, linIntBinaryCost, linIntCoreBudget,
    linIntPartsCost, linIntCodecCost]
  norm_poly

end GI.Impl
