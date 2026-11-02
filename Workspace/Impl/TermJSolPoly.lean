import Workspace.Impl.TermJSolKer

/-!
# Polynomial bounds for the zero-sum solve and the coefficient kernel

Both budgets are fixed polynomials in the input weight, with constants that depend only on
the cited Hermite algorithm (`tmJSolSolveBudget_poly`, `tmJSolKerBudget_poly`). The final
statements `tmJSol_solve_spec_poly` and `tmJSol_ker_spec_poly` give a bound `K * (W + 1) ^ D`.
-/

namespace GI.Impl
open GI.Lang
open GI.Cited (Val encInt encIntMatrix FullRankInst fullRankInput)
open _root_.Matrix
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

theorem tmJSolDropCost_poly : PBU (fun _ W _ => tmJSolDropCost W) := by
  unfold tmJSolDropCost; norm_poly

theorem tmJSolStack_poly : PBU (fun _ W _ => tmJSolStackCost W + tmJSolStackWt W) := by
  unfold tmJSolStackCost tmJSolStackWt; norm_poly

theorem tmJSolScale_poly : PBU (fun _ W _ => linVectorScaleCost (2 * W + 86) W) := by
  simp only [linVectorScaleCost, linVectorAccWt, linIntBinaryCost, linIntCoreBudget,
    linIntPartsCost, linIntCodecCost]
  norm_poly

theorem tmJSolRsIn_poly : PBU (fun _ W _ => tmJSolNegWt W + tmJSolRsIn W) := by
  unfold tmJSolRsIn tmJSolNegWt tmJSolStackWt; norm_poly

theorem tmJSolSolveBudget_poly (hH : GI.Cited.HermiteFullRank) :
    PBU (fun _ W _ => tmJSolSolveBudget hH W) := by
  have hin : PBU (fun _ W _ => tmJSolRsIn W) := tmJSolRsIn_poly.mono fun _ _ _ => by omega
  have hrs : PBU (fun _ W _ => tmJSolRsB hH W) :=
    linPoly_subst (linRowSolverBudget_poly hH) (PBU.const 0) hin (PBU.const 0)
  have hdi : PBU (fun _ W _ => tmJSolDropIn hH W) := by
    unfold tmJSolDropIn
    exact PBU.addc (PBU.smul 2 (PBU.add (PBU.addc PBU.W 2) hrs)) 6
  have hdc : PBU (fun _ W _ => tmJSolDropCost (tmJSolDropIn hH W)) :=
    linPoly_subst tmJSolDropCost_poly (PBU.const 0) hdi (PBU.const 0)
  have h := PBU.smul 1000 (PBU.addc (PBU.add (PBU.add (PBU.add (PBU.add (PBU.add (PBU.add
    PBU.W tmJSolStack_poly) tmJSolScale_poly) tmJSolRsIn_poly) hrs) hdi) hdc) 1)
  refine h.mono fun _ W _ => ?_
  unfold tmJSolSolveBudget
  omega

theorem tmJSolKerBudget_poly (hH : GI.Cited.HermiteFullRank) :
    PBU (fun _ W _ => tmJSolKerBudget hH W) := by
  have hsw : PBU (fun _ W _ => tmJSolStackWt W) := by unfold tmJSolStackWt; norm_poly
  have hherBase : PBU (fun _ X _ => tmJSolHerCost hH X) := by
    unfold tmJSolHerCost Prim.boundSize linRowSolverHermiteBudget linMatrixWt
    norm_poly
  have hhb : PBU (fun _ W _ => tmJSolKerHB hH W) :=
    linPoly_subst hherBase (PBU.const 0) hsw (PBU.const 0)
  have hdi : PBU (fun _ W _ => tmJSolKerDI hH W) := by
    unfold tmJSolKerDI
    exact PBU.addc (PBU.smul 2 (PBU.add (PBU.addc PBU.W 2) hhb)) 6
  have hdc : PBU (fun _ W _ => tmJSolDropCost (tmJSolKerDI hH W)) :=
    linPoly_subst tmJSolDropCost_poly (PBU.const 0) hdi (PBU.const 0)
  have how : PBU (fun _ W _ => tmJSolKerOW hH W) := by
    unfold tmJSolKerOW
    exact PBU.addc (PBU.add (PBU.smul 2 (PBU.mul PBU.W hhb)) PBU.W) 4
  have hmc : PBU (fun _ W _ => tmJSolKerMC hH W) := by
    unfold tmJSolKerMC
    exact PBU.add (PBU.mul PBU.W hdc)
      (PBU.mul (PBU.smul mapK (PBU.addc PBU.W 1)) (PBU.addc (PBU.add hdi how) 1))
  have h := PBU.smul 1000 (PBU.addc (PBU.add (PBU.add (PBU.add (PBU.add (PBU.add (PBU.add
    PBU.W tmJSolStack_poly) hhb) hdi) hdc) how) hmc) 1)
  refine h.mono fun _ W _ => ?_
  unfold tmJSolKerBudget
  omega

/-- From a uniform polynomial bound to the form `K * (W + 1) ^ D`. -/
theorem tmJSol_pbu_pow {f : ℕ → ℕ} (h : PBU (fun _ W _ => f W)) :
    ∃ K D : ℕ, ∀ W, f W ≤ K * (W + 1) ^ D := by
  obtain ⟨K, D, hb⟩ := h
  refine ⟨K * 2 ^ D, D, fun W => ?_⟩
  have h := hb 0 W 0
  change f W ≤ K * (W + 0 + 0 + 2) ^ D at h
  calc
    f W ≤ K * (W + 2) ^ D := by simpa using h
    _ ≤ K * (2 * (W + 1)) ^ D := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) D)
    _ = (K * 2 ^ D) * (W + 1) ^ D := by rw [mul_pow]; ring

/-- **The zero-sum solve in polynomial time.** On `[encIntMatrix M, encIntMatrix B, linVecVal s]`
with `M` nonsingular, the entry `b` of `tmJSolFuns b j` returns `.list [.nat 1, linVecVal c]`
with `s + c ᵥ* B + y ᵥ* M = 0` for some `y`, or `.nat 0` when no such `c` exists. -/
theorem tmJSol_solve_spec_poly (hH : GI.Cited.HermiteFullRank) :
    ∃ K D : ℕ, ∀ {P : Program} {b j : ℕ}, P.HasAt b (tmJSolFuns b j) →
      P.prims[j]? = some (linHermitePrim hH) →
      ∀ {t G : ℕ} (_ : 0 < t) (M : Matrix (Fin t) (Fin t) ℤ) (_ : M.det ≠ 0)
        (B : Matrix (Fin G) (Fin t) ℤ) (s : Fin t → ℤ),
        FunAll P b (.list [encIntMatrix M, encIntMatrix B, linVecVal s]) (fun out cost =>
          tmJSolSolveAnswer M B s out ∧
          cost ≤ K * ((Val.list [encIntMatrix M, encIntMatrix B, linVecVal s]).wt + 1) ^ D) := by
  obtain ⟨K, D, hb⟩ := tmJSol_pbu_pow (tmJSolSolveBudget_poly hH)
  exact ⟨K, D, fun {P} {b} {j} hP hj {t} {G} ht M hM B s =>
    (tmJSol_solve_spec hH (tmJSolAt.of_hasAt hP) hj ht M hM B s).mono
      fun _ _ h => ⟨h.1, h.2.trans (hb _)⟩⟩

/-- **The coefficient kernel in polynomial time.** On `[encIntMatrix M, encIntMatrix B]` with `M`
nonsingular, the entry `b + 1` of `tmJSolFuns b j` returns `encIntMatrix K` whose rows generate
the subgroup `{c | ∃ y, c ᵥ* B + y ᵥ* M = 0}` of `Fin G → ℤ`. -/
theorem tmJSol_ker_spec_poly (hH : GI.Cited.HermiteFullRank) :
    ∃ K D : ℕ, ∀ {P : Program} {b j : ℕ}, P.HasAt b (tmJSolFuns b j) →
      P.prims[j]? = some (linHermitePrim hH) →
      ∀ {t G : ℕ} (_ : 0 < t) (M : Matrix (Fin t) (Fin t) ℤ) (_ : M.det ≠ 0)
        (B : Matrix (Fin G) (Fin t) ℤ),
        FunAll P (b + 1) (.list [encIntMatrix M, encIntMatrix B]) (fun out cost =>
          tmJSolKerAnswer M B out ∧
          cost ≤ K * ((Val.list [encIntMatrix M, encIntMatrix B]).wt + 1) ^ D) := by
  obtain ⟨K, D, hb⟩ := tmJSol_pbu_pow (tmJSolKerBudget_poly hH)
  exact ⟨K, D, fun {P} {b} {j} hP hj {t} {G} ht M hM B =>
    (tmJSol_ker_spec hH (tmJSolAt.of_hasAt hP) hj ht M hM B).mono
      fun _ _ h => ⟨h.1, h.2.trans (hb _)⟩⟩

end GI.Impl
