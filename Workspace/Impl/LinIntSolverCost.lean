module

public import Workspace.Impl.LinIntPoly

@[expose] public section

/-! A uniform K (weight+1)^D bound for the complete Hermite row solver. -/
namespace GI.Impl
open GI.Cited GI.Lang
set_option maxRecDepth 16000
set_option maxHeartbeats 5000000

theorem linRowMulCost_mono_all {W V r s c t : ℕ}
    (hW : W ≤ V) (hr : r ≤ s) (hc : c ≤ t) :
    linRowMulCost W r c ≤ linRowMulCost V s t := by
  simp only [linRowMulCost, linRowMulStepCost, linRowMulEntryWt, linRowMulDotIn,
    linRowMulColWt, linRowMulColIn, linColumnCost, linDotLoopCost, linDotStepCost,
    linDotProductWt, linDotAccWt, linVectorAccWt]
  gcongr

/-- The deterministic Hermite stages increase monotonically with all size bounds. -/
theorem linHermiteLiftCost_mono_all {W V r s : ℕ} (hW : W ≤ V) (hr : r ≤ s) :
    linHermiteLiftCost W r ≤ linHermiteLiftCost V s := by
  have hp : linHermiteLiftPadCost W r ≤ linHermiteLiftPadCost V s := by
    unfold linHermiteLiftPadCost linPadCost; gcongr
  have ha : linHermiteLiftRowArg W r ≤ linHermiteLiftRowArg V s := by
    unfold linHermiteLiftRowArg; omega
  have hm := linRowMulCost_mono_all ha hr hr
  unfold linHermiteLiftCost linHermiteLiftRowCost
  omega

theorem linHermiteFinishCost_mono_all {W V r s c t B D C E : ℕ}
    (hW : W ≤ V) (hr : r ≤ s) (hc : c ≤ t) (hB : B ≤ D) (hC : C ≤ E) :
    linHermiteFinishCost W r c B C ≤ linHermiteFinishCost V s t D E := by
  have ht := linTakeCost_mono (show linHermiteFinishArg W ≤ linHermiteFinishArg V by
    unfold linHermiteFinishArg; omega)
  have htri := linTriCost_mono hc hB hC
  have ha : linHermiteFinishLiftArg W r c B C ≤ linHermiteFinishLiftArg V s t D E := by
    unfold linHermiteFinishLiftArg; omega
  have hl := linHermiteLiftCost_mono_all ha hr
  unfold linHermiteFinishCost
  omega

/-- Fixed polynomial arguments may be substituted into a uniform bound. -/
theorem linPoly_subst {f g₁ g₂ g₃ : ℕ → ℕ → ℕ → ℕ}
    (hf : PBU f) (h₁ : PBU g₁) (h₂ : PBU g₂) (h₃ : PBU g₃) :
    PBU (fun k W B => f (g₁ k W B) (g₂ k W B) (g₃ k W B)) := by
  obtain ⟨C, D, h⟩ := hf
  exact (PBU.smul C (PBU.pow (PBU.addc (PBU.add (PBU.add h₂ h₃) h₁) 2) D)).mono
    (fun _ _ _ => h _ _ _)

theorem linHermiteFinishCost_poly_comp {a r c b d : ℕ → ℕ → ℕ → ℕ}
    (ha : PBU a) (hr : PBU r) (hc : PBU c) (hb : PBU b) (hd : PBU d) :
    PBU (fun k W B => linHermiteFinishCost (a k W B) (r k W B) (c k W B) (b k W B) (d k W B)) := by
  have htri := linPoly_subst linTriCost_poly hc hb hd
  have htakeBase : PBU (fun _ W _ => linTakeCost W) := by unfold linTakeCost; norm_poly
  have htake := linPoly_subst htakeBase (PBU.const 0) (PBU.smul 10 (PBU.addc ha 1)) (PBU.const 0)
  have hlift := linPoly_subst linHermiteLiftCost_poly hr
    (PBU.smul 10 (PBU.addc (PBU.add (PBU.add ha hr) htri) 1)) (PBU.const 0)
  exact PBU.smul 1000 (PBU.addc (PBU.add (PBU.add (PBU.add (PBU.add ha hr) htake) htri) hlift) 1)

noncomputable def linRowSolverHermiteBudget (h : HermiteFullRank) (W : ℕ) : ℕ :=
  4 * linMatrixWt W W (W ^ linHermiteDegree h) + 6

noncomputable def linRowSolverBudget (h : HermiteFullRank) (W : ℕ) : ℕ :=
  let H := linRowSolverHermiteBudget h W
  1000 * (W + W + ((linHermitePrim h).boundSize W + W + H + 2) + H +
    linHermiteFinishCost (10 * (W + H + W + 1)) W W (W ^ linHermiteDegree h) W + 1)

theorem linRowSolverBudget_poly (h : HermiteFullRank) : PBU (fun _ W _ => linRowSolverBudget h W) := by
  have hh : PBU (fun _ W _ => linRowSolverHermiteBudget h W) := by
    unfold linRowSolverHermiteBudget linMatrixWt
    norm_poly
  have hp : PBU (fun _ W _ => (linHermitePrim h).boundSize W) := by
    unfold Prim.boundSize
    norm_poly
  have harg := PBU.smul 10 (PBU.addc (PBU.add (PBU.add PBU.W hh) PBU.W) 1)
  have hfin := linHermiteFinishCost_poly_comp harg PBU.W PBU.W
    (PBU.pow PBU.W (linHermiteDegree h)) PBU.W
  exact PBU.smul 1000 (PBU.addc (PBU.add (PBU.add
    (PBU.add (PBU.add PBU.W PBU.W) (PBU.addc (PBU.add (PBU.add hp PBU.W) hh) 2)) hh) hfin) 1)

/-- Dense full-column-rank input bounds both dimensions, all source bit bounds,
and the primitive's input size. -/
theorem linRowSolverCost_le (h : HermiteFullRank) (I : FullRankInst) (w : Fin I.c → ℤ) :
    linRowSolverCost h I (Val.list [fullRankInput I, linVecVal w]).wt ≤
      linRowSolverBudget h (Val.list [fullRankInput I, linVecVal w]).wt := by
  let W := (Val.list [fullRankInput I, linVecVal w]).wt
  have wi : (fullRankInput I).wt ≤ W := (wt_le_wt_list (by simp)).le
  have wm : (encIntMatrix I.A).wt < (fullRankInput I).wt := wt_le_wt_list (by simp [fullRankInput])
  have hr : I.r ≤ W := by
    have hl := length_lt_wt_list ((List.finRange I.r).map fun i => linVecVal (I.A i))
    simp only [List.length_map, List.length_finRange] at hl
    exact (hl.trans wm).le.trans wi
  have hc : I.c ≤ W := I.c_le.trans hr
  have hs : (fullRankInput I).cells.length ≤ W := (fullRankInput I).size_le_wt.trans wi
  have hbits : (fullRankInput I).cells.length ^ linHermiteDegree h ≤ W ^ linHermiteDegree h :=
    Nat.pow_le_pow_left hs _
  have hmat : linMatrixWt I.r I.r ((fullRankInput I).cells.length ^ linHermiteDegree h) ≤
      linMatrixWt W W (W ^ linHermiteDegree h) := by unfold linMatrixWt; gcongr
  have hmat' : linMatrixWt I.r I.c ((fullRankInput I).cells.length ^ linHermiteDegree h) ≤
      linMatrixWt W W (W ^ linHermiteDegree h) := by unfold linMatrixWt; gcongr
  have hh : linHermiteWt (linHermiteDegree h) I ≤ linRowSolverHermiteBudget h W := by
    unfold linHermiteWt linRowSolverHermiteBudget
    omega
  have hp := (linHermitePrim h).bound_le hs
  have hcall : linHermiteCost h I ≤ (linHermitePrim h).boundSize W + W + linRowSolverHermiteBudget h W + 2 := by
    unfold linHermiteCost
    omega
  have harg : linRowSolverArg h I W ≤ 10 * (W + linRowSolverHermiteBudget h W + W + 1) := by
    unfold linRowSolverArg
    omega
  have hfin := linHermiteFinishCost_mono_all harg hr hc hbits (le_refl W)
  change linRowSolverCost h I W ≤ linRowSolverBudget h W
  unfold linRowSolverCost linRowSolverBudget linRowSolverFinishCost
  dsimp only
  omega

/-- The end-to-end solver's explicit bound is polynomial in the input bit weight,
with constants depending only on the cited Hermite algorithm. -/
theorem linRowSolverCost_poly (h : HermiteFullRank) :
    ∃ K D : ℕ, ∀ (I : FullRankInst) (w : Fin I.c → ℤ),
      linRowSolverCost h I (Val.list [fullRankInput I, linVecVal w]).wt ≤
        K * ((Val.list [fullRankInput I, linVecVal w]).wt + 1) ^ D := by
  obtain ⟨K, D, hb⟩ := linRowSolverBudget_poly h
  refine ⟨K * 2 ^ D, D, fun I w => ?_⟩
  let W := (Val.list [fullRankInput I, linVecVal w]).wt
  have h := hb 0 W 0
  change linRowSolverBudget _ W ≤ K * (W + 0 + 0 + 2) ^ D at h
  calc
    _ ≤ linRowSolverBudget _ W := linRowSolverCost_le _ I w
    _ ≤ K * (W + 2) ^ D := by simpa using h
    _ ≤ K * (2 * (W + 1)) ^ D := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) D)
    _ = (K * 2 ^ D) * (W + 1) ^ D := by rw [mul_pow]; ring

end GI.Impl
