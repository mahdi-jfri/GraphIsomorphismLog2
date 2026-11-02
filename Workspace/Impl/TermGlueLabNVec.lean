import Workspace.Impl.TermGlueLabNVecP
import Workspace.Impl.TermGlueLabNLink

/-!
# The vector wrapper of the label driver meets its contract

Proof of Theorem A.23, step 6. The wrapper `tmGLNVecFuns` (file
`TermGlueLabNVecP.lean`) returns `[E(p_{y'}), E(p_x)]` for the context of step 5
(`tmGLN_vec_ok : Iface.TmGLNVecOK`).

The target `y'` here is the one the label driver works with: row `i` is `y_i^{(y i)⁻¹}`, with
`y` the program's own lift of `τ` (`tmGLPL1_spec`). Two facts link it to the target
`tmGLAlign I τ` of step 6, which is aligned by `rowLift`:
* `tmGLN_align_types`: it has the type multiset of `x`. The two lifts differ by a zero-sum
  `N`-tuple (`tmGLP_lift_zero`), so the rows differ by elements of `N`, and `tmGLAlign I τ`
  has the types of `x` (`tmGL_align_types`).
* its label and label point are those of `tmGLAlign I τ` (`tmGLN_lab_align`, `tmGLP_align_any`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Multicoset GI.Lang GI.Paper Equiv
open GI.Cited (Val encPerm encGroup encIntMatrix gens encInt)

attribute [local instance] stringRAct

section Types

variable {Ω C : Type} {Pp : Params} {S : State Ω C} {L : GiantLabels S}

/-- **The program-aligned target has the types of `x`.** -/
theorem tmGLN_align_types {I : RowTerminal Pp S L} {r τ : Perm I.B} (hτ : τ ∈ tmGlRes I r)
    {y : Fin L.q → Perm I.B} (hy : cleanRowPerm I.e y ∈ S.domGroup) (hy0 : y I.i0 = τ) :
    types I.Nb (rowAct (fun i => (y i)⁻¹) 1 (rowTuple I.e S.y)) =
      types I.Nb (rowTuple I.e S.x) := by
  have hτH : τ ∈ I.Hb := hτ.1.1
  set k := rowLift I.e I.i0 τ with hkdef
  have hμ : TmGLZero I.Nb I.φ (k⁻¹ * y) := (tmGLP_lift_zero hτH hy hy0).1
  -- `ν_i = k_i μ_i⁻¹ k_i⁻¹` is zero-sum, so its entries lie in `N`
  have hcls : ∀ i, τ⁻¹⁻¹ * (k i)⁻¹ ∈ I.Nb :=
    tmGL_cls_inv I.normalizes hτH (I.lift_mem hτH)
  have hν := tmGL_conj_zero I.normalizes (tmGL_kerI I) (I.Hb.inv_mem hτH) (e := fun i => (k i)⁻¹)
    hcls (tmGLP_zero_inv hμ) 1
  have hrow : rowAct (fun i => (y i)⁻¹) 1 (rowTuple I.e S.y) =
      rowAct (fun i => ((k i)⁻¹)⁻¹ * ((k⁻¹ * y) i)⁻¹ * (k i)⁻¹) 1 (tmGLAlign I τ) := by
    rw [tmGLAlign, ← rowAct_mul]
    congr 1
    funext i
    simp only [Pi.mul_apply, Pi.inv_apply, ← hkdef]
    group
  rw [hrow]
  simp only [Perm.one_apply] at hν
  rw [types_rowAct_J hν.1, tmGL_align_types hτ]

end Types

/-! ### Costs -/

/-- The cost bound of the vector wrapper, for an input of weight `B`. -/
def tmGLNVecC (Cs Ds Cv Dv B : ℕ) : ℕ :=
  10 * B + 4 * (300 * (5 * B + tmGLSVecC Cs Ds Cv Dv (10 * B + 18) + 10) +
    10 ^ 4 * (B + linTailCost B + tmGLSPtC Cs Ds Cv Dv (30 * B + 8 * linTailCost B + 50) + 2)) +
    50

theorem tmGLN_svecC_mono (Cs Ds Cv Dv : ℕ) {W V : ℕ} (h : W ≤ V) :
    tmGLSVecC Cs Ds Cv Dv W ≤ tmGLSVecC Cs Ds Cv Dv V := by
  have := tmGLS_mpair_mono Cs Ds Cv Dv (show 50 * (W + 1) ^ 3 ≤ 50 * (V + 1) ^ 3 by gcongr)
  unfold tmGLSVecC
  gcongr

theorem tmGLN_sptC_mono (Cs Ds Cv Dv : ℕ) {W V : ℕ} (h : W ≤ V) :
    tmGLSPtC Cs Ds Cv Dv W ≤ tmGLSPtC Cs Ds Cv Dv V := by
  have h1 := tmGLN_svecC_mono Cs Ds Cv Dv h
  have h2 := tmGLS_orC_mono h h
  unfold tmGLSPtC
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)

theorem tmGLNVecC_mono (Cs Ds Cv Dv : ℕ) {W V : ℕ} (h : W ≤ V) :
    tmGLNVecC Cs Ds Cv Dv W ≤ tmGLNVecC Cs Ds Cv Dv V := by
  have hL := linTailCost_mono h
  have h1 := tmGLN_svecC_mono Cs Ds Cv Dv (show 10 * W + 18 ≤ 10 * V + 18 by omega)
  have h2 := tmGLN_sptC_mono Cs Ds Cv Dv
    (show 30 * W + 8 * linTailCost W + 50 ≤ 30 * V + 8 * linTailCost V + 50 by omega)
  unfold tmGLNVecC
  omega

/-- The weight of the argument `[[gens N, ctx], z]` of one vector call. -/
theorem tmGLN_in_wt {vs : List Val} {gN ctx z : Val} {j : ℕ} (h1 : vs[1]? = some gN)
    (hz : vs[j]? = some z) :
    (Val.list [.list [gN, ctx], z]).wt ≤ 6 * (Val.list vs).wt + 4 * ctx.wt + 18 := by
  have wg : gN.wt < (Val.list vs).wt := by
    obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp h1
    exact wt_le_wt_list (List.getElem_mem hj)
  have wz : z.wt < (Val.list vs).wt := by
    obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hz
    exact wt_le_wt_list (List.getElem_mem hj)
  have hg := wt_list2_le gN ctx
  have hi := wt_list2_le (.list [gN, ctx]) z
  omega

end GI.Impl
