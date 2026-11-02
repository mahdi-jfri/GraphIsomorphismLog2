import Workspace.Impl.TermGlueLabNSet
import Workspace.Impl.TermGlueLabNM6
import Workspace.Impl.TermGlueLabNCmp
import Workspace.Impl.TermGlueLabPPolyO
import Workspace.Impl.TermGlueLabSVPoly
import Workspace.Impl.TermGlueLabSPoly

/-!
# The label driver: the costs of the callees are polynomial

The ten callee contracts of `tmGLN_ne_spec` come with the costs of the modules
(`tmGLN_front_ok`, `tmGLN_m5_ok`, `tmGLN_vecm_ok`, `tmGLN_m6_ok`). Each of them is bounded by a
polynomial (`TmGLNPoly`). The bounds are composed from the `PBU` lemmas of the callees
(`TermGlueLabPPolyO`, `TermGlueLabSVPoly`, `TermGlueLabSPoly`) with `tmGLP_pbu_subst` and
`linPoly_subst`, and turned into `TmGLNPoly` by `tmGLN_poly_of_pbu`.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang
open GI.Cited (PointwiseStab Membership NormalizedFactor ConstructiveMembership GroupOrder
  HermiteFullRank SmithNonsingular VectorStabilizer)

/-- A cost polynomial in the second slot of `PBU` is polynomial in the sense of `TmGLNPoly`. -/
theorem tmGLN_poly_of_pbu {f : ℕ → ℕ} (h : PBU fun _ W _ => f W) : TmGLNPoly f := by
  obtain ⟨C, D, hC⟩ := h
  refine ⟨C * 2 ^ D, D, fun W => ?_⟩
  have h1 : f W ≤ C * (W + 0 + 0 + 2) ^ D := hC 0 W 0
  have h2 : (W + 0 + 0 + 2) ^ D ≤ (2 * (W + 1)) ^ D := Nat.pow_le_pow_left (by omega) D
  show f W ≤ C * 2 ^ D * (W + 1) ^ D
  rw [Nat.mul_assoc, ← Nat.mul_pow]
  exact h1.trans (Nat.mul_le_mul_left C h2)

/-- The cost of the two `mkGroup` calls. -/
theorem tmGLN_mkC_poly : TmGLNPoly fun B => mkGroupK * ((B + 2) * (B + 1)) ^ 3 :=
  tmGLN_poly_of_pbu (PBU.smul _ (PBU.pow (PBU.mul (PBU.addc PBU.W 2) (PBU.addc PBU.W 1)) 3))

/-- The cost of the lift context. -/
theorem tmGLN_lcC_poly (hst : PointwiseStab) : TmGLNPoly fun B => tmGLPLcC hst (3 * B + 2) :=
  tmGLN_poly_comp (tmGLN_poly_of_pbu (tmGLPLcC_poly hst)) (tmGLN_poly_of_pbu (tmGLP_pbu_aff 3 2))

/-- The cost of one lift. -/
theorem tmGLN_l1C_poly (pf : Prim) : TmGLNPoly fun B => tmGLPL1C pf (4 * B + 2) :=
  tmGLN_poly_comp (tmGLN_poly_of_pbu (tmGLPL1C_poly pf)) (tmGLN_poly_of_pbu (tmGLP_pbu_aff 4 2))

theorem tmGLN_xC_poly : TmGLNPoly tmGLPXLabC := tmGLN_poly_of_pbu tmGLPXLabC_poly

theorem tmGLN_bsC_poly : TmGLNPoly tmGLPBsC := tmGLN_poly_of_pbu tmGLPBsC_poly

/-- The cost of the labels of `y'`. -/
theorem tmGLN_yC_poly (pm pf : Prim) : TmGLNPoly (tmGLPYLabC pm pf) := by
  have hF : PBU fun _ W _ => tmGLPFindC pm pf (20 * W + 40) :=
    tmGLP_pbu_subst (f := fun _ W _ => tmGLPFindC pm pf W) (tmGLPFindC_poly pm pf)
      (tmGLP_pbu_aff 20 40)
  exact tmGLN_poly_of_pbu ((PBU.add (PBU.mul (PBU.addc PBU.W 1)
    (PBU.add (PBU.smul 2 hF) (PBU.smul (10 ^ 4) (tmGLP_pbu_pw 3))))
    (PBU.smul (10 ^ 6) (tmGLP_pbu_pw 4))).mono fun _ _ _ => le_of_eq rfl)

/-- The cost of step 4. -/
theorem tmGLN_supC_poly (K D : ℕ) : TmGLNPoly (tmGLPSupC K D) :=
  tmGLN_poly_of_pbu ((PBU.add (PBU.smul 3 (PBU.smul K (PBU.pow (PBU.smul (10 ^ 4)
    (tmGLP_pbu_pw 6)) D))) (PBU.smul (10 ^ 9) (tmGLP_pbu_pw 8))).mono fun _ _ _ => le_of_eq rfl)

/-- The cost of the vector module. -/
theorem tmGLN_vecC_poly (Cs Ds Cv Dv : ℕ) : TmGLNPoly (tmGLNVecC Cs Ds Cv Dv) := by
  have hT : PBU fun _ W _ => linTailCost W := by
    unfold linTailCost; exact PBU.smul _ (tmGLP_pbu_pw 3)
  have hV : PBU fun _ W _ => tmGLSVecC Cs Ds Cv Dv (10 * W + 18) :=
    tmGLP_pbu_subst (f := fun _ W _ => tmGLSVecC Cs Ds Cv Dv W) (tmGLSVecC_poly Cs Ds Cv Dv)
      (tmGLP_pbu_aff 10 18)
  have hP : PBU fun _ W _ => tmGLSPtC Cs Ds Cv Dv (30 * W + 8 * linTailCost W + 50) :=
    tmGLP_pbu_subst (f := fun _ W _ => tmGLSPtC Cs Ds Cv Dv W) (tmGLSPtC_poly Cs Ds Cv Dv)
      (g := fun _ W _ => 30 * W + 8 * linTailCost W + 50)
      (PBU.addc (PBU.add (PBU.smul 30 PBU.W) (PBU.smul 8 hT)) 50)
  exact tmGLN_poly_of_pbu ((PBU.addc (PBU.add (PBU.smul 10 PBU.W) (PBU.smul 4 (PBU.add
    (PBU.smul 300 (PBU.addc (PBU.add (PBU.smul 5 PBU.W) hV) 10))
    (PBU.smul (10 ^ 4) (PBU.addc (PBU.add (PBU.add PBU.W hT) hP) 2))))) 50).mono
    fun _ _ _ => le_of_eq rfl)

/-- The cost of the step-6 module. -/
theorem tmGLN_s6C_poly (Ka Da c kp : ℕ) : TmGLNPoly fun B => tmGLS6C Ka Da c kp (B + 1) B := by
  have h : PBU fun k W _ => tmGLS6C Ka Da c kp (W + 1) W :=
    linPoly_subst (f := fun _ W B => tmGLS6C Ka Da c kp B W) (g₁ := fun k _ _ => k)
      (g₂ := fun _ W _ => W) (g₃ := fun _ W _ => W + 1) (tmGLS6C_poly Ka Da c kp) PBU.k PBU.W
      (PBU.addc PBU.W 1)
  exact tmGLN_poly_of_pbu h

/-! ### Step 5 -/

/-- The item bound of step 5, with the lift bound of weight `B` in the third slot. -/
private theorem tmGLN_s5G_poly (pm pf : Prim) (Cs Ds Cv Dv Cc Dc Cm Dm : ℕ) :
    PBU fun _ W B => tmGLNS5G pm pf Cs Ds Cv Dv Cc Dc Cm Dm B W := by
  have hY : PBU fun _ _ B => tmGLPL1C pf (4 * B) :=
    linPoly_subst (f := fun _ M _ => tmGLPL1C pf M) (g₁ := fun k _ _ => k)
      (g₂ := fun _ _ B => 4 * B) (g₃ := fun _ _ B => B) (tmGLPL1C_poly pf) PBU.k
      (PBU.smul 4 PBU.B) PBU.B
  exact linPoly_subst (f := fun _ W Y => tmGLPGenC pm pf Y Cs Ds Cv Dv Cc Dc Cm Dm W)
    (g₁ := fun k _ _ => k) (g₂ := fun _ W _ => W) (g₃ := fun _ _ B => tmGLPL1C pf (4 * B))
    (tmGLPGenC_poly pm pf Cs Ds Cv Dv Cc Dc Cm Dm) PBU.k PBU.W hY

/-- The orientation bound of step 5, with the number of rows `B` in the third slot. -/
private theorem tmGLN_s5E_poly (pm pf : Prim) : PBU fun _ W B => tmGLPEpsC pm pf B W :=
  linPoly_subst (f := fun q W _ => tmGLPEpsC pm pf q W) (g₁ := fun _ _ B => B)
    (g₂ := fun _ W _ => W) (g₃ := fun _ _ _ => 0) (tmGLPEpsC_poly pm pf) PBU.B PBU.W
    (PBU.const 0)

/-- The cost of step 5 in two slots: the input weight `W` and the bound `B`. -/
private theorem tmGLN_s5Cost2_poly (pm pf : Prim) {FA FQ FI : ℕ → ℕ}
    (hFA : PBU fun _ W _ => FA W) (hFQ : PBU fun _ W _ => FQ W) (hFI : PBU fun _ W _ => FI W)
    (Ce De Cs Ds Cv Dv Cc Dc Cm Dm : ℕ) :
    PBU fun _ W B => tmGLNS5C W
      (tmGLPStep5OC (tmGLPStep5C (tmGLPSetDC FA FQ FI Ce De)
        (tmGLPGenOC (tmGLNS5G pm pf Cs Ds Cv Dv Cc Dc Cm Dm B) (tmGLPEpsC pm pf B)) W) W)
      (tmGLPStep5C (tmGLPSetDC FA FQ FI Ce De) (tmGLNS5G pm pf Cs Ds Cv Dv Cc Dc Cm Dm B) W) := by
  have hS : PBU fun _ W _ => tmGLPSetDC FA FQ FI Ce De W := tmGLPSetDC_poly hFA hFQ hFI Ce De
  have hG := tmGLN_s5G_poly pm pf Cs Ds Cv Dv Cc Dc Cm Dm
  have hO : PBU fun _ W B =>
      tmGLPGenOC (tmGLNS5G pm pf Cs Ds Cv Dv Cc Dc Cm Dm B) (tmGLPEpsC pm pf B) W :=
    tmGLPGenOC_poly (G := fun _ W B => tmGLNS5G pm pf Cs Ds Cv Dv Cc Dc Cm Dm B W)
      (Ep := fun _ W B => tmGLPEpsC pm pf B W) hG (tmGLN_s5E_poly pm pf)
  have hPo : PBU fun _ W B => tmGLPStep5C (tmGLPSetDC FA FQ FI Ce De)
      (tmGLPGenOC (tmGLNS5G pm pf Cs Ds Cv Dv Cc Dc Cm Dm B) (tmGLPEpsC pm pf B)) W :=
    tmGLPStep5C_poly (SC := fun _ W _ => tmGLPSetDC FA FQ FI Ce De W)
      (G := fun _ W B => tmGLPGenOC (tmGLNS5G pm pf Cs Ds Cv Dv Cc Dc Cm Dm B)
        (tmGLPEpsC pm pf B) W) hS hO
  have hOr := tmGLPStep5OC_poly hPo
  have hPl : PBU fun _ W B => tmGLPStep5C (tmGLPSetDC FA FQ FI Ce De)
      (tmGLNS5G pm pf Cs Ds Cv Dv Cc Dc Cm Dm B) W :=
    tmGLPStep5C_poly (SC := fun _ W _ => tmGLPSetDC FA FQ FI Ce De W)
      (G := fun _ W B => tmGLNS5G pm pf Cs Ds Cv Dv Cc Dc Cm Dm B W) hS hG
  exact (PBU.addc (PBU.add (PBU.smul 4000 (tmGLP_pbu_pw 2)) (PBU.smul 4 (PBU.add hOr hPl)))
    100).mono fun _ _ _ => le_of_eq rfl

/-- The cost of step 5 is polynomial when `FA FQ FI` are. -/
theorem tmGLN_s5Cost_poly (pm pf : Prim) {FA FQ FI : ℕ → ℕ}
    (hFA : PBU fun _ W _ => FA W) (hFQ : PBU fun _ W _ => FQ W) (hFI : PBU fun _ W _ => FI W)
    (Ce De Cs Ds Cv Dv Cc Dc Cm Dm : ℕ) :
    TmGLNPoly (tmGLNS5Cost pm pf FA FQ FI Ce De Cs Ds Cv Dv Cc Dc Cm Dm) := by
  have h := tmGLN_s5Cost2_poly pm pf hFA hFQ hFI Ce De Cs Ds Cv Dv Cc Dc Cm Dm
  have h' := linPoly_subst (g₁ := fun k _ _ => k) (g₂ := fun _ W _ => W) (g₃ := fun _ W _ => W)
    h PBU.k PBU.W PBU.W
  exact tmGLN_poly_of_pbu (f := tmGLNS5Cost pm pf FA FQ FI Ce De Cs Ds Cv Dv Cc Dc Cm Dm) h'

/-- The cost of the step-5 module with the setup module. -/
theorem tmGLN_m5C_poly (hm : Membership) (hfac : NormalizedFactor) (hcm : ConstructiveMembership)
    (ho : GroupOrder) (hH : HermiteFullRank) (hS : SmithNonsingular) :
    TmGLNPoly (tmGLNM5C hm hfac hcm (tmGLNFA ho hcm) (tmGLNFQ hH hS) (tmGLNFI hH)) :=
  tmGLN_s5Cost_poly _ _ (tmGLNFA_poly ho hcm) (tmGLNFQ_poly hH hS) (tmGLNFI_poly hH) _ _ _ _ _ _
    _ _ _ _

end GI.Impl
