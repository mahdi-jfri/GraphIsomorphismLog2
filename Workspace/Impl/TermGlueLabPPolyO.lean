module

public import Workspace.Impl.TermGlueLabPGen
public import Workspace.Impl.TermGlueLabPOEps
public import Workspace.Impl.TermGlueLabPS5O
public import Workspace.Impl.TermGlueLabPSetZ
public import Workspace.Impl.TermGlueLabPBs
public import Workspace.Impl.TermGlueLabPXLab
public import Workspace.Impl.TermGlueLabPLiftS

@[expose] public section

/-!
# Polynomial bounds of step 5 of the label program

The cost bounds of step 5 are polynomial (`PBU`). They are composed stage by stage
with `tmGLP_pbu_subst` (one callee bound at a time), since `norm_poly` is slow on the fully
unfolded nested costs.

* the transporters: `tmGLPRel2C`, `tmGLPRelC`, `tmGLPTryC`, `tmGLPFindC`, `tmGLPORowC`,
  `tmGLPOffC` (the costs of the cited primitives enter through their fixed constants `c`, `k`);
* the orientation: `tmGLPOrC`, `tmGLPEpsC` (first slot `q`, the number of rows);
* one generator: `tmGLPHalfC`, `tmGLPGenC` (third slot `Y`, the bound of one lift),
  `tmGLPGenOC` (from bounds `G`, `Ep` of its callees);
* the whole step: `tmGLPItemsC`, `tmGLPSetC`, `tmGLPSetDC`, `tmGLPStep5C`, `tmGLPStep5OC`,
  for callee bounds that are themselves `PBU` (in any of the three slots);
* the small programs: `tmGLPBsC`, `tmGLPXLabC`, and the lift bounds `tmGLPLcC`, `tmGLPL1C`
  (second slot: the size `M` of their input).
-/

namespace GI.Impl

open GI.Lang

/-- `(W + 1)^j` is polynomial. -/
theorem tmGLP_pbu_pw (j : ℕ) : PBU fun _ W _ => (W + 1) ^ j := PBU.pow (PBU.addc PBU.W 1) j

/-- `a W + c` is polynomial. -/
theorem tmGLP_pbu_aff (a c : ℕ) : PBU fun _ W _ => a * W + c := PBU.addc (PBU.smul a PBU.W) c

/-- `a (W + 1)^2` is polynomial. -/
theorem tmGLP_pbu_sq (a : ℕ) : PBU fun _ W _ => a * (W + 1) ^ 2 := PBU.smul a (tmGLP_pbu_pw 2)

/-! ### The transporters -/

theorem tmGLPRel2C_poly (pf : Prim) : PBU fun _ W _ => tmGLPRel2C pf W := by
  unfold tmGLPRel2C
  norm_poly

theorem tmGLPRelC_poly (pm pf : Prim) : PBU fun _ W _ => tmGLPRelC pm pf W := by
  have h2 := tmGLP_pbu_subst (tmGLPRel2C_poly pf) (tmGLP_pbu_sq 30)
  have h1 : PBU fun _ W _ => pm.c * (100 * (W + 1) ^ 2 + 2) ^ pm.k :=
    PBU.smul pm.c (PBU.pow (PBU.addc (tmGLP_pbu_sq 100) 2) pm.k)
  exact (PBU.add (PBU.add h1 (PBU.smul 5 h2)) (PBU.smul (10 ^ 9) (tmGLP_pbu_pw 4))).mono
    fun _ _ _ => le_of_eq rfl

theorem tmGLPTryC_poly (pm pf : Prim) : PBU fun _ W _ => tmGLPTryC pm pf W := by
  have h := tmGLP_pbu_subst (tmGLPRelC_poly pm pf) (tmGLP_pbu_aff 6 7)
  exact (PBU.add (PBU.smul 6 h) (PBU.smul (10 ^ 5) (tmGLP_pbu_pw 2))).mono
    fun _ _ _ => le_of_eq rfl

theorem tmGLPFindC_poly (pm pf : Prim) : PBU fun _ W _ => tmGLPFindC pm pf W := by
  have h := tmGLP_pbu_subst (tmGLPTryC_poly pm pf) (tmGLP_pbu_aff 4 10)
  exact (PBU.add (PBU.mul (tmGLP_pbu_pw 1) (PBU.add (PBU.smul 3 h)
    (PBU.smul (10 ^ 3) (tmGLP_pbu_pw 1)))) (PBU.smul (10 ^ 7) (tmGLP_pbu_pw 3))).mono
    fun _ W _ => le_of_eq (by unfold tmGLPFindC; simp only [pow_one])

theorem tmGLPORowC_poly (pm pf : Prim) : PBU fun _ W _ => tmGLPORowC pm pf W := by
  have h := tmGLP_pbu_subst (tmGLPFindC_poly pm pf) (tmGLP_pbu_sq 100)
  exact (PBU.add (PBU.smul 4 h) (PBU.smul (10 ^ 7) (tmGLP_pbu_pw 3))).mono
    fun _ _ _ => le_of_eq rfl

/-- **The transporters for one element** have a polynomial cost bound. -/
theorem tmGLPOffC_poly (pm pf : Prim) : PBU fun _ W _ => tmGLPOffC pm pf W := by
  have h := tmGLPORowC_poly pm pf
  exact (PBU.add (PBU.mul (tmGLP_pbu_pw 1) (PBU.add (PBU.smul 2 h)
    (PBU.smul (10 ^ 4) (tmGLP_pbu_pw 3)))) (PBU.smul (10 ^ 6) (tmGLP_pbu_pw 4))).mono
    fun _ W _ => le_of_eq (by unfold tmGLPOffC; simp only [pow_one])

/-! ### The orientation -/

theorem tmGLPOrC_poly : PBU fun q W _ => tmGLPOrC q W := by
  unfold tmGLPOrC itParC
  norm_poly

/-- **The orientation entry** has a polynomial cost bound (first slot: the number of rows). -/
theorem tmGLPEpsC_poly (pm pf : Prim) : PBU fun q W _ => tmGLPEpsC pm pf q W := by
  have hO := tmGLP_pbu_subst (tmGLPOffC_poly pm pf) (tmGLP_pbu_aff 3 5)
  have hR : PBU fun q W B => tmGLPOrC q (tmGLPOffC pm pf (3 * W + 5)) :=
    tmGLP_pbu_subst tmGLPOrC_poly hO
  exact (PBU.add (PBU.smul 1000 (tmGLP_pbu_pw 1)) (PBU.smul 10 (PBU.add hO hR))).mono
    fun _ W _ => le_of_eq (by unfold tmGLPEpsC; simp only [pow_one])

/-! ### One generator -/

theorem tmGLPXsC_poly : PBU fun _ W _ => tmGLPXsC W := by
  unfold tmGLPXsC
  norm_poly

theorem tmGLPHalfO_poly (pm pf : Prim) : PBU fun _ W _ => tmGLPHalfO pm pf W :=
  tmGLP_pbu_subst (tmGLPOffC_poly pm pf) (tmGLP_pbu_aff 6 5)

theorem tmGLPHalfX_poly (pm pf : Prim) : PBU fun _ W Y => tmGLPHalfX pm pf Y W :=
  tmGLP_pbu_subst (g := fun _ W Y => 2 * (W + tmGLPHalfO pm pf W + Y) + 7) tmGLPXsC_poly
    (PBU.addc (PBU.smul 2 (PBU.add (PBU.add PBU.W (tmGLPHalfO_poly pm pf)) PBU.B)) 7)

theorem tmGLPHalfV_poly (pm pf : Prim) (Cs Ds Cv Dv : ℕ) :
    PBU fun _ W Y => tmGLPHalfV pm pf Y Cs Ds Cv Dv W :=
  tmGLP_pbu_subst (g := fun _ W Y => 2 * (W + tmGLPHalfX pm pf Y W) + 6)
    (tmGLPMPairC_poly Cs Ds Cv Dv)
    (PBU.addc (PBU.smul 2 (PBU.add PBU.W (tmGLPHalfX_poly pm pf))) 6)

/-- **The offset vector of one element** (third slot: the bound `Y` of one lift). -/
theorem tmGLPHalfC_poly (pm pf : Prim) (Cs Ds Cv Dv : ℕ) :
    PBU fun _ W Y => tmGLPHalfC pm pf Y Cs Ds Cv Dv W :=
  (PBU.add (PBU.smul 1000 (PBU.addc PBU.W 1)) (PBU.smul 10 (PBU.add (PBU.add (PBU.add
    (tmGLPHalfO_poly pm pf) PBU.B) (tmGLPHalfX_poly pm pf))
    (tmGLPHalfV_poly pm pf Cs Ds Cv Dv)))).mono fun _ _ _ => le_of_eq rfl

theorem tmGLPGenI_poly : PBU fun _ W _ => tmGLPGenI W := by
  unfold tmGLPGenI
  exact PBU.smul invK (tmGLP_pbu_pw 4)

theorem tmGLPGenW_poly : PBU fun _ W _ => tmGLPGenW W := by
  unfold tmGLPGenW
  exact PBU.addc (PBU.smul 2 (PBU.add PBU.W
    (PBU.addc (PBU.smul 2 (PBU.add PBU.W tmGLPGenI_poly)) 6))) 6

/-- **The item of one generator** (third slot: the bound `Y` of one lift). -/
theorem tmGLPGenC_poly (pm pf : Prim) (Cs Ds Cv Dv Cc Dc Cm Dm : ℕ) :
    PBU fun _ W Y => tmGLPGenC pm pf Y Cs Ds Cv Dv Cc Dc Cm Dm W := by
  have hH := tmGLP_pbu_subst (tmGLPHalfC_poly pm pf Cs Ds Cv Dv) tmGLPGenW_poly
  have hM := tmGLP_pbu_subst (tmGLPMPairC_poly Cc Dc Cm Dm) tmGLPGenW_poly
  exact (PBU.add (PBU.smul 1000 (PBU.addc PBU.W 1))
    (PBU.smul 100 (PBU.add (PBU.add tmGLPGenI_poly hH) hM))).mono fun _ _ _ => le_of_eq rfl

theorem tmGLPBlkC_poly : PBU fun _ W _ => tmGLPBlkC W := by
  unfold tmGLPBlkC
  exact PBU.smul _ (tmGLP_pbu_pw 4)

theorem tmGLPConsC_poly : PBU fun _ W _ => tmGLPConsC W := by
  unfold tmGLPConsC
  exact PBU.smul _ (tmGLP_pbu_pw 2)

/-- **The item of one generator with the orientation coordinate**, for callee bounds `G` (the
item without it) and `Ep` (the orientation entry) that are polynomial in any slots. -/
theorem tmGLPGenOC_poly {G Ep : ℕ → ℕ → ℕ → ℕ} (hG : PBU G) (hE : PBU Ep) :
    PBU fun k W B => tmGLPGenOC (G k · B) (Ep k · B) W := by
  have hE' := tmGLP_pbu_subst hE tmGLPGenW_poly
  have hB := tmGLP_pbu_subst tmGLPBlkC_poly hG
  have hC := tmGLP_pbu_subst (g := fun k W B => 2 * G k W B + 206) tmGLPConsC_poly
    (PBU.addc (PBU.smul 2 hG) 206)
  exact (PBU.add (PBU.smul 1000 (PBU.addc PBU.W 1)) (PBU.smul 100 (PBU.add (PBU.add (PBU.add
    (PBU.add tmGLPGenI_poly hE') hG) hB) hC))).mono fun _ _ _ => le_of_eq rfl

/-! ### The whole step -/

/-- **The map over the generators**, for an item bound `G` polynomial in any slots. -/
theorem tmGLPItemsC_poly {G : ℕ → ℕ → ℕ → ℕ} (hG : PBU G) :
    PBU fun k W B => tmGLPItemsC (G k · B) W := by
  have h := tmGLP_pbu_subst hG (tmGLP_pbu_aff 4 6)
  exact (PBU.mul (PBU.smul 4000 (tmGLP_pbu_pw 2)) (PBU.addc h 2)).mono
    fun _ _ _ => le_of_eq (by unfold tmGLPItemsC; ring)

theorem tmGLPBud_poly (Ce De : ℕ) : PBU fun _ W _ => tmGLPBud Ce De W := by
  unfold tmGLPBud
  exact PBU.smul Ce (PBU.pow (PBU.addc (tmGLP_pbu_sq 20) 2) De)

/-- **The setup**, for callee bounds `FA FQ FI` (abelian coordinates, quotient, inverse)
that are polynomial. -/
theorem tmGLPSetC_poly {FA FQ FI : ℕ → ℕ} (hFA : PBU fun _ W _ => FA W)
    (hFQ : PBU fun _ W _ => FQ W) (hFI : PBU fun _ W _ => FI W) (Ce De : ℕ) :
    PBU fun _ W _ => tmGLPSetC FA FQ FI Ce De W := by
  have hA : PBU fun _ W _ => tmGLPSetA FA W := tmGLP_pbu_subst hFA (tmGLP_pbu_aff 4 6)
  have hZ : PBU fun _ W _ => tmGLPSetZ Ce De W :=
    tmGLP_pbu_subst (tmGLPItemsC_poly (tmGLPBud_poly Ce De)) (tmGLP_pbu_aff 4 6)
  have hAp : PBU fun _ W _ => tmGLPSetAp FA Ce De W :=
    (PBU.mul (PBU.smul loopModK (PBU.addc hZ 1))
      (PBU.addc (PBU.smul 10 (PBU.add hA hZ)) 20)).mono fun _ _ _ => le_of_eq (by
        unfold tmGLPSetAp; ring)
  have hQ : PBU fun _ W _ => tmGLPSetQ FA FQ Ce De W :=
    tmGLP_pbu_subst (g := fun _ W _ => 8 * (tmGLPSetAp FA Ce De W + tmGLPSetA FA W) + 20) hFQ
      (PBU.addc (PBU.smul 8 (PBU.add hAp hA)) 20)
  have hI : PBU fun _ W _ => tmGLPSetI FA FQ FI Ce De W :=
    tmGLP_pbu_subst (g := fun _ W _ => 8 * (tmGLPSetQ FA FQ Ce De W + tmGLPSetA FA W) + 20) hFI
      (PBU.addc (PBU.smul 8 (PBU.add hQ hA)) 20)
  exact (PBU.add (PBU.smul 1000 (PBU.addc PBU.W 1)) (PBU.smul 100 (PBU.add (PBU.add (PBU.add
    (PBU.add hA hZ) hAp) hQ) hI))).mono fun _ _ _ => le_of_eq rfl

/-- **The setup for every `t`.** -/
theorem tmGLPSetDC_poly {FA FQ FI : ℕ → ℕ} (hFA : PBU fun _ W _ => FA W)
    (hFQ : PBU fun _ W _ => FQ W) (hFI : PBU fun _ W _ => FI W) (Ce De : ℕ) :
    PBU fun _ W _ => tmGLPSetDC FA FQ FI Ce De W :=
  (PBU.addc (PBU.add (PBU.smul 3 (tmGLPSetC_poly hFA hFQ hFI Ce De))
    (PBU.smul 100 (PBU.addc PBU.W 1))) 1000).mono fun _ _ _ => le_of_eq rfl

/-- **Step 5**, for a setup bound `SC` and an item bound `G` polynomial in any slots. -/
theorem tmGLPStep5C_poly {SC G : ℕ → ℕ → ℕ → ℕ} (hS : PBU SC) (hG : PBU G) :
    PBU fun k W B => tmGLPStep5C (SC k · B) (G k · B) W := by
  have hW : PBU fun k W B => tmGLPStep5W (SC k W B) W :=
    (PBU.addc (PBU.smul 20 (PBU.add PBU.W hS)) 50).mono fun _ _ _ => le_of_eq rfl
  have hI := tmGLP_pbu_subst (tmGLPItemsC_poly hG) hW
  exact (PBU.add (PBU.smul 1000 (PBU.addc PBU.W 1)) (PBU.smul 100 (PBU.add hS hI))).mono
    fun _ _ _ => le_of_eq rfl

/-- **Step 5 with the orientation modulus**, for a bound `C5` of step 5 polynomial in any
slots. -/
theorem tmGLPStep5OC_poly {C5 : ℕ → ℕ → ℕ → ℕ} (h5 : PBU C5) :
    PBU fun k W B => tmGLPStep5OC (C5 k W B) W := by
  have hC := tmGLP_pbu_subst (g := fun k W B => 2 * C5 k W B + 206) tmGLPConsC_poly
    (PBU.addc (PBU.smul 2 h5) 206)
  exact (PBU.add (PBU.add (PBU.smul 100 (PBU.addc PBU.W 1))
    (PBU.smul 1000 (PBU.addc h5 10))) (PBU.smul 10 hC)).mono fun _ _ _ => le_of_eq rfl

/-! ### The small programs -/

theorem tmGLPBsC_poly : PBU fun _ W _ => tmGLPBsC W := by
  unfold tmGLPBsC
  exact PBU.smul _ (tmGLP_pbu_pw 4)

theorem tmGLPXLabC_poly : PBU fun _ W _ => tmGLPXLabC W := by
  unfold tmGLPXLabC
  exact PBU.smul _ (tmGLP_pbu_pw 3)

/-- The context of the lifts (`rowKerCost` with the PointwiseStab constants). -/
theorem tmGLPLcC_poly (hst : GI.Cited.PointwiseStab) : PBU fun _ M _ => tmGLPLcC hst M := by
  unfold tmGLPLcC rowKerCost
  exact PBU.add (PBU.add (PBU.smul _ (PBU.pow (PBU.addc (PBU.smul 100 (PBU.pow PBU.W 4)) 2) _))
    (PBU.smul _ (PBU.pow PBU.W 12))) (PBU.smul _ (PBU.pow PBU.W 12))

/-- One lift (`liftLabCost` with the NormalizedFactor constants). -/
theorem tmGLPL1C_poly (pf : Prim) : PBU fun _ M _ => tmGLPL1C pf M := by
  unfold tmGLPL1C liftLabCost
  exact PBU.add (PBU.add (PBU.smul _ (PBU.pow (PBU.addc (PBU.smul 2000 (PBU.pow PBU.W 4)) 2) _))
    (PBU.smul _ (PBU.pow PBU.W 6))) (PBU.smul _ (PBU.pow PBU.W 8))

end GI.Impl
