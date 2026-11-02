import Workspace.Impl.TermGlueLabSVPt

/-!
# Polynomial bounds of the two label vector programs

The costs `tmGLSVecC` and `tmGLSPtC` of `Impl/TermGlueLabSVProg.lean` are
polynomial in the input weight, for fixed envelope constants `Cs Ds Cv Dv` of the coordinate
sums and of the vector program. Proved stage by stage (`norm_poly` times out on nested costs).
-/

namespace GI.Impl

/-- The matrix pair bound `tmGLPMPairC` (also the bound of the offset-vector program). -/
theorem tmGLS_mpair_poly (Cs Ds Cv Dv : ℕ) : PBU fun _ W _ => tmGLPMPairC Cs Ds Cv Dv W := by
  have hX : PBU fun _ W _ => tmGLPMPX Cs Ds W :=
    PBU.smul Cs (PBU.pow (PBU.addc (PBU.smul 64 PBU.W) 202) Ds)
  have hZ : PBU fun _ W _ => tmGLPMPZ Cs Ds Cv Dv W :=
    PBU.smul Cv (PBU.pow (PBU.addc (PBU.smul 3 (PBU.add PBU.W hX)) 8) Dv)
  exact PBU.add (PBU.add (PBU.smul 1000 (PBU.addc PBU.W 1)) (PBU.smul 40 hX)) (PBU.smul 40 hZ)

/-- **The label vector program is polynomial.** -/
theorem tmGLSVecC_poly (Cs Ds Cv Dv : ℕ) : PBU fun _ W _ => tmGLSVecC Cs Ds Cv Dv W := by
  have hg : PBU fun _ W _ => 50 * (W + 1) ^ 3 := PBU.smul 50 (PBU.pow (PBU.addc PBU.W 1) 3)
  have hp : PBU fun _ W _ => tmGLPMPairC Cs Ds Cv Dv (50 * (W + 1) ^ 3) :=
    tmGLP_pbu_subst (tmGLS_mpair_poly Cs Ds Cv Dv) hg
  exact PBU.add (PBU.smul (10 ^ 7) (PBU.pow (PBU.addc PBU.W 1) 4)) (PBU.smul 3 hp)

/-- The orientation program's bound at `q ≤ W`. -/
theorem tmGLS_orC_poly : PBU fun _ W _ => tmGLPOrC W W :=
  PBU.add (PBU.smul (10 ^ 7) (PBU.pow (PBU.addc PBU.W 1) 4))
    (PBU.smul (10 ^ 6) (PBU.pow (PBU.addc PBU.W 1) 3))

/-- **The label point vector program is polynomial.** -/
theorem tmGLSPtC_poly (Cs Ds Cv Dv : ℕ) : PBU fun _ W _ => tmGLSPtC Cs Ds Cv Dv W :=
  PBU.smul (10 ^ 7) (PBU.pow (PBU.addc (PBU.add (PBU.add (tmGLSVecC_poly Cs Ds Cv Dv)
    tmGLS_orC_poly) PBU.W) 1) 2)

end GI.Impl
