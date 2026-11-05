module

public import Workspace.Impl.TermGlueLabS6
public import Workspace.Impl.TermGlueLabPPoly

@[expose] public section

/-!
# Polynomial bounds of step 6 of the label program

The cost bounds of the generator cut (`tmGLSRedC`), of the output program
(`tmGLSOutC`) and of step 6 (`tmGLS6C`) are polynomial (`PBU`). For step 6 the second slot is
the input weight `W` and the third slot is the bound `C5` of step 5, so that the assembly can
substitute step 5's own polynomial bound with `tmGLP_pbu_subst`. The constants `Ka`, `Da` of the
affine procedure and `c`, `k` of the PointwiseStab primitive are fixed.
-/

namespace GI.Impl

/-- `(W + 1)^j` is polynomial. -/
theorem tmGLS_pbu_pw (j : ℕ) : PBU fun _ W _ => (W + 1) ^ j := PBU.pow (PBU.addc PBU.W 1) j

theorem tmGLSRedC_poly (c kp : ℕ) : PBU fun _ W _ => tmGLSRedC c kp W := by
  unfold tmGLSRedC
  exact PBU.add (PBU.smul c (PBU.pow (PBU.smul 100 (tmGLS_pbu_pw 2)) kp))
    (PBU.smul _ (tmGLS_pbu_pw 9))

theorem tmGLSOutC_poly (c kp : ℕ) : PBU fun _ W _ => tmGLSOutC c kp W := by
  unfold tmGLSOutC
  have h := tmGLP_pbu_subst (tmGLSRedC_poly c kp)
    (g := fun _ W _ => 2 * W + 6) (PBU.addc (PBU.smul 2 PBU.W) 6)
  exact PBU.add (PBU.smul 2 h) (PBU.smul _ (tmGLS_pbu_pw 8))

theorem tmGLS6A_poly : PBU fun _ W B => tmGLS6A B W := by
  unfold tmGLS6A
  exact PBU.add (PBU.smul 1000 (tmGLS_pbu_pw 6)) (PBU.smul 4 PBU.B)

theorem tmGLS6KA_poly (Ka Da : ℕ) : PBU fun _ W B => tmGLS6KA Ka Da B W := by
  unfold tmGLS6KA
  exact PBU.smul Ka (PBU.pow (PBU.addc tmGLS6A_poly 1) Da)

/-- **The cost of step 6 is polynomial** in the input weight `W` and step 5's bound `B`. -/
theorem tmGLS6C_poly (Ka Da c kp : ℕ) : PBU fun _ W B => tmGLS6C Ka Da c kp B W := by
  unfold tmGLS6C
  have hO := tmGLP_pbu_subst (tmGLSOutC_poly c kp)
    (g := fun _ W B => 4 * W + 2 * tmGLS6KA Ka Da B W + 10)
    (PBU.addc (PBU.add (PBU.smul 4 PBU.W) (PBU.smul 2 (tmGLS6KA_poly Ka Da))) 10)
  exact PBU.add (PBU.add (PBU.add (PBU.add (PBU.smul _ (tmGLS_pbu_pw 9)) (PBU.smul 3 PBU.B))
    (PBU.smul 20 tmGLS6A_poly)) (PBU.smul 10 (tmGLS6KA_poly Ka Da))) (PBU.smul 5 (PBU.smul 3 hO))

end GI.Impl
