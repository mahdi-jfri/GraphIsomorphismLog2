module

public import Workspace.Impl.TermGlueLabNProg

@[expose] public section

/-!
# The label driver: discharges of the contracts of the label programs

Proof of Theorem A.23, steps 2 and 3. The labels of `x` and of `y'` meet the
driver's contracts `Iface.TmGLNXOK` and `Iface.TmGLNYOK`: apply the specs `tmGLPXLab_spec`,
`tmGLPYLab_spec`, and bound their costs at the input weight by the cost at the bound `B`.
-/

namespace GI.Impl

open GI.Lang GI.Multicoset Equiv
open GI.Cited (Val Membership NormalizedFactor)

/-- **The labels of `x` meet their contract.** -/
theorem tmGLN_x_ok {P : Program} {b : ℕ} (h : P.HasAt b (tmGLPXLabFuns b)) :
    Iface.TmGLNXOK P b tmGLPXLabC := by
  intro n Ω _ N q X us hT B hB
  exact (tmGLPXLab_spec h hT).mono fun u c ⟨hu, hc⟩ =>
    ⟨hu, hc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))⟩

theorem tmGLN_yC_mono (pm pf : Prim) {W V : ℕ} (h : W ≤ V) :
    tmGLPYLabC pm pf W ≤ tmGLPYLabC pm pf V := by
  unfold tmGLPYLabC
  exact Nat.add_le_add (Nat.mul_le_mul (by omega) (Nat.add_le_add
    (Nat.mul_le_mul_left 2 (tmGLPFindC_mono pm pf (by omega)))
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))))
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4))

/-- **The labels of `y'` meet their contract.** -/
theorem tmGLN_y_ok (hm : Membership) (hfac : NormalizedFactor) {P : Program}
    {b find rel jm jf : ℕ} (h : P.HasAt b (tmGLPYLabFuns b find))
    (hfd : P.HasAt find (tmGLPFindFuns find rel)) (hr : TmGLPRelAt P rel jm jf)
    (hjm : P.prims[jm]? = some (membershipPrim hm))
    (hjf : P.prims[jf]? = some (normalizedFactorPrim hfac)) :
    Iface.TmGLNYOK P b (tmGLPYLabC (membershipPrim hm) (normalizedFactorPrim hfac)) := by
  intro n Ω _ H σN hNH hn q X Y vs hT ks hks Z hZ B hB
  exact (tmGLPYLab_spec hm hfac h hfd hr hjm hjf hNH hn hT hks hZ).mono fun u c ⟨hu, hc⟩ =>
    ⟨hu, hc.trans (tmGLN_yC_mono _ _ hB)⟩

end GI.Impl
