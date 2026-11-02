import Workspace.Impl.AggLiftLoop
import Workspace.Impl.AggKerRed
import Workspace.Impl.AggInc

/-!
# The kernel cut of `LiftAndContinue`, from the window-group module

`lcChild_spec` and `lcMap_spec` take the module that cuts the first parts of a graph form to at
most `k²` generators as a hypothesis `LcKrOK` with a monotone cost bound. The window-group module
of the certificate phase (`krFuns`, `kr_spec`, one **PointwiseStab** call) is such a module.

* `abKrC`: its cost bound, `boundSize (100 M⁴) + krK M⁹`.
* `ab_krOK`: `LcKrOK` holds for `krFuns` placed at `bkr`.
* `abKrC_mono`: the bound is monotone.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang
open GI.Cited (PointwiseStab)

/-- The cost bound of the window-group module, for size parameter `M`. -/
noncomputable def abKrC (hst : PointwiseStab) (M : ℕ) : ℕ :=
  (pointwiseStabPrim hst).boundSize (100 * M ^ 4) + krK * M ^ 9

theorem abKrC_mono (hst : PointwiseStab) : Monotone (abKrC hst) := fun _ _ h =>
  Nat.add_le_add (boundSize_mono _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 4)))
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 9))

/-- **The window-group module meets the contract of the kernel cut.** -/
theorem ab_krOK (hst : PointwiseStab) {P : Program} {bkr j : ℕ} (hb : P.HasAt bkr (krFuns bkr j))
    (hj : P.prims[j]? = some (pointwiseStabPrim hst)) : LcKrOK P bkr (abKrC hst) :=
  fun _ _ ps => kr_spec hst hb hj ps

end GI.Impl
