import Workspace.Cited.GMP
import Workspace.Cited.AutCardLeSq
import Workspace.SmallSimple
import Mathlib.Data.Finite.Prod

/-!
# `|Aut T| ≤ |T|²` from the outer automorphism bound

`GI.Cited.AutCardLeSq` is attributed to [GMP, Lemma 7.7] "applied to the regular
representation". Here it is derived from `GI.Cited.GMPOutBound` (`|Out T| ≤ 2 √|T|`):
`|Aut T| = |Out T| · |Inn T| ≤ 2 √|T| · |T| ≤ |T|²`, since `|T| ≥ 34 ≥ 4`
(`GI.SmallSimple.thirtyfour_le_card`).
-/

namespace GI

open GI.Cited

/-- `GI.Cited.GMPOutBound` implies `GI.Cited.AutCardLeSq`. -/
theorem autCardLeSq_of_outBound (hOut : GMPOutBound) : AutCardLeSq := by
  intro T _ _ hs hT
  haveI := hs
  set n := Nat.card T
  have hc : ¬ ∀ x y : T, x * y = y * x := by
    obtain ⟨x, y, h⟩ := hT
    exact fun hc => h (hc x y)
  have h34 : 34 ≤ n := GI.SmallSimple.thirtyfour_le_card hc
  -- `|Out T| ≤ |T|`, since `2 √n ≤ n` for `n ≥ 4`
  have hidx : (MulAut.conj : T →* MulAut T).range.index ≤ n := by
    have h := hOut T hs hT
    have hn : (34 : ℝ) ≤ n := by exact_mod_cast h34
    have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (by linarith)
    have h2 : (2 : ℝ) ≤ Real.sqrt n := Real.le_sqrt_of_sq_le (by linarith)
    have : 2 * Real.sqrt n ≤ n := by nlinarith [Real.sqrt_nonneg (n : ℝ)]
    exact_mod_cast h.trans this
  -- `|Inn T| ≤ |T|`
  have hinn : Nat.card (MulAut.conj : T →* MulAut T).range ≤ n :=
    Nat.card_le_card_of_surjective _ (MulAut.conj : T →* MulAut T).rangeRestrict_surjective
  rw [← (MulAut.conj : T →* MulAut T).range.index_mul_card, sq]
  exact Nat.mul_le_mul hidx hinn

end GI
