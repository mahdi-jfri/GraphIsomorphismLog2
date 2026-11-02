import Workspace.Impl.AggItemCiSojRectProg
import Workspace.Impl.AggItemCiSojStartProg
import Workspace.Impl.AggItemCiSojBudgetStart

/-! # Small scalar estimates for the start controller -/

namespace GI.Impl

open GI.Lang
open GI.Cited (Val)

/-- The physical-data wrapper uses one linear bookkeeping stage. -/
theorem itcs_physical_cost_scalar {W Cg Cl Cr Cd n : ℕ}
    (hW : W ≤ n) (hg : Cg ≤ n) (hl : Cl ≤ n) (hr : Cr ≤ n) (hd : Cd ≤ n) :
    itcsPhysicalDataC W Cg Cl Cr Cd ≤ 10^9*(n+100) := by
  unfold itcsPhysicalDataC
  omega

/-- The color-table and inherited-state wrapper uses one such stage. -/
theorem itcs_colors_cost_scalar {W Cp Cr Cx Cy Cs n : ℕ}
    (hW : W ≤ n) (hp : Cp ≤ n) (hr : Cr ≤ n) (hx : Cx ≤ n) (hy : Cy ≤ n) (hs : Cs ≤ n) :
    itcsColorsStateC W Cp Cr Cx Cy Cs ≤ 10^9*(n+100) := by
  unfold itcsColorsStateC
  omega

/-- Both initial query occurrences fit the same linear bookkeeping stage. -/
theorem itcs_ask_cost_scalar {W Cd C₀ C₁ n : ℕ}
    (hW : W ≤ n) (hd : Cd ≤ n) (h₀ : C₀ ≤ n) (h₁ : C₁ ≤ n) :
    itcsAskC W Cd C₀ C₁ ≤ 10^9*(n+100) := by
  unfold itcsAskC
  omega

/-- The full rectangle controller pays for all source and target tables and
all certified-call continuations in one further structural stage. -/
theorem itcs_rect_cost_scalar {W Cr Cb Cs Cg Ca Cf Cw Ct Cp Cq n : ℕ}
    (hW : W ≤ n) (hr : Cr ≤ n) (hb : Cb ≤ n) (hs : Cs ≤ n)
    (hg : Cg ≤ n) (ha : Ca ≤ n) (hf : Cf ≤ n) (hw : Cw ≤ n)
    (ht : Ct ≤ n) (hp : Cp ≤ n) (hq : Cq ≤ n) :
    itcsRectPrepC W Cr Cb Cs Cg Ca Cf Cw Ct Cp Cq ≤ 10^9*(n+100) := by
  unfold itcsRectPrepC
  omega

/-- A fixed list of at most ten values has the linear constructor bound used
by the query, state and controller arguments. -/
theorem itcs_start_list_weight (vs : List Val) {n : ℕ}
    (hl : vs.length ≤ 10) (hw : ∀ v∈vs, v.wt ≤ n) :
    (Val.list vs).wt ≤ 10^9*(n+100) := by
  have h := wt_list_map_le vs id (W:=n) (by simpa only [id_eq] using hw)
  simp only [List.map_id] at h
  have h' := h.trans (Nat.add_le_add_right (Nat.mul_le_mul_right (2*n+1) hl) 4)
  omega

/-- The direct state constructor has the same scalar bound once its five
actual arguments have been covered. -/
theorem itcs_state_cost_scalar (sv gv dv xv yv : Val) {n : ℕ}
    (hs : sv.wt ≤ n) (hg : gv.wt ≤ n) (hd : dv.wt ≤ n) (hx : xv.wt ≤ n) (hy : yv.wt ≤ n) :
    itcsStateC sv gv dv xv yv ≤ 10^9*(n+100) := by
  have h := itcs_wt_list5 sv gv dv xv yv
  unfold itcsStateC
  omega

/-- The ordered-pair source dispatch also fits the fixed structural profile.
Its square of the scan size is paid within degree four of the common profile. -/
theorem itcs_start_cost_bound {W Cf Cp Ci Cr Cb Ct Cpart Ccert Crect n : ℕ}
    (hW : W ≤ n) (hf : Cf ≤ n) (hp : Cp ≤ n) (hi : Ci ≤ n) (hr : Cr ≤ n)
    (hb : Cb ≤ n) (ht : Ct ≤ n) (hpart : Cpart ≤ n) (hcert : Ccert ≤ n) (hrect : Crect ≤ n) :
    itcsStartC W Cf Cp Ci Cr Cb Ct Cpart Ccert Crect ≤ itcsWrapperC n := by
  let s := n+100
  have hsum : W+Cf+Cp+Ci+Cr+Cb+Ct+Cpart+Ccert+Crect+100 ≤ 10*s := by dsimp only [s]; omega
  have hs100 : 100 ≤ s := by dsimp only [s]; omega
  have hs : n ≤ s := by dsimp only [s]; omega
  have hpow := Nat.pow_le_pow_left hsum 2
  have hpEq : (10*s)^2=100*s^2 := by ring
  rw [hpEq] at hpow
  have hss : s ≤ s^2 := Nat.le_self_pow (by decide : 2≠0) s
  have hs2 : 2 ≤ s^2 := (show 2≤s by omega).trans hss
  have hprod : 2*s^2 ≤ s^4 := by
    have h := Nat.mul_le_mul_right (s^2) hs2
    have he : s^2*s^2=s^4 := by ring
    rwa [he] at h
  have hcost : itcsStartC W Cf Cp Ci Cr Cb Ct Cpart Ccert Crect ≤ 2*10^9*s^2 := by
    unfold itcsStartC
    omega
  have hfinal : 2*10^9*s^2 ≤ 10^9*s^4 := by
    calc
      2*10^9*s^2 = 10^9*(2*s^2) := by ring
      _ ≤ 10^9*s^4 := Nat.mul_le_mul_left _ hprod
  exact (hcost.trans hfinal).trans (itcs_wrapper_power n (10^9) 100 4 (le_refl _) (le_refl _) (by decide))

end GI.Impl
