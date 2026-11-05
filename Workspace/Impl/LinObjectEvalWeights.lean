module

public import Workspace.Impl.LinObjectEvalCost

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

theorem linObjectEvalArg2 (a b : Val) (W U : ℕ) (ha : a.wt ≤ U) (hb : b.wt ≤ W + 2) :
    (Val.list [a,b]).wt ≤ 100 * (W + U + 1) ^ 2 := by
  have hw := wt_list2_le a b
  have hp : W + U + 1 ≤ (W + U + 1) ^ 2 := Nat.le_self_pow (by decide) _
  omega

theorem linObjectEvalArg3 (a b c : Val) (W U : ℕ)
    (ha : a.wt ≤ W + 2) (hb : b.wt ≤ W + 2) (hc : c.wt ≤ U) :
    (Val.list [a,b,c]).wt ≤ 100 * (W + U + 1) ^ 2 := by
  have hw := wt_list3_le a b c
  have hp : W + U + 1 ≤ (W + U + 1) ^ 2 := Nat.le_self_pow (by decide) _
  omega

theorem linObjectEvalArg4 (a b c d : Val) (W U : ℕ)
    (ha : a.wt ≤ W + 2) (hb : b.wt ≤ W + 2) (hc : c.wt ≤ W + 2) (hd : d.wt ≤ U) :
    (Val.list [a,b,c,d]).wt ≤ 100 * (W + U + 1) ^ 2 := by
  have hw := wt_list4_le a b c d
  have hp : W + U + 1 ≤ (W + U + 1) ^ 2 := Nat.le_self_pow (by decide) _
  omega

theorem linObjectEvalArg3Middle (a b c : Val) (W U : ℕ)
    (ha : a.wt ≤ W + 2) (hb : b.wt ≤ U) (hc : c.wt ≤ W + 2) :
    (Val.list [a,b,c]).wt ≤ 100 * (W + U + 1) ^ 2 := by
  have hw := wt_list3_le a b c
  have hp : W + U + 1 ≤ (W + U + 1) ^ 2 := Nat.le_self_pow (by decide) _
  omega

noncomputable def linObjectEvalIntegerValue (d : ℕ) (v : Val) : Fin d → ℤ :=
  Function.invFun (linVecVal (n := d)) v

theorem linObjectEvalIntegerValue_vec {d : ℕ} (z : Fin d → ℤ) :
    linObjectEvalIntegerValue d (linVecVal z) = z :=
  Function.leftInverse_invFun linVecVal_injective z

noncomputable def linObjectEvalRowImage {d : ℕ} (V : Matrix (Fin d) (Fin d) ℤ) (v : Val) : Val :=
  linVecVal (Matrix.vecMul (linObjectEvalIntegerValue d v) V)

@[simp] theorem linObjectEvalRowImage_vec {d : ℕ} (V : Matrix (Fin d) (Fin d) ℤ) (z : Fin d → ℤ) :
    linObjectEvalRowImage V (linVecVal z) = linVecVal (Matrix.vecMul z V) := by
  rw [linObjectEvalRowImage,linObjectEvalIntegerValue_vec]

end GI.Impl
