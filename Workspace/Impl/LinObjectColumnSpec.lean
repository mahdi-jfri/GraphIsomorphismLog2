module

public import Workspace.Impl.LinObjectMatrixCost

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

set_option maxHeartbeats 300000 in
theorem linObjectAffineColumn_spec {P : Program} {b jsci jder jmem jm jh d C : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership} {hc : ConstructiveMembership}
    (h : linObjectAffineMatrixAt P b jsci jder jmem jm jh hs hd hm hc)
    (ctx g : Val) (m : Fin d → ℕ) (hmpos : ∀ i, 0 < m i)
    (L : linFiniteVec m →+ linFiniteVec m) (c : linFiniteVec m)
    (F : linFiniteVec m → linFiniteVec m) (hF : ∀ x, F x = L x + c)
    (j : Fin d) (hC : 100 ≤ C) (hdC : d ≤ C)
    (horders : normReadVal ctx [4] = some (linVecVal (fun i => (m i : ℤ))))
    (hw : (Val.list [.list [ctx,g,linFiniteIntVecVal m c,.nat d],.nat j.val]).wt ≤ C)
    (heval : FunDet P (b + 51) (.list [ctx,g,linVecVal (Pi.single j (1 : ℤ))])
      (linFiniteIntVecVal m (F (Pi.single j 1))) C) :
    FunDet P (b + 1) (.list [.list [ctx,g,linFiniteIntVecVal m c,.nat d],.nat j.val])
      (linFiniteIntVecVal m (L (Pi.single j 1))) (linObjectMatrixColumnCost C) := by
  have hCp : C + 1 ≤ (C + 1) ^ 2 := Nat.le_self_pow (by decide) _
  let BB := linObjectMatrixBasisBudget C
  let DB := linObjectMatrixDiffBudget C
  let CC := linObjectMatrixColumnBound C
  have hp : C + BB + DB + 1 ≤ (C + BB + DB + 1) ^ 2 := Nat.le_self_pow (by decide) _
  have hcC : C ≤ CC := by change C ≤ 100 * (C + BB + DB + 1) ^ 2; omega
  have hbC : BB ≤ CC := by change BB ≤ 100 * (C + BB + DB + 1) ^ 2; omega
  have hdC' : DB ≤ CC := by change DB ≤ 100 * (C + BB + DB + 1) ^ 2; omega
  have hCC : 100 ≤ CC := hC.trans hcC
  have hjw := wt_nat_le j.val
  have hdw := wt_nat_le d
  have hOne : (encInt 1).wt = 21 := rfl
  have hbarg : (Val.list [.nat j.val,encInt 1,.nat d]).wt ≤ 100 * (C + 1) ^ 2 := by
    have hw := wt_list3_le (.nat j.val) (encInt 1) (.nat d)
    have hp : C + 1 ≤ (C + 1) ^ 2 := Nat.le_self_pow (by decide) _
    omega
  have hb : FunDet P (b + 11) (.list [.nat j.val,encInt 1,.nat d]) (linVecVal (Pi.single j (1 : ℤ))) BB :=
    (linBasis_spec h.basis j 1).mono
      (linPolyEnvelope_bound linObjectMatrixBasisPoly (hdC.trans (by omega)) hbarg (Nat.zero_le _))
  have wctx : ctx.wt ≤ C := by
    have h1 : ctx.wt < (Val.list [ctx,g,linFiniteIntVecVal m c,.nat d]).wt := wt_le_wt_list (by simp)
    have h2 : (Val.list [ctx,g,linFiniteIntVecVal m c,.nat d]).wt <
      (Val.list [.list [ctx,g,linFiniteIntVecVal m c,.nat d],.nat j.val]).wt := wt_le_wt_list (by simp)
    omega
  have wm : (linVecVal (fun i => (m i : ℤ))).wt ≤ C := (normReadVal_wt horders).trans wctx
  have wc : (linFiniteIntVecVal m c).wt ≤ C := by
    have h1 : (linFiniteIntVecVal m c).wt < (Val.list [ctx,g,linFiniteIntVecVal m c,.nat d]).wt :=
      wt_le_wt_list (by simp)
    have h2 : (Val.list [ctx,g,linFiniteIntVecVal m c,.nat d]).wt <
      (Val.list [.list [ctx,g,linFiniteIntVecVal m c,.nat d],.nat j.val]).wt := wt_le_wt_list (by simp)
    omega
  have we := heval.wt_lt.le
  have hdiff : F (Pi.single j 1) - c = L (Pi.single j 1) := by rw [hF]; abel
  have hdiffarg : (Val.list [linVecVal (fun i => (m i : ℤ)),linFiniteIntVecVal m (F (Pi.single j 1)),
      linFiniteIntVecVal m c]).wt ≤ 100 * (C + 1) ^ 2 := by
    have hw := wt_list3_le (linVecVal (fun i => (m i : ℤ)))
      (linFiniteIntVecVal m (F (Pi.single j 1))) (linFiniteIntVecVal m c)
    have hp : C + 1 ≤ (C + 1) ^ 2 := Nat.le_self_pow (by decide) _
    omega
  have hdiffcall : FunDet P (b + 14) (.list [linVecVal (fun i => (m i : ℤ)),
      linFiniteIntVecVal m (F (Pi.single j 1)),linFiniteIntVecVal m c])
      (linFiniteIntVecVal m (L (Pi.single j 1))) DB := by
    have hr := linFiniteDifference_spec h.difference m hmpos (F (Pi.single j 1)) c
    rw [hdiff] at hr
    exact hr.mono (linPolyEnvelope_bound linFiniteDifferenceCost_poly (Nat.zero_le _) hdiffarg (Nat.zero_le _))
  exact linObjectAffineColumn_comp h.column ctx g (linFiniteIntVecVal m c)
    (linVecVal (fun i => (m i : ℤ))) (linVecVal (Pi.single j (1 : ℤ)))
    (linFiniteIntVecVal m (F (Pi.single j 1))) (linFiniteIntVecVal m (L (Pi.single j 1)))
    horders hCC (hw.trans hcC) (hb.mono hbC) (heval.mono hcC) (hdiffcall.mono hdC')

end GI.Impl
