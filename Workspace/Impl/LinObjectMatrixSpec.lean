import Workspace.Impl.LinObjectColumnSpec

namespace GI.Impl
open GI.Cited GI.Lang

set_option maxHeartbeats 500000 in
set_option maxRecDepth 2000 in
theorem linObjectAffineMatrix_spec {P : Program} {b jsci jder jmem jm jh d C : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership} {hc : ConstructiveMembership}
    (h : linObjectAffineMatrixAt P b jsci jder jmem jm jh hs hd hm hc)
    (ctx g : Val) (m : Fin d → ℕ) (hmpos : ∀ i, 0 < m i)
    (L : linFiniteVec m →+ linFiniteVec m) (c : linFiniteVec m)
    (F : linFiniteVec m → linFiniteVec m) (hF : ∀ x, F x = L x + c)
    (hC : 100 ≤ C) (hdC : d ≤ C)
    (horders : normReadVal ctx [4] = some (linVecVal (fun i => (m i : ℤ))))
    (hw : (Val.list [ctx,g]).wt ≤ C)
    (heval0 : FunDet P (b + 51) (.list [ctx,g,linVecVal (0 : Fin d → ℤ)]) (linFiniteIntVecVal m c) C)
    (heval : ∀ j : Fin d, FunDet P (b + 51) (.list [ctx,g,linVecVal (Pi.single j (1 : ℤ))])
      (linFiniteIntVecVal m (F (Pi.single j 1))) C) :
    FunDet P b (.list [ctx,g]) (.list [encIntMatrix (tmGLMat m L),linFiniteIntVecVal m c])
      (linObjectMatrixCost C) := by
  let CC := linObjectMatrixColumnSource C
  let IB := linObjectMatrixRangeBudget C
  let MB := linObjectMatrixMapBudget C
  let TB := linObjectMatrixTransposeBudget C
  let EE := linObjectMatrixEntryBound C
  let κ := Val.list [ctx,g,linFiniteIntVecVal m c,.nat d]
  let ids := encFun (fun i : Fin d => i.val)
  let M : Matrix (Fin d) (Fin d) ℤ := fun j i => ((L (Pi.single j 1) i).val : ℤ)
  have wc : ctx.wt ≤ C := (wt_le_wt_list (by simp : ctx ∈ [ctx,g])).le.trans hw
  have wg : g.wt ≤ C := (wt_le_wt_list (by simp : g ∈ [ctx,g])).le.trans hw
  have woff := heval0.wt_lt.le
  have hdw := wt_nat_le d
  have hcCC : C ≤ CC := by
    have hp : C + 1 ≤ (C + 1) ^ 2 := Nat.le_self_pow (by decide) _
    change C ≤ 100 * (C + 1) ^ 2
    omega
  have hCC : 100 ≤ CC := hC.trans hcCC
  have hr : FunDet P (b + 5) (.nat d) ids IB :=
    (linRange_spec h.range d).mono (linPolyEnvelope_bound linObjectOffsetsRangePoly hdC (Nat.zero_le _) (Nat.zero_le _))
  have wids := hr.wt_lt.le
  have hcols (j : Fin d) : FunDet P (b + 1) (.list [κ,.nat j.val])
      (linFiniteIntVecVal m (L (Pi.single j 1))) (linObjectMatrixColumnBudget C) := by
    have wj := wt_nat_le j.val
    have wκ := wt_list4_le ctx g (linFiniteIntVecVal m c) (.nat d)
    have win := wt_list2_le κ (.nat j.val)
    have hp : C + 1 ≤ (C + 1) ^ 2 := Nat.le_self_pow (by decide) _
    have hin : (Val.list [κ,.nat j.val]).wt ≤ CC := by
      change _ ≤ 100 * (C + 1) ^ 2
      dsimp only [κ] at win ⊢
      omega
    exact linObjectAffineColumn_spec h ctx g m hmpos L c F hF j hCC (hdC.trans hcCC)
      horders hin ((heval j).mono hcCC)
  have hmapArg : (Val.list [κ,ids]).wt ≤ linObjectMatrixMapArg C := by
    have wκ := wt_list4_le ctx g (linFiniteIntVecVal m c) (.nat d)
    have win := wt_list2_le κ ids
    have hp : C + IB + 1 ≤ (C + IB + 1) ^ 2 := Nat.le_self_pow (by decide) _
    change _ ≤ 100 * (C + IB + 1) ^ 2
    dsimp only [κ] at win ⊢
    omega
  have hmap : FunDet P (b + 2) (.list [κ,ids]) (encIntMatrix M) MB := by
    have he : Function.Injective (fun j : Fin d => Val.nat j.val) := by
      intro i j heq
      exact Fin.ext (Val.nat.inj heq)
    have hh := linMapEncoded_spec h.map (fun j : Fin d => Val.nat j.val) he
      (fun j => linFiniteIntVecVal m (L (Pi.single j 1))) κ (List.finRange d)
      (linObjectMatrixColumnBudget C) (fun j _ => hcols j)
    have hcst : linMapBudget (Val.list [κ,ids]).wt (linObjectMatrixColumnBudget C) ≤ MB :=
      linPolyEnvelope_bound linObjectEvalMapPoly (Nat.zero_le _) (hmapArg.trans (by omega)) (by omega)
    exact hh.mono hcst
  have wcols := hmap.wt_lt.le
  have htrArg : (Val.list [.nat d,encIntMatrix M]).wt ≤ linObjectMatrixTransposeArg C := by
    have win := wt_list2_le (.nat d) (encIntMatrix M)
    have hp : C + MB + 1 ≤ (C + MB + 1) ^ 2 := Nat.le_self_pow (by decide) _
    change _ ≤ 100 * (C + MB + 1) ^ 2
    omega
  have ht : FunDet P (b + 39) (.list [.nat d,encIntMatrix M]) (encIntMatrix M.transpose) TB :=
    (tmGLPTr_spec h.transpose M).mono
      (linPolyEnvelope_bound linObjectMatrixTransposePoly (hdC.trans (by omega)) (htrArg.trans (by omega)) (Nat.zero_le _))
  have hz : FunDet P (b + 8) (.list [.nat d,encInt 0]) (linVecVal (0 : Fin d → ℤ))
      (100000 * (C + 1) ^ 2) :=
    (linObjectZeroRow_spec h.zero d).mono (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hdC 1) 2))
  have hp : C + 100000 * (C + 1) ^ 2 + IB + MB + TB + 1 ≤
      (C + 100000 * (C + 1) ^ 2 + IB + MB + TB + 1) ^ 2 := Nat.le_self_pow (by decide) _
  have hcEE : C ≤ EE := by change C ≤ 100 * (C + 100000 * (C + 1) ^ 2 + IB + MB + TB + 1) ^ 2; omega
  have hzEE : 100000 * (C + 1) ^ 2 ≤ EE := by
    change _ ≤ 100 * (C + 100000 * (C + 1) ^ 2 + IB + MB + TB + 1) ^ 2; omega
  have hiEE : IB ≤ EE := by change IB ≤ 100 * (C + 100000 * (C + 1) ^ 2 + IB + MB + TB + 1) ^ 2; omega
  have hmEE : MB ≤ EE := by change MB ≤ 100 * (C + 100000 * (C + 1) ^ 2 + IB + MB + TB + 1) ^ 2; omega
  have htEE : TB ≤ EE := by change TB ≤ 100 * (C + 100000 * (C + 1) ^ 2 + IB + MB + TB + 1) ^ 2; omega
  have hfinal := linObjectAffineMatrix_comp h.entry ctx g (linVecVal (0 : Fin d → ℤ))
    (linFiniteIntVecVal m c) ids (encIntMatrix M) (encIntMatrix M.transpose)
    ((List.finRange d).map fun i => encInt (m i : ℤ)) horders (hC.trans hcEE) (hw.trans hcEE)
    (by simpa only [List.length_map,List.length_finRange] using hz.mono hzEE)
    (heval0.mono hcEE)
    (by simpa only [List.length_map,List.length_finRange] using hr.mono hiEE)
    (by simpa only [List.length_map,List.length_finRange] using hmap.mono hmEE)
    (by simpa only [List.length_map,List.length_finRange] using ht.mono htEE)
  exact hfinal

end GI.Impl
