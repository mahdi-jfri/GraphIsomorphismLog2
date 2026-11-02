import Workspace.Impl.LinPrimeAction
import Workspace.Impl.LinPrimaryRecord

/-! Project both retained affine matrices by reducing their destination rows.
The original record remains available to lift the returned cover elements. -/
namespace GI.Impl
open GI.Cited GI.Lang

theorem linPrimeMatrixReduceCost_mono {W V r s : ℕ} (h : W ≤ V) (hr : r ≤ s) :
    linFiniteMatrixReduceCost W r ≤ linFiniteMatrixReduceCost V s := by
  unfold linFiniteMatrixReduceCost linFiniteMatrixReduceStepCost linFiniteMatrixReduceAcc
    linFiniteMatrixReduceRowBudget linConstRemCost linMapBudget linScalarRemCost
    linVectorAccWt linIntBinaryCost linIntCoreBudget linIntPartsCost linIntCodecCost
  gcongr

def linPrimeRecordF (reduce : ℕ) : Expr :=
  .letE (.call reduce (mk2 (arg 0) (.get (arg 1) (.nat 1))))
    (.letE (.call reduce (mk2 (arg 0) (.get (arg 1) (.nat 2))))
      (mk3 (arg 0) (.var 1) (.var 2)))

def linPrimeRecordFuns (b : ℕ) : List Expr :=
  [linPrimeRecordF (b + 1)] ++ linFiniteMatrixReduceFuns (b + 1)

theorem linPrimeRecordFuns_length (b : ℕ) : (linPrimeRecordFuns b).length = 26 := rfl

structure linPrimeRecordAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linPrimeRecordF (b + 1))
  reduce : P.HasAt (b + 1) (linFiniteMatrixReduceFuns (b + 1))

theorem linPrimeRecordAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linPrimeRecordFuns b)) : linPrimeRecordAt P b where
  entry := (h.block (gs := [linPrimeRecordF (b + 1)]) 0 rfl).single
  reduce := h.block 1 rfl

def linPrimeRecordBudget (W : ℕ) : ℕ := linFiniteMatrixReduceCost (100 * (W + 1)) W

def linPrimeRecordCost (W : ℕ) : ℕ := 100000 * (W + linPrimeRecordBudget W + 1)

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 5000 in
theorem linPrimeRecord_reduce_spec {P : Program} {b r s : ℕ} (h : linPrimeRecordAt P b)
    (q : Fin r → ℤ) (M N : Matrix (Fin r) (Fin s) ℤ) (old : Val) :
    let record := Val.list [old, encIntMatrix M, encIntMatrix N]
    let a := Val.list [linVecVal q, record]
    FunDet P b a (.list [linVecVal q, encIntMatrix (fun i j => M i j % q i),
      encIntMatrix (fun i j => N i j % q i)]) (linPrimeRecordCost a.wt) := by
  let record := Val.list [old, encIntMatrix M, encIntMatrix N]
  let a := Val.list [linVecVal q, record]
  let W := a.wt
  let U := encIntMatrix (fun i j => M i j % q i)
  let V := encIntMatrix (fun i j => N i j % q i)
  have wq : (linVecVal q).wt < W := wt_le_wt_list (by simp [a, W])
  have wr : record.wt < W := wt_le_wt_list (by simp [a, W])
  have wM : (encIntMatrix M).wt < record.wt := wt_le_wt_list (by simp [record])
  have wN : (encIntMatrix N).wt < record.wt := wt_le_wt_list (by simp [record])
  have hr : r ≤ W := by
    have hh := length_lt_wt_list ((List.finRange r).map fun i => encInt (q i))
    simp only [List.length_map, List.length_finRange] at hh
    change r < (linVecVal q).wt at hh
    omega
  have waM : (Val.list [linVecVal q, encIntMatrix M]).wt ≤ 100 * (W + 1) := by
    have := wt_list2_le (linVecVal q) (encIntMatrix M)
    omega
  have waN : (Val.list [linVecVal q, encIntMatrix N]).wt ≤ 100 * (W + 1) := by
    have := wt_list2_le (linVecVal q) (encIntMatrix N)
    omega
  have hM := (linFiniteMatrixReduce_spec h.reduce q M).mono (linPrimeMatrixReduceCost_mono waM hr)
  have hN := (linFiniteMatrixReduce_spec h.reduce q N).mono (linPrimeMatrixReduceCost_mono waN hr)
  have wU : U.wt ≤ linPrimeRecordBudget W := hM.wt_lt.le
  have wV : V.wt ≤ linPrimeRecordBudget W := hN.wt_lt.le
  have dq := Det.arg' (P := P) (vs := [linVecVal q, record]) (rest := []) (j := 0) rfl
  have dr := Det.arg' (P := P) (vs := [linVecVal q, record]) (rest := []) (j := 1) rfl
  have dM := Det.call (Det.mk2 dq (Det.get' dr (Det.nat 1) rfl)) hM
  have dq' := Det.arg' (P := P) (vs := [linVecVal q, record]) (rest := [U]) (j := 0) rfl
  have dr' := Det.arg' (P := P) (vs := [linVecVal q, record]) (rest := [U]) (j := 1) rfl
  have dN := Det.call (Det.mk2 dq' (Det.get' dr' (Det.nat 2) rfl)) hN
  have dout := Det.mk3
    (Det.arg' (P := P) (vs := [linVecVal q, record]) (rest := [U, V]) (j := 0) rfl)
    (Det.var' (P := P) (env := [a, U, V]) (i := 1) rfl)
    (Det.var' (P := P) (env := [a, U, V]) (i := 2) rfl)
  apply FunDet.intro h.entry
  refine (Det.letE dM (Det.letE dN dout)).mono ?_
  have wo := wt_list3_le (linVecVal q) U V
  have wm := wt_list2_le (linVecVal q) (encIntMatrix M)
  have wn := wt_list2_le (linVecVal q) (encIntMatrix N)
  change _ ≤ linPrimeRecordCost W
  unfold linPrimeRecordCost
  dsimp only [a, W, U, V, record, linPrimeRecordBudget] at *
  omega

theorem linPrimeRecord_spec {P : Program} {b d p : ℕ} {G : Type*} [Group G]
    (h : linPrimeRecordAt P b) {m : Fin d → ℕ}
    (D : linPrimeSplitData m p) (hm : ∀ i, 0 < m i)
    (ρ : G →* (linFiniteVec m ≃+ linFiniteVec m)) (c : G → linFiniteVec m) (g : G) :
    let a := Val.list [linVecVal (linFiniteModuli (linPrimaryOrders p D.exponent)),
      linFiniteAffineVal m ρ c g]
    FunDet P b a (linFiniteAffineVal (linPrimaryOrders p D.exponent)
      (linPrimeAction D hm ρ) (fun g => linPrimeProjection D (c g)) g)
      (linPrimeRecordCost a.wt) := by
  simpa only [linFiniteAffineVal, linPrimeAction_homogeneous] using
    linPrimeRecord_reduce_spec h (linFiniteModuli (linPrimaryOrders p D.exponent))
      (linFiniteActionMatrix m ρ c g) (linFiniteActionMatrix m ρ c g⁻¹)
      (linVecVal (linFiniteModuli m))

theorem linPrimeRecordCost_poly : PBU (fun _ W _ => linPrimeRecordCost W) := by
  have hh := linPoly_subst linFiniteMatrixReduceCost_poly PBU.W
    (PBU.smul 100 (PBU.addc PBU.W 1)) (PBU.const 0)
  exact PBU.smul 100000 (PBU.addc (PBU.add PBU.W hh) 1)

end GI.Impl
