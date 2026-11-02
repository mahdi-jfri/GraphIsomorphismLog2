import Workspace.Impl.TermGlueLabPTr
import Workspace.Impl.LinFiniteProduct

/-!
# The matrix program of the linear part

Step 5 of the label program. On `[ctx, C]` with `ctx = [t, U, V, d]` (`U`, `V`,
`C` square of size `t`, `d` a vector), `tmGLPMatF mul tr red` returns the matrix
`(i, j) ↦ (U C V)_{j i} mod d_i`: two products by termlin's `linDenseMul` (at `mul`), the
transpose (`tmGLPTrFuns`, at `tr`) and termlin's row reduction `linFiniteMatrixReduce` (at `red`).
By `tmGLP_mat` this is the contract's matrix of `κ_h` in the coordinates `E` when the rows of `C`
are coordinates of `h⁻¹ a_j h` and `U = V⁻¹` (`tmGLPMat_spec`, cost `tmGLPMatC W t`).
-/

namespace GI.Impl

open GI.Lang
open GI.Cited (Val encInt encIntMatrix)

/-- The weight of a computed value is below its cost bound. -/
theorem tmGLP_fundet_wt {P : Program} {f : ℕ} {a v : Val} {c : ℕ} (h : FunDet P f a v c) :
    v.wt < c := by
  obtain ⟨body, -, he⟩ := FunAll.wt_lt h
  obtain ⟨w, c', -, ⟨rfl, hc⟩, hw⟩ := EvalAll.exists_eval he
  omega

/-- A call with bounded argument cost and bounded callee cost. -/
theorem tmGLP_call_le {P : Program} {env : List Val} {a : Expr} {f : ℕ} {vin vout : Val}
    {ca cb A C : ℕ} (ha : Det P env a vin ca) (hca : ca ≤ A) (hf : FunDet P f vin vout cb)
    (hcb : cb ≤ C) : Det P env (.call f a) vout (A + 2 * C + 1) ∧ vout.wt < C := by
  have hw := tmGLP_fundet_wt hf
  exact ⟨(Det.call ha hf).mono (by omega), by omega⟩

/-- A pair of values with bounded costs and weights. -/
theorem tmGLP_mk2_le {P : Program} {env : List Val} {a b : Expr} {va vb : Val}
    {ca cb A B X Y : ℕ} (ha : Det P env a va ca) (hca : ca ≤ A) (hb : Det P env b vb cb)
    (hcb : cb ≤ B) (hX : va.wt ≤ X) (hY : vb.wt ≤ Y) :
    Det P env (mk2 a b) (.list [va, vb]) (A + B + 4 * (X + Y) + 19) ∧
      (Val.list [va, vb]).wt ≤ 2 * (X + Y) + 6 := by
  have h := wt_list2_le va vb
  exact ⟨(Det.mk2 ha hb).mono (by omega), by omega⟩

/-- The context `[t, U, V, d]`. -/
def tmGLPMCtx {t : ℕ} (U V : Matrix (Fin t) (Fin t) ℤ) (d : Fin t → ℤ) : Val :=
  .list [.nat t, encIntMatrix U, encIntMatrix V, linVecVal d]

/-- **The matrix program**, on `[ctx, C]`. -/
def tmGLPMatF (mul tr red : ℕ) : Expr :=
  .call red (mk2 (.get (arg 0) (.nat 3))
    (.call tr (mk2 (.get (arg 0) (.nat 0))
      (.call mul (mk2 (mk2 (.get (arg 0) (.nat 0))
        (.call mul (mk2 (mk2 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 2))) (arg 1))))
        (.get (arg 0) (.nat 1)))))))

/-- Bound of the first product. -/
def tmGLPMatC1 (W t : ℕ) : ℕ := linMatrixMulCost (2 * (2 * (W + W) + 6 + W) + 6) t t t

/-- Bound of the second product. -/
def tmGLPMatC2 (W t : ℕ) : ℕ :=
  linMatrixMulCost (2 * (2 * (W + tmGLPMatC1 W t) + 6 + W) + 6) t t t

/-- Bound of the transpose. -/
def tmGLPMatC3 (W t : ℕ) : ℕ := tmGLPTrC (2 * (W + tmGLPMatC2 W t) + 6) t t

/-- Bound of the reduction. -/
def tmGLPMatC4 (W t : ℕ) : ℕ :=
  linFiniteMatrixReduceCost (2 * (W + tmGLPMatC3 W t) + 6) t

/-- **The cost bound of the matrix program.** -/
def tmGLPMatC (W t : ℕ) : ℕ :=
  1000 * (W + 1) + 2 * tmGLPMatC1 W t + 2 * tmGLPMatC2 W t + 2 * tmGLPMatC3 W t +
    2 * tmGLPMatC4 W t + 100 * (tmGLPMatC1 W t + tmGLPMatC2 W t + tmGLPMatC3 W t) + 100

theorem tmGLPTrC_mono {W V r c : ℕ} (h : W ≤ V) : tmGLPTrC W r c ≤ tmGLPTrC V r c := by
  unfold tmGLPTrC tmGLPTrColC tmGLPColW
  have := linColumnCost_mono (show 2 * (W + c + 2) + 6 ≤ 2 * (V + c + 2) + 6 by omega) r
  gcongr

/-- **The matrix program.** On `[[t, U, V, d], C]` it returns the matrix
`(i, j) ↦ (U C V)_{j i} mod d_i`. -/
theorem tmGLPMat_spec {P : Program} {f mul tr red : ℕ} (hf : P.funs[f]? = some (tmGLPMatF mul tr red))
    (hmul : linDenseMulAt P mul) (htr : P.HasAt tr (tmGLPTrFuns tr))
    (hred : P.HasAt red (linFiniteMatrixReduceFuns red)) {t : ℕ}
    (U V C : Matrix (Fin t) (Fin t) ℤ) (d : Fin t → ℤ) :
    FunDet P f (.list [tmGLPMCtx U V d, encIntMatrix C])
      (encIntMatrix (fun i j => (U * C * V) j i % d i))
      (tmGLPMatC (Val.list [tmGLPMCtx U V d, encIntMatrix C]).wt t) := by
  set W := (Val.list [tmGLPMCtx U V d, encIntMatrix C]).wt with hW
  have wx : (tmGLPMCtx U V d).wt < W := wt_le_wt_list (by simp)
  have wC : (encIntMatrix C).wt < W := wt_le_wt_list (by simp)
  have wt' : (Val.nat t).wt < (tmGLPMCtx U V d).wt := wt_le_wt_list (by simp)
  have wU : (encIntMatrix U).wt < (tmGLPMCtx U V d).wt := wt_le_wt_list (by simp)
  have wV : (encIntMatrix V).wt < (tmGLPMCtx U V d).wt := wt_le_wt_list (by simp)
  have wd : (linVecVal d).wt < (tmGLPMCtx U V d).wt := wt_le_wt_list (by simp)
  have ga0 := Det.arg' (P := P) (vs := [tmGLPMCtx U V d, encIntMatrix C]) (rest := []) (j := 0) rfl
  have ga1 := Det.arg' (P := P) (vs := [tmGLPMCtx U V d, encIntMatrix C]) (rest := []) (j := 1) rfl
  have dt := Det.get' ga0 (Det.nat 0) (vs := [.nat t, encIntMatrix U, encIntMatrix V, linVecVal d])
    (v := .nat t) rfl
  have dU := Det.get' ga0 (Det.nat 1) (vs := [.nat t, encIntMatrix U, encIntMatrix V, linVecVal d])
    (v := encIntMatrix U) rfl
  have dV := Det.get' ga0 (Det.nat 2) (vs := [.nat t, encIntMatrix U, encIntMatrix V, linVecVal d])
    (v := encIntMatrix V) rfl
  have dd := Det.get' ga0 (Det.nat 3) (vs := [.nat t, encIntMatrix U, encIntMatrix V, linVecVal d])
    (v := linVecVal d) rfl
  -- the first product `C V`
  have p1 := tmGLP_mk2_le dt (A := 4 * W + 10) (by omega) dV (B := 4 * W + 10) (by omega)
    (X := W) (Y := W) (by omega) (by omega)
  have p2 := tmGLP_mk2_le p1.1 le_rfl ga1 (B := 2 * W + 6) (by omega) (X := 2 * (W + W) + 6)
    (Y := W) p1.2 (by omega)
  have c1 := tmGLP_call_le p2.1 le_rfl (linDenseMul_spec hmul C V) (C := tmGLPMatC1 W t)
    (linDenseMulCost_mono p2.2)
  -- the second product `U (C V)`
  have q1 := tmGLP_mk2_le dt (A := 4 * W + 10) (by omega) c1.1 le_rfl (X := W)
    (Y := tmGLPMatC1 W t) (by omega) c1.2.le
  have q2 := tmGLP_mk2_le q1.1 le_rfl dU (B := 4 * W + 10) (by omega)
    (X := 2 * (W + tmGLPMatC1 W t) + 6) (Y := W) q1.2 (by omega)
  have c2 := tmGLP_call_le q2.1 le_rfl (linDenseMul_spec hmul U (C * V)) (C := tmGLPMatC2 W t)
    (linDenseMulCost_mono q2.2)
  -- the transpose
  have r1 := tmGLP_mk2_le dt (A := 4 * W + 10) (by omega) c2.1 le_rfl (X := W)
    (Y := tmGLPMatC2 W t) (by omega) c2.2.le
  have c3 := tmGLP_call_le r1.1 le_rfl (tmGLPTr_spec htr (U * (C * V))) (C := tmGLPMatC3 W t)
    (tmGLPTrC_mono r1.2)
  -- the reduction
  have s1 := tmGLP_mk2_le dd (A := 4 * W + 10) (by omega) c3.1 le_rfl (X := W)
    (Y := tmGLPMatC3 W t) (by omega) c3.2.le
  have c4 := tmGLP_call_le s1.1 le_rfl (linFiniteMatrixReduce_spec hred d (U * (C * V)).transpose)
    (C := tmGLPMatC4 W t) (linFiniteMatrixReduceCost_mono s1.2)
  have e : (fun i j => (U * (C * V)).transpose i j % d i) = (fun i j => (U * C * V) j i % d i) := by
    rw [Matrix.mul_assoc]; rfl
  rw [e] at c4
  refine FunDet.intro hf (c4.1.mono ?_)
  unfold tmGLPMatC
  omega

/-! ### The offset vectors -/

/-- **The vector program**, on `[ctx, z]`: the vector `i ↦ (z V)_i mod d_i`, as the column of
`((z) V)ᵀ` reduced by rows (the column reader of the transpose module at `tr + 8`). -/
def tmGLPVecF (mul tr red : ℕ) : Expr :=
  .call (tr + 8) (mk2 (.nat 0) (.call red (mk2 (.get (arg 0) (.nat 3))
    (.call tr (mk2 (.get (arg 0) (.nat 0))
      (.call mul (mk2 (mk2 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 2))) (mk1 (arg 1)))))))))

/-- Bound of the product. -/
def tmGLPVecC1 (W t : ℕ) : ℕ := linMatrixMulCost (2 * (2 * (W + W) + 6 + (2 * W + 6)) + 6) 1 t t

/-- Bound of the transpose. -/
def tmGLPVecC2 (W t : ℕ) : ℕ := tmGLPTrC (2 * (W + tmGLPVecC1 W t) + 6) 1 t

/-- Bound of the reduction. -/
def tmGLPVecC3 (W t : ℕ) : ℕ := linFiniteMatrixReduceCost (2 * (W + tmGLPVecC2 W t) + 6) t

/-- Bound of the column. -/
def tmGLPVecC4 (W t : ℕ) : ℕ := linColumnCost (2 * (3 + tmGLPVecC3 W t) + 6) t

/-- **The cost bound of the vector program.** -/
def tmGLPVecC (W t : ℕ) : ℕ :=
  1000 * (W + 1) + 2 * tmGLPVecC1 W t + 2 * tmGLPVecC2 W t + 2 * tmGLPVecC3 W t +
    2 * tmGLPVecC4 W t + 100 * (tmGLPVecC1 W t + tmGLPVecC2 W t + tmGLPVecC3 W t) + 100

/-- A vector as a matrix with one row. -/
theorem tmGLP_row_enc {t : ℕ} (z : Fin t → ℤ) :
    Val.list [linVecVal z] = encIntMatrix (Matrix.of fun (_ : Fin 1) j => z j) := rfl

/-- **The vector program.** -/
theorem tmGLPVec_spec {P : Program} {f mul tr red : ℕ} (hf : P.funs[f]? = some (tmGLPVecF mul tr red))
    (hmul : linDenseMulAt P mul) (htr : P.HasAt tr (tmGLPTrFuns tr))
    (hred : P.HasAt red (linFiniteMatrixReduceFuns red)) {t : ℕ}
    (U V : Matrix (Fin t) (Fin t) ℤ) (d : Fin t → ℤ) (z : Fin t → ℤ) :
    FunDet P f (.list [tmGLPMCtx U V d, linVecVal z])
      (linVecVal fun i => Matrix.vecMul z V i % d i)
      (tmGLPVecC (Val.list [tmGLPMCtx U V d, linVecVal z]).wt t) := by
  set W := (Val.list [tmGLPMCtx U V d, linVecVal z]).wt with hW
  have hcol : P.HasAt (tr + 8) (linColumnFuns (tr + 8)) := htr.block 8 rfl
  have wx : (tmGLPMCtx U V d).wt < W := wt_le_wt_list (by simp)
  have wz : (linVecVal z).wt < W := wt_le_wt_list (by simp)
  have wt' : (Val.nat t).wt < (tmGLPMCtx U V d).wt := wt_le_wt_list (by simp)
  have wV : (encIntMatrix V).wt < (tmGLPMCtx U V d).wt := wt_le_wt_list (by simp)
  have wd : (linVecVal d).wt < (tmGLPMCtx U V d).wt := wt_le_wt_list (by simp)
  have ga0 := Det.arg' (P := P) (vs := [tmGLPMCtx U V d, linVecVal z]) (rest := []) (j := 0) rfl
  have ga1 := Det.arg' (P := P) (vs := [tmGLPMCtx U V d, linVecVal z]) (rest := []) (j := 1) rfl
  have dt := Det.get' ga0 (Det.nat 0) (vs := [.nat t, encIntMatrix U, encIntMatrix V, linVecVal d])
    (v := .nat t) rfl
  have dV := Det.get' ga0 (Det.nat 2) (vs := [.nat t, encIntMatrix U, encIntMatrix V, linVecVal d])
    (v := encIntMatrix V) rfl
  have dd := Det.get' ga0 (Det.nat 3) (vs := [.nat t, encIntMatrix U, encIntMatrix V, linVecVal d])
    (v := linVecVal d) rfl
  have dr := Det.mk1 ga1
  rw [tmGLP_row_enc] at dr
  have wr : (encIntMatrix (Matrix.of fun (_ : Fin 1) j => z j)).wt ≤ 2 * W + 6 := by
    rw [← tmGLP_row_enc]
    have := wt_list_le [linVecVal z]
    simp at this
    omega
  -- the product `(z) V`
  have p1 := tmGLP_mk2_le dt (A := 4 * W + 10) (by omega) dV (B := 4 * W + 10) (by omega)
    (X := W) (Y := W) (by omega) (by omega)
  have p2 := tmGLP_mk2_le p1.1 le_rfl dr (B := 6 * W + 20) (by omega) (X := 2 * (W + W) + 6)
    (Y := 2 * W + 6) p1.2 wr
  have c1 := tmGLP_call_le p2.1 le_rfl (linDenseMul_spec hmul (Matrix.of fun (_ : Fin 1) j => z j) V)
    (C := tmGLPVecC1 W t) (linDenseMulCost_mono p2.2)
  -- the transpose
  have r1 := tmGLP_mk2_le dt (A := 4 * W + 10) (by omega) c1.1 le_rfl (X := W)
    (Y := tmGLPVecC1 W t) (by omega) c1.2.le
  have c2 := tmGLP_call_le r1.1 le_rfl (tmGLPTr_spec htr ((Matrix.of fun (_ : Fin 1) j => z j) * V))
    (C := tmGLPVecC2 W t) (tmGLPTrC_mono r1.2)
  -- the reduction
  have s1 := tmGLP_mk2_le dd (A := 4 * W + 10) (by omega) c2.1 le_rfl (X := W)
    (Y := tmGLPVecC2 W t) (by omega) c2.2.le
  have c3 := tmGLP_call_le s1.1 le_rfl
    (linFiniteMatrixReduce_spec hred d ((Matrix.of fun (_ : Fin 1) j => z j) * V).transpose)
    (C := tmGLPVecC3 W t) (linFiniteMatrixReduceCost_mono s1.2)
  -- the column
  have u1 := tmGLP_mk2_le (Det.nat 0) (A := 3) (by omega) c3.1 le_rfl (X := 3)
    (Y := tmGLPVecC3 W t) (by have := wt_nat_le 0; omega) c3.2.le
  have c4 := tmGLP_call_le u1.1 le_rfl (linColumn_spec hcol _ (0 : Fin 1))
    (C := tmGLPVecC4 W t) (linColumnCost_mono u1.2 t)
  have e : (fun i => ((Matrix.of fun (_ : Fin 1) j => z j) * V).transpose i 0 % d i) =
      (fun i => Matrix.vecMul z V i % d i) := by
    funext i
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  rw [e] at c4
  refine FunDet.intro hf (c4.1.mono ?_)
  unfold tmGLPVecC
  omega

end GI.Impl
