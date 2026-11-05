module

public import Workspace.Impl.TermGlueLabQ
public import Workspace.Impl.TermGlueLabQInv

@[expose] public section

/-!
# The inverse of `V` by one Hermite call

Step 5 of the label program. The coordinates `x ↦ x V mod d` need `V⁻¹` for the
matrices of the linear part (`tmGLP_mat`). `tmGLPInvF hf` on `[t, t, V]` (the Hermite input of
the square matrix `V`) calls the Hermite function at `hf` and keeps the multiplier `U`. Since
`V` is unimodular, `U V = 1 = V U` (`tmGLQ_inv_of_hermite`). The spec is `tmGLPInv_spec`, with
cost `tmGLPInvC hH W`. Needs `0 < t` (the Hermite task takes at least one column).
-/

namespace GI.Impl

open GI.Cited GI.Lang Matrix

/-- A unimodular matrix has injective `mulVec`. -/
theorem tmGLP_mulVec_inj {t : ℕ} {V : Matrix (Fin t) (Fin t) ℤ} (hV : IsUnit V.det) :
    Function.Injective V.mulVec := by
  intro x y h
  have e := congrArg (V⁻¹).mulVec h
  simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hV] using e

/-- The Hermite instance of a unimodular square matrix. -/
def tmGLPInst {t : ℕ} (ht : 0 < t) (V : Matrix (Fin t) (Fin t) ℤ) (hV : IsUnit V.det) :
    FullRankInst := ⟨t, t, ht, le_rfl, V, tmGLP_mulVec_inj hV⟩

/-- **The inverse**, on `[t, t, V]`: the multiplier of the Hermite call at `hf`. -/
def tmGLPInvF (hf : ℕ) : Expr := .letE (.call hf (.var 0)) (.get (.var 1) (.nat 0))

/-- The cost bound of the inverse. -/
noncomputable def tmGLPInvC (hH : HermiteFullRank) (W : ℕ) : ℕ :=
  10 * (W + (linHermitePrim hH).boundSize W + tmGLQHW hH W + 1) + 4 * tmGLQHW hH W + 20

/-- **The inverse of a unimodular matrix.** -/
theorem tmGLPInv_spec (hH : HermiteFullRank) {P : Program} {f hf jh : ℕ}
    (hfun : P.funs[f]? = some (tmGLPInvF hf)) (hh : P.funs[hf]? = some (linHermiteF jh))
    (hjh : P.prims[jh]? = some (linHermitePrim hH)) {t : ℕ} (ht : 0 < t)
    (V : Matrix (Fin t) (Fin t) ℤ) (hV : IsUnit V.det) :
    FunAll P f (fullRankInput (tmGLPInst ht V hV)) (fun w cost => ∃ U : Matrix (Fin t) (Fin t) ℤ,
      w = encIntMatrix U ∧ U * V = 1 ∧ V * U = 1 ∧
        cost ≤ tmGLPInvC hH (fullRankInput (tmGLPInst ht V hV)).wt) := by
  let I := tmGLPInst ht V hV
  let a := fullRankInput I
  let W := a.wt
  have wm : (encIntMatrix I.A).wt < W := wt_le_wt_list (by simp)
  have hr : I.r ≤ W := by
    have hl := length_lt_wt_list ((List.finRange I.r).map fun i => linVecVal (I.A i))
    simp only [List.length_map, List.length_finRange] at hl
    exact (hl.trans wm).le
  have hc : I.c ≤ W := I.c_le.trans hr
  have hs : (fullRankInput I).cells.length ≤ W := (fullRankInput I).size_le_wt
  have hbits : (fullRankInput I).cells.length ^ linHermiteDegree hH ≤ W ^ linHermiteDegree hH :=
    Nat.pow_le_pow_left hs _
  have hmat : linMatrixWt I.r I.r ((fullRankInput I).cells.length ^ linHermiteDegree hH) ≤
      linMatrixWt W W (W ^ linHermiteDegree hH) := by unfold linMatrixWt; gcongr
  have hmat' : linMatrixWt I.r I.c ((fullRankInput I).cells.length ^ linHermiteDegree hH) ≤
      linMatrixWt W W (W ^ linHermiteDegree hH) := by unfold linMatrixWt; gcongr
  have hHW : linHermiteWt (linHermiteDegree hH) I ≤ tmGLQHW hH W := by
    unfold linHermiteWt tmGLQHW linRowSolverHermiteBudget
    omega
  have hpH := (linHermitePrim hH).bound_le hs
  apply FunAll.intro hfun
  have dh : EvalAll P [a] (.call hf (.var 0)) (fun v cost =>
      linHermiteOut (linHermiteDegree hH) I v ∧
        cost ≤ 10 * (W + (linHermitePrim hH).boundSize W + tmGLQHW hH W + 1)) := by
    apply EvalAll.call_funAll (Det.var' (P := P) (env := [a]) (i := 0) rfl)
    intro v ca hv
    obtain ⟨rfl, hca⟩ := hv
    refine (linHermite_spec hH hh hjh I).mono fun out cost ho => ⟨ho.1, ?_⟩
    have wo := linHermiteOut_wt ho.1
    have hc2 := ho.2
    unfold linHermiteCost at hc2
    simp only [W, a] at *
    omega
  refine EvalAll.letE dh fun v cv hv => ?_
  obtain ⟨⟨U, H, rfl, hU, hUM, hHerm, hUB, hHB⟩, hcv⟩ := hv
  have wUH : (Val.list [encIntMatrix U, encIntMatrix H]).wt ≤ tmGLQHW hH W :=
    (linHermiteOut_wt (d := linHermiteDegree hH) (I := I)
      ⟨U, H, rfl, hU, hUM, hHerm, hUB, hHB⟩).trans hHW
  have wU : (encIntMatrix U).wt < (Val.list [encIntMatrix U, encIntMatrix H]).wt :=
    wt_le_wt_list (by simp)
  have hinv := tmGLQ_inv_of_hermite hU hV hUM hHerm
  have dg := Det.get' (Det.var' (P := P) (env := [a] ++ [.list [encIntMatrix U, encIntMatrix H]])
    (i := 1) (v := .list [encIntMatrix U, encIntMatrix H]) rfl) (Det.nat 0)
    (vs := [encIntMatrix U, encIntMatrix H]) (v := encIntMatrix U) rfl
  refine dg.post fun c hc => ⟨U, rfl, hinv.1, hinv.2, ?_⟩
  have := Nat.le_of_lt wU
  change _ ≤ 10 * (W + (linHermitePrim hH).boundSize W + tmGLQHW hH W + 1) + 4 * tmGLQHW hH W + 20
  omega

end GI.Impl
