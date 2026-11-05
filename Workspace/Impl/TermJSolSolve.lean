module

public import Workspace.Impl.TermJSolProg

@[expose] public section

/-!
# The zero-sum solve (specification)

`tmJSol_solve_spec`: on `[encIntMatrix M, encIntMatrix B, linVecVal s]`, the entry `b` of
`tmJSolFuns b j` returns `.list [.nat 1, linVecVal c]` for some `c` with
`s + c ᵥ* B + y ᵥ* M = 0` for some `y`, and `.nat 0` when there is no such `c`.
The rows of `B` are the vectors `β_1, …, β_G`: `encIntMatrix B` is the list of the
`linVecVal (B i)`. The cost is at most `tmJSolSolveBudget hH W` in the input weight `W`, a fixed
polynomial (`tmJSol_solve_spec_poly`).
-/

namespace GI.Impl
open GI.Lang
open GI.Cited (Val encInt encIntMatrix FullRankInst fullRankInput)
open _root_.Matrix
set_option maxHeartbeats 4000000

/-- The answer of the zero-sum solve. -/
def tmJSolSolveAnswer {t G : ℕ} (M : Matrix (Fin t) (Fin t) ℤ) (B : Matrix (Fin G) (Fin t) ℤ)
    (s : Fin t → ℤ) (out : Val) : Prop :=
  (out = .nat 0 ∧ ¬ ∃ (c : Fin G → ℤ) (y : Fin t → ℤ), s + c ᵥ* B + y ᵥ* M = 0) ∨
    ∃ c : Fin G → ℤ, out = .list [.nat 1, linVecVal c] ∧
      ∃ y : Fin t → ℤ, s + c ᵥ* B + y ᵥ* M = 0

/-- A deterministic result weighs less than its cost bound. -/
theorem tmJSol_funDet_wt {P : Program} {f : ℕ} {v w : Val} {c : ℕ} (h : FunDet P f v w c) :
    w.wt < c := by
  obtain ⟨body, -, he⟩ := FunAll.wt_lt h
  obtain ⟨w', c', -, ⟨rfl, hc⟩, hw⟩ := EvalAll.exists_eval he
  omega

theorem tmJSol_rowBudget_mono (hH : GI.Cited.HermiteFullRank) {W V : ℕ} (h : W ≤ V) :
    linRowSolverBudget hH W ≤ linRowSolverBudget hH V := by
  have hh : linRowSolverHermiteBudget hH W ≤ linRowSolverHermiteBudget hH V := by
    unfold linRowSolverHermiteBudget linMatrixWt; gcongr
  have hp : (linHermitePrim hH).boundSize W ≤ (linHermitePrim hH).boundSize V := by
    unfold Prim.boundSize; gcongr
  have hf := linHermiteFinishCost_mono_all
    (show 10 * (W + linRowSolverHermiteBudget hH W + W + 1) ≤
      10 * (V + linRowSolverHermiteBudget hH V + V + 1) by omega) h h
    (Nat.pow_le_pow_left h (linHermiteDegree hH)) h
  unfold linRowSolverBudget
  dsimp only
  omega

/-! ### The cost budget, in the input weight `W` -/

/-- The weight of `-s`. -/
def tmJSolNegWt (W : ℕ) : ℕ := 2 * (W * (20 * (2 * (2 * W + 86) + 1))) + W + 4
/-- The weight of the input of the row solver. -/
def tmJSolRsIn (W : ℕ) : ℕ := 2 * (tmJSolStackWt W + tmJSolNegWt W) + 6
/-- The cost of the row solver. -/
noncomputable def tmJSolRsB (hH : GI.Cited.HermiteFullRank) (W : ℕ) : ℕ :=
  linRowSolverBudget hH (tmJSolRsIn W)
/-- The weight of the input of the final drop. -/
noncomputable def tmJSolDropIn (hH : GI.Cited.HermiteFullRank) (W : ℕ) : ℕ :=
  2 * (W + 2 + tmJSolRsB hH W) + 6

/-- The cost budget of the solve. -/
noncomputable def tmJSolSolveBudget (hH : GI.Cited.HermiteFullRank) (W : ℕ) : ℕ :=
  1000 * (W + tmJSolStackCost W + tmJSolStackWt W + linVectorScaleCost (2 * W + 86) W +
    tmJSolNegWt W + tmJSolRsIn W + tmJSolRsB hH W + tmJSolDropIn hH W +
    tmJSolDropCost (tmJSolDropIn hH W) + 1)

/-- The weight of `-s`, from the weight `W` of an input that contains `s`. -/
theorem tmJSol_negWt {t : ℕ} (s : Fin t → ℤ) (W : ℕ) (ht : t ≤ W)
    (hs : (linVecVal s).wt < W) :
    (linVecVal fun i => -1 * s i).wt ≤ tmJSolNegWt W := by
  have hm1 : (encInt (-1)).wt ≤ 40 := by
    rw [show encInt (-1) = .list [.nat 1, .list [.nat 1]] from rfl]; decide
  have hb : ∀ v ∈ (List.finRange t).map (fun i => encInt (-1 * s i)),
      v.wt ≤ 20 * (2 * (2 * W + 86) + 1) := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
    exact linEncIntMulWt _ _ _ (by omega) (by have := linVecEntryWt s i; omega)
  have h := linWtList hb
  simp only [List.length_map, List.length_finRange] at h
  have hm := Nat.mul_le_mul_right (20 * (2 * (2 * W + 86) + 1)) ht
  change (Val.list ((List.finRange t).map fun i => encInt (-1 * s i))).wt ≤ _
  unfold tmJSolNegWt
  generalize 20 * (2 * (2 * W + 86) + 1) = X at h hm ⊢
  omega

set_option maxRecDepth 20000 in
/-- **The zero-sum solve.** -/
theorem tmJSol_solve_spec (hH : GI.Cited.HermiteFullRank) {P : Program} {b j : ℕ}
    (hA : tmJSolAt P b j) (hj : P.prims[j]? = some (linHermitePrim hH))
    {t G : ℕ} (ht : 0 < t) (M : Matrix (Fin t) (Fin t) ℤ) (hM : M.det ≠ 0)
    (B : Matrix (Fin G) (Fin t) ℤ) (s : Fin t → ℤ) :
    FunAll P b (.list [encIntMatrix M, encIntMatrix B, linVecVal s]) (fun out cost =>
      tmJSolSolveAnswer M B s out ∧
      cost ≤ tmJSolSolveBudget hH (Val.list [encIntMatrix M, encIntMatrix B, linVecVal s]).wt) := by
  let a := Val.list [encIntMatrix M, encIntMatrix B, linVecVal s]
  let W := a.wt
  let I := tmJSolInst ht M B hM
  let w : Fin t → ℤ := fun i => -1 * s i
  let negs := linVecVal w
  have wM : (encIntMatrix M).wt < W := wt_le_wt_list (by simp)
  have wsv : (linVecVal s).wt < W := wt_le_wt_list (by simp)
  have lM := length_lt_wt_list (tmJSolRows M)
  simp only [tmJSolRows_length] at lM
  have htW : t < W := lM.trans wM
  -- stacking
  have hst := tmJSolStack_spec hA.stack hA.app ht M B hM [linVecVal s]
  have dst := Det.call (Det.var' (P := P) (env := [a]) (i := 0) rfl) hst.1
  have wI : (fullRankInput I).wt ≤ tmJSolStackWt W := hst.2
  -- negation
  have hm1 : (encInt (-1)).wt ≤ 40 := by
    rw [show encInt (-1) = .list [.nat 1, .list [.nat 1]] from rfl]; decide
  let e2 := [a, fullRankInput I]
  have dm1 : Det P e2 linIntMinusOneE (encInt (-1)) 100 :=
    (Det.mk2 (Det.nat 1) (Det.mk1 (Det.nat 1))).mono (by decide)
  have ds2 := Det.arg' (P := P) (vs := [encIntMatrix M, encIntMatrix B, linVecVal s])
    (rest := [fullRankInput I]) (j := 2) rfl
  have hsc := linVectorScale_spec hA.ints hA.scale (-1) s
  have wsc := tmJSol_funDet_wt hsc
  have wsin := wt_list2_le (encInt (-1)) (linVecVal s)
  have hscm := linVectorScaleCost_mono (show (Val.list [encInt (-1), linVecVal s]).wt ≤
    2 * W + 86 by omega) htW.le
  have dsc := Det.call (Det.mk2 dm1 ds2) hsc
  have wneg : negs.wt ≤ tmJSolNegWt W := tmJSol_negWt s W htW.le wsv
  -- the row solver
  let e3 := [a, fullRankInput I, negs]
  have wrin := wt_list2_le (fullRankInput I) negs
  have hrin : (Val.list [fullRankInput I, negs]).wt ≤ tmJSolRsIn W := by
    unfold tmJSolRsIn; omega
  have hrb : linRowSolverCost hH I (Val.list [fullRankInput I, negs]).wt ≤
      tmJSolRsB hH W :=
    (linRowSolverCost_le hH I w).trans (tmJSol_rowBudget_mono hH hrin)
  have d1 := Det.var' (P := P) (env := e3) (i := 1) rfl
  have d2 := Det.var' (P := P) (env := e3) (i := 2) rfl
  have darg := Det.mk2 d1 d2
  have dsolve : EvalAll P e3 (.call (b + 9) (mk2 (.var 1) (.var 2))) (fun v c =>
      linRowAnswer I.A w v ∧ v.wt < tmJSolRsB hH W ∧
        c ≤ 3 * (W + tmJSolRsIn W + tmJSolRsB hH W) + 20) := by
    apply EvalAll.call_funAll darg
    rintro v ca ⟨rfl, hca⟩
    refine (linRowSolver_spec hH hA.rs hA.her hj hA.fin hA.take hA.tri hA.triF hA.lift hA.liftF
      I w).wt_lt.mono fun out cost ho => ?_
    have h1 : cost ≤ linRowSolverCost hH I (Val.list [fullRankInput I, negs]).wt := ho.1.2
    have h2 : out.wt < cost := ho.2
    have hca' : ca ≤ (fullRankInput I).wt + 1 + (negs.wt + 1) +
        2 * (Val.list [fullRankInput I, negs]).wt + 7 := hca
    refine ⟨ho.1.1, by omega, ?_⟩
    unfold tmJSolRsIn at *
    omega
  -- assemble
  apply FunAll.intro hA.solve
  apply EvalAll.letE dst
  rintro v1 c1 ⟨rfl, hc1⟩
  have hc1' : c1 ≤ W + 1 + tmJSolStackCost W + (fullRankInput I).wt + 1 := hc1
  apply EvalAll.letE dsc
  rintro v2 c2 ⟨rfl, hc2⟩
  have w11 : (Val.list [Val.nat 1]).wt ≤ 20 := by decide
  have w1 : (Val.nat 1).wt = 3 := rfl
  have hc2' : c2 ≤ 2 * W + 400 + 2 * (2 * W + 86) + linVectorScaleCost (2 * W + 86) W +
      negs.wt := by
    have e1 : (Val.list [encIntMatrix M, encIntMatrix B, linVecVal s]).wt = W := rfl
    have e2 : (linVecVal fun i => -1 * s i).wt = negs.wt := rfl
    omega
  apply EvalAll.letE dsolve
  rintro v3 c3 ⟨hans, wv3, hc3⟩
  let e4 := [a, fullRankInput I, negs, v3]
  have dv3 := Det.var' (P := P) (env := e4) (i := 3) (v := v3) rfl
  have hscW : linVectorScaleCost (Val.list [encInt (-1), linVecVal s]).wt t ≤
      linVectorScaleCost (2 * W + 86) W := hscm
  rcases hans with ⟨rfl, hno⟩ | ⟨z, rfl, hz⟩
  · -- no solution
    have dt := Det.isNat dv3
    have d := Det.ite_pos (e := mk2 (.nat 1) (.call (b + 3) (mk2 (.length (arg 0))
      (.get (.var 3) (.nat 1))))) dt (by decide) (Det.nat (P := P) (env := e4) 0)
    refine d.post fun cost hc => ⟨Or.inl ⟨rfl, ?_⟩, ?_⟩
    · intro hex
      exact hno ((tmJSol_solve_exists M B s).mp hex)
    · have wn0 : (Val.nat 0).wt = 2 := rfl
      have hm1' := hm1
      change cost ≤ (Val.nat 0).wt + 1 + 4 + (0 + 3) + (Val.nat 0).wt + 1 at hc
      have := wt_list2_le (encInt (-1)) (linVecVal s)
      change _ ≤ tmJSolSolveBudget hH W
      unfold tmJSolSolveBudget
      omega
  · -- a solution
    have dt := Det.isNat dv3
    have d0 : Det P e4 (arg 0) (.list (tmJSolRows M)) _ :=
      Det.arg' (P := P) (vs := [encIntMatrix M, encIntMatrix B, linVecVal s])
        (rest := [fullRankInput I, negs, .list [.nat 1, linVecVal z]]) (j := 0) rfl
    have dl := Det.length d0
    simp only [tmJSolRows_length] at dl
    have dz := Det.get' dv3 (Det.nat 1) (show [Val.nat 1, linVecVal z][1]? = some (linVecVal z)
      from rfl)
    have hdr := tmJSolDrop_vec_spec hA.drop (t := t) (G := G) z
    have wdr := tmJSol_funDet_wt hdr
    have dcall := Det.call (Det.mk2 dl dz) hdr
    have dout := Det.mk2 (Det.nat (P := P) (env := e4) 1) dcall
    have d := Det.ite_zero (t := Expr.nat 0) dt dout
    refine d.post fun cost hc => ⟨Or.inr ⟨fun k => z (Fin.natAdd t k), rfl,
      fun i => z (Fin.castAdd G i), ?_⟩, ?_⟩
    · exact (tmJSol_solve_iff M B s z).mp hz
    · have wz : (linVecVal z).wt < (Val.list [.nat 1, linVecVal z]).wt := wt_le_wt_list (by simp)
      have wdin := wt_list2_le (.nat t) (linVecVal z)
      have wt0 := wt_nat_le t
      have hdin : (Val.list [.nat t, linVecVal z]).wt ≤ tmJSolDropIn hH W := by
        unfold tmJSolDropIn; omega
      have hdc := tmJSolDropCost_mono hdin
      have wo := wt_list2_le (.nat 1) (linVecVal fun k => z (Fin.natAdd t k))
      have wn1 : (Val.nat 1).wt = 3 := rfl
      have e5 : (linVecVal (n := I.r) z).wt = (linVecVal (n := t + G) z).wt := rfl
      have e6 : (Val.list [.nat t, linVecVal (n := I.r) z]).wt =
          (Val.list [.nat t, linVecVal (n := t + G) z]).wt := rfl
      have e7 : tmJSolDropCost (Val.list [.nat t, linVecVal (n := I.r) z]).wt =
          tmJSolDropCost (Val.list [.nat t, linVecVal (n := t + G) z]).wt := rfl
      have e8 : (Val.list [.nat 1, linVecVal (n := I.r) z]).wt =
          (Val.list [.nat 1, linVecVal (n := t + G) z]).wt := rfl
      have hWa : (Val.list [encIntMatrix M, encIntMatrix B, linVecVal s]).wt = W := rfl
      change _ ≤ tmJSolSolveBudget hH W
      unfold tmJSolSolveBudget
      clear * - hc hc1' hc2' hc3 wv3 wz wdin wt0 hdin hdc wo wn1 e5 e6 e7 e8 hWa wdr htW wI wneg
        hscW
      omega

end GI.Impl
