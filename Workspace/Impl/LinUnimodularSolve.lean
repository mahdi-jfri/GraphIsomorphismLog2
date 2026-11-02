import Workspace.Impl.LinObjectLiftCost
import Workspace.Impl.GenNormGlue

/-! Lift a finite normal-form coordinate back through the unimodular
Smith multiplier. The full-rank solver is used only in positive dimension. -/
namespace GI.Impl
open GI.Cited GI.Lang Matrix

def linUnimodularPositiveF (solve : ℕ) : Expr :=
  .letE (.call solve (mk2 (mk3 (arg 0) (arg 0) (arg 1)) (arg 2)))
    (.get (.var 1) (.nat 1))

def linUnimodularF (positive : ℕ) : Expr :=
  .ite (arg 0) (.call positive (.var 0)) .nil

def linUnimodularFuns (b jh : ℕ) : List Expr :=
  [linUnimodularF (b + 1), linUnimodularPositiveF (b + 2)] ++ linRowSystemFuns (b + 2) jh

theorem linUnimodularFuns_length (b jh : ℕ) : (linUnimodularFuns b jh).length = 60 := by
  simp [linUnimodularFuns, linRowSystemFuns_length]

structure linUnimodularAt (P : Program) (b jh : ℕ) : Prop where
  entry : P.funs[b]? = some (linUnimodularF (b + 1))
  positive : P.funs[b + 1]? = some (linUnimodularPositiveF (b + 2))
  solve : linRowSystemAt P (b + 2) jh

theorem linUnimodularAt_of {P : Program} {b jh : ℕ}
    (h : P.HasAt b (linUnimodularFuns b jh)) : linUnimodularAt P b jh := by
  have hs : P.HasAt (b + 2) (linRowSystemFuns (b + 2) jh) := by
    simpa only [List.length_cons, List.length_nil, Nat.reduceAdd] using
      (Program.HasAt.right (A := [linUnimodularF (b + 1), linUnimodularPositiveF (b + 2)])
        (B := linRowSystemFuns (b + 2) jh) h)
  exact ⟨(h.block (gs := [linUnimodularF (b + 1)]) 0 rfl).single,
    (h.block (gs := [linUnimodularPositiveF (b + 2)]) 1 rfl).single, linRowSystemAt_of hs⟩

def linUnimodularInst {d : ℕ} (V : Matrix (Fin d) (Fin d) ℤ)
    (hV : IsUnit V.det) (hd : 0 < d) : FullRankInst where
  r := d
  c := d
  c_pos := hd
  c_le := le_rfl
  A := V
  rank := by
    intro x y hxy
    have hh := congrArg (Matrix.mulVec V⁻¹) hxy
    simpa only [Matrix.mulVec_mulVec, V.nonsing_inv_mul hV, Matrix.one_mulVec] using hh

theorem linUnimodular_row_answer {d : ℕ} (V : Matrix (Fin d) (Fin d) ℤ)
    (hV : IsUnit V.det) (w : Fin d → ℤ) {out : Val} (h : linRowAnswer V w out) :
    out = .list [.nat 1, linVecVal (Matrix.vecMul w V⁻¹)] := by
  rcases h with ⟨_, hno⟩ | ⟨z, rfl, hz⟩
  · exact False.elim (hno ⟨Matrix.vecMul w V⁻¹, by
      rw [Matrix.vecMul_vecMul, V.nonsing_inv_mul hV, Matrix.vecMul_one]⟩)
  · have hh := congrArg (fun x => Matrix.vecMul x V⁻¹) hz
    dsimp only at hh
    rw [Matrix.vecMul_vecMul, V.mul_nonsing_inv hV, Matrix.vecMul_one] at hh
    rw [hh]

noncomputable def linUnimodularBudget (hH : HermiteFullRank) (W : ℕ) : ℕ :=
  linObjectLiftSolveCoefficient hH * (100 * (W + 1) + 2) ^ linObjectLiftSolveDegree hH

noncomputable def linUnimodularPositiveCost (hH : HermiteFullRank) (W : ℕ) : ℕ :=
  100000 * (W + linUnimodularBudget hH W + 1)

noncomputable def linUnimodularCost (hH : HermiteFullRank) (W : ℕ) : ℕ :=
  10000000 * (W + linUnimodularBudget hH W + 1)

theorem linUnimodularCost_poly (hH : HermiteFullRank) :
    PBU (fun _ W _ => linUnimodularCost hH W) := by
  unfold linUnimodularCost linUnimodularBudget
  norm_poly

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 3000 in
theorem linUnimodular_positive_spec (hH : HermiteFullRank) {P : Program} {b jh d : ℕ}
    (h : linUnimodularAt P b jh) (hj : P.prims[jh]? = some (linHermitePrim hH))
    (V : Matrix (Fin d) (Fin d) ℤ) (hV : IsUnit V.det) (w : Fin d → ℤ) (hd : 0 < d) :
    let a := Val.list [.nat d, encIntMatrix V, linVecVal w]
    FunAll P (b + 1) a (fun out cost => out = linVecVal (Matrix.vecMul w V⁻¹) ∧
      cost ≤ linUnimodularPositiveCost hH a.wt) := by
  let a := Val.list [.nat d, encIntMatrix V, linVecVal w]
  let W := a.wt
  let I := linUnimodularInst V hV hd
  let B := linUnimodularBudget hH W
  have wd : (Val.nat d).wt < W := wt_le_wt_list (by simp [a, W])
  have wm : (encIntMatrix V).wt < W := wt_le_wt_list (by simp [a, W])
  have ww : (linVecVal w).wt < W := wt_le_wt_list (by simp [a, W])
  have harg : (Val.list [fullRankInput I, linVecVal w]).wt ≤ 100 * (W + 1) := by
    have hh := wt_list3_le (.nat d) (.nat d) (encIntMatrix V)
    have ht := wt_list2_le (fullRankInput I) (linVecVal w)
    change (Val.list [Val.list [.nat d, .nat d, encIntMatrix V], linVecVal w]).wt ≤ _
    dsimp only [fullRankInput, I, linUnimodularInst] at ht
    omega
  have hbudget : linRowSolverCost hH I (Val.list [fullRankInput I, linVecVal w]).wt ≤ B := by
    have hh := (linRowSolverBudget_poly hH).choose_spec.choose_spec
      0 (Val.list [fullRankInput I, linVecVal w]).wt 0
    exact (linRowSolverCost_le hH I w).trans (hh.trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)))
  have hs : FunAll P (b + 2) (.list [fullRankInput I, linVecVal w])
      (fun out cost => out = .list [.nat 1, linVecVal (Matrix.vecMul w V⁻¹)] ∧ cost ≤ B) :=
    (linRowSystem_spec hH h.solve hj I w).mono fun out cost ho =>
      ⟨linUnimodular_row_answer V hV w ho.1, ho.2.trans hbudget⟩
  have dd := Det.arg' (P := P) (vs := [.nat d, encIntMatrix V, linVecVal w]) (rest := []) (j := 0) rfl
  have dm := Det.arg' (P := P) (vs := [.nat d, encIntMatrix V, linVecVal w]) (rest := []) (j := 1) rfl
  have dw := Det.arg' (P := P) (vs := [.nat d, encIntMatrix V, linVecVal w]) (rest := []) (j := 2) rfl
  apply FunAll.intro h.positive
  apply EvalAll.letE (normBound_call (Det.mk2 (Det.mk3 dd dd dm) dw) hs)
  intro ans ca hans
  obtain ⟨rfl, wans, hca⟩ := hans
  have dout := Det.get' (Det.var' (P := P)
    (env := [a, .list [.nat 1, linVecVal (Matrix.vecMul w V⁻¹)]]) (i := 1) rfl) (Det.nat 1) rfl
  refine dout.post fun cost hc => ⟨rfl, ?_⟩
  have wo : (linVecVal (Matrix.vecMul w V⁻¹)).wt <
      (Val.list [.nat 1, linVecVal (Matrix.vecMul w V⁻¹)]).wt := wt_le_wt_list (by simp)
  have hw := wt_list2_le (fullRankInput I) (linVecVal w)
  have hi : (fullRankInput I).wt < (Val.list [fullRankInput I, linVecVal w]).wt :=
    wt_le_wt_list (by simp)
  have hn : (Val.nat 1).wt = 3 := rfl
  change _ ≤ linUnimodularPositiveCost hH W
  unfold linUnimodularPositiveCost
  dsimp only [a, W, B, I, linUnimodularInst, fullRankInput] at *
  omega

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 3000 in
theorem linUnimodular_spec (hH : HermiteFullRank) {P : Program} {b jh d : ℕ}
    (h : linUnimodularAt P b jh) (hj : P.prims[jh]? = some (linHermitePrim hH))
    (V : Matrix (Fin d) (Fin d) ℤ) (hV : IsUnit V.det) (w : Fin d → ℤ) :
    let a := Val.list [.nat d, encIntMatrix V, linVecVal w]
    FunAll P b a (fun out cost => out = linVecVal (Matrix.vecMul w V⁻¹) ∧
      cost ≤ linUnimodularCost hH a.wt) := by
  let a := Val.list [.nat d, encIntMatrix V, linVecVal w]
  let W := a.wt
  have wd : (Val.nat d).wt < W := wt_le_wt_list (by simp [a, W])
  have dt := Det.arg' (P := P) (vs := [.nat d, encIntMatrix V, linVecVal w])
    (rest := []) (j := 0) rfl
  apply FunAll.intro h.entry
  apply EvalAll.ite dt (fun v cost ho => ⟨d, ho.1⟩)
  intro q cc hq
  obtain ⟨hq, hcc⟩ := hq
  have hq' : q = d := Val.nat.inj hq
  subst q
  by_cases hz : d = 0
  · rw [if_pos hz]
    have he : linVecVal (Matrix.vecMul w V⁻¹) = .list [] := by
      simp [linVecVal, hz]
    rw [he]
    refine (Det.nil (P := P) (env := [a])).post fun cost hc => ⟨rfl, ?_⟩
    have hnil : (Val.list []).wt = 4 := rfl
    change _ ≤ linUnimodularCost hH W
    unfold linUnimodularCost
    dsimp only [a, W] at *
    omega
  · rw [if_neg hz]
    apply EvalAll.call_funAll (Det.var' (P := P) (env := [a]) (i := 0) rfl)
    intro v ca hv
    obtain ⟨rfl, hca⟩ := hv
    refine (linUnimodular_positive_spec hH h hj V hV w (Nat.pos_of_ne_zero hz)).wt_lt.mono
      fun out cost ho => ⟨ho.1.1, ?_⟩
    have hw := ho.2
    have hc := ho.1.2
    change _ ≤ linUnimodularCost hH W
    unfold linUnimodularCost linUnimodularPositiveCost at *
    dsimp only [a, W] at *
    omega

end GI.Impl
