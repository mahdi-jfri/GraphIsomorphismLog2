import Workspace.Impl.LinIntFinish
import Workspace.Impl.LinNormal

/-! The full-column-rank integer row solver. Its only cited call is the
Hermite task. Everything after that call is a proved language program. -/
namespace GI.Impl
open GI.Cited GI.Lang Matrix

/-- Input [[r,c,M],w]. Hermite returns [U,H]. -/
def linRowSolverF (hermite finish : ℕ) : Expr :=
  .letE (.call hermite (arg 0))
    (.call finish (mk4 (.get (arg 0) (.nat 0)) (.get (.var 1) (.nat 0))
      (.get (.var 1) (.nat 1)) (arg 1)))

/-- Observable result for a rectangular integer row equation. -/
def linRowAnswer {r c : ℕ} (M : Matrix (Fin r) (Fin c) ℤ) (w : Fin c → ℤ) (out : Val) : Prop :=
  (out = .nat 0 ∧ ¬ ∃ z, z ᵥ* M = w) ∨
    ∃ z : Fin r → ℤ, out = .list [.nat 1, linVecVal z] ∧ z ᵥ* M = w

theorem linHermiteSolve_answer {r c : ℕ} (hcr : c ≤ r)
    (M H : Matrix (Fin r) (Fin c) ℤ) (U : Matrix (Fin r) (Fin r) ℤ)
    (hU : IsUnit U.det) (h : U * M = H) (hH : IsHermiteForm H) (w : Fin c → ℤ) :
    linRowAnswer M w (linTriVal (linHermiteSolve hcr U H w)) := by
  cases hs : linHermiteSolve hcr U H w with
  | none => exact Or.inl ⟨rfl, (linHermiteSolve_none_iff hcr M H U hU h hH w).mp hs⟩
  | some z => exact Or.inr ⟨z, rfl, linHermiteSolve_sound hcr M H U h hH w z hs⟩

noncomputable def linRowSolverArg (h : HermiteFullRank) (I : FullRankInst) (W : ℕ) : ℕ :=
  10 * (W + linHermiteWt (linHermiteDegree h) I + I.r + 1)

noncomputable def linRowSolverFinishCost (h : HermiteFullRank) (I : FullRankInst) (W : ℕ) : ℕ :=
  linHermiteFinishCost (linRowSolverArg h I W) I.r I.c
    ((fullRankInput I).cells.length ^ linHermiteDegree h) W

/-- A fixed polynomial expression in the input size, dimensions and the fixed
Hermite-task exponent and time bound. No enumeration of integer coefficients. -/
noncomputable def linRowSolverCost (h : HermiteFullRank) (I : FullRankInst) (W : ℕ) : ℕ :=
  1000 * (W + I.r + linHermiteCost h I + linHermiteWt (linHermiteDegree h) I +
    linRowSolverFinishCost h I W + 1)

set_option maxHeartbeats 2000000 in
theorem linRowSolver_spec (hH : HermiteFullRank) {P : Program} {f hermite finish j take tri lift : ℕ}
    {TI : linTriIndices} {LI : linLiftIndices}
    (hf : P.funs[f]? = some (linRowSolverF hermite finish))
    (hh : P.funs[hermite]? = some (linHermiteF j))
    (hj : P.prims[j]? = some (linHermitePrim hH))
    (hfinish : P.funs[finish]? = some (linHermiteFinishF take tri lift))
    (ht : P.HasAt take (linTakeFuns take))
    (htri : linTriInstalled P TI) (htriF : P.funs[tri]? = some (linTriUpperF tri TI))
    (hl : linLiftInstalled P LI) (hlF : P.funs[lift]? = some (linHermiteLiftF LI))
    (I : FullRankInst) (w : Fin I.c → ℤ) :
    FunAll P f (.list [fullRankInput I, linVecVal w]) (fun out cost =>
      linRowAnswer I.A w out ∧ cost ≤ linRowSolverCost hH I (Val.list [fullRankInput I, linVecVal w]).wt) := by
  let a := Val.list [fullRankInput I, linVecVal w]
  let W := a.wt
  let HW := linHermiteWt (linHermiteDegree hH) I
  let HC := linHermiteCost hH I
  let FC := linRowSolverFinishCost hH I W
  have wi : (fullRankInput I).wt < W := wt_le_wt_list (by simp)
  have ww : (linVecVal w).wt < W := wt_le_wt_list (by simp)
  have wr : (Val.nat I.r).wt < W :=
    (wt_le_wt_list (by simp [fullRankInput])).trans wi
  have hw (i : Fin I.c) : (w i).natAbs < 2 ^ W :=
    (linEncIntAbs (w i)).trans_le (Nat.pow_le_pow_right (by decide) ((linVecEntryWt w i).trans ww).le)
  have dha := Det.arg' (P := P) (vs := [fullRankInput I, linVecVal w]) (rest := []) (j := 0) rfl
  have dh : EvalAll P [a] (.call hermite (arg 0)) (fun v cost =>
      linHermiteOut (linHermiteDegree hH) I v ∧ cost ≤ 10 * (W + HC + HW + 1)) := by
    apply EvalAll.call_funAll dha
    intro v ca hv
    obtain ⟨rfl, hc⟩ := hv
    refine (linHermite_spec hH hh hj I).mono fun out cost ho => ⟨ho.1, ?_⟩
    have wo := linHermiteOut_wt ho.1
    simp only [HC, HW, W, a] at *
    omega
  apply FunAll.intro hf
  apply EvalAll.letE dh
  intro v cv hv
  obtain ⟨U, H, rfl, hU, hUM, hHerm, hUB, hHB⟩ := hv.1
  have wU : (encIntMatrix U).wt ≤ HW := by
    have ho := linHermiteOut_wt (d := linHermiteDegree hH) (I := I)
      ⟨U, H, rfl, hU, hUM, hHerm, hUB, hHB⟩
    exact (wt_le_wt_list (by simp : encIntMatrix U ∈ [encIntMatrix U, encIntMatrix H])).le.trans ho
  have wH : (encIntMatrix H).wt ≤ HW := by
    have ho := linHermiteOut_wt (d := linHermiteDegree hH) (I := I)
      ⟨U, H, rfl, hU, hUM, hHerm, hUB, hHB⟩
    exact (wt_le_wt_list (by simp : encIntMatrix H ∈ [encIntMatrix U, encIntMatrix H])).le.trans ho
  have wfa := wt_list4_le (.nat I.r) (encIntMatrix U) (encIntMatrix H) (linVecVal w)
  have wfin : (Val.list [.nat I.r, encIntMatrix U, encIntMatrix H, linVecVal w]).wt ≤ linRowSolverArg hH I W := by
    unfold linRowSolverArg
    dsimp only [HW] at *
    omega
  have hs := (linHermiteFinish_spec hfinish ht htri htriF hl hlF I.c_le U H w
    _ W hHB hw).mono (linHermiteFinishCost_mono wfin I.r I.c _ W)
  have wo : (linTriVal (linHermiteSolve I.c_le U H w)).wt ≤ FC := hs.wt_lt.le
  have di := Det.arg' (P := P) (vs := [fullRankInput I, linVecVal w])
    (rest := [.list [encIntMatrix U, encIntMatrix H]]) (j := 0) rfl
  have dr := Det.get' di (Det.nat 0) (show [Val.nat I.r, .nat I.c, encIntMatrix I.A][0]? = some (.nat I.r) from rfl)
  have dv := Det.var' (P := P) (env := [a, .list [encIntMatrix U, encIntMatrix H]]) (i := 1) rfl
  have du := Det.get' dv (Det.nat 0) rfl
  have dm := Det.get' dv (Det.nat 1) rfl
  have dw := Det.arg' (P := P) (vs := [fullRankInput I, linVecVal w])
    (rest := [.list [encIntMatrix U, encIntMatrix H]]) (j := 1) rfl
  have df := Det.call (Det.mk4 dr du dm dw) hs
  refine df.post fun cost hc => ?_
  refine ⟨linHermiteSolve_answer I.c_le I.A H U hU hUM hHerm w, ?_⟩
  have wUH := wt_list2_le (encIntMatrix U) (encIntMatrix H)
  have w3 := wt_list3_le (.nat I.r) (encIntMatrix U) (encIntMatrix H)
  have w2 := wt_list2_le (.nat I.r) (encIntMatrix U)
  have w1 := wt_list1_le (.nat I.r)
  have hn0 : (Val.nat 0).wt = 2 := rfl
  have hn1 : (Val.nat 1).wt = 3 := rfl
  change _ ≤ linRowSolverCost hH I W
  unfold linRowSolverCost
  simp only [FC, HC, HW, W, a, linRowSolverFinishCost] at *
  omega

end GI.Impl
