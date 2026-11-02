import Workspace.Impl.LinConstRem

/-! Reduce every matrix row by the invariant factor of its target coordinate. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linFiniteMatrixReduceStep (row : ℕ) : Expr :=
  .snoc (arg 2) (.call row (mk2
    (.get (.get (arg 0) (.nat 0)) (arg 1))
    (.get (.get (arg 0) (.nat 1)) (arg 1))))

def linFiniteMatrixReduceFuns (b : ℕ) : List Expr :=
  loopFuns b (.length (arg 0)) .nil (linFiniteMatrixReduceStep (b + 3)) ++ linConstRemFuns (b + 3)

theorem linFiniteMatrixReduceFuns_length (b : ℕ) : (linFiniteMatrixReduceFuns b).length = 25 := rfl

def linFiniteMatrixReduceRowBudget (W : ℕ) : ℕ := linConstRemCost (4 * W + 6)
def linFiniteMatrixReduceAcc (W r : ℕ) : ℕ := linVectorAccWt r (linFiniteMatrixReduceRowBudget W)
def linFiniteMatrixReduceStepCost (W r : ℕ) : ℕ :=
  10000 * (W + r + linFiniteMatrixReduceAcc W r + linFiniteMatrixReduceRowBudget W + 1)
def linFiniteMatrixReduceCost (W r : ℕ) : ℕ :=
  r * linFiniteMatrixReduceStepCost W r +
    loopModK * (r + 1) * (W + r + linFiniteMatrixReduceAcc W r + 1)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem linFiniteMatrixReduce_spec {P : Program} {b r c : ℕ}
    (hp : P.HasAt b (linFiniteMatrixReduceFuns b))
    (m : Fin r → ℤ) (A : Matrix (Fin r) (Fin c) ℤ) :
    FunDet P b (.list [linVecVal m, encIntMatrix A]) (encIntMatrix (fun i j => A i j % m i))
      (linFiniteMatrixReduceCost (Val.list [linVecVal m, encIntMatrix A]).wt r) := by
  let a := Val.list [linVecVal m, encIntMatrix A]
  let W := a.wt
  let rows := (List.finRange r).map fun i => linVecVal (fun j => A i j % m i)
  let D := linFiniteMatrixReduceRowBudget W
  let M := linFiniteMatrixReduceAcc W r
  have wm : (linVecVal m).wt < W := wt_le_wt_list (by simp [W, a])
  have wA : (encIntMatrix A).wt < W := wt_le_wt_list (by simp [W, a])
  have wr (i : Fin r) : (linVecVal (A i)).wt < W :=
    (wt_le_wt_list (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)).trans wA
  have hrow (i : Fin r) : FunDet P (b + 3) (.list [encInt (m i), linVecVal (A i)])
      (linVecVal (fun j => A i j % m i)) D := by
    have hs := linConstRem_spec (hp.block 3 rfl) (m i) ((List.finRange c).map (A i))
    simp only [List.map_map, Function.comp_def] at hs
    have wi := wt_list2_le (encInt (m i)) (linVecVal (A i))
    have wx := (linVecEntryWt m i).trans wm
    have hh : (Val.list [encInt (m i), linVecVal (A i)]).wt ≤ 4 * W + 6 := by
      have := wr i
      omega
    exact hs.mono (linConstRemCost_mono hh)
  have hacc (k : ℕ) : (Val.list (rows.take k)).wt ≤ M := by
    have hh := linWtList (vs := rows.take k) (B := D) (by
      intro v hv
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hv)
      exact (hrow i).wt_lt.le)
    have hl : (rows.take k).length ≤ r := by
      simp only [List.length_take, rows, List.length_map, List.length_finRange]
      exact min_le_right _ _
    unfold M linFiniteMatrixReduceAcc linVectorAccWt
    nlinarith [Nat.mul_le_mul_right D hl]
  have hk := Det.length (Det.arg' (P := P) (vs := [linVecVal m, encIntMatrix A])
    (rest := []) (j := 0) rfl)
  simp only [List.length_map, List.length_finRange] at hk
  have hl := loopBdd_spec (hp.block 0 rfl) hk Det.nil (by
      have hw := a.two_le_size.trans a.size_le_wt
      change 2 * a.wt + 0 + 5 + r + 3 + 5 ≤ 10 * (a.wt + r + 1)
      omega)
    (Inv := fun k acc => acc = .list (rows.take k)) (M := M)
    (D := fun _ => linFiniteMatrixReduceStepCost W r) (by simp)
    (fun k acc _ he => he ▸ hacc k) (fun k acc hkr he => ?_)
  · refine hl.mono fun out cost ho => ⟨?_, ?_⟩
    · have hh : rows.length = r := by simp [rows]
      have he := ho.1
      rw [← hh, List.take_length] at he
      exact he
    · simpa only [Finset.sum_const, Finset.card_range, smul_eq_mul,
        linFiniteMatrixReduceCost] using ho.2
  · subst acc
    let i : Fin r := ⟨k, hkr⟩
    have hget : (List.finRange r)[k]? = some i := by simp [i, hkr]
    have da := Det.arg' (P := P) (vs := [a, .nat k, .list (rows.take k)]) (rest := []) (j := 0) rfl
    have di := Det.arg' (P := P) (vs := [a, .nat k, .list (rows.take k)]) (rest := []) (j := 1) rfl
    have dm := Det.get' (Det.get' da (Det.nat 0) rfl) di (by rw [List.getElem?_map, hget]; rfl)
    have dA := Det.get' (Det.get' da (Det.nat 1) rfl) di (by rw [List.getElem?_map, hget]; rfl)
    have dr := Det.call (Det.mk2 dm dA) (hrow i)
    have dacc := Det.arg' (P := P) (vs := [a, .nat k, .list (rows.take k)])
      (rest := []) (j := 2) rfl
    have heq : rows.take (k + 1) = rows.take k ++ [linVecVal (fun j => A i j % m i)] := by
      rw [List.take_add_one]
      have hh : rows[k]? = some (linVecVal (fun j => A i j % m i)) := by simp [rows, i, hkr]
      rw [hh]
      rfl
    refine (Det.snoc dacc dr).post fun cost hc => ⟨by dsimp only; rw [heq], ?_⟩
    have wo := (hrow i).wt_lt.le
    have wpre := hacc k
    have wpost := hacc (k + 1)
    rw [heq] at wpost
    have wx := (linVecEntryWt m i).trans wm
    have wy := wr i
    have warg := wt_list2_le (encInt (m i)) (linVecVal (A i))
    have wenv := wt_list3_le a (.nat k) (.list (rows.take k))
    have wk := wt_nat_le k
    change cost ≤ linFiniteMatrixReduceStepCost W r + 100 * (W + r + M + 1)
    unfold linFiniteMatrixReduceStepCost
    dsimp only [W, a, M, D, linVecVal, encIntMatrix] at *
    omega

theorem linFiniteMatrixReduceCost_poly : PBU (fun r W _ => linFiniteMatrixReduceCost W r) := by
  unfold linFiniteMatrixReduceCost linFiniteMatrixReduceStepCost linFiniteMatrixReduceAcc
    linFiniteMatrixReduceRowBudget linConstRemCost linMapBudget linScalarRemCost
    linVectorAccWt linIntBinaryCost linIntCoreBudget linIntPartsCost linIntCodecCost
  norm_poly

end GI.Impl
