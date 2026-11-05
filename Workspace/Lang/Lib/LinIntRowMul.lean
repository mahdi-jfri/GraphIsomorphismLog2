module

public import Workspace.Lang.Lib.LinIntColumn

@[expose] public section

/-! A row times an integer matrix. Columns are extracted from the dense row
encoding, then paired with the input row in the proved dot-product loop.
The explicit column count handles matrices with no rows. -/
namespace GI.Lang
open GI.Cited (Val encInt encIntMatrix)
open Matrix

/-- On [context,column,accumulator], append the next dot product. -/
def linRowMulStep (column dot : ℕ) : Expr :=
  .snoc (arg 2)
    (.letE (.call column (mk2 (arg 1) (.get (arg 0) (.nat 2))))
      (.call dot (mk3 (.get (arg 0) (.nat 1)) (.var 1) linIntZeroE)))

def linRowMulFuns (b column dot : ℕ) : List Expr :=
  loopFuns b (arg 0) .nil (linRowMulStep column dot)

def linRowMulColIn (W c : ℕ) : ℕ := 4 * (W + c + 10)
def linRowMulColWt (W r c : ℕ) : ℕ := linVectorAccWt r (linRowMulColIn W c)
def linRowMulDotIn (W r c : ℕ) : ℕ := 2 * (W + linRowMulColWt W r c + 100) + 7
def linRowMulEntryWt (W r c : ℕ) : ℕ := linDotAccWt (linRowMulDotIn W r c) r

def linRowMulStepCost (W r c : ℕ) : ℕ :=
  linColumnCost (linRowMulColIn W c) r + linDotLoopCost (linRowMulDotIn W r c) r +
    1000 * (W + c + linVectorAccWt c (linRowMulEntryWt W r c) +
      linRowMulColWt W r c + linRowMulEntryWt W r c + 100)

def linRowMulCost (W r c : ℕ) : ℕ :=
  c * linRowMulStepCost W r c + loopModK * (c + 1) *
    (W + c + linVectorAccWt c (linRowMulEntryWt W r c) + 1)

set_option maxHeartbeats 2000000 in
/-- Integer row-times-matrix, with polynomial cost in the dense dimensions and bit weight. -/
theorem linRowMul_spec {P : Program} {b column dot ib r c : ℕ} (h : linIntSpec P ib)
    (hp : P.HasAt b (linRowMulFuns b column dot))
    (hcol : P.HasAt column (linColumnFuns column))
    (hdot : P.HasAt dot (linDotLoopFuns dot ib))
    (v : Fin r → ℤ) (A : Matrix (Fin r) (Fin c) ℤ) :
    FunDet P b (.list [.nat c, linVecVal v, encIntMatrix A]) (linVecVal (v ᵥ* A))
      (linRowMulCost (Val.list [.nat c, linVecVal v, encIntMatrix A]).wt r c) := by
  let a := Val.list [.nat c, linVecVal v, encIntMatrix A]
  let T := linRowMulColIn a.wt c
  let K := linRowMulColWt a.wt r c
  let D := linRowMulDotIn a.wt r c
  let B := linRowMulEntryWt a.wt r c
  let M := linVectorAccWt c B
  let outs := (List.finRange c).map fun j => encInt ((v ᵥ* A) j)
  have wv : (linVecVal v).wt < a.wt := wt_le_wt_list (by simp)
  have wA : (encIntMatrix A).wt < a.wt := wt_le_wt_list (by simp)
  have colIn (j : Fin c) : (Val.list [.nat j.val, encIntMatrix A]).wt ≤ T := by
    have wj := wt_nat_le j.val
    have wa := wt_list2_le (.nat j.val) (encIntMatrix A)
    have hj := j.isLt
    unfold T linRowMulColIn
    omega
  have colWt (j : Fin c) : (linVecVal (fun i => A i j)).wt ≤ K := by
    have hw := linWtList (vs := (List.finRange r).map fun i => encInt (A i j)) (B := T) (by
      intro z hz
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hz
      have hrow : (linVecVal (A i)).wt < (encIntMatrix A).wt := wt_le_wt_list (by exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
      have hent := (linVecEntryWt (A i) j).trans hrow
      have hT : a.wt ≤ T := by unfold T linRowMulColIn; omega
      exact hent.le.trans (wA.le.trans hT))
    simpa [K, linRowMulColWt, linVectorAccWt, linVecVal] using hw
  have dotIn (j : Fin c) :
      (Val.list [linVecVal v, linVecVal (fun i => A i j), encInt 0]).wt ≤ D := by
    have hw := wt_list3_le (linVecVal v) (linVecVal (fun i => A i j)) (encInt 0)
    have hz : (encInt 0).wt ≤ 100 := by decide
    have hk := colWt j
    unfold D linRowMulDotIn
    omega
  have outWt (j : Fin c) : (encInt ((v ᵥ* A) j)).wt ≤ B := by
    have hv := linDotPartial_wt v (fun i => A i j) D
      (fun i => (linVecEntryWt v i).le.trans (wv.le.trans (by unfold D linRowMulDotIn; omega)))
      (fun i => (linVecEntryWt (fun k => A k j) i).le.trans ((colWt j).trans (by unfold D linRowMulDotIn; omega))) r le_rfl
    rw [linDotPartial_full] at hv
    exact hv
  have accWt (i : ℕ) : (Val.list (outs.take i)).wt ≤ M := by
    have ht := linWtList (vs := outs.take i) (B := B) (by
      intro z hz
      have hz' := List.mem_of_mem_take hz
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hz'
      exact outWt j)
    have hl : (outs.take i).length ≤ c := by have := List.length_take_le i outs; simpa [outs] using this
    unfold M linVectorAccWt
    nlinarith
  have dk := Det.arg' (P := P) (vs := [.nat c, linVecVal v, encIntMatrix A]) (rest := []) (j := 0) rfl
  have hlp : P.HasAt b (loopFuns b (arg 0) .nil (linRowMulStep column dot)) := hp
  have hloop := loopBdd_spec hlp dk Det.nil (by
    change 2 * a.wt + 0 + 5 + 5 ≤ 10 * (a.wt + c + 1)
    have := a.two_le_size.trans a.size_le_wt
    omega)
    (Inv := fun i acc => acc = .list (outs.take i)) (M := M)
    (D := fun _ => linRowMulStepCost a.wt r c) (by simp)
    (fun i acc _ he => he ▸ accWt i) (fun i acc hi he => ?_)
  · refine hloop.mono fun w cost hw => ⟨?_, ?_⟩
    · have houtlen : outs.length = c := by simp [outs]
      have he := hw.1
      rw [← houtlen, List.take_length] at he
      exact he
    · simpa [linRowMulCost, M, a, Finset.sum_const, Finset.card_range, smul_eq_mul] using hw.2
  · subst acc
    let j : Fin c := ⟨i, hi⟩
    let env := [Val.list [a, .nat i, .list (outs.take i)]]
    have di := Det.arg' (P := P) (vs := [a, .nat i, .list (outs.take i)]) (rest := []) (j := 1) rfl
    have dm := Det.get' (Det.arg' (P := P) (vs := [a, .nat i, .list (outs.take i)]) (rest := []) (j := 0) rfl)
      (Det.nat 2) (show [Val.nat c, linVecVal v, encIntMatrix A][2]? = _ from rfl)
    have dc := Det.call (Det.mk2 di dm) (linColumn_spec hcol A j)
    have dv := Det.get' (Det.arg' (P := P) (vs := [a, .nat i, .list (outs.take i)])
      (rest := [linVecVal (fun k => A k j)]) (j := 0) rfl) (Det.nat 1)
      (show [Val.nat c, linVecVal v, encIntMatrix A][1]? = _ from rfl)
    have dcol := Det.var' (P := P) (env := env ++ [linVecVal (fun k => A k j)]) (i := 1) rfl
    have dz := Det.mk2 (Det.nat (P := P) (env := env ++ [linVecVal (fun k => A k j)]) 0) Det.nil
    have dd := Det.call (Det.mk3 dv dcol dz) (linDotLoop_spec h hdot v (fun k => A k j))
    have da := Det.arg' (P := P) (vs := [a, .nat i, .list (outs.take i)]) (rest := []) (j := 2) rfl
    have dres := Det.snoc da (Det.letE dc dd)
    have ho : (∑ k : Fin r, v k * A k j) = (v ᵥ* A) j := rfl
    rw [ho] at dres
    have heq : outs.take (i + 1) = outs.take i ++ [encInt ((v ᵥ* A) j)] := by
      rw [List.take_add_one]
      have hh : outs[i]? = some (encInt ((v ᵥ* A) j)) := by simp [outs, hi, j]
      rw [hh]; rfl
    refine dres.post fun cost hc => ⟨?_, ?_⟩
    · change Val.list (outs.take i ++ [encInt ((v ᵥ* A) j)]) = Val.list (outs.take (i + 1))
      rw [heq]
    · have hcc := linColumnCost_mono (colIn j) r
      have hdc := linDotLoopCost_mono (dotIn j) r
      have wenv := wt_list3_le a (.nat i) (.list (outs.take i))
      have wi := wt_nat_le i
      have wm := accWt i
      have wo := accWt (i + 1)
      rw [heq] at wo
      have wout := outWt j
      have wc := colWt j
      have wcarg := colIn j
      have wdarg := dotIn j
      have wz : (encInt 0).wt ≤ 100 := by decide
      have wzlit : (Val.list [.nat 0, .list []]).wt = (encInt 0).wt := rfl
      have wk := linVecEntryWt (fun k => A k j)
      beta_reduce at hc ⊢
      change cost ≤ linRowMulStepCost a.wt r c + 100 * (a.wt + c + M + 1)
      unfold linRowMulStepCost
      change cost ≤ linColumnCost T r + linDotLoopCost D r + 1000 * (a.wt + c + M + K + B + 100) +
        100 * (a.wt + c + M + 1)
      have hzval : Val.list [.nat 0, .list []] = encInt 0 := rfl
      have hcolarg : (Val.list [.nat i, encIntMatrix A]).wt =
          (Val.list [.nat j.val, encIntMatrix A]).wt := rfl
      rw [hcolarg, hzval] at hc
      change (Val.list [.nat j.val, encIntMatrix A]).wt ≤ T at wcarg
      change (Val.list [linVecVal v, linVecVal (fun k => A k j), encInt 0]).wt ≤ D at wdarg
      have w00 : (Val.nat 0).wt = 2 := rfl
      have wnil : (Val.list []).wt = 4 := rfl
      have hT : T = 4 * (a.wt + c + 10) := rfl
      have hD : D = 2 * (a.wt + K + 100) + 7 := rfl
      omega

theorem linRowMulCost_mono {W V : ℕ} (h : W ≤ V) (r c : ℕ) :
    linRowMulCost W r c ≤ linRowMulCost V r c := by
  have ht : linRowMulColIn W c ≤ linRowMulColIn V c := by unfold linRowMulColIn; omega
  have hk : linRowMulColWt W r c ≤ linRowMulColWt V r c := by
    unfold linRowMulColWt linVectorAccWt
    nlinarith
  have hd : linRowMulDotIn W r c ≤ linRowMulDotIn V r c := by unfold linRowMulDotIn; omega
  have hb : linRowMulEntryWt W r c ≤ linRowMulEntryWt V r c := by
    unfold linRowMulEntryWt linDotAccWt
    omega
  have hm : linVectorAccWt c (linRowMulEntryWt W r c) ≤
      linVectorAccWt c (linRowMulEntryWt V r c) := by unfold linVectorAccWt; nlinarith
  have hc1 := linColumnCost_mono ht r
  have hc2 := linDotLoopCost_mono hd r
  have hs : linRowMulStepCost W r c ≤ linRowMulStepCost V r c := by unfold linRowMulStepCost; omega
  unfold linRowMulCost
  exact Nat.add_le_add (Nat.mul_le_mul_left c hs) (Nat.mul_le_mul_left _ (by omega))

end GI.Lang
