module

public import Workspace.Impl.TermJSolDrop

@[expose] public section

/-!
# Stacking the relation matrix above the stabilizer rows (program)

`tmJSolStackF app`, on `[encIntMatrix M, encIntMatrix B, …]`, returns the Hermite input
`fullRankInput (tmJSolInst ht M B hM)`: the numbers `t + G` and `t`, and the rows of `M`
followed by the rows of `B` (one call of the append module at `app`).
-/

namespace GI.Impl
open GI.Lang
open GI.Cited (Val encInt encIntMatrix FullRankInst fullRankInput)

/-- On `[M, B, …]`: `[t + G, t, M ++ B]`, with the rows of `M` first. -/
def tmJSolStackF (app : ℕ) : Expr :=
  mk3 (.arith .add (.length (arg 0)) (.length (arg 1))) (.length (arg 0))
    (.call app (mk2 (arg 0) (arg 1)))

/-- The rows of a matrix, as encoded vectors. -/
def tmJSolRows {r c : ℕ} (A : Matrix (Fin r) (Fin c) ℤ) : List Val :=
  (List.finRange r).map fun i => linVecVal (A i)

theorem tmJSolRows_enc {r c : ℕ} (A : Matrix (Fin r) (Fin c) ℤ) :
    encIntMatrix A = .list (tmJSolRows A) := rfl

@[simp] theorem tmJSolRows_length {r c : ℕ} (A : Matrix (Fin r) (Fin c) ℤ) :
    (tmJSolRows A).length = r := by simp [tmJSolRows]

set_option backward.isDefEq.respectTransparency false in
/-- The rows of the stacked matrix are the rows of `M` followed by the rows of `B`. -/
theorem tmJSolRows_stack {t G : ℕ} (M : Matrix (Fin t) (Fin t) ℤ)
    (B : Matrix (Fin G) (Fin t) ℤ) :
    tmJSolRows (tmJSolStack M B) = tmJSolRows M ++ tmJSolRows B := by
  unfold tmJSolRows
  rw [tmJSol_map_finRange_add]
  congr 1 <;> apply List.map_congr_left <;> intro i _ <;> congr 1 <;> funext j <;>
    simp [tmJSolStack, Matrix.of_apply]

/-- The weight of an appended list. -/
theorem tmJSol_wt_append (xs ys : List Val) :
    (Val.list (xs ++ ys)).wt ≤ 3 * ((Val.list xs).wt + (Val.list ys).wt) + 4 := by
  have h := wt_list_le (xs ++ ys)
  have hx := sum_wt_lt_wt_list xs
  have hy := sum_wt_lt_wt_list ys
  have lx := length_lt_wt_list xs
  have ly := length_lt_wt_list ys
  simp only [List.map_append, List.sum_append, List.length_append] at h
  omega

/-- The cost bound of the stacking function. -/
def tmJSolStackCost (W : ℕ) : ℕ := 100000 * (W + 1) ^ 2

/-- The weight of the Hermite input, in the weight of the argument. -/
def tmJSolStackWt (W : ℕ) : ℕ := 20 * W + 30

set_option maxHeartbeats 1000000 in
/-- **Stacking.** The result is the Hermite input of the stacked matrix. -/
theorem tmJSolStack_spec {P : Program} {f app : ℕ} (hf : P.funs[f]? = some (tmJSolStackF app))
    (hap : P.HasAt app (appendFuns app)) {t G : ℕ} (ht : 0 < t)
    (M : Matrix (Fin t) (Fin t) ℤ) (B : Matrix (Fin G) (Fin t) ℤ) (hM : M.det ≠ 0)
    (rest : List Val) :
    FunDet P f (.list (encIntMatrix M :: encIntMatrix B :: rest))
      (fullRankInput (tmJSolInst ht M B hM))
      (tmJSolStackCost (Val.list (encIntMatrix M :: encIntMatrix B :: rest)).wt) ∧
    (fullRankInput (tmJSolInst ht M B hM)).wt ≤
      tmJSolStackWt (Val.list (encIntMatrix M :: encIntMatrix B :: rest)).wt := by
  let vs := encIntMatrix M :: encIntMatrix B :: rest
  let W := (Val.list vs).wt
  have wM : (Val.list (tmJSolRows M)).wt < W := wt_le_wt_list (by simp [vs, tmJSolRows_enc])
  have wB : (Val.list (tmJSolRows B)).wt < W := wt_le_wt_list (by simp [vs, tmJSolRows_enc])
  have lM := length_lt_wt_list (tmJSolRows M)
  have lB := length_lt_wt_list (tmJSolRows B)
  simp only [tmJSolRows_length] at lM lB
  have wout := tmJSol_wt_append (tmJSolRows M) (tmJSolRows B)
  have hout : fullRankInput (tmJSolInst ht M B hM) =
      .list [.nat (t + G), .nat t, .list (tmJSolRows M ++ tmJSolRows B)] := by
    simp only [fullRankInput, tmJSolInst, tmJSolRows_enc, tmJSolRows_stack]
  have wtg := wt_nat_le (t + G)
  have wt0 := wt_nat_le t
  have w3 := wt_list3_le (.nat (t + G)) (.nat t) (.list (tmJSolRows M ++ tmJSolRows B))
  refine ⟨?_, ?_⟩
  swap
  · rw [hout]
    change _ ≤ 20 * W + 30
    omega
  rw [hout]
  apply FunDet.intro hf
  have d0 : Det P [.list vs] (arg 0) (.list (tmJSolRows M)) _ :=
    Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have d1 : Det P [.list vs] (arg 1) (.list (tmJSolRows B)) _ :=
    Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl
  have l0 := Det.length d0
  have l1 := Det.length d1
  simp only [tmJSolRows_length] at l0 l1
  have dsum := Det.arith' (op := .add) l0 l1 (z := t + G) rfl
  have happ := append_spec hap (tmJSolRows M) (tmJSolRows B)
  have happ' : FunAll P app (.list [.list (tmJSolRows M), .list (tmJSolRows B)]) (fun w c =>
      w = .list (tmJSolRows M ++ tmJSolRows B) ∧ c ≤ loopModK * (G + 1) *
        ((Val.list [.list (tmJSolRows M), .list (tmJSolRows B)]).wt + G +
          (Val.list (tmJSolRows M ++ tmJSolRows B)).wt + 1)) :=
    happ.mono fun w c h => ⟨h.1, by have h2 := h.2; rw [h.1] at h2; simpa using h2⟩
  have dcall := Det.call (Det.mk2 d0 d1) happ'
  have d := Det.mk3 dsum l0 dcall
  refine d.mono ?_
  have w2 := wt_list2_le (.list (tmJSolRows M)) (.list (tmJSolRows B))
  have hX : (Val.list [.list (tmJSolRows M), .list (tmJSolRows B)]).wt + G +
      (Val.list (tmJSolRows M ++ tmJSolRows B)).wt + 1 ≤ 11 * (W + 1) := by omega
  have hm := Nat.mul_le_mul (show G + 1 ≤ W + 1 by omega) hX
  have hsq : (W + 1) ^ 2 = (W + 1) * (W + 1) := sq _
  unfold tmJSolStackCost
  change _ ≤ 100000 * (W + 1) ^ 2
  rw [hsq]
  simp only [loopModK] at *
  nlinarith

end GI.Impl
