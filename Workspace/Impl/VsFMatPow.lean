import Workspace.Impl.VsFMatMul

/-!
# The `p`-th power of a matrix modulo `p`

The Frobenius map `x ↦ x^p` needs the `p`-th power of a `d × d` matrix. We start from `X` and
multiply on the right by `X`, `p - 1` times, with the product program `vsFMatMulFuns`.

* `vsFMatMulL p A X z`: the rows `z + a X` for the rows `a` of `A`; `vsFMatPowL p X z k`: `k`
  such products, starting from `X`. With `z = 0` this is `X^(k+1)`.
* `vsFMatPowFuns b` (21 functions), `vsFMatPow_spec`: on `[p, X, z]` the result is
  `vsFMatPowL p X z (p - 1)`.
-/

namespace GI.Impl

open GI.Lang GI.Cited
open GI.Machine (BinOp)

/-- The rows `z + a X`, for the rows `a` of `A`. -/
def vsFMatMulL (p : ℕ) (A X : List (List ℕ)) (z : List ℕ) : List (List ℕ) :=
  A.map fun a => vsFRowMul p a X z

/-- `k` right multiplications by `X`, starting from `X`. -/
def vsFMatPowL (p : ℕ) (X : List (List ℕ)) (z : List ℕ) (k : ℕ) : List (List ℕ) :=
  (fun A => vsFMatMulL p A X z)^[k] X

/-- A `d × d` matrix with entries below `p`. -/
structure VsFSq (p d : ℕ) (A : List (List ℕ)) : Prop where
  len : A.length = d
  rows : ∀ a ∈ A, (∀ y ∈ a, y < p) ∧ a.length = d

theorem vsFMatMulL_sq {p d : ℕ} (hp : 0 < p) {A X : List (List ℕ)} {z : List ℕ}
    (hA : VsFSq p d A) (hz : ∀ y ∈ z, y < p) (hzl : z.length = d) :
    VsFSq p d (vsFMatMulL p A X z) := by
  refine ⟨by rw [vsFMatMulL, List.length_map, hA.len], fun a ha => ?_⟩
  simp only [vsFMatMulL, List.mem_map] at ha
  obtain ⟨a', -, rfl⟩ := ha
  exact ⟨vsFMulAcc_foldl_lt hp a' X (acc := (0, z)) hz,
    by rw [vsFRowMul, vsFMulAcc_foldl_length]; exact hzl⟩

theorem vsFMatPowL_succ (p : ℕ) (X : List (List ℕ)) (z : List ℕ) (k : ℕ) :
    vsFMatPowL p X z (k + 1) = vsFMatMulL p (vsFMatPowL p X z k) X z := by
  rw [vsFMatPowL, vsFMatPowL, Function.iterate_succ_apply']

theorem vsFMatPowL_sq {p d : ℕ} (hp : 0 < p) {X : List (List ℕ)} {z : List ℕ} (hX : VsFSq p d X)
    (hz : ∀ y ∈ z, y < p) (hzl : z.length = d) (k : ℕ) : VsFSq p d (vsFMatPowL p X z k) := by
  induction k with
  | zero => exact hX
  | succ k ih => rw [vsFMatPowL_succ]; exact vsFMatMulL_sq hp ih hz hzl

theorem wt_vsFSq_le {p d N : ℕ} (hpN : p ≤ N) (hdN : d ≤ N) {A : List (List ℕ)}
    (hA : VsFSq p d A) : (Val.list (A.map natList)).wt ≤ 11 * (N + 1) ^ 3 + 4 :=
  wt_vsFMat_le (fun r hr y hy => ((hA.rows r hr).1 y hy).le.trans hpN)
    (fun r hr => (hA.rows r hr).2.trans_le hdN) (by rw [hA.len]; omega)

theorem wt_vsFMatCtx_le {p d N : ℕ} (hpN : p ≤ N) (hdN : d ≤ N) {X : List (List ℕ)}
    (hX : VsFSq p d X) {z : List ℕ} (hz : ∀ y ∈ z, y < p) (hzl : z.length = d) :
    (vsFMatCtx p X z).wt ≤ 60 * (N + 1) ^ 3 := by
  have h1 := wt_vsFSq_le hpN hdN hX
  have h2 := wt_natList_le_sq (fun y hy => (hz y hy).le.trans hpN) (hzl.trans_le hdN)
  have h3 := wt_list3_le (.nat p) (.list (X.map natList)) (natList z)
  have h4 := wt_nat_le p
  have hN1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hN2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have e : (vsFMatCtx p X z).wt = (Val.list [.nat p, .list (X.map natList), natList z]).wt := rfl
  omega

/-- The step, on `[ctx, i, A]`: the product `A X` with start vector `z`. -/
def vsFPowStepF (mm : ℕ) : Expr := .call mm (mk2 (arg 0) (arg 2))

/-- The power, on `[p, X, z]`: iterate the step `p - 1` times from `X`. -/
def vsFMatPowF (it : ℕ) : Expr :=
  .call it (mk3 (.var 0) (.arith .sub (arg 0) (.nat 1)) (arg 1))

/-- The power, at base `b` (21 functions). -/
def vsFMatPowFuns (b : ℕ) : List Expr :=
  [vsFMatPowF (b + 1)] ++ iterFuns (b + 1) (b + 4) ++ [vsFPowStepF (b + 5)] ++ vsFMatMulFuns (b + 5)

theorem vsFMatPowFuns_length (b : ℕ) : (vsFMatPowFuns b).length = 21 := rfl

theorem vsFPowStep_spec {P : Program} {g mm : ℕ} (hg : P.funs[g]? = some (vsFPowStepF mm))
    (hmm : P.HasAt mm (vsFMatMulFuns mm)) {p N d : ℕ} (hp : 0 < p) (hpN : p ≤ N) (hdN : d ≤ N)
    {X A : List (List ℕ)} {z : List ℕ} (hX : VsFSq p d X) (hA : VsFSq p d A)
    (hz : ∀ y ∈ z, y < p) (hzl : z.length = d) (i : ℕ) (hi : i ≤ N) :
    FunDet P g (.list [vsFMatCtx p X z, .nat i, .list (A.map natList)])
      (.list ((vsFMatMulL p A X z).map natList)) (6 * 10 ^ 6 * (N + 1) ^ 5) := by
  have HB : VsFMatFits p N X z :=
    ⟨hz, hzl.trans_le hdN, fun r hr y hy => ((hX.rows r hr).1 y hy).le.trans hpN,
      fun r hr => (hX.rows r hr).2.trans_le hdN, fun r hr => by rw [(hX.rows r hr).2, hzl],
      by rw [hX.len]; exact hdN⟩
  have HA : ∀ a ∈ A, (∀ y ∈ a, y < p) ∧ a.length ≤ N ∧ X.length ≤ a.length := fun a ha =>
    ⟨(hA.rows a ha).1, (hA.rows a ha).2.trans_le hdN, by rw [(hA.rows a ha).2, hX.len]⟩
  have hmul := vsFMatMul_spec hmm hp hpN HB HA (by rw [hA.len]; exact hdN)
  have ev : (A.map fun a => natList (vsFRowMul p a X z)) = (vsFMatMulL p A X z).map natList := by
    simp [vsFMatMulL]
  rw [ev] at hmul
  have d0 := Det.arg' (P := P) (rest := []) (vs := [vsFMatCtx p X z, .nat i, .list (A.map natList)])
    (j := 0) rfl
  have d2 := Det.arg' (P := P) (rest := []) (vs := [vsFMatCtx p X z, .nat i, .list (A.map natList)])
    (j := 2) rfl
  refine FunDet.intro hg ((Det.call (Det.mk2 d0 d2) hmul).mono ?_)
  have wc := wt_vsFMatCtx_le hpN hdN hX hz hzl
  have wA := wt_vsFSq_le hpN hdN hA
  have wO := wt_vsFSq_le hpN hdN (vsFMatMulL_sq (X := X) hp hA hz hzl)
  have w3 := wt_list3_le (vsFMatCtx p X z) (.nat i) (.list (A.map natList))
  have w2 := wt_list2_le (vsFMatCtx p X z) (.list (A.map natList))
  have wi := wt_nat_le i
  have hN1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hN2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN3 : (N + 1) ^ 3 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem vsFMatPow_cost {N Q5 S a M : ℕ} {p : ℕ} (hpN : p ≤ N) (hS : S ≤ N * (6 * 10 ^ 6 * Q5))
    (ha : a ≤ 200 * Q5) (hM : M ≤ 100 * Q5) (hNQ : N + 1 ≤ Q5) {c : ℕ}
    (hc : c ≤ S + loopModK * (p - 1 + 1) * (a + (p - 1) + M + 1)) :
    c ≤ 10 ^ 7 * ((N + 1) * Q5) + 100 * a := by
  have hK : loopModK = 1000 := rfl
  rw [hK] at hc
  have k1 : 1000 * (p - 1 + 1) * (a + (p - 1) + M + 1) ≤ 1000 * (N + 1) * (400 * Q5) :=
    Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) (by omega)
  have k2 : N * (6 * 10 ^ 6 * Q5) ≤ 6 * 10 ^ 6 * ((N + 1) * Q5) := by nlinarith
  have e : 1000 * (N + 1) * (400 * Q5) = 400000 * ((N + 1) * Q5) := by ring
  omega

/-- **The `p`-th power.** On `[p, X, z]`, for a `d × d` matrix `X` and a start vector `z` of
length `d`, all with entries below `p`, the result is `vsFMatPowL p X z (p - 1)`. With `z = 0`
this is `X^p` modulo `p`. -/
theorem vsFMatPow_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsFMatPowFuns b)) {p N d : ℕ}
    (hp : 0 < p) (hpN : p ≤ N) (hdN : d ≤ N) {X : List (List ℕ)} {z : List ℕ}
    (hX : VsFSq p d X) (hz : ∀ y ∈ z, y < p) (hzl : z.length = d) :
    FunDet P b (vsFMatCtx p X z) (.list ((vsFMatPowL p X z (p - 1)).map natList))
      (2 * 10 ^ 7 * (N + 1) ^ 6) := by
  have hf : P.funs[b]? = some (vsFMatPowF (b + 1)) := h.get (j := 0) (by simp [vsFMatPowFuns])
  have hit : P.HasAt (b + 1) (iterFuns (b + 1) (b + 4)) := h.block 1 rfl
  have hst : P.funs[b + 4]? = some (vsFPowStepF (b + 5)) :=
    h.get (j := 4) (by rw [vsFMatPowFuns_length]; omega)
  have hmm : P.HasAt (b + 5) (vsFMatMulFuns (b + 5)) := h.block 5 rfl
  have hN1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hN2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN3 : (N + 1) ^ 3 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have wc := wt_vsFMatCtx_le hpN hdN hX hz hzl
  have wX := wt_vsFSq_le hpN hdN hX
  have hiter := iter_spec hit (c := vsFMatCtx p X z) (k := p - 1) (acc0 := .list (X.map natList))
    (Inv := fun i acc => acc = .list ((vsFMatPowL p X z i).map natList))
    (M := 11 * (N + 1) ^ 3 + 4) (B := fun _ => 6 * 10 ^ 6 * (N + 1) ^ 5) rfl
    (fun i acc _ hacc => by rw [hacc]; exact wt_vsFSq_le hpN hdN (vsFMatPowL_sq hp hX hz hzl i))
    (fun i acc hi hacc => by
      rw [hacc]
      refine FunAll.mono (vsFPowStep_spec hst hmm hp hpN hdN hX (vsFMatPowL_sq hp hX hz hzl i) hz hzl i
        (by omega)) fun w c hw => ⟨?_, hw.2⟩
      beta_reduce
      rw [hw.1, vsFMatPowL_succ])
  have wa : (Val.list [vsFMatCtx p X z, .nat (p - 1), .list (X.map natList)]).wt ≤
      200 * (N + 1) ^ 5 := by
    have := wt_list3_le (vsFMatCtx p X z) (.nat (p - 1)) (.list (X.map natList))
    have := wt_nat_le (p - 1)
    omega
  have hiter' : FunDet P (b + 1) (.list [vsFMatCtx p X z, .nat (p - 1), .list (X.map natList)])
      (.list ((vsFMatPowL p X z (p - 1)).map natList))
      (10 ^ 7 * ((N + 1) * (N + 1) ^ 5) +
        100 * (Val.list [vsFMatCtx p X z, .nat (p - 1), .list (X.map natList)]).wt) := by
    refine hiter.mono fun w c hw => ⟨hw.1, ?_⟩
    have hc := hw.2
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
    exact vsFMatPow_cost hpN (Nat.mul_le_mul_right _ (by omega)) wa (by omega)
      (hN1.trans (hN2.trans hN3)) hc
  have dv := Det.var' (P := P) (env := [vsFMatCtx p X z]) (i := 0) rfl
  have dp := Det.arg' (P := P) (rest := []) (vs := [.nat p, .list (X.map natList), natList z])
    (j := 0) rfl
  have dx := Det.arg' (P := P) (rest := []) (vs := [.nat p, .list (X.map natList), natList z])
    (j := 1) rfl
  have dk := Det.arith' (op := .sub) (z := p - 1) dp (Det.nat 1) rfl
  have darg := Det.mk3 dv dk dx
  refine FunDet.intro hf ((Det.call darg hiter').mono ?_)
  have wO := wt_vsFSq_le hpN hdN (vsFMatPowL_sq hp hX hz hzl (p - 1))
  have e : (vsFMatCtx p X z).wt = (Val.list [.nat p, .list (X.map natList), natList z]).wt := rfl
  have hN5 : (N + 1) ^ 5 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have e6 : (N + 1) * (N + 1) ^ 5 = (N + 1) ^ 6 := by ring
  rw [e6]
  omega

end GI.Impl
