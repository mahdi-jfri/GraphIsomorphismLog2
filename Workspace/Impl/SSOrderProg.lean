module

public import Workspace.Impl.SSOrderCnt

@[expose] public section

/-!
# The order wrapper

`ssProdStepF` multiplies the running product by one plus the number of filled slots of a level
(`ssProdStepF_spec`); iterated over the `n` levels it gives `∏ (ssCnt T k + 1)`
(`ssProdLoop_spec`). `ssOrdF` builds the table for the base `[0, …, n-1]` and runs the product
(`ssOrdF_spec`); by `ss_card_gens` the result is `|⟨gs⟩|`.

The running product can be as large as `(n + 1)^n`, so its weight is bounded through its bit
length (`ss_prod_wt`).
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

theorem ssCnt_le (T : List (SsSlot n)) (k : ℕ) : ssCnt T k ≤ n := by
  unfold ssCnt
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- The running product has a short bit length. -/
theorem ss_prod_wt (T : List (SsSlot n)) {k : ℕ} (hk : k ≤ n) :
    (Val.nat (∏ i ∈ Finset.range k, (ssCnt T i + 1))).wt ≤ n * n + 3 * n + 3 := by
  have h1 : ∏ i ∈ Finset.range k, (ssCnt T i + 1) ≤ (n + 1) ^ n := by
    calc ∏ i ∈ Finset.range k, (ssCnt T i + 1) ≤ (n + 1) ^ (Finset.range k).card :=
          Finset.prod_le_pow_card _ _ _ fun i _ => by have := ssCnt_le T i; omega
      _ = (n + 1) ^ k := by rw [Finset.card_range]
      _ ≤ (n + 1) ^ n := Nat.pow_le_pow_right (by omega) hk
  have h2 := (GI.Machine.len_mono h1).trans (GI.Machine.len_pow_le (n + 1) n)
  have h3 : n * GI.Machine.len (n + 1) ≤ n * (n + 1) := Nat.mul_le_mul_left _ (GI.Machine.len_le_self _)
  rw [wt_nat]
  have : n * (n + 1) = n * n + n := by ring
  omega

/-- One product step: on `[[n, T], k, acc]`, multiply `acc` by one plus the count of level
`k`. -/
def ssProdStepF (cnt : ℕ) : Expr :=
  .arith .mul (arg 2) (.arith .add (.nat 1)
    (.call cnt (mk3 (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (arg 1))
      (.get (arg 0) (.nat 0)) (.nat 0))))

theorem ss_prod_step_cost {X W E : ℕ} (hW : W = 40 * X + 50) (hE : E ≤ 10 ^ 5 * (X + 1) ^ 2) :
    34 * (W + 1) + E ≤ 2 * 10 ^ 5 * (X + 1) ^ 2 := by
  have h : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  generalize (X + 1) ^ 2 = Q at *
  omega

/-- **One product step.** -/
theorem ssProdStepF_spec {P : Program} {f cb : ℕ} (hf : P.funs[f]? = some (ssProdStepF cb))
    (hit : P.HasAt cb (iterFuns cb (cb + 3))) (hst : P.funs[cb + 3]? = some ssCntStepF)
    {T : List (SsSlot n)} {k acc X : ℕ} (hk : k < n) (hTl : T.length = n * n)
    (hT : (ssEncTab T).wt ≤ X) (hX : n * n + 3 * n + 3 ≤ X) (hacc : (Val.nat acc).wt ≤ X)
    (hacc' : (Val.nat (acc * (1 + ssCnt T k))).wt ≤ X) :
    FunDet P f (.list [.list [.nat n, ssEncTab T], .nat k, .nat acc])
      (.nat (acc * (1 + ssCnt T k))) (2 * 10 ^ 5 * (X + 1) ^ 2) := by
  have hnw : ∀ m, m + 2 ≤ X → (Val.nat m).wt ≤ X := fun m h => (wt_nat_le m).trans h
  have hc : (Val.list [.nat n, ssEncTab T]).wt ≤ 4 * X + 6 := st_wt_list2 (hnw n (by omega)) hT
  have ha : (Val.list [.list [.nat n, ssEncTab T], .nat k, .nat acc]).wt ≤ 6 * (4 * X + 6) + 7 :=
    st_wt_list3 hc ((hnw k (by omega)).trans (by omega)) (hacc.trans (by omega))
  have hc3 : (Val.list [.nat n, ssEncTab T, .nat k]).wt ≤ 6 * X + 7 :=
    st_wt_list3 (hnw n (by omega)) hT (hnw k (by omega))
  have ha3 : (Val.list [.list [.nat n, ssEncTab T, .nat k], .nat n, .nat 0]).wt ≤
      6 * (6 * X + 7) + 7 :=
    st_wt_list3 hc3 ((hnw n (by omega)).trans (by omega)) ((hnw 0 (by omega)).trans (by omega))
  have hcnt := ssCntLoop_spec hit hst hk hTl hT hX
  have hcw : (Val.nat (ssCnt T k)).wt ≤ X := hnw _ (by have := ssCnt_le T k; omega)
  have hcw1 : (Val.nat (1 + ssCnt T k)).wt ≤ X := hnw _ (by have := ssCnt_le T k; omega)
  set W := 40 * X + 50 with hW
  clear_value W
  set a := Val.list [.list [.nat n, ssEncTab T], .nat k, .nat acc] with hadef
  have haW : a.wt ≤ W := by omega
  have dc : StDC P [a] (arg 0) (.list [.nat n, ssEncTab T]) 3 0 W :=
    StDC.arg rfl haW (by omega) (by omega)
  have dn := StDC.get (x := 0) (v := .nat n) dc (StDC.nat 0 (by omega)) rfl
    ((hnw n (by omega)).trans (by omega))
  have dT := StDC.get (x := 1) (v := ssEncTab T) dc (StDC.nat 1 (by omega)) rfl (by omega)
  have dk : StDC P [a] (arg 1) (.nat k) 3 0 W := StDC.arg rfl haW (by omega)
    ((hnw k (by omega)).trans (by omega))
  have d3 := StDC.mk3 dn dT dk (by omega) (by omega)
  have dA := StDC.mk3 d3 dn (StDC.nat 0 (by omega)) (by omega) (by omega)
  have dC := StDC.call dA hcnt (by omega)
  have d1 := StDC.arith (op := .add) (z := 1 + ssCnt T k) (StDC.nat 1 (by omega)) dC rfl
    (by omega)
  have dacc : StDC P [a] (arg 2) (.nat acc) 3 0 W := StDC.arg rfl haW (by omega) (by omega)
  have dm := StDC.arith (op := .mul) (z := acc * (1 + ssCnt T k)) dacc d1 rfl (by omega)
  exact StDC.funDet hf dm ((ss_prod_step_cost hW le_rfl).trans' (Nat.le_of_eq (by norm_num)))

theorem ss_prod_loop_cost {n X A c : ℕ}
    (hc : c ≤ n * (2 * 10 ^ 5 * (X + 1) ^ 2) + 1000 * (n + 1) * (A + n + X + 1))
    (hA : A ≤ 50 * X + 50) (hn : n ≤ X) : c ≤ 10 ^ 6 * (X + 1) ^ 3 := by
  have h1 : n * (2 * 10 ^ 5 * (X + 1) ^ 2) ≤ (X + 1) * (2 * 10 ^ 5 * (X + 1) ^ 2) :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 : 1000 * (n + 1) * (A + n + X + 1) ≤ 1000 * (X + 1) * (60 * (X + 1)) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e1 : (X + 1) * (2 * 10 ^ 5 * (X + 1) ^ 2) = 2 * 10 ^ 5 * (X + 1) ^ 3 := by ring
  have e2 : 1000 * (X + 1) * (60 * (X + 1)) = 60000 * (X + 1) ^ 2 := by ring
  have h3 : (X + 1) ^ 2 ≤ (X + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  rw [e1] at h1
  rw [e2] at h2
  generalize (X + 1) ^ 2 = Q2 at *
  generalize (X + 1) ^ 3 = Q3 at *
  omega

/-- **The product over the levels.** -/
theorem ssProdLoop_spec {P : Program} {b : ℕ} (hit : P.HasAt b (iterFuns b (b + 3)))
    (hst : P.funs[b + 3]? = some (ssProdStepF (b + 4)))
    (hit' : P.HasAt (b + 4) (iterFuns (b + 4) (b + 7)))
    (hst' : P.funs[b + 7]? = some ssCntStepF) {T : List (SsSlot n)} {X : ℕ}
    (hTl : T.length = n * n) (hT : (ssEncTab T).wt ≤ X) (hX : n * n + 3 * n + 3 ≤ X) :
    FunDet P b (.list [.list [.nat n, ssEncTab T], .nat n, .nat 1])
      (.nat (∏ i ∈ Finset.range n, (ssCnt T i + 1))) (10 ^ 6 * (X + 1) ^ 3) := by
  have hnw : ∀ m, m + 2 ≤ X → (Val.nat m).wt ≤ X := fun m h => (wt_nat_le m).trans h
  have hc : (Val.list [.nat n, ssEncTab T]).wt ≤ 4 * X + 6 := st_wt_list2 (hnw n (by omega)) hT
  have ha : (Val.list [.list [.nat n, ssEncTab T], .nat n, .nat 1]).wt ≤ 50 * X + 50 := by
    have := st_wt_list3 hc ((hnw n (by omega)).trans (by omega))
      ((hnw 1 (by omega)).trans (by omega))
    omega
  have hpw : ∀ k ≤ n, (Val.nat (∏ i ∈ Finset.range k, (ssCnt T i + 1))).wt ≤ X :=
    fun k hk => (ss_prod_wt T hk).trans hX
  refine (iter_spec hit (Inv := fun k acc => acc = .nat (∏ i ∈ Finset.range k, (ssCnt T i + 1)))
    (M := X) (B := fun _ => 2 * 10 ^ 5 * (X + 1) ^ 2) (by simp) (fun k acc hk h => by
      rw [h]; exact hpw k hk)
    (fun k acc hk h => by
      subst h
      have e : (∏ i ∈ Finset.range k, (ssCnt T i + 1)) * (1 + ssCnt T k) =
          ∏ i ∈ Finset.range (k + 1), (ssCnt T i + 1) := by
        rw [Finset.prod_range_succ, Nat.add_comm 1]
      refine FunAll.mono (ssProdStepF_spec hst hit' hst' hk hTl hT hX (hpw k hk.le)
        (by rw [e]; exact hpw (k + 1) hk)) fun w c ⟨hw, hc⟩ => ⟨?_, hc⟩
      show _ = _
      rw [hw, e])).mono fun w c ⟨hw, hc⟩ => ⟨hw, ?_⟩
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
  unfold loopModK at hc
  exact ss_prod_loop_cost hc ha (by omega)

end GI.Impl
