import Workspace.Impl.VsQGL
import Workspace.Proved.VsBFldNT

/-!
# The power `X^{F_q}` of a matrix

`F_q` (`vsBF n q`) is a product of up to `n` numbers, far too large to write down. The walk
computes `X^{F_q}` by raising to the power `j` for `j = 1, …, n` unless `q ∣ j`
(`vsBWalk_eq`). Each step is a binary power with a small exponent.

* `vsB_pow_spec`: one power `x^e r` with the power program of `vsQGLFuns`.
* `vsBWalkFuns b pow` (3 functions), `vsBWalk_spec`: on `[q, X, n]` it returns `X^{F_q}`.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Matrix

variable {p d E N : ℕ}

theorem vsB_pow_spec [NeZero p] {P : Program} {b : ℕ} (hb : P.HasAt b (vsQGLFuns b))
    (h : VsQSz p d E N) (x r : Matrix (Fin d) (Fin d) (ZMod p)) {e : ℕ} (he : (Val.nat e).wt ≤ N) :
    FunDet P (b + 3) (.list [.nat 0, vsQE p d E x, .nat e, vsQE p d E r])
      (vsQE p d E (x ^ e * r)) (10 ^ 8 * (N + 1) ^ 6) := by
  have h1 : P.funs[b + 1]? = some (vsQMul3F b) := hb.get (j := 1) (by rw [vsQGLFuns_length]; omega)
  have h3 : P.funs[b + 3]? = some (vsQPowF (b + 3) (b + 1)) :=
    hb.get (j := 3) (by rw [vsQGLFuns_length]; omega)
  have hm3 : ∀ u v : Matrix (Fin d) (Fin d) (ZMod p), FunDet P (b + 1)
      (.list [.nat 0, vsQE p d E u, vsQE p d E v]) (vsQE p d E (u * v)) (7 * 10 ^ 6 * (N + 1) ^ 5) := by
    intro u v
    apply FunDet.intro h1
    have d1 := Det.arg' (P := P) (vs := [.nat 0, vsQE p d E u, vsQE p d E v]) (rest := []) (j := 1) rfl
    have d2 := Det.arg' (P := P) (vs := [.nat 0, vsQE p d E u, vsQE p d E v]) (rest := []) (j := 2) rfl
    refine (Det.call (Det.mk2 d1 d2) (vsQMul_spec hb h u v)).mono ?_
    have wu := wt_vsQE_le h u
    have wv := wt_vsQE_le h v
    have wuv := wt_vsQE_le h (u * v)
    have w3 := wt_list3_le (.nat 0) (vsQE p d E u) (vsQE p d E v)
    have w2 := wt_list2_le (vsQE p d E u) (vsQE p d E v)
    have q3 : 1 * (N + 1) ^ 3 ≤ 1 * (N + 1) ^ 5 := vsQ_powle (by omega : 1 ≤ N + 1) (by omega)
    have w0 : (Val.nat 0).wt = 2 := rfl
    have o3 := vsQ_one_le_pow N 3
    omega
  refine (vsQPow_spec h3 (vsQE p d E) (.nat 0) (fun u => wt_vsQE_le h u) hm3 e x r).mono ?_
  have hbits : e.bits.length ≤ N := by
    rw [wt_nat, linLenBits] at he; omega
  have w0 : (Val.nat 0).wt = 2 := rfl
  have c1 : (e.bits.length + 1) * vsQPowUnit (Val.nat 0).wt (100 * (N + 1) ^ 3)
      (7 * 10 ^ 6 * (N + 1) ^ 5) e.bits.length ≤ (N + 1) * (3 * 10 ^ 7 * (N + 1) ^ 5) := by
    apply Nat.mul_le_mul (by omega)
    unfold vsQPowUnit
    have q3 : 1 * (N + 1) ^ 3 ≤ 1 * (N + 1) ^ 5 := vsQ_powle (by omega : 1 ≤ N + 1) (by omega)
    have q1 := vsQ_le_pow N (k := 5) (by omega)
    omega
  have e6 : (N + 1) * (3 * 10 ^ 7 * (N + 1) ^ 5) = 3 * 10 ^ 7 * (N + 1) ^ 6 := by ring
  omega

/-- The step of the walk, on `[a, i, X]` with `a = [q, X₀, n]`. -/
def vsBWalkStep (pow : ℕ) : Expr :=
  .ite (.arith .mod (.arith .add (arg 1) (.nat 1)) (.get (arg 0) (.nat 0)))
    (.call pow (mk4 (.nat 0) (arg 2) (arg 1) (arg 2))) (arg 2)

/-- The walk at base `b` (3 functions); `pow` is the power function of `vsQGLFuns`. -/
def vsBWalkFuns (b pow : ℕ) : List Expr :=
  loopFuns b (.get (.var 0) (.nat 2)) (.get (.var 0) (.nat 1)) (vsBWalkStep pow)

theorem vsBWalk_succ {M : Type*} [Monoid M] (n q : ℕ) (x : M) :
    vsBWalk (n + 1) q x = if q ∣ n + 1 then vsBWalk n q x else vsBWalk n q x ^ (n + 1) := by
  rw [vsBWalk, List.range_succ, List.foldl_append, ← vsBWalk]
  rfl

set_option maxHeartbeats 2000000 in
/-- **The walk.** On `[q, X, n]` it returns `X^{F_q}` (as `vsBWalk`), when `n + 2 ≤ N`. -/
theorem vsBWalk_spec [NeZero p] {P : Program} {b g : ℕ} (h : P.HasAt b (vsBWalkFuns b (g + 3)))
    (hg : P.HasAt g (vsQGLFuns g)) (hz : VsQSz p d E N) (q n : ℕ) (hn : n + 2 ≤ N) (hq : q ≤ N)
    (X : Matrix (Fin d) (Fin d) (ZMod p)) :
    FunDet P b (.list [.nat q, vsQE p d E X, .nat n]) (vsQE p d E (vsBWalk n q X))
      (10 ^ 10 * (N + 1) ^ 7) := by
  set a := Val.list [.nat q, vsQE p d E X, .nat n] with ha
  have la : ∀ k v, [Val.nat q, vsQE p d E X, .nat n][k]? = some v → Det P [a] (.get (.var 0) (.nat k)) v _ :=
    fun k v hv => Det.get' (Det.var' (P := P) (env := [a]) (i := 0) rfl) (Det.nat k) hv
  have wX := wt_vsQE_le hz X
  have wq := wt_nat_le q
  have wn := wt_nat_le n
  have ea : (Val.list [Val.nat q, vsQE p d E X, .nat n]).wt = a.wt := rfl
  have wXa : (vsQE p d E X).wt < a.wt := wt_le_wt_list (by simp [a])
  have wna : (Val.nat n).wt < a.wt := wt_le_wt_list (by simp [a])
  have wa : a.wt ≤ 300 * (N + 1) ^ 3 := by
    have := wt_list3_le (.nat q) (vsQE p d E X) (.nat n)
    have : N + 1 ≤ (N + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    omega
  have hM : ∀ i acc, i ≤ n → (acc = vsQE p d E (vsBWalk i q X)) → acc.wt ≤ 100 * (N + 1) ^ 3 := by
    rintro i acc - rfl; exact wt_vsQE_le hz _
  refine (loopBdd_spec h (la 2 _ rfl) (la 1 _ rfl) ?_ (Inv := fun i acc => acc = vsQE p d E (vsBWalk i q X))
    (by simp [vsBWalk]) hM (D := fun _ => 2 * 10 ^ 8 * (N + 1) ^ 6) ?_).mono ?_
  · have := wt_nat_le 1; have := wt_nat_le 2
    omega
  · rintro i acc hi rfl
    have g0 := Det.arg' (P := P) (rest := []) (vs := [a, .nat i, vsQE p d E (vsBWalk i q X)]) (j := 0) rfl
    have g1 := Det.arg' (P := P) (rest := []) (vs := [a, .nat i, vsQE p d E (vsBWalk i q X)]) (j := 1) rfl
    have g2 := Det.arg' (P := P) (rest := []) (vs := [a, .nat i, vsQE p d E (vsBWalk i q X)]) (j := 2) rfl
    have dq := Det.get' g0 (Det.nat 0) (show [Val.nat q, vsQE p d E X, .nat n][0]? = some (.nat q) from rfl)
    have dm := Det.arith' (op := .mod) (Det.arith' (op := .add) g1 (Det.nat 1) (z := i + 1) rfl) dq
      (z := (i + 1) % q) rfl
    have wi : (Val.nat i).wt ≤ N := by have := wt_nat_le i; omega
    have dp := Det.call (Det.mk4 (Det.nat 0) g2 g1 g2) (vsB_pow_spec hg hz (vsBWalk i q X) (vsBWalk i q X) wi)
    have dall := Det.ite' dm dp g2
    have hv : (if (i + 1) % q = 0 then vsQE p d E (vsBWalk i q X)
        else vsQE p d E (vsBWalk i q X ^ i * vsBWalk i q X)) = vsQE p d E (vsBWalk (i + 1) q X) := by
      rw [vsBWalk_succ, ← pow_succ]
      by_cases hd : q ∣ i + 1
      · rw [if_pos (Nat.mod_eq_zero_of_dvd hd), if_pos hd]
      · rw [if_neg (fun h0 => hd (Nat.dvd_of_mod_eq_zero h0)), if_neg hd]
    rw [hv] at dall
    refine dall.post fun c hc => ⟨rfl, ?_⟩
    have wsa := wt_stepArg_le a i (vsQE p d E (vsBWalk i q X))
    have w1 := wt_vsQE_le hz (vsBWalk i q X)
    have w2 := wt_vsQE_le hz (vsBWalk (i + 1) q X)
    have w3 := wt_vsQE_le hz (vsBWalk i q X ^ i * vsBWalk i q X)
    have w4 := wt_list4_le (.nat 0) (vsQE p d E (vsBWalk i q X)) (.nat i) (vsQE p d E (vsBWalk i q X))
    have wm1 := wt_nat_le (i + 1)
    have wm2 := wt_nat_le ((i + 1) % q)
    have hmq : (i + 1) % q ≤ i + 1 := Nat.mod_le _ _
    have w0 := wt_nat_le 0; have w1' := wt_nat_le 1
    have q36 : (N + 1) ^ 3 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have q16 : N + 1 ≤ (N + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    have ea : (Val.list [Val.nat q, vsQE p d E X, .nat n]).wt = a.wt := rfl
    have q66 : 1 ≤ (N + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
    simp only [max_def] at hc
    dsimp only
    split_ifs at hc <;> omega
  · rintro w c ⟨rfl, hc⟩
    refine ⟨rfl, hc.trans ?_⟩
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    have h1 : n * (2 * 10 ^ 8 * (N + 1) ^ 6) ≤ (N + 1) * (2 * 10 ^ 8 * (N + 1) ^ 6) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : loopModK * (n + 1) * (a.wt + n + 100 * (N + 1) ^ 3 + 1) ≤
        loopModK * (N + 1) * (1000 * (N + 1) ^ 3) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by
        have : N + 1 ≤ (N + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
        omega)
    have e1 : (N + 1) * (2 * 10 ^ 8 * (N + 1) ^ 6) = 2 * 10 ^ 8 * (N + 1) ^ 7 := by ring
    have e2 : loopModK * (N + 1) * (1000 * (N + 1) ^ 3) = 10 ^ 6 * (N + 1) ^ 4 := by
      simp only [loopModK]; ring
    have : (N + 1) ^ 4 ≤ (N + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega

end GI.Impl
