import Workspace.Impl.GenCls
import Mathlib.Data.Nat.Choose.Bounds

/-!
# The product refinement: two numbers

* `fact_spec`: `r!`, a bound on the number of cosets of the coordinate group (it is at most the
  number of permutations of the `r` coordinates);
* `choose_spec`: `binom(m, l)`, the ratio of each coordinate interval.

Both are loops whose accumulator is a number.
-/

namespace GI.Impl

open GI.Lang
open GI.Cited (Val)
open GI.Machine (len len_mono len_le_self)

/-- The factorial at base `b` (three functions): on `r`, `r!`. -/
def factFuns (b : ℕ) : List Expr :=
  loopFuns b (.var 0) (.nat 1) (.arith .mul (arg 2) (.arith .add (arg 1) (.nat 1)))

/-- The binomial coefficient at base `b`: on `[m, l]`, `binom(m, l)`. -/
def chooseFuns (b : ℕ) : List Expr :=
  loopFuns b (.get (.var 0) (.nat 1)) (.nat 1)
    (.arith .div (.arith .mul (arg 2) (.arith .sub (.get (arg 0) (.nat 0)) (arg 1)))
      (.arith .add (arg 1) (.nat 1)))

/-- The constant of the two loops. -/
def numK : ℕ := 10 ^ 5

theorem wt_nat_mono {a b : ℕ} (h : a ≤ b) : (Val.nat a).wt ≤ (Val.nat b).wt := by
  rw [wt_nat, wt_nat]; have := len_mono h; omega

set_option maxHeartbeats 1000000 in
/-- **The factorial.** -/
theorem fact_spec {P : Program} {b : ℕ} (h : P.HasAt b (factFuns b)) (r : ℕ) :
    FunDet P b (.nat r) (.nat r.factorial)
      (numK * (r + 1) * (r + (Val.nat r.factorial).wt + 10)) := by
  set M := (Val.nat r.factorial).wt with hM
  have hk : Det P [.nat r] (.var 0) (.nat r) _ := Det.var' rfl
  have h0 := Det.nat (P := P) (env := [Val.nat r]) 1
  have wr := wt_nat_le r
  have wr' : (Val.nat r).wt ≤ M := wt_nat_mono (Nat.self_le_factorial r)
  refine (loopBdd_spec h hk h0 (M := M) (Inv := fun i acc => acc = .nat i.factorial)
    (D := fun _ => 20 * M + 20) ?_ rfl ?_ ?_).mono ?_
  · have := wt_nat_le 1; have := Nat.one_le_two_pow (n := 0); omega
  · rintro i acc hi rfl
    exact wt_nat_mono (Nat.factorial_le hi)
  · rintro i acc hi rfl
    have dA := Det.arg' (P := P) (vs := [.nat r, .nat i, .nat i.factorial]) (rest := []) (j := 2) rfl
    have dI := Det.arg' (P := P) (vs := [.nat r, .nat i, .nat i.factorial]) (rest := []) (j := 1) rfl
    have d := Det.arith (op := .mul) dA (Det.arith' (op := .add) dI (Det.nat 1) (z := i + 1) rfl)
    refine d.post fun c hc => ⟨by
      show Val.nat (i.factorial * (i + 1)) = _
      rw [Nat.factorial_succ, Nat.mul_comm], ?_⟩
    have e1 : GI.Machine.BinOp.eval .mul i.factorial (i + 1) = (i + 1).factorial := by
      show i.factorial * (i + 1) = _; rw [Nat.factorial_succ, Nat.mul_comm]
    rw [e1] at hc
    have w1 := wt_nat_mono (Nat.factorial_le (show i + 1 ≤ r by omega))
    have w2 := wt_nat_mono (Nat.factorial_le (show i ≤ r by omega))
    have w3 := wt_list3_le (.nat r) (.nat i) (.nat i.factorial)
    have w4 := wt_nat_le i
    have w5 := wt_nat_le 1
    omega
  · rintro w c ⟨rfl, hc⟩
    refine ⟨rfl, ?_⟩
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
    have h1 : r * (20 * M + 20) ≤ (r + 1) * (20 * (r + M + 10)) := Nat.mul_le_mul (by omega) (by omega)
    have h2 : loopModK * (r + 1) * ((Val.nat r).wt + r + M + 1) ≤ 1000 * (r + 1) * (3 * (r + M + 10)) :=
      Nat.mul_le_mul (by simp [loopModK]) (by omega)
    have e2 : (r + 1) * (20 * (r + M + 10)) + 1000 * (r + 1) * (3 * (r + M + 10)) ≤
        numK * (r + 1) * (r + M + 10) := by
      simp only [numK]; nlinarith
    omega

theorem choose_succ_eq (m i : ℕ) : m.choose i * (m - i) / (i + 1) = m.choose (i + 1) := by
  rw [← Nat.choose_succ_right_eq, Nat.mul_div_cancel _ (by omega)]

set_option maxHeartbeats 1000000 in
/-- **The binomial coefficient.** -/
theorem choose_spec {P : Program} {b : ℕ} (h : P.HasAt b (chooseFuns b)) (m l : ℕ) :
    FunDet P b (.list [.nat m, .nat l]) (.nat (m.choose l))
      (numK * (l + 1) * ((Val.list [.nat m, .nat l]).wt + l + m + 10) ^ 2) := by
  set a := Val.list [.nat m, .nat l] with ha
  set M := m + 3 with hM
  have hwc : ∀ i, (Val.nat (m.choose i)).wt ≤ M := fun i => by
    rw [wt_nat]
    have h1 := Nat.choose_le_two_pow m i
    have h2 := len_mono h1
    have h3 : len (2 ^ m) ≤ m + 1 := by
      have := GI.Machine.len_two_pow m
      omega
    omega
  have hk : Det P [a] (.get (.var 0) (.nat 1)) (.nat l) _ :=
    Det.get' (Det.var' (P := P) (env := [a]) (i := 0) rfl) (Det.nat 1) rfl
  have h0 := Det.nat (P := P) (env := [a]) 1
  have wl : (Val.nat l).wt < a.wt := wt_le_wt_list (by simp [ha])
  have wm : (Val.nat m).wt < a.wt := wt_le_wt_list (by simp [ha])
  have hwa := wt_list2_le (.nat m) (.nat l)
  have wl' := wt_nat_le l
  have wm' := wt_nat_le m
  refine (loopBdd_spec h hk h0 (M := M) (Inv := fun i acc => acc = .nat (m.choose i))
    (D := fun _ => 100 * (a.wt + l + m + 10)) ?_ (by simp) ?_ ?_).mono ?_
  · have := wt_nat_le 1; omega
  · rintro i acc hi rfl; exact hwc i
  · rintro i acc hi rfl
    set A := Val.list [a, .nat i, .nat (m.choose i)]
    have dA := Det.arg' (P := P) (vs := [a, .nat i, .nat (m.choose i)]) (rest := []) (j := 0) rfl
    have dC := Det.arg' (P := P) (vs := [a, .nat i, .nat (m.choose i)]) (rest := []) (j := 2) rfl
    have dI := Det.arg' (P := P) (vs := [a, .nat i, .nat (m.choose i)]) (rest := []) (j := 1) rfl
    have dM := Det.get' dA (Det.nat 0) (v := .nat m) rfl
    have dS := Det.arith' (op := .sub) dM dI (z := m - i) rfl
    have dP := Det.arith (op := .mul) dC dS
    have dQ := Det.arith' (op := .add) dI (Det.nat 1) (z := i + 1) rfl
    have d := Det.arith (op := .div) dP dQ
    have e1 : GI.Machine.BinOp.eval .div (GI.Machine.BinOp.eval .mul (m.choose i) (m - i)) (i + 1) =
        m.choose (i + 1) := choose_succ_eq m i
    rw [e1] at d
    refine d.post fun c hc => ⟨rfl, ?_⟩
    have wP : (Val.nat (GI.Machine.BinOp.eval .mul (m.choose i) (m - i))).wt ≤ 2 * m + 4 := by
      show (Val.nat (m.choose i * (m - i))).wt ≤ _
      rw [wt_nat]
      have h1 := GI.Machine.len_mul_le (m.choose i) (m - i)
      have h2 := hwc i
      rw [wt_nat] at h2
      have h3 := len_le_self (m - i)
      omega
    have w1 := hwc (i + 1)
    have w2 := hwc i
    have w3 := wt_list3_le a (.nat i) (.nat (m.choose i))
    have w4 := wt_nat_le i
    have w5 := wt_nat_le 1
    have w6 := wt_nat_le 0
    omega
  · rintro w c ⟨rfl, hc⟩
    refine ⟨rfl, ?_⟩
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
    set Z := a.wt + l + m + 10
    have h1 : l * (100 * Z) ≤ (l + 1) * (100 * Z) := Nat.mul_le_mul_right _ (by omega)
    have h2 : loopModK * (l + 1) * (a.wt + l + M + 1) ≤ 1000 * (l + 1) * Z :=
      Nat.mul_le_mul (by simp [loopModK]) (by omega)
    have hZ : Z ≤ Z ^ 2 := Nat.le_self_pow (by norm_num) _
    have e2 : (l + 1) * (100 * Z) + 1000 * (l + 1) * Z ≤ numK * (l + 1) * Z ^ 2 := by
      have : (l + 1) * Z ≤ (l + 1) * Z ^ 2 := Nat.mul_le_mul_left _ hZ
      simp only [numK]; nlinarith
    omega

end GI.Impl
