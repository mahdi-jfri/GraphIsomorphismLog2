module

public import Workspace.Degree.ProgCost
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Bounds of the form `exp(C log(n + 2) log(d + 2))`

`PolyB2` is a polynomial bound in two numbers, the size `n` and the cost `S` of the string solver.
`LogExpB` is a bound `exp(C log(n + 2) log(d + 2))`. Polynomials in `n` have such a bound, and the
class is closed under sums, products and powers.
-/

@[expose] public section

namespace GI.Degree

/-- A polynomial bound in `S` and `n`. -/
def PolyB2 (F : ℕ → ℕ → ℕ) : Prop := ∃ K e, ∀ S n, F S n ≤ K * (n + S + 1) ^ e

namespace PolyB2

theorem const (c : ℕ) : PolyB2 fun _ _ => c := ⟨c, 0, fun S n => by simp⟩

theorem idS : PolyB2 fun S _ => S := ⟨1, 1, fun S n => by simp; omega⟩

theorem idN : PolyB2 fun _ n => n := ⟨1, 1, fun S n => by simp; omega⟩

theorem of_poly {f : ℕ → ℕ} (hf : PolyB f) : PolyB2 fun _ n => f n := by
  obtain ⟨K, e, hf⟩ := hf
  exact ⟨K, e, fun S n => (hf n).trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (by omega) _))⟩

theorem of_poly' {f : ℕ → ℕ} (hf : PolyB f) : PolyB2 fun _ => f := of_poly hf

theorem mono_le {X : ℕ} {e e' : ℕ} (hX : 1 ≤ X) (h : e ≤ e') : X ^ e ≤ X ^ e' :=
  Nat.pow_le_pow_right hX h

theorem add {F G : ℕ → ℕ → ℕ} (hF : PolyB2 F) (hG : PolyB2 G) : PolyB2 fun S n => F S n + G S n := by
  obtain ⟨K, e, hF⟩ := hF
  obtain ⟨K', e', hG⟩ := hG
  refine ⟨K + K', e + e', fun S n => ?_⟩
  have h1 : (n + S + 1) ^ e ≤ (n + S + 1) ^ (e + e') := mono_le (by omega) (by omega)
  have h2 : (n + S + 1) ^ e' ≤ (n + S + 1) ^ (e + e') := mono_le (by omega) (by omega)
  have := Nat.add_le_add ((hF S n).trans (Nat.mul_le_mul_left K h1))
    ((hG S n).trans (Nat.mul_le_mul_left K' h2))
  rw [Nat.add_mul]
  exact this

theorem mul {F G : ℕ → ℕ → ℕ} (hF : PolyB2 F) (hG : PolyB2 G) : PolyB2 fun S n => F S n * G S n := by
  obtain ⟨K, e, hF⟩ := hF
  obtain ⟨K', e', hG⟩ := hG
  refine ⟨K * K', e + e', fun S n => ?_⟩
  calc F S n * G S n ≤ (K * (n + S + 1) ^ e) * (K' * (n + S + 1) ^ e') :=
        Nat.mul_le_mul (hF S n) (hG S n)
    _ = K * K' * (n + S + 1) ^ (e + e') := by ring

theorem pow {F : ℕ → ℕ → ℕ} (hF : PolyB2 F) (k : ℕ) : PolyB2 fun S n => F S n ^ k := by
  induction k with
  | zero => simpa using const 1
  | succ k ih => simpa [pow_succ] using mul ih hF

end PolyB2

/-- Prove `PolyB2` of an expression. -/
macro "poly2" : tactic => `(tactic| repeat' first
  | with_reducible assumption
  | with_reducible apply PolyB2.idS
  | with_reducible apply PolyB2.idN
  | with_reducible apply PolyB2.add
  | with_reducible apply PolyB2.mul
  | with_reducible apply PolyB2.pow
  | (with_reducible apply PolyB2.of_poly; assumption)
  | (with_reducible apply PolyB2.of_poly'; assumption)
  | with_reducible apply PolyB2.const)

/-- A bound `exp(C log(n + 2) log(d + 2))`. -/
def LogExpB (f : ℕ → ℕ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ n d : ℕ, f n d ≤ Real.exp (C * Real.log ((n : ℝ) + 2) * Real.log ((d : ℝ) + 2))

namespace LogExpB

theorem log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem log_ge (m : ℕ) : Real.log 2 ≤ Real.log ((m : ℝ) + 2) :=
  Real.log_le_log (by norm_num) (by have := m.cast_nonneg (α := ℝ); linarith)

theorem prod_ge (n d : ℕ) :
    Real.log 2 * Real.log 2 ≤ Real.log ((n : ℝ) + 2) * Real.log ((d : ℝ) + 2) :=
  mul_le_mul (log_ge n) (log_ge d) log2_pos.le (log2_pos.le.trans (log_ge n))

theorem const (c : ℝ) : LogExpB fun _ _ => c := by
  refine ⟨|Real.log (max c 1)| / (Real.log 2 * Real.log 2), fun n d => ?_⟩
  have hp := prod_ge n d
  have h2 : 0 < Real.log 2 * Real.log 2 := mul_pos log2_pos log2_pos
  have h3 : Real.log (max c 1) ≤ |Real.log (max c 1)| / (Real.log 2 * Real.log 2) *
      Real.log ((n : ℝ) + 2) * Real.log ((d : ℝ) + 2) := by
    rw [mul_assoc, div_mul_eq_mul_div, le_div_iff₀ h2]
    calc Real.log (max c 1) * (Real.log 2 * Real.log 2)
        ≤ |Real.log (max c 1)| * (Real.log 2 * Real.log 2) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) h2.le
      _ ≤ |Real.log (max c 1)| * (Real.log ((n : ℝ) + 2) * Real.log ((d : ℝ) + 2)) :=
          mul_le_mul_of_nonneg_left hp (abs_nonneg _)
  calc c ≤ max c 1 := le_max_left _ _
    _ = Real.exp (Real.log (max c 1)) := (Real.exp_log (by positivity)).symm
    _ ≤ _ := Real.exp_le_exp.2 h3

theorem n2 : LogExpB fun n _ => (n : ℝ) + 2 := by
  refine ⟨1 / Real.log 2, fun n d => ?_⟩
  have hd := log_ge d
  have hn : 0 ≤ Real.log ((n : ℝ) + 2) := log2_pos.le.trans (log_ge n)
  have h3 : Real.log ((n : ℝ) + 2) ≤ 1 / Real.log 2 * Real.log ((n : ℝ) + 2) *
      Real.log ((d : ℝ) + 2) := by
    have key : 1 / Real.log 2 * Real.log ((n : ℝ) + 2) * Real.log ((d : ℝ) + 2) =
        Real.log ((n : ℝ) + 2) * (Real.log ((d : ℝ) + 2) / Real.log 2) := by ring
    rw [key]
    have : 1 ≤ Real.log ((d : ℝ) + 2) / Real.log 2 := (one_le_div log2_pos).2 hd
    nlinarith
  calc (n : ℝ) + 2 = Real.exp (Real.log ((n : ℝ) + 2)) := (Real.exp_log (by positivity)).symm
    _ ≤ _ := Real.exp_le_exp.2 h3

theorem mul {f g : ℕ → ℕ → ℝ} (hf : LogExpB f) (hg : LogExpB g) (h0 : ∀ n d, 0 ≤ f n d)
    (h1 : ∀ n d, 0 ≤ g n d) : LogExpB fun n d => f n d * g n d := by
  obtain ⟨C, hf⟩ := hf
  obtain ⟨C', hg⟩ := hg
  refine ⟨C + C', fun n d => ?_⟩
  calc f n d * g n d ≤ Real.exp (C * Real.log ((n : ℝ) + 2) * Real.log ((d : ℝ) + 2)) *
        Real.exp (C' * Real.log ((n : ℝ) + 2) * Real.log ((d : ℝ) + 2)) :=
        mul_le_mul (hf n d) (hg n d) (h1 n d) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; ring_nf

theorem pow {f : ℕ → ℕ → ℝ} (hf : LogExpB f) (h0 : ∀ n d, 0 ≤ f n d) (k : ℕ) :
    LogExpB fun n d => f n d ^ k := by
  induction k with
  | zero => simpa using const 1
  | succ k ih => simpa [pow_succ] using mul ih hf (fun n d => pow_nonneg (h0 n d) _) h0

theorem mono {f g : ℕ → ℕ → ℝ} (hg : LogExpB g) (h : ∀ n d, f n d ≤ g n d) : LogExpB f := by
  obtain ⟨C, hg⟩ := hg
  exact ⟨C, fun n d => (h n d).trans (hg n d)⟩

/-- `exp(a log(x + 2) log(y + 2))` with `x + 2 ≤ (n + 2)^8` and `y + 2 ≤ (d + 2)^3`. -/
theorem expLog {a : ℝ} (ha : 0 ≤ a) {x y : ℕ → ℕ → ℝ} (hx0 : ∀ n d, 0 ≤ x n d)
    (hy0 : ∀ n d, 0 ≤ y n d) (hx : ∀ n d, x n d + 2 ≤ ((n : ℝ) + 2) ^ 8)
    (hy : ∀ n d, y n d + 2 ≤ ((d : ℝ) + 2) ^ 3) :
    LogExpB fun n d => Real.exp (a * Real.log (x n d + 2) * Real.log (y n d + 2)) := by
  refine ⟨24 * a, fun n d => Real.exp_le_exp.2 ?_⟩
  have hl1 : Real.log (x n d + 2) ≤ 8 * Real.log ((n : ℝ) + 2) := by
    have := Real.log_le_log (by linarith [hx0 n d]) (hx n d)
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hl2 : Real.log (y n d + 2) ≤ 3 * Real.log ((d : ℝ) + 2) := by
    have := Real.log_le_log (by linarith [hy0 n d]) (hy n d)
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have p1 : 0 ≤ Real.log (x n d + 2) := Real.log_nonneg (by linarith [hx0 n d])
  have p2 : 0 ≤ Real.log (y n d + 2) := Real.log_nonneg (by linarith [hy0 n d])
  have := mul_le_mul hl1 hl2 p2 (by linarith)
  have := mul_le_mul_of_nonneg_left this ha
  nlinarith

end LogExpB

end GI.Degree
