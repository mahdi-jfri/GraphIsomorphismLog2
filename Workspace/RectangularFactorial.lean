module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic

@[expose] public section

namespace GI.ImprimitiveIndex

/-- A function supplies a distinct subset of its rectangular domain by
taking its graph. This gives an elementary binomial lower bound. -/
def graphSubset (a b : ℕ) (f : Fin a → Fin b) :
    {s : Finset (Fin a × Fin b) // s.card = a} :=
  ⟨Finset.univ.map ⟨fun i => (i, f i), fun _ _ h => congrArg Prod.fst h⟩, by simp⟩

theorem graphSubset_injective (a b : ℕ) : Function.Injective (graphSubset a b) := by
  intro f g he
  funext i
  have hi : (i, f i) ∈ (graphSubset a b f).val := Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩
  rw [he] at hi
  rcases Finset.mem_map.mp hi with ⟨j, _, hj⟩
  rcases Prod.mk.inj hj with ⟨rfl, h⟩
  exact h.symm

theorem pow_le_choose_mul (a b : ℕ) : b ^ a ≤ Nat.choose (a * b) a := by
  have hc := Fintype.card_le_of_injective _ (graphSubset_injective a b)
  simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_finset_len,
    Fintype.card_prod] using hc

/-- The factorial estimate needed for a genuine equal-block partition.
It follows by adding one block and applying the graph-subset bound. -/
theorem rectangular_factorial (a b : ℕ) :
    a.factorial ^ b * b.factorial ^ a ≤ (a * b).factorial := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hchoose := pow_le_choose_mul a (b + 1)
    have hfac := Nat.choose_mul_factorial_mul_factorial (show a ≤ a * (b + 1) by nlinarith)
    have hsub : a * (b + 1) - a = a * b := by
      rw [Nat.mul_add, Nat.mul_one, Nat.add_sub_cancel]
    rw [hsub] at hfac
    calc
      a.factorial ^ (b + 1) * (b + 1).factorial ^ a =
          (b + 1) ^ a * a.factorial * (a.factorial ^ b * b.factorial ^ a) := by
        rw [pow_succ, Nat.factorial_succ, mul_pow]
        ring
      _ ≤ Nat.choose (a * (b + 1)) a * a.factorial * (a * b).factorial :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ hchoose) ih
      _ = (a * (b + 1)).factorial := hfac

theorem two_pow_pred_le_factorial (b : ℕ) : 2 ^ (b - 1) ≤ b.factorial := by
  cases b with
  | zero => simp
  | succ b =>
    induction b with
    | zero => simp
    | succ b ih =>
      simp only [Nat.add_sub_cancel] at ih ⊢
      rw [pow_succ, Nat.factorial_succ]
      exact (Nat.mul_le_mul ih (by omega : 2 ≤ b + 1 + 1)).trans_eq (Nat.mul_comm _ _)

/-- The partition-stabilizer denominator loses an exponential factor.
This numerical inequality uses no group classification. -/
theorem block_factorial_exponential (a b : ℕ) (ha : 1 ≤ a) :
    2 ^ ((a - 1) * (b - 1)) * (b.factorial * a.factorial ^ b) ≤
      (a * b).factorial := by
  have hpow := Nat.pow_le_pow_left (two_pow_pred_le_factorial b) (a - 1)
  have hpow' : 2 ^ ((a - 1) * (b - 1)) ≤ b.factorial ^ (a - 1) := by
    simpa only [← pow_mul, Nat.mul_comm (b - 1) (a - 1)] using hpow
  calc
    2 ^ ((a - 1) * (b - 1)) * (b.factorial * a.factorial ^ b) ≤
        b.factorial ^ (a - 1) * (b.factorial * a.factorial ^ b) :=
      Nat.mul_le_mul_right _ hpow'
    _ = a.factorial ^ b * b.factorial ^ a := by
      rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel ha]
      exact Nat.mul_comm _ _
    _ ≤ (a * b).factorial := rectangular_factorial a b

end GI.ImprimitiveIndex
