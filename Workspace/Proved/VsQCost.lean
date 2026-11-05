module

public import Workspace.Proved.VsQProb

@[expose] public section

/-!
# The arithmetic of the cost recursion (M8)

The driver splits a problem of dimension `D` into children. Its cost is bounded by induction:
`vsQFa c D = c (2D - 1)` when the group acts as an abelian group, and `vsQFn c K D = c D^K` in
general. A node costs at most `Cn (1 + T (b + 1))`, where `T` is the number of cosets and `b`
the number of children per coset. The lemmas below are the inequalities of the four kinds of
splits; `c ≥ 10 Cn` throughout.

* `vsQ_cost_chainA`: an abelian chain (`T = 1`, `b ≥ 2` parts of sum `D`).
* `vsQ_cost_chainN`: a chain in general.
* `vsQ_cost_equal`: `b ≥ 2` equal parts, `T ≤ (b + 1)^E`, `K ≥ 2E + 2`.
* `vsQ_cost_abel`: one part, `T ≤ 24 D`, abelian children, `K ≥ 8`.
-/

namespace GI.Proved

/-- The cost bound for an abelian action. -/
def vsQFa (c D : ℕ) : ℕ := c * (2 * D - 1)

/-- The cost bound in general. -/
def vsQFn (c K D : ℕ) : ℕ := c * D ^ K

theorem vsQ_two_pow_add {x s K : ℕ} (hx : 1 ≤ x) (hs : 1 ≤ s) (hK : 2 ≤ K) :
    x ^ K + s ^ K + 2 ≤ (x + s) ^ K := by
  induction K, hK using Nat.le_induction with
  | base => nlinarith
  | succ K hK ih =>
    have h1 : (x + s) ^ (K + 1) = (x + s) * (x + s) ^ K := by ring
    have h2 : 1 ≤ x ^ K := Nat.one_le_pow _ _ hx
    have h3 : 1 ≤ s ^ K := Nat.one_le_pow _ _ hs
    rw [h1, pow_succ, pow_succ]
    nlinarith

/-- A sum of `K`-th powers of parts at least `1`. -/
theorem vsQ_sum_pow_le {K : ℕ} (hK : 2 ≤ K) :
    ∀ xs : List ℕ, xs ≠ [] → (∀ x ∈ xs, 1 ≤ x) →
      (xs.map (· ^ K)).sum + 2 * (xs.length - 1) ≤ xs.sum ^ K
  | [], h, _ => absurd rfl h
  | [x], _, _ => by simp
  | x :: y :: xs, _, hx => by
    have ih := vsQ_sum_pow_le hK (y :: xs) (by simp) fun z hz => hx z (by simp [hz])
    have h1 : 1 ≤ x := hx x (by simp)
    have h2 : 1 ≤ (y :: xs).sum := by
      have := hx y (by simp); simp only [List.sum_cons]; omega
    have h3 := vsQ_two_pow_add h1 h2 hK
    simp only [List.map_cons, List.sum_cons, List.length_cons] at ih h2 h3 ⊢
    omega

theorem vsQ_sum_two_sub {xs : List ℕ} (hx : ∀ x ∈ xs, 1 ≤ x) :
    (xs.map fun x => 2 * x - 1).sum + xs.length = 2 * xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have h1 := hx x (by simp)
    have := ih fun z hz => hx z (by simp [hz])
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

theorem vsQFa_le_Fn {c K D : ℕ} (hD : 1 ≤ D) (hK : 2 ≤ K) : vsQFa c D ≤ vsQFn c K D := by
  unfold vsQFa vsQFn
  apply Nat.mul_le_mul_left
  have : D ^ 2 ≤ D ^ K := Nat.pow_le_pow_right hD hK
  have : 2 * D ≤ D ^ 2 + 1 := by nlinarith
  omega

theorem vsQ_cost_leaf {c Cn D : ℕ} (hc : 10 * Cn ≤ c) (hD : 1 ≤ D) : Cn ≤ vsQFa c D := by
  unfold vsQFa
  have : 1 ≤ 2 * D - 1 := by omega
  nlinarith

/-- **An abelian chain.** -/
theorem vsQ_cost_chainA {c Cn : ℕ} (hc : 10 * Cn ≤ c) {xs : List ℕ} (hb : 2 ≤ xs.length)
    (hx : ∀ x ∈ xs, 1 ≤ x) :
    Cn * (1 + 1 * (xs.length + 1)) + (xs.map (vsQFa c)).sum ≤ vsQFa c xs.sum := by
  have h1 := vsQ_sum_two_sub hx
  have e : (xs.map (vsQFa c)).sum = c * (xs.map fun x => 2 * x - 1).sum := by
    unfold vsQFa; rw [← List.sum_map_mul_left]
  rw [e]
  unfold vsQFa
  generalize hS : (xs.map fun x => 2 * x - 1).sum = S at h1
  have h2 : 2 * xs.sum - 1 = S + (xs.length - 1) := by omega
  rw [h2, Nat.mul_add c]
  have : Cn * (1 + 1 * (xs.length + 1)) ≤ c * (xs.length - 1) := by
    have : Cn * (xs.length + 2) ≤ 10 * Cn * (xs.length - 1) := by
      have : xs.length + 2 ≤ 10 * (xs.length - 1) := by omega
      nlinarith
    calc Cn * (1 + 1 * (xs.length + 1)) = Cn * (xs.length + 2) := by ring
      _ ≤ 10 * Cn * (xs.length - 1) := this
      _ ≤ c * (xs.length - 1) := Nat.mul_le_mul_right _ hc
  omega

/-- **A chain in general.** -/
theorem vsQ_cost_chainN {c Cn K : ℕ} (hc : 10 * Cn ≤ c) (hK : 2 ≤ K) {xs : List ℕ}
    (hb : 2 ≤ xs.length) (hx : ∀ x ∈ xs, 1 ≤ x) :
    Cn * (1 + 1 * (xs.length + 1)) + (xs.map (vsQFn c K)).sum ≤ vsQFn c K xs.sum := by
  have h1 := vsQ_sum_pow_le hK xs (by rintro rfl; simp at hb) hx
  have e : (xs.map (vsQFn c K)).sum = c * (xs.map (· ^ K)).sum := by
    unfold vsQFn; rw [← List.sum_map_mul_left]
  rw [e]
  unfold vsQFn
  have h2 : c * ((xs.map (· ^ K)).sum + 2 * (xs.length - 1)) ≤ c * xs.sum ^ K :=
    Nat.mul_le_mul_left _ h1
  have h3 : Cn * (1 + 1 * (xs.length + 1)) ≤ c * (2 * (xs.length - 1)) := by
    have : Cn * (xs.length + 2) ≤ 10 * Cn * (2 * (xs.length - 1)) := by
      have : xs.length + 2 ≤ 10 * (2 * (xs.length - 1)) := by omega
      nlinarith
    calc Cn * (1 + 1 * (xs.length + 1)) = Cn * (xs.length + 2) := by ring
      _ ≤ 10 * Cn * (2 * (xs.length - 1)) := this
      _ ≤ c * (2 * (xs.length - 1)) := Nat.mul_le_mul_right _ hc
  rw [Nat.mul_add] at h2
  omega

/-- **Equal parts.** -/
theorem vsQ_cost_equal {c Cn K E b D T : ℕ} (hc : 10 * Cn ≤ c) (hK : 2 * E + 2 ≤ K)
    (hb : 2 ≤ b) (hD : 1 ≤ D) (hT : T ≤ (b + 1) ^ E) :
    Cn * (1 + T * (b + 1)) + T * (b * vsQFn c K D) ≤ vsQFn c K (b * D) := by
  unfold vsQFn
  have hb2 : b + 1 ≤ b ^ 2 := by nlinarith
  have hbE : (b + 1) ^ E ≤ b ^ (2 * E) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left hb2 E
  have hbK : b ^ (2 * E + 2) ≤ b ^ K := Nat.pow_le_pow_right (by omega) hK
  have e1 : b ^ (2 * E + 2) = b ^ (2 * E) * b ^ 2 := by ring
  have hDK : 1 ≤ D ^ K := Nat.one_le_pow _ _ hD
  -- the children
  have k1 : T * b * 2 ≤ b ^ K := by
    have : T * b * 2 ≤ b ^ (2 * E) * b ^ 2 := by
      have : b * 2 ≤ b ^ 2 := by nlinarith
      calc T * b * 2 = T * (b * 2) := by ring
        _ ≤ b ^ (2 * E) * b ^ 2 := Nat.mul_le_mul (hT.trans hbE) this
    omega
  -- the node
  have k2 : 1 + T * (b + 1) ≤ 5 * b ^ K := by
    have : T * (b + 1) ≤ b ^ (2 * E) * b ^ 2 := Nat.mul_le_mul (hT.trans hbE) hb2
    have : 1 ≤ b ^ K := Nat.one_le_pow _ _ (by omega)
    omega
  have e2 : (b * D) ^ K = b ^ K * D ^ K := by ring
  rw [e2]
  have k3 : T * (b * (c * D ^ K)) * 2 ≤ c * (b ^ K * D ^ K) := by
    calc T * (b * (c * D ^ K)) * 2 = (T * b * 2) * (c * D ^ K) := by ring
      _ ≤ b ^ K * (c * D ^ K) := Nat.mul_le_mul_right _ k1
      _ = c * (b ^ K * D ^ K) := by ring
  have k4 : Cn * (1 + T * (b + 1)) * 2 ≤ c * (b ^ K * D ^ K) := by
    calc Cn * (1 + T * (b + 1)) * 2 ≤ Cn * (5 * b ^ K) * 2 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ k2)
      _ = 10 * Cn * b ^ K := by ring
      _ ≤ c * b ^ K := Nat.mul_le_mul_right _ hc
      _ ≤ c * (b ^ K * D ^ K) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hDK)
  omega

/-- **One part with an abelian group.** -/
theorem vsQ_cost_abel {c Cn K D T : ℕ} (hc : 10 * Cn ≤ c) (hK : 8 ≤ K) (hD : 2 ≤ D)
    (hT : T ≤ 24 * D) :
    Cn * (1 + T * (1 + 1)) + T * vsQFa c D ≤ vsQFn c K D := by
  unfold vsQFa vsQFn
  have hD8 : D ^ 2 * 2 ^ 6 ≤ D ^ K := by
    have : D ^ 2 * 2 ^ 6 ≤ D ^ 2 * D ^ 6 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hD 6)
    have e : D ^ 2 * D ^ 6 = D ^ 8 := by ring
    have : D ^ 8 ≤ D ^ K := Nat.pow_le_pow_right (by omega) hK
    omega
  have k1 : T * (c * (2 * D - 1)) ≤ c * (48 * D ^ 2) := by
    calc T * (c * (2 * D - 1)) ≤ (24 * D) * (c * (2 * D)) :=
          Nat.mul_le_mul hT (Nat.mul_le_mul_left _ (by omega))
      _ = c * (48 * D ^ 2) := by ring
  have k2 : Cn * (1 + T * (1 + 1)) ≤ c * (5 * D ^ 2) := by
    have h49 : 1 + T * (1 + 1) ≤ 49 * D ^ 2 := by nlinarith
    have : 10 * (Cn * (49 * D ^ 2)) ≤ 10 * (c * (5 * D ^ 2)) := by
      calc 10 * (Cn * (49 * D ^ 2)) = (10 * Cn) * (49 * D ^ 2) := by ring
        _ ≤ c * (49 * D ^ 2) := Nat.mul_le_mul_right _ hc
        _ ≤ c * (50 * D ^ 2) := Nat.mul_le_mul_left _ (by omega)
        _ = 10 * (c * (5 * D ^ 2)) := by ring
    exact (Nat.mul_le_mul_left _ h49).trans (Nat.le_of_mul_le_mul_left this (by norm_num))
  have k3 : c * (48 * D ^ 2) + c * (5 * D ^ 2) ≤ c * D ^ K := by
    rw [← Nat.mul_add]; apply Nat.mul_le_mul_left; omega
  omega

end GI.Proved
