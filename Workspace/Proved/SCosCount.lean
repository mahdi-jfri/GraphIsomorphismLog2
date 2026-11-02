import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The arithmetic of the running time

The recursion of [LM, Proposition 3.9] costs at most `Q` per node, apart from its recursive
calls, where `Q` is a polynomial in the degree. We show that a call on a set `Φ` of `k`
points costs at most `scosBnd Q c k = 2 Q (k^d + 1)` with `d = 2c + 4`, where `(m + 1)^c`
bounds the number of cosets of the kernel on `m` blocks (`GI.Proved.scos_palfy_classes`).

The program's cost proof is an induction on `k` with three kinds of nodes.
* `scosCount_split`: an intransitive node calls itself on an orbit `O` and on `Φ \ O`.
* `scosCount_trans`: a transitive node on `k ≥ 2` points with `m ≥ 2` blocks of `s` points
  calls itself on `ℓ ≤ (m + 1)^c` problems on `Φ` whose orbits have at most `s` points.
* A problem whose orbits have at most `s` points costs at most `scosSmall Q c s j =
  2 Q (s^(d-1) j + 2 j + 1)` for `j = |Φ|` (`scosCount_small_step`, `scosCount_small_trans`,
  by induction on `j`).
The only real estimate is in `scosCount_trans`: `(m + 1)^c ≤ m^(2c)` and `m s ≤ k` give
`ℓ s^(d-1) k ≤ k^d / 8`.
-/

namespace GI.Proved

/-- The cost bound of a call on `k` points. -/
def scosBnd (Q c k : ℕ) : ℕ := 2 * Q * (k ^ (2 * c + 4) + 1)

/-- The cost bound of a call on `j` points whose orbits have at most `s` points. -/
def scosSmall (Q c s j : ℕ) : ℕ := 2 * Q * (s ^ (2 * c + 3) * j + 2 * j + 1)

theorem scos_add_pow_ge {a b d : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hd : 2 ≤ d) :
    a ^ d + b ^ d + 2 ≤ (a + b) ^ d := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  induction e with
  | zero =>
    have : 1 ≤ a * b := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    show a ^ 2 + b ^ 2 + 2 ≤ (a + b) ^ 2
    nlinarith
  | succ e ih =>
    have ih := ih (by omega)
    have h1 : a ^ (e + 1 + 2) = a * a ^ (e + 2) := by ring
    have h2 : b ^ (e + 1 + 2) = b * b ^ (e + 2) := by ring
    have h3 : (a + b) ^ (e + 1 + 2) = (a + b) * (a + b) ^ (e + 2) := by ring
    rw [h1, h2, h3]
    have ha' : a ^ (e + 2) ≤ (a + b) ^ (e + 2) := Nat.pow_le_pow_left (by omega) _
    have hb' : b ^ (e + 2) ≤ (a + b) ^ (e + 2) := Nat.pow_le_pow_left (by omega) _
    have k1 : a * a ^ (e + 2) + a * b ^ (e + 2) + a * 2 ≤ a * (a + b) ^ (e + 2) := by
      rw [← Nat.mul_add, ← Nat.mul_add]; exact Nat.mul_le_mul_left a ih
    have k2 := Nat.mul_le_mul_left b hb'
    rw [Nat.add_mul]
    omega

/-- **An intransitive node.** -/
theorem scosCount_split (Q c a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Q + scosBnd Q c a + scosBnd Q c b ≤ scosBnd Q c (a + b) := by
  unfold scosBnd
  have := scos_add_pow_ge (d := 2 * c + 4) ha hb (by omega)
  nlinarith

/-- **A small node that is transitive**: then `j ≤ s`. -/
theorem scosCount_small_trans (Q c s j : ℕ) (hj : j ≤ s) :
    scosBnd Q c j ≤ scosSmall Q c s j := by
  unfold scosBnd scosSmall
  have : j ^ (2 * c + 4) ≤ s ^ (2 * c + 3) * j := by
    rw [pow_succ]; exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hj _)
  have := Nat.mul_le_mul_left (2 * Q) (show j ^ (2 * c + 4) + 1 ≤
    s ^ (2 * c + 3) * j + 2 * j + 1 by omega)
  linarith

/-- **A small node that is intransitive**: an orbit of `o ≤ s` points and the rest. -/
theorem scosCount_small_step (Q c s j o : ℕ) (ho : 1 ≤ o) (hos : o ≤ s) (hoj : o ≤ j) :
    Q + scosBnd Q c o + scosSmall Q c s (j - o) ≤ scosSmall Q c s j := by
  have h1 : o ^ (2 * c + 4) ≤ s ^ (2 * c + 3) * o := by
    rw [pow_succ]; exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hos _)
  unfold scosBnd scosSmall
  have e : s ^ (2 * c + 3) * j = s ^ (2 * c + 3) * o + s ^ (2 * c + 3) * (j - o) := by
    rw [← Nat.mul_add, Nat.add_sub_cancel' hoj]
  rw [e]
  have h2 : (o ^ (2 * c + 4) + 1) + (s ^ (2 * c + 3) * (j - o) + 2 * (j - o) + 1) + 1 ≤
      s ^ (2 * c + 3) * o + s ^ (2 * c + 3) * (j - o) + 2 * j + 1 := by omega
  have := Nat.mul_le_mul_left (2 * Q) h2
  nlinarith

/-- **A transitive node.** For `k ≥ 2` points, `m ≥ 2` blocks of `s` points (`m s ≤ k`) and
`ℓ ≤ (m + 1)^c` children whose orbits have at most `s` points. -/
theorem scosCount_trans (Q c k m s ℓ : ℕ) (hk : 2 ≤ k) (hm : 2 ≤ m) (hs : 1 ≤ s)
    (hms : m * s ≤ k)
    (hℓ : ℓ ≤ (m + 1) ^ c) :
    Q + ℓ * (Q + scosSmall Q c s k) ≤ scosBnd Q c k := by
  unfold scosBnd scosSmall
  -- `(m + 1)^c ≤ m^(2c)` and `(k + 1)^(c+1) ≤ k^(2c+2)`.
  have hm2 : (m + 1) ^ c ≤ m ^ (2 * c) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left (by nlinarith) c
  have hmk : m ≤ k := by nlinarith
  have hℓk : ℓ ≤ (k + 1) ^ c := hℓ.trans (Nat.pow_le_pow_left (by omega) c)
  -- The main term: `ℓ s^(2c+3) k ≤ k^(2c+4) / 8`.
  have hs2 : 2 * s ≤ k := by nlinarith
  have hmain : 8 * (ℓ * (s ^ (2 * c + 3) * k)) ≤ k ^ (2 * c + 4) := by
    have e1 : ℓ * (s ^ (2 * c + 3) * k) ≤ m ^ (2 * c) * s ^ (2 * c) * s ^ 3 * k := by
      have : s ^ (2 * c + 3) = s ^ (2 * c) * s ^ 3 := by ring
      rw [this]
      have := Nat.mul_le_mul_right (s ^ (2 * c) * s ^ 3 * k) (hℓ.trans hm2)
      calc ℓ * (s ^ (2 * c) * s ^ 3 * k) ≤ m ^ (2 * c) * (s ^ (2 * c) * s ^ 3 * k) := this
        _ = m ^ (2 * c) * s ^ (2 * c) * s ^ 3 * k := by ring
    have e2 : m ^ (2 * c) * s ^ (2 * c) ≤ k ^ (2 * c) := by
      rw [← Nat.mul_pow]; exact Nat.pow_le_pow_left hms _
    have e3 : 8 * s ^ 3 ≤ k ^ 3 := by
      have : (2 * s) ^ 3 ≤ k ^ 3 := Nat.pow_le_pow_left hs2 3
      nlinarith
    calc 8 * (ℓ * (s ^ (2 * c + 3) * k)) ≤ 8 * (m ^ (2 * c) * s ^ (2 * c) * s ^ 3 * k) :=
          Nat.mul_le_mul_left 8 e1
      _ = (m ^ (2 * c) * s ^ (2 * c)) * (8 * s ^ 3) * k := by ring
      _ ≤ k ^ (2 * c) * k ^ 3 * k :=
          Nat.mul_le_mul_right k (Nat.mul_le_mul e2 e3)
      _ = k ^ (2 * c + 4) := by ring
  -- The rest: `ℓ (4k + 3) ≤ k^(2c+4)`.
  have hrest : ℓ * (4 * k + 3) ≤ k ^ (2 * c + 4) := by
    have h1 : (k + 1) ^ (c + 1) ≤ k ^ (2 * c + 2) := by
      rw [show 2 * c + 2 = 2 * (c + 1) by ring, pow_mul]
      exact Nat.pow_le_pow_left (by nlinarith) _
    have h2 : 4 * k ^ (2 * c + 2) ≤ k ^ (2 * c + 4) := by
      have e : k ^ (2 * c + 4) = k ^ (2 * c + 2) * k ^ 2 := by ring
      have : 4 ≤ k ^ 2 := by nlinarith
      rw [e]
      exact (Nat.mul_comm 4 _).le.trans (Nat.mul_le_mul_left _ this)
    have h3 : ℓ * (4 * k + 3) ≤ 4 * (k + 1) ^ (c + 1) := by
      have : ℓ * (4 * k + 3) ≤ (k + 1) ^ c * (4 * (k + 1)) :=
        Nat.mul_le_mul hℓk (by omega)
      calc ℓ * (4 * k + 3) ≤ (k + 1) ^ c * (4 * (k + 1)) := this
        _ = 4 * (k + 1) ^ (c + 1) := by ring
    omega
  -- Put together, after dividing by `Q`.
  have key : 1 + ℓ * (1 + 2 * (s ^ (2 * c + 3) * k + 2 * k + 1)) ≤
      2 * (k ^ (2 * c + 4) + 1) := by
    have e : ℓ * (1 + 2 * (s ^ (2 * c + 3) * k + 2 * k + 1)) =
        2 * (ℓ * (s ^ (2 * c + 3) * k)) + ℓ * (4 * k + 3) := by ring
    omega
  have := Nat.mul_le_mul_left Q key
  have e2 : Q * (1 + ℓ * (1 + 2 * (s ^ (2 * c + 3) * k + 2 * k + 1))) =
      Q + ℓ * (Q + 2 * Q * (s ^ (2 * c + 3) * k + 2 * k + 1)) := by ring
  have e3 : Q * (2 * (k ^ (2 * c + 4) + 1)) = 2 * Q * (k ^ (2 * c + 4) + 1) := by ring
  omega

end GI.Proved
