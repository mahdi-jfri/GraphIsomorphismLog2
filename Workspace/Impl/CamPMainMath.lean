module

public import Workspace.Impl.CamSmallM
public import Workspace.Impl.CamXOrbits

@[expose] public section

/-!
# The sizes read by `camProg`

With a Maróti identification `e` and `1 ≤ k`, `2k < m`, `25 ≤ n`:
- `1 ≤ r`, `r ≤ n` and `m ≤ n`, since `n = binom(m, k)^r` and `binom(m, k) ≥ m ≥ 2`;
- a list of distinct points that is exactly the set of points agreeing with `x₀` outside
  coordinate `i` has length `binom(m, k)` (`cam_orbit_length`).
-/

namespace GI.Impl

open GI.Cited Equiv

variable {n m k r : ℕ}

theorem cam_m_le_choose (hk1 : 1 ≤ k) (hk : 2 * k < m) : m ≤ m.choose k := by
  induction k with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · have h1 := ih hj (by omega)
      have h2 : m.choose j ≤ m.choose (j + 1) := Nat.choose_le_succ_of_lt_half_left (by omega)
      omega

theorem cam_sizes (e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})) (hn : 25 ≤ n)
    (hk1 : 1 ≤ k) (hk : 2 * k < m) : 1 ≤ r ∧ r ≤ n ∧ m ≤ n := by
  have hne := cam_n_eq e
  have hc := cam_m_le_choose hk1 hk
  have hr : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · rw [h, pow_zero] at hne; omega
    · exact h
  refine ⟨hr, ?_, ?_⟩
  · have h1 : 2 ^ r ≤ (m.choose k) ^ r := Nat.pow_le_pow_left (by omega) r
    have h2 := Nat.lt_two_pow_self (n := r)
    omega
  · have : (m.choose k) ^ 1 ≤ (m.choose k) ^ r := Nat.pow_le_pow_right (by omega) hr
    rw [pow_one] at this
    omega

/-- **The size of an orbit of a factor.** -/
theorem cam_orbit_length (e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})) (i : Fin r)
    (x₀ : Fin n) (O : List (Fin n)) (hO : O.Nodup)
    (hmem : ∀ y, y ∈ O ↔ ∀ j, j ≠ i → e y j = e x₀ j) : O.length = m.choose k := by
  classical
  have h1 : Fin O.length ≃ {y // ∀ j, j ≠ i → e y j = e x₀ j} :=
    Equiv.ofBijective (fun w => ⟨O.get w, (hmem _).mp (List.get_mem O w)⟩)
      ⟨fun w w' h => hO.injective_get (congrArg Subtype.val h), fun y => by
        obtain ⟨w, hw⟩ := List.mem_iff_get.mp ((hmem y).mpr y.2)
        exact ⟨w, Subtype.ext hw⟩⟩
  have h2 : {y // ∀ j, j ≠ i → e y j = e x₀ j} ≃ {A : Finset (Fin m) // A.card = k} :=
    { toFun := fun y => e y.1 i
      invFun := fun A => ⟨e.symm (Function.update (e x₀) i A), fun j hj => by
        simp [Function.update_of_ne hj]⟩
      left_inv := fun y => by
        apply Subtype.ext
        apply e.injective
        funext j
        by_cases hj : j = i
        · subst hj; simp
        · simp [Function.update_of_ne hj, y.2 j hj]
      right_inv := fun A => by simp }
  have := Fintype.card_congr (h1.trans h2)
  rw [Fintype.card_fin, Fintype.card_finset_len, Fintype.card_fin] at this
  exact this

/-- Different indices give different factors: their orbits differ. -/
theorem cam_prod_single_inj (e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k}))
    (hm : 3 ≤ m) (hkm : k ≤ m) (h2 : 2 ≤ m.choose k) (x₀ : Fin n) {i j : Fin r}
    (h : camProd e {i} = camProd e {j}) : i = j := by
  by_contra hij
  have hc : 1 < Fintype.card {A : Finset (Fin m) // A.card = k} := by
    rw [Fintype.card_finset_len, Fintype.card_fin]; omega
  obtain ⟨B, hB⟩ := Fintype.exists_ne_of_one_lt_card hc (e x₀ i)
  set y := e.symm (Function.update (e x₀) i B) with hy
  have h1 : y ∈ MulAction.orbit (camProd e {i}) x₀ :=
    (camX_orbit_factor hm hkm i x₀ y).mpr fun j' hj' => by simp [hy, Function.update_of_ne hj']
  rw [h, camX_orbit_factor hm hkm j x₀ y] at h1
  have := h1 i hij
  simp [hy] at this
  exact hB this
