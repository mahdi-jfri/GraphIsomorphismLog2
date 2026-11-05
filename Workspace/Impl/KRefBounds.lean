module

public import Workspace.Impl.KRefCodes
public import Workspace.Impl.KRefStable

@[expose] public section

/-!
# The size parameter and weight bounds

All values of the program have weight at most `krefZ n k = 1000 * X ^ 4`, where
`X = n^k + n + k^k + k + 2`. This file proves the bounds that the program proofs use.
-/

namespace GI.Impl

open GI.Lang GI.Cited

/-- The basic size. -/
def krefX (n k : ℕ) : ℕ := n ^ k + n + k ^ k + k + 2

/-- The bound on all weights. -/
def krefZ (n k : ℕ) : ℕ := 1000 * krefX n k ^ 4

section

variable {n k : ℕ}

theorem krefX_two : 2 ≤ krefX n k := by unfold krefX; omega
theorem n_le_krefX : n ≤ krefX n k := by unfold krefX; omega
theorem k_le_krefX : k ≤ krefX n k := by unfold krefX; omega
theorem N_le_krefX : n ^ k ≤ krefX n k := by unfold krefX; omega
theorem kk_le_krefX : k ^ k ≤ krefX n k := by unfold krefX; omega

theorem krefX_pow_le {a b : ℕ} (h : a ≤ b) : krefX n k ^ a ≤ krefX n k ^ b :=
  Nat.pow_le_pow_right (by have := @krefX_two n k; omega) h

/-- `c * X ^ a ≤ Z` for `c ≤ 1000` and `a ≤ 4`. -/
theorem kref_le_Z {c a v : ℕ} (hc : c ≤ 1000) (ha : a ≤ 4) (h : v ≤ c * krefX n k ^ a) :
    v ≤ krefZ n k :=
  h.trans (Nat.mul_le_mul hc (krefX_pow_le ha))

theorem krefX_sq : krefX n k * krefX n k = krefX n k ^ 2 := (sq _).symm
theorem krefX_cube : krefX n k * krefX n k ^ 2 = krefX n k ^ 3 := by ring
theorem krefX_four : krefX n k * krefX n k ^ 3 = krefX n k ^ 4 := by ring

theorem X_le_Z : krefX n k ≤ krefZ n k :=
  kref_le_Z (c := 1) (a := 1) (by norm_num) (by norm_num) (by simp)

/-- The weight of a list whose entries weigh at most `C`. -/
theorem kref_wt_listMap {α : Type} {l : List α} {f : α → Val} {C : ℕ} (h : ∀ a ∈ l, (f a).wt ≤ C) :
    (Val.list (l.map f)).wt ≤ 2 * (l.length * C) + l.length + 4 := by
  have h1 := wt_list_le (l.map f)
  have h2 : ((l.map f).map Val.wt).sum ≤ l.length * C := by
    have := List.sum_le_card_nsmul ((l.map f).map Val.wt) C (by
      simp only [List.map_map, List.mem_map, Function.comp_apply, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      exact h)
    simpa using this
  simp only [List.length_map] at h1
  omega

/-- A list of numbers of length at most `X` with entries at most `X`. -/
theorem kref_wt_natList_X {xs : List ℕ} (hl : xs.length ≤ krefX n k)
    (h : ∀ a ∈ xs, a ≤ krefX n k) : (natList xs).wt ≤ 7 * krefX n k ^ 2 := by
  have h1 := wt_natList_le h
  have h2 : xs.length * (2 * krefX n k + 5) ≤ krefX n k * (2 * krefX n k + 5) :=
    Nat.mul_le_mul_right _ hl
  have := @krefX_two n k
  have h3 : krefX n k * (2 * krefX n k + 5) = 2 * (krefX n k * krefX n k) + 5 * krefX n k := by
    ring
  rw [krefX_sq] at h3
  have h4 : krefX n k ≤ krefX n k ^ 2 := by
    calc krefX n k = krefX n k ^ 1 := (pow_one _).symm
      _ ≤ krefX n k ^ 2 := krefX_pow_le (by norm_num)
  have h5 : 2 * krefX n k ≤ krefX n k ^ 2 := by
    rw [← krefX_sq]; exact Nat.mul_le_mul_right _ krefX_two
  omega

/-! ### The powers, digits, maps -/

theorem krefPowList_le (m e : ℕ) : ∀ p ∈ krefPowList m e, p ≤ max 1 (m ^ e) := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  rw [List.mem_range] at hi
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp
    · simp [Nat.zero_pow hi0]
  · exact le_max_of_le_right (Nat.pow_le_pow_right hm hi.le)

theorem kref_pw_le : ∀ p ∈ krefPowList n k, p ≤ krefX n k := fun p hp =>
  (krefPowList_le n k p hp).trans (max_le (by have := @krefX_two n k; omega) N_le_krefX)

theorem kref_pwk_le : ∀ p ∈ krefPowList k k, p ≤ krefX n k := fun p hp =>
  (krefPowList_le k k p hp).trans (max_le (by have := @krefX_two n k; omega) kk_le_krefX)

theorem length_krefPowList (m e : ℕ) : (krefPowList m e).length = e := by simp [krefPowList]

theorem kref_wt_pw : (natList (krefPowList n k)).wt ≤ 7 * krefX n k ^ 2 :=
  kref_wt_natList_X (by rw [length_krefPowList]; exact k_le_krefX) kref_pw_le

theorem kref_wt_pwk : (natList (krefPowList k k)).wt ≤ 7 * krefX n k ^ 2 :=
  kref_wt_natList_X (by rw [length_krefPowList]; exact k_le_krefX) kref_pwk_le

theorem kref_dig_le (x : Fin k → Fin n) : ∀ a ∈ krefDig x, a < n := by
  intro a ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  exact (x i).isLt

theorem length_krefDig (x : Fin k → Fin n) : (krefDig x).length = k := by simp [krefDig]

theorem kref_wt_dig (x : Fin k → Fin n) : (natList (krefDig x)).wt ≤ 7 * krefX n k ^ 2 :=
  kref_wt_natList_X (by rw [length_krefDig]; exact k_le_krefX)
    fun a ha => ((kref_dig_le x a ha).le.trans n_le_krefX)

theorem kref_wt_dig_snoc (x : Fin k → Fin n) {z : ℕ} (hz : z ≤ n) :
    (natList (krefDig x ++ [z])).wt ≤ 7 * krefX n k ^ 2 + 2 * krefX n k + 6 := by
  have h := wt_list_snoc_le ((krefDig x).map Val.nat) (.nat z)
  have := kref_wt_dig x
  have := wt_nat_le z
  have := @n_le_krefX n k
  have e : natList (krefDig x ++ [z]) = Val.list ((krefDig x).map Val.nat ++ [.nat z]) := by
    simp [natList]
  rw [e]
  have e2 : (Val.list ((krefDig x).map Val.nat)).wt = (natList (krefDig x)).wt := rfl
  omega

/-- The merge maps: `ρ_i(r) = k` if `r = i`, else `r`. -/
def krefRhos (k : ℕ) : List (List ℕ) :=
  (List.range k).map fun i => (List.range k).map fun r => if r = i then k else r

theorem kref_rho_le {ρ : List ℕ} (hρ : ρ ∈ krefRhos k) : ∀ a ∈ ρ, a ≤ k := by
  intro a ha
  unfold krefRhos at hρ
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hρ
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
  rw [List.mem_range] at hr
  split_ifs <;> omega

theorem length_krefRho {ρ : List ℕ} (hρ : ρ ∈ krefRhos k) : ρ.length = k := by
  unfold krefRhos at hρ
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hρ
  simp

theorem kref_wt_rho {ρ : List ℕ} (hρ : ρ ∈ krefRhos k) :
    (natList ρ).wt ≤ 7 * krefX n k ^ 2 :=
  kref_wt_natList_X (by rw [length_krefRho hρ]; exact k_le_krefX)
    fun a ha => (kref_rho_le hρ a ha).trans k_le_krefX

theorem kref_wt_rhos : (Val.list ((krefRhos k).map natList)).wt ≤ 30 * krefX n k ^ 3 := by
  have h := kref_wt_listMap (l := krefRhos k) (f := natList) (C := 7 * krefX n k ^ 2)
    fun ρ hρ => kref_wt_rho hρ
  have hl : (krefRhos k).length ≤ krefX n k := by simp [krefRhos, k_le_krefX]
  have h2 : (krefRhos k).length * (7 * krefX n k ^ 2) ≤ 7 * krefX n k ^ 3 := by
    calc (krefRhos k).length * (7 * krefX n k ^ 2) ≤ krefX n k * (7 * krefX n k ^ 2) :=
          Nat.mul_le_mul_right _ hl
      _ = 7 * krefX n k ^ 3 := by ring
  have h3 : krefX n k ≤ krefX n k ^ 3 := by
    calc krefX n k = krefX n k ^ 1 := (pow_one _).symm
      _ ≤ krefX n k ^ 3 := krefX_pow_le (by norm_num)
  have := @krefX_two n k
  omega

theorem kref_wt_dig_tau (τ : Fin k → Fin k) : (natList (krefDig τ)).wt ≤ 7 * krefX n k ^ 2 :=
  kref_wt_natList_X (by rw [length_krefDig]; exact k_le_krefX)
    fun a ha => ((kref_dig_le τ a ha).le.trans k_le_krefX)

theorem kref_wt_taus :
    (Val.list ((krefTups k k).map fun τ => natList (krefDig τ))).wt ≤ 30 * krefX n k ^ 3 := by
  have h := kref_wt_listMap (l := krefTups k k) (f := fun τ => natList (krefDig τ))
    (C := 7 * krefX n k ^ 2) fun τ _ => kref_wt_dig_tau τ
  have hl : (krefTups k k).length ≤ krefX n k := by rw [length_krefTups]; exact kk_le_krefX
  have h2 : (krefTups k k).length * (7 * krefX n k ^ 2) ≤ 7 * krefX n k ^ 3 := by
    calc (krefTups k k).length * (7 * krefX n k ^ 2) ≤ krefX n k * (7 * krefX n k ^ 2) :=
          Nat.mul_le_mul_right _ hl
      _ = 7 * krefX n k ^ 3 := by ring
  have h3 : krefX n k ≤ krefX n k ^ 3 := by
    calc krefX n k = krefX n k ^ 1 := (pow_one _).symm
      _ ≤ krefX n k ^ 3 := krefX_pow_le (by norm_num)
  have := @krefX_two n k
  omega

/-- A range of numbers at most `X^2`. -/
theorem kref_wt_range {m : ℕ} (hm : m ≤ 2 * krefX n k ^ 2) :
    (natList (List.range m)).wt ≤ 30 * krefX n k ^ 4 := by
  have h1 := wt_natList_le (xs := List.range m) (B := m) (fun a ha => (List.mem_range.mp ha).le)
  rw [List.length_range] at h1
  have h2 : m * (2 * m + 5) ≤ 2 * krefX n k ^ 2 * (2 * (2 * krefX n k ^ 2) + 5) :=
    Nat.mul_le_mul hm (by omega)
  have h3 : 2 * krefX n k ^ 2 * (2 * (2 * krefX n k ^ 2) + 5) =
      8 * (krefX n k ^ 2 * krefX n k ^ 2) + 10 * krefX n k ^ 2 := by ring
  have h4 : krefX n k ^ 2 * krefX n k ^ 2 = krefX n k ^ 4 := by ring
  have h5 : krefX n k ^ 2 ≤ krefX n k ^ 4 := krefX_pow_le (by norm_num)
  have h6 : 1 ≤ krefX n k ^ 4 := Nat.one_le_pow _ _ (by have := @krefX_two n k; omega)
  omega

theorem kref_X4 : 2 ≤ krefX n k ∧ krefX n k ≤ krefX n k ^ 2 ∧ krefX n k ^ 2 ≤ krefX n k ^ 3 ∧
    krefX n k ^ 3 ≤ krefX n k ^ 4 ∧ krefZ n k = 1000 * krefX n k ^ 4 :=
  ⟨krefX_two, krefX_pow_le (a := 1) (b := 2) (by norm_num) |>.trans' (by simp),
    krefX_pow_le (by norm_num), krefX_pow_le (by norm_num), rfl⟩

theorem kref_two_X_le_sq : 2 * krefX n k ≤ krefX n k ^ 2 := by
  rw [← krefX_sq]; exact Nat.mul_le_mul_right _ krefX_two

theorem kref_X_le_sq : krefX n k ≤ krefX n k ^ 2 := by
  calc krefX n k = krefX n k ^ 1 := (pow_one _).symm
    _ ≤ krefX n k ^ 2 := krefX_pow_le (by norm_num)

end

end GI.Impl
