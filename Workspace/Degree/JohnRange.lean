module

public import Workspace.Proved.JohnModel

@[expose] public section

/-!
# Finding `Υ` and `Δ` when `3k ≤ m`

The Johnson identification of the general algorithm (`Proved/JohnModel.lean`) finds the two labels
`Υ` and `Δ` of [H, §2.8] by their counts in row `0`: `Δ` occurs most often, and `Υ` occurs
`k (m - k)` times. It needs `(k + 1)² < m + 2`. Here `m ≥ 8` and `3k ≤ m` only.

* `Υ` is still the only label that occurs `k (m - k)` times (`john_val_ups`). So the step of
  the general algorithm that finds `Υ` stays, and `john_ups_iffR` is `john_ups_iff` in this range.
* `Δ` need not occur most often. It is found by distance instead. In the graph of `Υ`, the
  distance from `x0` to `z` is `k - |ι x0 ∩ ι z|`. The ball of radius `d` around `x0` is the set
  of `z` with `k ≤ d + |ι x0 ∩ ι z|` (`john_ball_step`). So the points outside the ball of radius
  `k - 1` are the points whose `k`-set is disjoint from that of `x0`.

The counts are `johnVal m k j = binom(k, j) binom(m - k, j)` for the pairs that meet in `k - j`
elements.
-/

namespace GI.Degree

open Finset GI.Proved

variable {n m k : ℕ}

/-! ### The counts -/

/-- `binom(N, a) ≤ binom(N, b)` for `a ≤ b ≤ N / 2`. -/
theorem choose_le_choose_half {N a b : ℕ} (hab : a ≤ b) (hb : b ≤ N / 2) :
    N.choose a ≤ N.choose b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

/-- `k ≤ binom(k, j)` for `1 ≤ j < k`. -/
theorem self_le_choose {k j : ℕ} (h1 : 1 ≤ j) (h2 : j < k) : k ≤ k.choose j := by
  rcases le_or_gt j (k / 2) with h | h
  · simpa using choose_le_choose_half (N := k) h1 h
  · rw [← Nat.choose_symm h2.le]
    simpa using choose_le_choose_half (N := k) (a := 1) (b := k - j) (by omega) (by omega)

theorem choose_two_mul (M : ℕ) : M.choose 2 * 2 = M * (M - 1) := by
  have h := Nat.choose_succ_right_eq M 1
  rw [Nat.choose_one_right] at h
  simpa using h

theorem choose_three_mul (M : ℕ) : M.choose 3 * 3 = M.choose 2 * (M - 2) := by
  simpa using Nat.choose_succ_right_eq M 2

/-- **Only the pairs that meet in `k - 1` elements occur `k (m - k)` times**, when `m ≥ 8` and
`3k ≤ m`. For `m = 7, k = 2` the disjoint pairs also occur `10` times. -/
theorem john_val_ups (h8 : 8 ≤ m) (hk : 1 ≤ k) (h3 : 3 * k ≤ m) {j : ℕ} (hj : j ≤ k)
    (he : johnVal m k j = k * (m - k)) : j = 1 := by
  unfold johnVal at he
  obtain ⟨t, ht⟩ : ∃ t, m - k = t + 6 := ⟨m - k - 6, by omega⟩
  rw [ht] at he
  have hkt : 2 * k ≤ t + 6 := by omega
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · rcases Nat.lt_or_ge j 1 with hj1 | hj1
    · obtain rfl : j = 0 := by omega
      simp at he
      nlinarith
    · omega
  exfalso
  have hc2 := choose_two_mul (t + 6)
  have hM2 : (t + 6).choose 2 ≤ (t + 6).choose j := choose_le_choose_half hj2 (by omega)
  rw [show t + 6 - 1 = t + 5 by omega] at hc2
  rcases Nat.lt_or_ge j k with hjk | hjk
  · -- `binom(k, j) ≥ k` and `binom(t + 6, j) ≥ binom(t + 6, 2) > t + 6`.
    have hkj := self_le_choose (by omega : 1 ≤ j) hjk
    have h1 : t + 6 < (t + 6).choose 2 := by nlinarith
    have h2 : k * (t + 6) < k * (t + 6).choose j :=
      Nat.mul_lt_mul_of_pos_left (h1.trans_le hM2) (by omega)
    have h3' : k * (t + 6).choose j ≤ k.choose j * (t + 6).choose j :=
      Nat.mul_le_mul_right _ hkj
    omega
  · obtain rfl : j = k := le_antisymm hj hjk
    rw [Nat.choose_self, one_mul] at he
    rcases Nat.lt_or_ge j 3 with hj3 | hj3
    · -- `j = 2`: `binom(t + 6, 2) > 2 (t + 6)`.
      obtain rfl : j = 2 := by omega
      nlinarith
    · -- `j ≥ 3`: `binom(t + 6, j) ≥ binom(t + 6, 3) > j (t + 6)`.
      have hM3 : (t + 6).choose 3 ≤ (t + 6).choose j := choose_le_choose_half hj3 (by omega)
      have hc3 := choose_three_mul (t + 6)
      rw [show t + 6 - 2 = t + 4 by omega] at hc3
      have h6 : (t + 6).choose 3 * 6 = (t + 6) * (t + 5) * (t + 4) := by nlinarith
      have hjM : 2 * j * (t + 6) ≤ (t + 6) * (t + 6) := Nat.mul_le_mul_right _ hkt
      nlinarith

section
variable {ι : Fin n ≃ {A : Finset (Fin m) // A.card = k}} {lab : Fin (n * n) → ℕ}

/-- **The label `Υ`**, when `m ≥ 8` and `3k ≤ m`. As `john_ups_iff`, with `john_val_ups` in place
of the bound `(k + 1)² < m + 2`. -/
theorem john_ups_iffR (h : JohnHyp0 ι lab) (h8 : 8 ≤ m) (h3 : 3 * k ≤ m) (x y : Fin n) :
    lab (johnPair x y) = johnUps m k (johnRow n (johnLabL lab)) ↔ johnInter ι x y + 1 = k := by
  have hk := h.one_le
  set cnt := johnCnt (johnRow n (johnLabL lab)) with hcnt
  have hmem : k * (m - k) ∈ cnt := john_ups_mem h
  obtain ⟨hlt, hget⟩ := john_findIdx hmem
  obtain ⟨ht, hval⟩ := john_cnt_getElem h hlt
  have hd : johnUps m k (johnRow n (johnLabL lab)) = lab (johnPair h.x0 ⟨_, ht⟩) := by
    unfold johnUps
    rw [← hcnt]
    exact john_row_getD h ht
  rw [hd, h.lab_iff]
  have h1 : johnInter ι h.x0 ⟨_, ht⟩ + 1 = k := by
    have e : johnVal m k (k - johnInter ι h.x0 ⟨_, ht⟩) = k * (m - k) := hval.symm.trans hget
    have := john_val_ups h8 hk h3 (Nat.sub_le _ _) e
    have := john_inter_le ι h.x0 ⟨_, ht⟩
    omega
  omega

end

/-! ### Balls in the graph `Υ` -/

section
variable (ι : Fin n ≃ {A : Finset (Fin m) // A.card = k})

theorem john_inter_comm (x y : Fin n) : johnInter ι x y = johnInter ι y x := by
  unfold johnInter; rw [inter_comm]

/-- A neighbour in `Υ` meets `ι x0` in at least one element fewer. -/
theorem john_inter_step {x0 y z : Fin n} (hyz : johnInter ι y z + 1 = k) :
    johnInter ι x0 y ≤ johnInter ι x0 z + 1 := by
  unfold johnInter at *
  have hsub : (ι x0).1 ∩ (ι y).1 ⊆ ((ι x0).1 ∩ (ι z).1) ∪ ((ι y).1 \ (ι z).1) := by
    intro a ha
    rw [mem_inter] at ha
    by_cases hz : a ∈ (ι z).1
    · exact mem_union_left _ (mem_inter.mpr ⟨ha.1, hz⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨ha.2, hz⟩)
  have hd : #((ι y).1 \ (ι z).1) = 1 := by
    have := card_sdiff_add_card_inter (ι y).1 (ι z).1
    rw [(ι y).2] at this
    omega
  calc #((ι x0).1 ∩ (ι y).1) ≤ #(((ι x0).1 ∩ (ι z).1) ∪ ((ι y).1 \ (ι z).1)) := card_le_card hsub
    _ ≤ #((ι x0).1 ∩ (ι z).1) + #((ι y).1 \ (ι z).1) := card_union_le _ _
    _ = _ := by rw [hd]

/-- A point `z` with `|ι x0 ∩ ι z| < k` has a neighbour in `Υ` that meets `ι x0` in one element
more: swap an element of `ι z` outside `ι x0` for one of `ι x0` outside `ι z`. -/
theorem john_exists_up (x0 z : Fin n) (hz : johnInter ι x0 z < k) :
    ∃ y, johnInter ι z y + 1 = k ∧ johnInter ι x0 y = johnInter ι x0 z + 1 := by
  set A := (ι x0).1
  set Z := (ι z).1
  have hA : #A = k := (ι x0).2
  have hZ : #Z = k := (ι z).2
  unfold johnInter at hz
  change #(A ∩ Z) < k at hz
  obtain ⟨a, haA, haAZ⟩ := exists_mem_notMem_of_card_lt_card (s := A ∩ Z) (t := A) (by omega)
  have haZ : a ∉ Z := fun h => haAZ (mem_inter.mpr ⟨haA, h⟩)
  obtain ⟨b, hbZ, hbAZ⟩ := exists_mem_notMem_of_card_lt_card (s := A ∩ Z) (t := Z) (by omega)
  have hbA : b ∉ A := fun h => hbAZ (mem_inter.mpr ⟨h, hbZ⟩)
  have hab : a ≠ b := fun e => haZ (e ▸ hbZ)
  set Y := insert a (Z.erase b)
  have haE : a ∉ Z.erase b := fun h => haZ (mem_of_mem_erase h)
  have hY : #Y = k := by
    rw [card_insert_of_notMem haE, card_erase_of_mem hbZ]; omega
  refine ⟨ι.symm ⟨Y, hY⟩, ?_, ?_⟩
  · unfold johnInter
    rw [Equiv.apply_symm_apply]
    change #(Z ∩ Y) + 1 = k
    have : Z ∩ Y = Z.erase b := by
      ext c
      simp only [Y, mem_inter, mem_insert, mem_erase]
      constructor
      · rintro ⟨hc, rfl | ⟨hcb, -⟩⟩
        · exact absurd hc haZ
        · exact ⟨hcb, hc⟩
      · rintro ⟨hcb, hc⟩; exact ⟨hc, Or.inr ⟨hcb, hc⟩⟩
    rw [this, card_erase_of_mem hbZ]; omega
  · unfold johnInter
    rw [Equiv.apply_symm_apply]
    change #(A ∩ Y) = #(A ∩ Z) + 1
    have : A ∩ Y = insert a (A ∩ Z) := by
      ext c
      simp only [Y, mem_inter, mem_insert, mem_erase]
      constructor
      · rintro ⟨hc, rfl | ⟨hcb, hcZ⟩⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hc, hcZ⟩
      · rintro (rfl | ⟨hc, hcZ⟩)
        · exact ⟨haA, Or.inl rfl⟩
        · exact ⟨hc, Or.inr ⟨fun e => hbA (e ▸ hc), hcZ⟩⟩
    rw [this, card_insert_of_notMem (fun h => haZ (mem_inter.mp h).2)]

/-- **One step of the ball.** `z` is within distance `d + 1` of `x0` exactly when it is within
distance `d`, or it has a neighbour in `Υ` within distance `d`. -/
theorem john_ball_step (x0 z : Fin n) (d : ℕ) :
    k ≤ d + 1 + johnInter ι x0 z ↔
      k ≤ d + johnInter ι x0 z ∨ ∃ y, k ≤ d + johnInter ι x0 y ∧ johnInter ι z y + 1 = k := by
  constructor
  · intro h
    by_cases h0 : k ≤ d + johnInter ι x0 z
    · exact Or.inl h0
    · obtain ⟨y, hzy, hy⟩ := john_exists_up ι x0 z (by omega)
      exact Or.inr ⟨y, by omega, hzy⟩
  · rintro (h | ⟨y, hy, hzy⟩)
    · omega
    · have := john_inter_step ι (x0 := x0) (y := y) (z := z)
        (by rw [john_inter_comm]; exact hzy)
      omega

/-- The ball of radius `0` is `x0`. -/
theorem john_ball_zero (x0 z : Fin n) : k ≤ johnInter ι x0 z ↔ z = x0 := by
  have hle : johnInter ι x0 z ≤ k := john_inter_le ι x0 z
  constructor
  · intro h
    have hsub : (ι x0).1 ∩ (ι z).1 = (ι x0).1 :=
      eq_of_subset_of_card_le inter_subset_left (by rw [(ι x0).2]; unfold johnInter at h; omega)
    have h1 : (ι x0).1 ⊆ (ι z).1 := fun a ha => (mem_inter.mp (hsub ▸ ha : a ∈ _)).2
    have h2 : (ι x0).1 = (ι z).1 := eq_of_subset_of_card_le h1 (by rw [(ι x0).2, (ι z).2])
    exact (ι.injective (Subtype.ext h2)).symm
  · rintro rfl
    unfold johnInter; rw [inter_self, (ι z).2]

end

end GI.Degree
