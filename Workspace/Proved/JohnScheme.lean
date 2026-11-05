module

public import Workspace.Impl.CamNormalizer
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Data.Fintype.Powerset

@[expose] public section

/-!
# The Johnson scheme

We collect the facts about the `k`-subsets of `Fin m` that the identification of [H, §2.8]
uses ([H] = Helfgott, Bajpai, Dona, arXiv:1710.04574v1).

* `john_exists_alt_pair`: `Alt(m)` is transitive on the ordered pairs of `k`-sets with a given
  intersection size, when at least two points lie outside both sets. So the orbitals of
  `Alt(m)` on `k`-sets are the relations "the intersection has `i` points".
* `john_card_inter_eq`: for a `k`-set `A`, the number of `k`-sets `Z` with `|A ∩ Z| = i` is
  `C(k, i) * C(m - k, k - i)`.
* `john_val_lt`: these numbers, read as functions of `j = k - i`, increase strictly when
  `(k + 1)² < m + 2`. So the disjointness relation is the unique largest orbital, and the
  relation `|A ∩ B| = k - 1` is the unique orbital of valency `k (m - k)`.
* `john_C_iff`: the sets `C(x, y)` of [H, §2.8]. If `|A ∩ B| = k - 1` and `i` is the point of
  `A` outside `B`, then a `k`-set `R` meets every `k`-set that meets `A` and misses `B` exactly
  when `i ∈ R`.
-/

namespace GI.Proved

open Equiv Finset

/-! ### Transitivity on pairs -/

/-- The type of a point with respect to two sets: whether it lies in each. -/
def johnType {m : ℕ} (A B : Finset (Fin m)) (a : Fin m) : Bool × Bool := (decide (a ∈ A), decide (a ∈ B))

theorem john_card_type {m : ℕ} (A B : Finset (Fin m)) (c : Bool × Bool) :
    Fintype.card {a // johnType A B a = c} =
      #(univ.filter fun a => (decide (a ∈ A), decide (a ∈ B)) = c) := by
  rw [Fintype.card_subtype]
  rfl

/-- The four parts cut out by two sets, counted from the sizes of the sets and of the
intersection. -/
theorem john_card_parts {m : ℕ} (A B : Finset (Fin m)) :
    #(univ.filter fun a => (decide (a ∈ A), decide (a ∈ B)) = (true, true)) = #(A ∩ B) ∧
    #(univ.filter fun a => (decide (a ∈ A), decide (a ∈ B)) = (true, false)) = #A - #(A ∩ B) ∧
    #(univ.filter fun a => (decide (a ∈ A), decide (a ∈ B)) = (false, true)) = #B - #(A ∩ B) ∧
    #(univ.filter fun a => (decide (a ∈ A), decide (a ∈ B)) = (false, false)) =
      m - (#A + #B - #(A ∩ B)) := by
  have e1 : (univ.filter fun a => (decide (a ∈ A), decide (a ∈ B)) = (true, true)) = A ∩ B := by
    ext a; simp
  have e2 : (univ.filter fun a => (decide (a ∈ A), decide (a ∈ B)) = (true, false)) = A \ B := by
    ext a; simp
  have e3 : (univ.filter fun a => (decide (a ∈ A), decide (a ∈ B)) = (false, true)) = B \ A := by
    ext a; simp only [mem_filter, mem_univ, true_and, Prod.mk.injEq, decide_eq_false_iff_not,
      decide_eq_true_eq, mem_sdiff]; tauto
  have e4 : (univ.filter fun a => (decide (a ∈ A), decide (a ∈ B)) = (false, false)) =
      (A ∪ B)ᶜ := by
    ext a; simp
  rw [e1, e2, e3, e4, card_sdiff, card_sdiff, card_compl, Fintype.card_fin, card_union]
  refine ⟨rfl, ?_, ?_, rfl⟩
  · rw [inter_comm]
  · rfl

/-- Two pairs of sets with the same sizes and the same intersection size are carried to each
other by a permutation. -/
theorem john_exists_perm_pair {m : ℕ} {A B A' B' : Finset (Fin m)} (hA : #A = #A')
    (hB : #B = #B') (hAB : #(A ∩ B) = #(A' ∩ B')) :
    ∃ σ : Perm (Fin m), ∀ a, (σ a ∈ A' ↔ a ∈ A) ∧ (σ a ∈ B' ↔ a ∈ B) := by
  have hcard : ∀ c, Fintype.card {a // johnType A B a = c} =
      Fintype.card {a // johnType A' B' a = c} := by
    intro c
    rw [john_card_type, john_card_type]
    obtain ⟨p1, p2, p3, p4⟩ := john_card_parts A B
    obtain ⟨q1, q2, q3, q4⟩ := john_card_parts A' B'
    rcases c with ⟨_ | _, _ | _⟩
    · rw [p4, q4, hA, hB, hAB]
    · rw [p3, q3, hB, hAB]
    · rw [p2, q2, hA, hAB]
    · rw [p1, q1, hAB]
  let σ : Fin m ≃ Fin m :=
    Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hcard c))
  refine ⟨σ, fun a => ?_⟩
  have h := Equiv.ofFiberEquiv_map (fun c => Fintype.equivOfCardEq (hcard c)) a
  simp only [johnType, Prod.mk.injEq] at h
  exact ⟨decide_eq_decide.mp h.1, decide_eq_decide.mp h.2⟩

/-- **Transitivity of `Alt(m)` on pairs.** If at least two points lie outside `A' ∪ B'`, then two
pairs of sets with the same sizes and the same intersection size are carried to each other by
an even permutation. -/
theorem john_exists_alt_pair {m : ℕ} {A B A' B' : Finset (Fin m)} (hA : #A = #A')
    (hB : #B = #B') (hAB : #(A ∩ B) = #(A' ∩ B')) (hout : 2 ≤ #(A' ∪ B')ᶜ) :
    ∃ σ ∈ alternatingGroup (Fin m), A.map σ.toEmbedding = A' ∧ B.map σ.toEmbedding = B' := by
  obtain ⟨σ, hσ⟩ := john_exists_perm_pair hA hB hAB
  have hmap : ∀ τ : Perm (Fin m), (∀ a, (τ a ∈ A' ↔ a ∈ A) ∧ (τ a ∈ B' ↔ a ∈ B)) →
      A.map τ.toEmbedding = A' ∧ B.map τ.toEmbedding = B' := by
    intro τ hτ
    constructor
    · ext b
      rw [mem_map_equiv, ← (hτ (τ.symm b)).1, Equiv.apply_symm_apply]
    · ext b
      rw [mem_map_equiv, ← (hτ (τ.symm b)).2, Equiv.apply_symm_apply]
  rcases Int.units_eq_one_or (Perm.sign σ) with hs | hs
  · exact ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hs, hmap σ hσ⟩
  · obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hout
    rw [mem_compl, mem_union, not_or] at hu hv
    refine ⟨swap u v * σ, ?_, hmap _ fun a => ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup, map_mul, hs, Perm.sign_swap huv]; rfl
    · rw [Perm.mul_apply]
      have key : ∀ S : Finset (Fin m), u ∉ S → v ∉ S → ∀ b, (swap u v b ∈ S ↔ b ∈ S) := by
        intro S hu hv b
        rcases eq_or_ne b u with rfl | hbu
        · rw [swap_apply_left]; exact iff_of_false hv hu
        rcases eq_or_ne b v with rfl | hbv
        · rw [swap_apply_right]; exact iff_of_false hu hv
        rw [swap_apply_of_ne_of_ne hbu hbv]
      rw [key A' hu.1 hv.1, key B' hu.2 hv.2]
      exact hσ a

/-! ### Counting -/

/-- The `k`-sets that meet a set `A` in `i` points, split into the part inside `A` and the part
outside. -/
theorem john_card_inter_eq {m k : ℕ} (A : Finset (Fin m)) (i : ℕ) (hi : i ≤ k) :
    #((powersetCard k (univ : Finset (Fin m))).filter fun Z => #(A ∩ Z) = i) =
      Nat.choose #A i * Nat.choose (m - #A) (k - i) := by
  have hc : #Aᶜ = m - #A := by rw [card_compl, Fintype.card_fin]
  rw [← hc, ← card_powersetCard, ← card_powersetCard, ← card_product]
  have hsplit : ∀ Z : Finset (Fin m), A ∩ Z ∪ Aᶜ ∩ Z = Z := fun Z => by
    ext a; simp only [mem_union, mem_inter, mem_compl]; tauto
  have hcardZ : ∀ Z : Finset (Fin m), #(A ∩ Z) + #(Aᶜ ∩ Z) = #Z := fun Z => by
    rw [← card_union_of_disjoint (disjoint_of_subset_left inter_subset_left
      (disjoint_of_subset_right inter_subset_left disjoint_compl_right)), hsplit]
  have hback : ∀ S T : Finset (Fin m), S ⊆ A → T ⊆ Aᶜ → A ∩ (S ∪ T) = S ∧ Aᶜ ∩ (S ∪ T) = T :=
    fun S T hS hT => by
      constructor <;> ext a <;> simp only [mem_inter, mem_union, mem_compl] <;>
        constructor <;> intro h
      · rcases h.2 with h' | h'
        · exact h'
        · exact absurd h.1 (mem_compl.mp (hT h'))
      · exact ⟨hS h, Or.inl h⟩
      · rcases h.2 with h' | h'
        · exact absurd (hS h') h.1
        · exact h'
      · exact ⟨mem_compl.mp (hT h), Or.inr h⟩
  refine card_nbij' (fun Z => (A ∩ Z, Aᶜ ∩ Z)) (fun p => p.1 ∪ p.2) ?_ ?_ ?_ ?_
  · intro Z hZ
    simp only [mem_coe, mem_filter, mem_powersetCard, subset_univ, true_and] at hZ
    simp only [mem_coe, mem_product, mem_powersetCard]
    have := hcardZ Z
    exact ⟨⟨inter_subset_left, hZ.2⟩, inter_subset_left, by omega⟩
  · rintro ⟨S, T⟩ h
    simp only [mem_coe, mem_product, mem_powersetCard] at h
    obtain ⟨⟨hS, hSc⟩, hT, hTc⟩ := h
    obtain ⟨b1, b2⟩ := hback S T hS hT
    simp only [mem_coe, mem_filter, mem_powersetCard, subset_univ, true_and]
    have := hcardZ (S ∪ T)
    rw [b1, b2] at this
    refine ⟨by omega, by rw [b1, hSc]⟩
  · intro Z _
    exact hsplit Z
  · rintro ⟨S, T⟩ h
    simp only [mem_coe, mem_product, mem_powersetCard] at h
    obtain ⟨b1, b2⟩ := hback S T h.1.1 h.2.1
    simp only [b1, b2]

/-- The valency of the orbital "`j` points outside": `C(k, j) * C(m - k, j)`. -/
def johnVal (m k j : ℕ) : ℕ := Nat.choose k j * Nat.choose (m - k) j

theorem john_val_pos {m k j : ℕ} (hj : j ≤ k) (hkm : 2 * k ≤ m) : 0 < johnVal m k j :=
  Nat.mul_pos (Nat.choose_pos hj) (Nat.choose_pos (by omega))

/-- One step of the ratio: `v(j + 1) (j + 1)² = v(j) (k - j) (m - k - j)`. -/
theorem john_val_succ (m k j : ℕ) :
    johnVal m k (j + 1) * ((j + 1) * (j + 1)) = johnVal m k j * ((k - j) * (m - k - j)) := by
  unfold johnVal
  have h1 := Nat.choose_succ_right_eq k j
  have h2 := Nat.choose_succ_right_eq (m - k) j
  calc Nat.choose k (j + 1) * Nat.choose (m - k) (j + 1) * ((j + 1) * (j + 1))
      = (Nat.choose k (j + 1) * (j + 1)) * (Nat.choose (m - k) (j + 1) * (j + 1)) := by ring
    _ = (Nat.choose k j * (k - j)) * (Nat.choose (m - k) j * (m - k - j)) := by rw [h1, h2]
    _ = _ := by ring

/-- In the range `(k + 1)² < m + 2`, the step `j → j + 1` multiplies the valency by more
than one. -/
theorem john_val_lt_succ {m k j : ℕ} (hb : (k + 1) ^ 2 < m + 2) (hj : j < k) :
    johnVal m k j < johnVal m k (j + 1) := by
  have hkm : 2 * k ≤ m := by nlinarith
  have hpos := john_val_pos (m := m) hj.le hkm
  have hsq : (j + 1) * (j + 1) < (k - j) * (m - k - j) := by
    have a1 : (j + 1) * (j + 1) ≤ k * k := Nat.mul_le_mul hj hj
    have a2 : k * k < m - k - j := by
      have : k * k + 2 * k + 1 < m + 2 := by nlinarith
      omega
    have a3 : m - k - j ≤ (k - j) * (m - k - j) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have h := john_val_succ m k j
  by_contra hle
  push Not at hle
  have := Nat.mul_le_mul hle (le_refl ((j + 1) * (j + 1)))
  have := Nat.mul_lt_mul_of_pos_left hsq hpos
  omega

/-- **The valencies increase strictly.** -/
theorem john_val_lt {m k j j' : ℕ} (hb : (k + 1) ^ 2 < m + 2) (hjj : j < j') (hj' : j' ≤ k) :
    johnVal m k j < johnVal m k j' := by
  induction j', hjj using Nat.le_induction with
  | base => exact john_val_lt_succ hb (by omega)
  | succ j' hj ih => exact (ih (by omega)).trans (john_val_lt_succ hb (by omega))

/-- The number of `k`-sets that meet a `k`-set `A` in `k - j` points. -/
theorem john_card_val {m k : ℕ} (A : Finset (Fin m)) (hA : #A = k) (j : ℕ) (hj : j ≤ k) :
    #((powersetCard k (univ : Finset (Fin m))).filter fun Z => #(A ∩ Z) = k - j) =
      johnVal m k j := by
  rw [john_card_inter_eq A (k - j) (by omega), hA, Nat.choose_symm hj,
    show k - (k - j) = j by omega]
  rfl

theorem john_val_one (m k : ℕ) : johnVal m k 1 = k * (m - k) := by
  unfold johnVal
  rw [Nat.choose_one_right, Nat.choose_one_right]

theorem john_val_zero (m k : ℕ) : johnVal m k 0 = 1 := by
  simp [johnVal]

/-! ### The sets `C(x, y)` -/

/-- **The sets `C(x, y)` of [H, §2.8].** Let `A, B` be `k`-sets with `|A ∩ B| = k - 1`, and let
`i` be the point of `A` outside `B`. If `3k ≤ m`, a `k`-set `R` meets every `k`-set `Z` that meets
`A` and misses `B` exactly when `i ∈ R`. -/
theorem john_C_iff {m k : ℕ} (h3 : 3 * k ≤ m) {A B : Finset (Fin m)} (hA : #A = k) (hB : #B = k)
    {i : Fin m} (hiA : i ∈ A) (hiB : i ∉ B) (hAB : #(A ∩ B) + 1 = k) (R : Finset (Fin m))
    (hR : #R = k) :
    (∀ Z : Finset (Fin m), #Z = k → ¬ Disjoint A Z → Disjoint B Z → ¬ Disjoint Z R) ↔ i ∈ R := by
  -- `A` is `(A ∩ B) ∪ {i}`.
  have hAsub : A ⊆ insert i (A ∩ B) := by
    have h1 : #(insert i (A ∩ B)) = k := by
      rw [card_insert_of_notMem (fun h => hiB (mem_inter.mp h).2), hAB]
    have h2 : insert i (A ∩ B) ⊆ A := insert_subset hiA inter_subset_left
    exact (eq_of_subset_of_card_le h2 (by rw [h1, hA])).symm.subset
  constructor
  · intro hall
    by_contra hiR
    -- A `k`-set through `i` that misses `B` and `R`.
    set U := ((insert i (B ∪ R))ᶜ : Finset (Fin m))
    have hU : k - 1 ≤ #U := by
      have := card_insert_le i (B ∪ R)
      have := card_union_le B R
      rw [card_compl, Fintype.card_fin]
      omega
    obtain ⟨T, hTU, hT⟩ := exists_subset_card_eq hU
    have hiT : i ∉ T := fun h => by simpa [U] using hTU h
    have hZ : #(insert i T) = k := by rw [card_insert_of_notMem hiT, hT]; omega
    refine hall (insert i T) hZ ?_ ?_ ?_
    · exact not_disjoint_iff.mpr ⟨i, hiA, mem_insert_self _ _⟩
    · rw [disjoint_insert_right]
      refine ⟨hiB, disjoint_left.mpr fun b hb hbT => ?_⟩
      simpa [U, hb] using hTU hbT
    · rw [disjoint_insert_left]
      refine ⟨hiR, disjoint_left.mpr fun b hbT hb => ?_⟩
      simpa [U, hb] using hTU hbT
  · intro hiR Z _ hAZ hBZ
    obtain ⟨a, haA, haZ⟩ := not_disjoint_iff.mp hAZ
    have : a = i := by
      rcases mem_insert.mp (hAsub haA) with h | h
      · exact h
      · exact absurd haZ (disjoint_left.mp hBZ (mem_inter.mp h).2)
    subst this
    exact not_disjoint_iff.mpr ⟨a, haZ, hiR⟩

end GI.Proved
