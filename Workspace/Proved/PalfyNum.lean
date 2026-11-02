import Mathlib

/-!
# Numerical facts and few generators

* `GI.Proved.palfy_hard_num`: if `q ≥ 2`, `m ≥ 1` and `2^k ≤ m^2`, then
  `24 q^6 (q (q m^2)^k)^3 ≤ (q^m)^69`. This is the arithmetic of the hard case.
  The key step is `m^{2k} ≤ 2^{16 m}` (`GI.Proved.palfy_pow_le`): with `2^j ≤ m < 2^{j+1}` we
  get `k ≤ 2j + 1`, so `m^{2k} ≤ 2^{2(2j+1)(j+1)}`, and `(2j+1)(j+1) ≤ 8 · 2^j ≤ 8m`.
* `GI.Proved.palfy_exists_gens`: for a subgroup `S` of a finite group `G` there is a finite set
  `T` with `⟨S, T⟩ = G` and `2^{|T|} ≤ |G : S|`. Each new generator at least doubles the
  subgroup.
-/

namespace GI.Proved

theorem palfy_aux_ind (j : ℕ) : (2 * j + 1) * (j + 1) ≤ 8 * 2 ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    have h1 : j + 1 ≤ 2 ^ j := Nat.lt_two_pow_self
    rw [pow_succ]
    nlinarith

theorem palfy_pow_le {k m : ℕ} (hm : 1 ≤ m) (hk : 2 ^ k ≤ m ^ 2) :
    m ^ (2 * k) ≤ 2 ^ (16 * m) ∧ k ≤ 2 * m := by
  set j := Nat.log 2 m
  have hj1 : 2 ^ j ≤ m := Nat.pow_log_le_self 2 (by omega)
  have hj2 : m < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  have hk' : k ≤ 2 * j + 1 := by
    by_contra h
    push Not at h
    have h3 : 2 ^ (2 * j + 2) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
    have h4 : m ^ 2 < 2 ^ (2 * j + 2) := by
      calc m ^ 2 < (2 ^ (j + 1)) ^ 2 := Nat.pow_lt_pow_left hj2 (by norm_num)
        _ = 2 ^ (2 * j + 2) := by rw [← pow_mul]; ring_nf
    omega
  have hjm : j < m := lt_of_lt_of_le (Nat.lt_two_pow_self) hj1
  refine ⟨?_, by omega⟩
  calc m ^ (2 * k) ≤ (2 ^ (j + 1)) ^ (2 * k) := Nat.pow_le_pow_left hj2.le _
    _ = 2 ^ ((j + 1) * (2 * k)) := by rw [← pow_mul]
    _ ≤ 2 ^ (16 * m) := by
      apply Nat.pow_le_pow_right (by norm_num)
      have := palfy_aux_ind j
      nlinarith

theorem palfy_hard_num {q m k : ℕ} (hq : 2 ≤ q) (hm : 1 ≤ m) (hk : 2 ^ k ≤ m ^ 2) :
    24 * q ^ 6 * (q * (q * m ^ 2) ^ k) ^ 3 ≤ (q ^ m) ^ 69 := by
  obtain ⟨h1, h2⟩ := palfy_pow_le hm hk
  have hq24 : 24 ≤ q ^ 5 := by
    calc 24 ≤ 2 ^ 5 := by norm_num
      _ ≤ q ^ 5 := Nat.pow_le_pow_left hq 5
  have h16 : 2 ^ (16 * m) ≤ q ^ (16 * m) := Nat.pow_le_pow_left hq _
  have hq1 : 1 ≤ q := by omega
  calc 24 * q ^ 6 * (q * (q * m ^ 2) ^ k) ^ 3
      = 24 * q ^ 9 * q ^ (3 * k) * (m ^ (2 * k)) ^ 3 := by ring
    _ ≤ q ^ 5 * q ^ 9 * q ^ (3 * (2 * m)) * (q ^ (16 * m)) ^ 3 :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hq24 le_rfl)
        (Nat.pow_le_pow_right hq1 (by omega))) (Nat.pow_le_pow_left (h1.trans h16) 3)
    _ = q ^ (14 + 54 * m) := by ring
    _ ≤ q ^ (69 * m) := Nat.pow_le_pow_right (by omega) (by omega)
    _ = (q ^ m) ^ 69 := by ring

/-- **Few generators.** -/
theorem palfy_exists_gens {G : Type*} [Group G] [Finite G] :
    ∀ (n : ℕ) (S : Subgroup G), S.index = n → ∃ T : Finset G,
      Subgroup.closure ((S : Set G) ∪ (T : Set G)) = ⊤ ∧ 2 ^ T.card ≤ S.index := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hS
    by_cases htop : S = ⊤
    · refine ⟨∅, ?_, ?_⟩
      · rw [Finset.coe_empty, Set.union_empty, Subgroup.closure_eq, htop]
      · rw [Finset.card_empty, pow_zero]; exact Nat.one_le_iff_ne_zero.mpr Subgroup.index_ne_zero_of_finite
    obtain ⟨g, -, hg⟩ : ∃ g ∈ (⊤ : Subgroup G), g ∉ S := by
      by_contra h
      push Not at h
      exact htop (eq_top_iff.mpr h)
    set S' := Subgroup.closure ((S : Set G) ∪ {g})
    have hSS' : S ≤ S' := fun x hx => Subgroup.subset_closure (Or.inl hx)
    have hgS' : g ∈ S' := Subgroup.subset_closure (Or.inr rfl)
    have hrel := Subgroup.relIndex_mul_index hSS'
    have hi0 : S.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hi0' : S'.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hr0 : S.relIndex S' ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hrel; exact hi0 hrel.symm
    have hr1 : S.relIndex S' ≠ 1 := by
      intro h1
      exact hg (Subgroup.relIndex_eq_one.mp h1 hgS')
    have hrel2 : 2 ≤ S.relIndex S' := by omega
    have hlt : S'.index < n := by
      rw [← hS, ← hrel]
      have : 1 ≤ S'.index := Nat.one_le_iff_ne_zero.mpr hi0'
      nlinarith
    obtain ⟨T', hT', hcard⟩ := ih _ hlt S' rfl
    refine ⟨insert g T', ?_, ?_⟩
    · rw [eq_top_iff, ← hT', Subgroup.closure_le]
      rintro x (hx | hx)
      · have : S' ≤ Subgroup.closure ((S : Set G) ∪ ((insert g T' : Finset G) : Set G)) := by
          apply Subgroup.closure_mono
          rintro y (hy | hy)
          · exact Or.inl hy
          · rw [Set.mem_singleton_iff] at hy
            exact Or.inr (by rw [hy, Finset.coe_insert]; exact Set.mem_insert g _)
        exact this hx
      · apply Subgroup.subset_closure
        right
        rw [Finset.coe_insert]
        exact Set.mem_insert_of_mem g hx
    · calc 2 ^ (insert g T').card ≤ 2 ^ (T'.card + 1) :=
            Nat.pow_le_pow_right (by norm_num) (Finset.card_insert_le g T')
        _ = 2 * 2 ^ T'.card := by ring
        _ ≤ S.relIndex S' * S'.index := Nat.mul_le_mul hrel2 hcard
        _ = S.index := hrel

end GI.Proved
