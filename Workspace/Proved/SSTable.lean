import Workspace.Cited.AlgoTerminal

/-!
# The Sims table and sifting

A *base* is a list `B` of points. A *table* is a flat list `T` of slots. Slot `i * n + j` belongs
to level `i` and point `j`; it is empty or holds a pair `(t, k)`, where `t` is a permutation that
fixes `B[0], …, B[i-1]` and maps `B[i]` to `j ≠ B[i]`, and `k` is the index of `t` in a
straight-line program (used only for constructive membership). The identity at the diagonal slot
`(i, B[i])` is implicit.

*Sifting* `g` goes through the levels. At level `i`, if `g` fixes `B[i]` it goes on; otherwise
it divides `g` by the entry at slot `(i, g B[i])` and goes on, or stops if that slot is empty.

This file defines the table, sifting (`ssSiftR`, and its Boolean form `ssThru`), and the sets
`ssS B T i` of permutations that fix `B[<i]` and sift through from level `i`. The main facts are
the decomposition `ssS_decomp` and the converse `ssS_mul_entry`.
-/

namespace GI.Proved

open Equiv GI.Cited

variable {n : ℕ}

/-- A slot of the table. -/
abbrev SsSlot (n : ℕ) := Option (Perm (Fin n) × ℕ)

/-- The slot of level `i` and point `j`. -/
def ssGet (T : List (SsSlot n)) (i : ℕ) (j : Fin n) : SsSlot n := (T[i * n + (j : ℕ)]?).join

/-- Sifting through the base points `bs`, starting at level `i`, with current permutation `g`
and the list `u` of program indices used so far. The result is the remainder, the indices used,
and `0` if `g` sifted through, or `i + 1` if it stopped at level `i`. -/
def ssSiftR (T : List (SsSlot n)) :
    List (Fin n) → ℕ → Perm (Fin n) → List ℕ → Perm (Fin n) × List ℕ × ℕ
  | [], _, g, u => (g, u, 0)
  | b :: bs, i, g, u =>
    if g b = b then ssSiftR T bs (i + 1) g u
    else match ssGet T i (g b) with
      | none => (g, u, i + 1)
      | some e => ssSiftR T bs (i + 1) (e.1⁻¹ * g) (u ++ [e.2])

/-- Whether `g` sifts through the base points `bs` from level `i`. -/
def ssThru (T : List (SsSlot n)) : List (Fin n) → ℕ → Perm (Fin n) → Bool
  | [], _, _ => true
  | b :: bs, i, g =>
    if g b = b then ssThru T bs (i + 1) g
    else match ssGet T i (g b) with
      | none => false
      | some e => ssThru T bs (i + 1) (e.1⁻¹ * g)

theorem ssSiftR_stop (T : List (SsSlot n)) (bs : List (Fin n)) (i : ℕ) (g : Perm (Fin n))
    (u : List ℕ) : (ssSiftR T bs i g u).2.2 = 0 ↔ ssThru T bs i g = true := by
  induction bs generalizing i g u with
  | nil => simp [ssSiftR, ssThru]
  | cons b bs ih =>
    simp only [ssSiftR, ssThru]
    split_ifs
    · exact ih _ _ _
    · cases ssGet T i (g b) with
      | none => simp
      | some e => exact ih _ _ _

/-- The slots of a well-formed table. -/
structure SsWF (B : List (Fin n)) (T : List (SsSlot n)) : Prop where
  slot : ∀ i (j : Fin n) e, ssGet T i j = some e → ∃ h : i < B.length,
    (∀ b ∈ B.take i, e.1 b = b) ∧ e.1 B[i] = j ∧ j ≠ B[i]

/-- The permutations that fix `B[0], …, B[i-1]` and sift through from level `i`. -/
noncomputable def ssS (B : List (Fin n)) (T : List (SsSlot n)) (i : ℕ) : Finset (Perm (Fin n)) :=
  by classical exact Finset.univ.filter fun g =>
    (∀ b ∈ B.take i, g b = b) ∧ ssThru T (B.drop i) i g = true

theorem mem_ssS {B : List (Fin n)} {T : List (SsSlot n)} {i : ℕ} {g : Perm (Fin n)} :
    g ∈ ssS B T i ↔ (∀ b ∈ B.take i, g b = b) ∧ ssThru T (B.drop i) i g = true := by
  classical
  unfold ssS
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

section Levels

variable {B : List (Fin n)} {T : List (SsSlot n)}

theorem take_succ_fix {i : ℕ} (hi : i < B.length) {g : Perm (Fin n)} :
    (∀ b ∈ B.take (i + 1), g b = b) ↔ (∀ b ∈ B.take i, g b = b) ∧ g B[i] = B[i] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi]
  simp only [Option.toList_some, List.mem_append, List.mem_singleton]
  constructor
  · intro h; exact ⟨fun b hb => h b (Or.inl hb), h _ (Or.inr rfl)⟩
  · rintro ⟨h1, h2⟩ b (hb | rfl)
    · exact h1 b hb
    · exact h2

theorem ssThru_drop {i : ℕ} (hi : i < B.length) (g : Perm (Fin n)) :
    ssThru T (B.drop i) i g = (if g B[i] = B[i] then ssThru T (B.drop (i + 1)) (i + 1) g
      else match ssGet T i (g B[i]) with
        | none => false
        | some e => ssThru T (B.drop (i + 1)) (i + 1) (e.1⁻¹ * g)) := by
  rw [List.drop_eq_getElem_cons hi]
  rfl

/-- The last level: only the identity, when the base contains every point. -/
theorem ssS_length (hB : ∀ x, x ∈ B) {g : Perm (Fin n)} (hg : g ∈ ssS B T B.length) : g = 1 := by
  rw [mem_ssS, List.take_length] at hg
  ext x
  simp [hg.1 x (hB x)]

theorem one_mem_ssS {i : ℕ} : (1 : Perm (Fin n)) ∈ ssS B T i := by
  rw [mem_ssS]
  refine ⟨fun b _ => rfl, ?_⟩
  generalize hd : B.drop i = bs
  clear hd
  induction bs generalizing i with
  | nil => rfl
  | cons b bs ih => simp only [ssThru, Perm.coe_one, id, if_true]; exact ih

/-- A permutation that also fixes `B[i]` is in `ssS` at level `i` iff it is at level `i + 1`. -/
theorem mem_ssS_succ_iff {i : ℕ} (hi : i < B.length) {g : Perm (Fin n)} :
    g ∈ ssS B T (i + 1) ↔ g ∈ ssS B T i ∧ g B[i] = B[i] := by
  rw [mem_ssS, mem_ssS, take_succ_fix hi, ssThru_drop hi]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, by rw [if_pos h2]; exact h3⟩, h2⟩
  · rintro ⟨⟨h1, h3⟩, h2⟩; rw [if_pos h2] at h3; exact ⟨⟨h1, h2⟩, h3⟩

theorem ssS_succ_subset {i : ℕ} (hi : i < B.length) {g : Perm (Fin n)}
    (hg : g ∈ ssS B T (i + 1)) : g ∈ ssS B T i := ((mem_ssS_succ_iff hi).mp hg).1

theorem ssS_anti {i i' : ℕ} (h : i ≤ i') (hi' : i' ≤ B.length) {g : Perm (Fin n)}
    (hg : g ∈ ssS B T i') : g ∈ ssS B T i := by
  induction i' with
  | zero => obtain rfl : i = 0 := by omega
            exact hg
  | succ k ih =>
    rcases Nat.lt_or_ge i (k + 1) with h' | h'
    · exact ih (by omega) (by omega) (ssS_succ_subset (by omega) hg)
    · obtain rfl : i = k + 1 := by omega
      exact hg

/-- **Decomposition.** An element of level `i` either is in level `i + 1`, or is an entry of
level `i` times an element of level `i + 1`. -/
theorem ssS_decomp (hwf : SsWF B T) {i : ℕ} (hi : i < B.length) {g : Perm (Fin n)}
    (hg : g ∈ ssS B T i) : g ∈ ssS B T (i + 1) ∨
      ∃ j e, ssGet T i j = some e ∧ e.1⁻¹ * g ∈ ssS B T (i + 1) := by
  rw [mem_ssS, ssThru_drop hi] at hg
  obtain ⟨h1, h2⟩ := hg
  by_cases hd : g B[i] = B[i]
  · rw [if_pos hd] at h2
    exact Or.inl (by rw [mem_ssS, take_succ_fix hi]; exact ⟨⟨h1, hd⟩, h2⟩)
  · rw [if_neg hd] at h2
    right
    cases he : ssGet T i (g B[i]) with
    | none => rw [he] at h2; simp at h2
    | some e =>
      rw [he] at h2
      refine ⟨_, e, he, ?_⟩
      obtain ⟨_, he1, he2, -⟩ := hwf.slot _ _ _ he
      rw [mem_ssS, take_succ_fix hi]
      refine ⟨⟨fun b hb => ?_, ?_⟩, h2⟩
      · rw [Perm.mul_apply, h1 b hb, Perm.inv_eq_iff_eq, he1 b hb]
      · rw [Perm.mul_apply, Perm.inv_eq_iff_eq, he2]

/-- The converse of `ssS_decomp`: an entry of level `i` times an element of level `i + 1` is in
level `i`. -/
theorem ssS_mul_entry (hwf : SsWF B T) {i : ℕ} {j : Fin n} {e : Perm (Fin n) × ℕ}
    (he : ssGet T i j = some e) {h : Perm (Fin n)} (hh : h ∈ ssS B T (i + 1)) :
    e.1 * h ∈ ssS B T i := by
  obtain ⟨hi, he1, he2, he3⟩ := hwf.slot _ _ _ he
  rw [mem_ssS_succ_iff hi, mem_ssS] at hh
  obtain ⟨⟨h1, h2⟩, h3⟩ := hh
  rw [mem_ssS, ssThru_drop hi]
  have hv : (e.1 * h) B[i] = j := by rw [Perm.mul_apply, h3, he2]
  refine ⟨fun b hb => by rw [Perm.mul_apply, h1 b hb, he1 b hb], ?_⟩
  rw [if_neg (by rw [hv]; exact he3), hv, he]
  simp only [inv_mul_cancel_left]
  rw [ssThru_drop hi, if_pos h3] at h2
  exact h2

/-- An entry of level `k` is in every level `i ≤ k`. -/
theorem entry_mem_ssS (hwf : SsWF B T) {k : ℕ} {j : Fin n} {e : Perm (Fin n) × ℕ}
    (he : ssGet T k j = some e) {i : ℕ} (hik : i ≤ k) : e.1 ∈ ssS B T i := by
  obtain ⟨hk, -⟩ := hwf.slot _ _ _ he
  have := ssS_mul_entry hwf he (one_mem_ssS (i := k + 1))
  rw [mul_one] at this
  exact ssS_anti hik hk.le this

/-- A permutation that sifts through from level 0 and fixes `B[<i]` is in level `i`. -/
theorem mem_ssS_of_thru {i : ℕ} (hi : i ≤ B.length) {g : Perm (Fin n)}
    (hg : ssThru T B 0 g = true) (hfix : ∀ b ∈ B.take i, g b = b) : g ∈ ssS B T i := by
  induction i with
  | zero => rw [mem_ssS]; exact ⟨by simp, by simpa using hg⟩
  | succ k ih =>
    have hk : k < B.length := by omega
    rw [take_succ_fix hk] at hfix
    exact (mem_ssS_succ_iff hk).mpr ⟨ih (by omega) hfix.1, hfix.2⟩

end Levels

end GI.Proved
