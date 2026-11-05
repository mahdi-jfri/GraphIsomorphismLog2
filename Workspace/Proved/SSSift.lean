module

public import Workspace.Proved.SSTable

@[expose] public section

/-!
# Sifting as a loop over the levels, and what it returns

The program sifts with a loop over the levels `0, …, L - 1` that carries the current permutation,
the program indices used so far and a stop flag (`ssSiftStep`). `ssSift_eq` shows that this loop
computes `ssSiftR`. Then:

* `ssSiftR_used`: the remainder is `ssW es X * g`, where `X` lists the program indices used and
  `ssW es X` is the product of the inverses of the corresponding entries of the program, in the
  order used (`g ↦ t⁻¹ * g` at each level).
* `ssSiftR_stop_zero`, `ssSiftR_stop_succ`: if `g` fixes `B[<i]`, the remainder fixes the base
  points before the level where sifting stopped, and at that level its slot is empty.
* `ssThru_mono`: a larger table lets more permutations through.
-/

namespace GI.Proved

open Equiv GI.Cited

variable {n : ℕ}

/-- One step of the sifting loop, at level `i`. The third component is the stop flag. -/
def ssSiftStep (B : List (Fin n)) (T : List (SsSlot n)) (acc : Perm (Fin n) × List ℕ × ℕ)
    (i : ℕ) : Perm (Fin n) × List ℕ × ℕ :=
  if acc.2.2 = 0 then
    match B[i]? with
    | none => acc
    | some b =>
      if acc.1 b = b then acc
      else match ssGet T i (acc.1 b) with
        | none => (acc.1, acc.2.1, i + 1)
        | some e => (e.1⁻¹ * acc.1, acc.2.1 ++ [e.2], 0)
  else acc

/-- Sifting `g` through the whole base. -/
def ssSift (B : List (Fin n)) (T : List (SsSlot n)) (g : Perm (Fin n)) :
    Perm (Fin n) × List ℕ × ℕ :=
  (List.range B.length).foldl (ssSiftStep B T) (g, [], 0)

theorem foldl_ssSiftStep_stopped (B : List (Fin n)) (T : List (SsSlot n)) (l : List ℕ)
    (acc : Perm (Fin n) × List ℕ × ℕ) (h : acc.2.2 ≠ 0) : l.foldl (ssSiftStep B T) acc = acc := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.foldl_cons, ssSiftStep, if_neg h]; exact ih

theorem foldl_ssSiftStep_range' (B : List (Fin n)) (T : List (SsSlot n)) :
    ∀ d i g u, B.length - i = d →
      (List.range' i d).foldl (ssSiftStep B T) (g, u, 0) = ssSiftR T (B.drop i) i g u := by
  intro d
  induction d with
  | zero =>
    intro i g u hd
    rw [List.drop_of_length_le (by omega)]
    rfl
  | succ d ih =>
    intro i g u hd
    have hi : i < B.length := by omega
    rw [List.range'_succ, List.foldl_cons, List.drop_eq_getElem_cons hi]
    simp only [ssSiftStep, if_true, List.getElem?_eq_getElem hi, ssSiftR]
    split_ifs with h1
    · exact ih _ _ _ (by omega)
    · cases ssGet T i (g B[i]) with
      | none => exact foldl_ssSiftStep_stopped _ _ _ _ (by simp)
      | some e => exact ih _ _ _ (by omega)

theorem ssSift_eq (B : List (Fin n)) (T : List (SsSlot n)) (g : Perm (Fin n)) :
    ssSift B T g = ssSiftR T B 0 g [] := by
  unfold ssSift
  rw [List.range_eq_range', foldl_ssSiftStep_range' B T _ 0 g [] (by omega), List.drop_zero]

/-! ### The remainder -/

/-- The product of the inverses of the program entries `es[k]` for `k ∈ X`, the first one
rightmost. -/
def ssW (es : List (Perm (Fin n))) : List ℕ → Perm (Fin n)
  | [] => 1
  | k :: X => ssW es X * (es[k]?.getD 1)⁻¹

theorem ssW_append (es : List (Perm (Fin n))) (X Y : List ℕ) :
    ssW es (X ++ Y) = ssW es Y * ssW es X := by
  induction X with
  | nil => simp [ssW]
  | cons k X ih => simp only [List.cons_append, ssW, ih, mul_assoc]

/-- The table is consistent with the program entries `es`: entry `(t, k)` has `es[k] = t`. -/
def SsCons (T : List (SsSlot n)) (es : List (Perm (Fin n))) : Prop :=
  ∀ i j e, ssGet T i j = some e → es[e.2]? = some e.1

theorem ssSiftR_used {T : List (SsSlot n)} {es : List (Perm (Fin n))} (hc : SsCons T es)
    (bs : List (Fin n)) (i : ℕ) (g : Perm (Fin n)) (u : List ℕ) :
    ∃ X, (ssSiftR T bs i g u).2.1 = u ++ X ∧ (ssSiftR T bs i g u).1 = ssW es X * g ∧
      X.length ≤ bs.length ∧ ∀ k ∈ X, k < es.length := by
  induction bs generalizing i g u with
  | nil => exact ⟨[], by simp [ssSiftR], by simp [ssSiftR, ssW], by simp, by simp⟩
  | cons b bs ih =>
    simp only [ssSiftR]
    split_ifs with h1
    · obtain ⟨X, h2, h3, h4, h5⟩ := ih (i + 1) g u
      exact ⟨X, h2, h3, by simp; omega, h5⟩
    · cases he : ssGet T i (g b) with
      | none => exact ⟨[], by simp, by simp [ssW], by simp, by simp⟩
      | some e =>
        obtain ⟨X, h2, h3, h4, h5⟩ := ih (i + 1) (e.1⁻¹ * g) (u ++ [e.2])
        have hk := hc _ _ _ he
        refine ⟨e.2 :: X, by simp [h2], ?_, by simp; omega, ?_⟩
        · rw [h3, ssW, hk, Option.getD_some, mul_assoc]
        · intro k hk'
          rcases List.mem_cons.mp hk' with rfl | hk'
          · exact (List.getElem?_eq_some_iff.mp hk).1
          · exact h5 k hk'

/-! ### Where sifting stops -/

section Stop

variable {B : List (Fin n)} {T : List (SsSlot n)}

theorem ssSiftR_stop_zero (hwf : SsWF B T) :
    ∀ d i g u, B.length - i = d → (∀ b ∈ B.take i, g b = b) →
      (ssSiftR T (B.drop i) i g u).2.2 = 0 → ∀ b ∈ B, (ssSiftR T (B.drop i) i g u).1 b = b := by
  intro d
  induction d with
  | zero =>
    intro i g u hd hfix _
    rw [List.drop_of_length_le (by omega)]
    simpa [ssSiftR, List.take_of_length_le (show B.length ≤ i by omega)] using hfix
  | succ d ih =>
    intro i g u hd hfix hstop
    have hi : i < B.length := by omega
    rw [List.drop_eq_getElem_cons hi] at hstop ⊢
    simp only [ssSiftR] at hstop ⊢
    split_ifs at hstop ⊢ with h1
    · exact ih (i + 1) g u (by omega) ((take_succ_fix hi).mpr ⟨hfix, h1⟩) hstop
    · cases he : ssGet T i (g B[i]) with
      | none => simp [he] at hstop
      | some e =>
        simp only [he] at hstop ⊢
        obtain ⟨_, he1, he2, -⟩ := hwf.slot _ _ _ he
        refine ih (i + 1) _ _ (by omega) ((take_succ_fix hi).mpr ⟨fun b hb => ?_, ?_⟩) hstop
        · rw [Perm.mul_apply, hfix b hb, Perm.inv_eq_iff_eq, he1 b hb]
        · rw [Perm.mul_apply, Perm.inv_eq_iff_eq, he2]

theorem ssSiftR_stop_succ (hwf : SsWF B T) :
    ∀ d i g u, B.length - i = d → (∀ b ∈ B.take i, g b = b) → ∀ k,
      (ssSiftR T (B.drop i) i g u).2.2 = k + 1 → ∃ hk : k < B.length,
        (∀ b ∈ B.take k, (ssSiftR T (B.drop i) i g u).1 b = b) ∧
        (ssSiftR T (B.drop i) i g u).1 B[k] ≠ B[k] ∧
        ssGet T k ((ssSiftR T (B.drop i) i g u).1 B[k]) = none := by
  intro d
  induction d with
  | zero =>
    intro i g u hd _ k hstop
    rw [List.drop_of_length_le (by omega)] at hstop
    simp [ssSiftR] at hstop
  | succ d ih =>
    intro i g u hd hfix k hstop
    have hi : i < B.length := by omega
    rw [List.drop_eq_getElem_cons hi] at hstop ⊢
    simp only [ssSiftR] at hstop ⊢
    split_ifs at hstop ⊢ with h1
    · exact ih (i + 1) g u (by omega) ((take_succ_fix hi).mpr ⟨hfix, h1⟩) k hstop
    · cases he : ssGet T i (g B[i]) with
      | none =>
        simp only [he] at hstop ⊢
        simp only [Nat.add_right_cancel_iff] at hstop
        subst hstop
        exact ⟨hi, hfix, h1, he⟩
      | some e =>
        simp only [he] at hstop ⊢
        obtain ⟨_, he1, he2, -⟩ := hwf.slot _ _ _ he
        refine ih (i + 1) _ _ (by omega) ((take_succ_fix hi).mpr ⟨fun b hb => ?_, ?_⟩) k hstop
        · rw [Perm.mul_apply, hfix b hb, Perm.inv_eq_iff_eq, he1 b hb]
        · rw [Perm.mul_apply, Perm.inv_eq_iff_eq, he2]

end Stop

/-! ### Larger tables -/

/-- Every filled slot of `T` is filled in the same way in `T'`. -/
def SsLe (T T' : List (SsSlot n)) : Prop := ∀ i j e, ssGet T i j = some e → ssGet T' i j = some e

theorem SsLe.refl (T : List (SsSlot n)) : SsLe T T := fun _ _ _ h => h

theorem SsLe.trans {T T' T'' : List (SsSlot n)} (h : SsLe T T') (h' : SsLe T' T'') : SsLe T T'' :=
  fun i j e he => h' i j e (h i j e he)

theorem ssThru_mono {T T' : List (SsSlot n)} (hle : SsLe T T') (bs : List (Fin n)) (i : ℕ)
    (g : Perm (Fin n)) (h : ssThru T bs i g = true) : ssThru T' bs i g = true := by
  induction bs generalizing i g with
  | nil => rfl
  | cons b bs ih =>
    simp only [ssThru] at h ⊢
    split_ifs at h ⊢ with h1
    · exact ih _ _ h
    · cases he : ssGet T i (g b) with
      | none => rw [he] at h; simp at h
      | some e => rw [he] at h; rw [hle _ _ _ he]; exact ih _ _ h

theorem ssThru_one (T : List (SsSlot n)) (bs : List (Fin n)) (i : ℕ) :
    ssThru T bs i 1 = true := by
  induction bs generalizing i with
  | nil => rfl
  | cons b bs ih => simp only [ssThru, Perm.coe_one, id, if_true]; exact ih _

/-- After the remainder is put in the empty slot where sifting stopped, the permutation sifts
through. -/
theorem ssThru_of_stop {B : List (Fin n)} {T T' : List (SsSlot n)} (hle : SsLe T T') :
    ∀ d i g u, B.length - i = d → ∀ k (hk : k < B.length),
      (ssSiftR T (B.drop i) i g u).2.2 = k + 1 →
      (∃ c, ssGet T' k ((ssSiftR T (B.drop i) i g u).1 B[k]) =
        some ((ssSiftR T (B.drop i) i g u).1, c)) →
      ssThru T' (B.drop i) i g = true := by
  intro d
  induction d with
  | zero =>
    intro i g u hd k hk hstop _
    rw [List.drop_of_length_le (by omega)] at hstop
    simp [ssSiftR] at hstop
  | succ d ih =>
    intro i g u hd k hk hstop hnew
    have hi : i < B.length := by omega
    rw [List.drop_eq_getElem_cons hi] at hstop hnew ⊢
    simp only [ssSiftR] at hstop hnew
    simp only [ssThru]
    split_ifs at hstop hnew ⊢ with h1
    · exact ih (i + 1) g u (by omega) k hk hstop hnew
    · cases he : ssGet T i (g B[i]) with
      | none =>
        simp only [he] at hstop hnew
        simp only [Nat.add_right_cancel_iff] at hstop
        subst hstop
        obtain ⟨c, hc⟩ := hnew
        rw [hc]
        simp only [inv_mul_cancel]
        exact ssThru_one _ _ _
      | some e =>
        simp only [he] at hstop hnew
        rw [hle _ _ _ he]
        exact ih (i + 1) _ _ (by omega) k hk hstop hnew

end GI.Proved
