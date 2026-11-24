/-
Bit encodings for graph inputs and isomorphism outputs.

We prove three groups of facts:
* `adjBits` and `inputBits` have lengths `n * n` and `2 * n * n`, and setting cell 0 of
  `rawInput (inputBits G H)` to `n` produces an `InputLayout G H`.
* `natBits`, `mapBits` and `answerBits` satisfy simple recurrences and length bounds in terms of
  `GI.Machine.len`.
* `BitsAt mem a bs` states that cells `a, …, a + bs.length - 1` hold the bits `bs` (as 0 or
  nonzero), and determines `rawOutput mem B`.

We also show that for `n ≤ 1`, the empty list generates `autGroup G`.
-/
module

public import Workspace.Turing.Interface
public import Workspace.Machine.Layout
public import Mathlib.Data.Nat.Digits.Lemmas

@[expose] public section

namespace GI.Turing

open GI.Machine GI.Statement

/-! ### Indexing fixed-width `flatMap` lists -/

private theorem length_flatMap_const {α β : Type*} (l : List α) (f : α → List β) (m : ℕ)
    (hf : ∀ a ∈ l, (f a).length = m) : (l.flatMap f).length = l.length * m := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    rw [hf a (by simp), ih (fun x hx => hf x (by simp [hx])), Nat.add_comm]

private theorem getElem?_flatMap_const {α β : Type*} (l : List α) (f : α → List β) (m : ℕ)
    (hf : ∀ a ∈ l, (f a).length = m) {i j : ℕ} (hi : i < l.length) (hj : j < m) :
    (l.flatMap f)[m * i + j]? = (f l[i])[j]? := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a as ih =>
    have hfa : (f a).length = m := hf a (by simp)
    simp only [List.flatMap_cons]
    cases i with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
      rw [List.getElem?_append_left (by omega)]
    | succ i' =>
      have hidx : m * (i' + 1) + j = (f a).length + (m * i' + j) := by rw [hfa]; ring
      rw [hidx, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
      exact ih (fun x hx => hf x (by simp [hx])) (by simp at hi; omega)

/-! ### `adjBits`, `inputBits` and `InputLayout` -/

/-- `adjBits G` has `n * n` bits. -/
theorem adjBits_length {n : ℕ} (G : SimpleGraph (Fin n)) : (adjBits G).length = n * n := by
  classical
  unfold adjBits
  rw [length_flatMap_const _ _ n (fun _ _ => by simp), List.length_finRange]

/-- `inputBits G H` has `2 * n * n` bits. -/
theorem inputBits_length {n : ℕ} (G H : SimpleGraph (Fin n)) :
    (inputBits G H).length = 2 * n * n := by
  unfold inputBits
  rw [List.length_append, adjBits_length, adjBits_length]
  ring

open Classical in
/-- Bit `n * i + j` of `adjBits G` is `decide (G.Adj i j)`. -/
theorem adjBits_getElem? {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n) :
    (adjBits G)[n * (i : ℕ) + j]? = some (decide (G.Adj i j)) := by
  unfold adjBits
  rw [getElem?_flatMap_const _ _ n (fun _ _ => by simp)
    (by simp [i.isLt]) j.isLt]
  simp [List.getElem_finRange]

open Classical in
/-- Updating cell 0 of `rawInput (inputBits G H)` to `n` gives an `InputLayout G H`. -/
theorem inputLayout_update_rawInput {n : ℕ} (G H : SimpleGraph (Fin n)) :
    InputLayout G H (Function.update (rawInput (inputBits G H)) 0 n) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp
  · intro i j
    have hlt := cell_lt i.isLt j.isLt
    have hne : 1 + n * (i : ℕ) + j ≠ 0 := by omega
    rw [Function.update_of_ne hne]
    simp only [rawInput, hne, ↓reduceIte, show 1 + n * (i : ℕ) + j - 1 = n * i + j by omega]
    have hget : (inputBits G H)[n * (i : ℕ) + j]? = some (decide (G.Adj i j)) := by
      unfold inputBits
      rw [List.getElem?_append_left (by rw [adjBits_length]; exact hlt)]
      exact adjBits_getElem? G i j
    rw [List.getD_eq_getElem?_getD, hget]
    by_cases hadj : G.Adj i j <;> simp [hadj]
  · intro i j
    have hlt := cell_lt i.isLt j.isLt
    have hne : 1 + n * n + n * (i : ℕ) + j ≠ 0 := by omega
    rw [Function.update_of_ne hne]
    simp only [rawInput, hne, ↓reduceIte,
      show 1 + n * n + n * (i : ℕ) + j - 1 = n * n + (n * i + j) by omega]
    have hget : (inputBits G H)[n * n + (n * (i : ℕ) + j)]? = some (decide (H.Adj i j)) := by
      unfold inputBits
      rw [List.getElem?_append_right (by rw [adjBits_length]; omega), adjBits_length,
        Nat.add_sub_cancel_left]
      exact adjBits_getElem? H i j
    rw [List.getD_eq_getElem?_getD, hget]
    by_cases hadj : H.Adj i j <;> simp [hadj]
  · intro a ha
    have hne : a ≠ 0 := by omega
    rw [Function.update_of_ne hne]
    simp only [rawInput, hne, ↓reduceIte]
    have hnone : (inputBits G H)[a - 1]? = none :=
      List.getElem?_eq_none (by rw [inputBits_length]; omega)
    rw [List.getD_eq_getElem?_getD, hnone]
    simp

/-! ### `natBits`, `mapBits` and `answerBits` -/

/-- The digit pairs of `natBits k`, without the terminating `false`. -/
def natDigitsBits (k : ℕ) : List Bool :=
  (Nat.digits 2 k).flatMap (fun d => [true, decide (d = 1)])

theorem natBits_eq (k : ℕ) : natBits k = natDigitsBits k ++ [false] := rfl

@[simp] theorem natDigitsBits_zero : natDigitsBits 0 = [] := by
  simp [natDigitsBits]

/-- Recurrence for `natDigitsBits k` when `k > 0`. -/
theorem natDigitsBits_pos {k : ℕ} (hk : 0 < k) :
    natDigitsBits k = [true, decide (k % 2 ≠ 0)] ++ natDigitsBits (k / 2) := by
  unfold natDigitsBits
  rw [Nat.digits_def' (by norm_num) hk, List.flatMap_cons]
  have hmod : decide (k % 2 = 1) = decide (k % 2 ≠ 0) := by
    have : k % 2 < 2 := Nat.mod_lt k (by norm_num)
    by_cases h : k % 2 = 1
    · simp [h]
    · have h0 : k % 2 = 0 := by omega
      simp [h0]
  rw [hmod]

/-- The number of binary digits of `k` equals `len k`. -/
theorem digits_two_length (k : ℕ) : (Nat.digits 2 k).length = len k := by
  by_cases hk : k = 0
  · subst hk; simp [len_zero]
  · rw [Nat.length_digits 2 k (by norm_num) hk, len_eq_log_add_one hk]

/-- `natDigitsBits k` has length `2 * len k`. -/
theorem natDigitsBits_length (k : ℕ) : (natDigitsBits k).length = 2 * len k := by
  unfold natDigitsBits
  rw [length_flatMap_const _ _ 2 (fun _ _ => rfl), digits_two_length, Nat.mul_comm]

/-- `natBits k` has length `2 * len k + 1`. -/
theorem natBits_length (k : ℕ) : (natBits k).length = 2 * len k + 1 := by
  rw [natBits_eq, List.length_append, natDigitsBits_length]; rfl

/-- Dividing a positive number by 2 lowers `len` by 1. -/
theorem len_div_two_add_one_of_pos {k : ℕ} (hk : 0 < k) : len (k / 2) + 1 = len k := by
  have h := congrArg List.length (Nat.digits_def' (b := 2) (by norm_num) hk)
  simp only [List.length_cons, digits_two_length] at h
  exact h.symm

private theorem length_flatMap_le {α β : Type*} (l : List α) (f : α → List β) (m : ℕ)
    (hf : ∀ a ∈ l, (f a).length ≤ m) : (l.flatMap f).length ≤ l.length * m := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have ha := hf a (by simp)
    have has := ih (fun x hx => hf x (by simp [hx]))
    omega

/-- Length bound for `mapBits f`. -/
theorem mapBits_length_le {n : ℕ} (f : Fin n → Fin n) :
    (mapBits f).length ≤ n * (2 * len n + 1) := by
  unfold mapBits
  have h := length_flatMap_le (List.finRange n) (fun i => natBits (f i)) (2 * len n + 1) (by
    intro i _
    rw [natBits_length]
    have hle : len (f i : ℕ) ≤ len n := len_mono (f i).isLt.le
    omega)
  simpa [List.length_finRange] using h

/-- Length bound for the generator portion of `answerBits`. -/
theorem gensBits_length_le {n : ℕ} (gens : List (Equiv.Perm (Fin n))) :
    (gens.flatMap fun g => true :: mapBits (fun i => g i)).length ≤
      gens.length * (1 + n * (2 * len n + 1)) := by
  refine length_flatMap_le gens (fun g => true :: mapBits (fun i => g i))
    (1 + n * (2 * len n + 1)) fun g _ => ?_
  simp only [List.length_cons]
  have hg := mapBits_length_le (fun i => g i)
  omega

/-- Length bound for `answerBits (some (σ, gens))`. -/
theorem answerBits_some_length_le {n : ℕ} {G H : SimpleGraph (Fin n)}
    (σ : G ≃g H) (gens : List (Equiv.Perm (Fin n))) :
    (answerBits (some (σ, gens))).length ≤
      2 + (gens.length + 1) * (1 + n * (2 * len n + 1)) := by
  simp only [answerBits, List.length_append, List.length_cons, List.length_nil]
  have hσ := mapBits_length_le (fun i => σ i)
  have hg := gensBits_length_le gens
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-! ### `BitsAt` and `rawOutput` -/

/-- Cells `a, …, a + bs.length - 1` hold the bits `bs`, with nonzero standing for `true`. -/
def BitsAt (mem : ℕ → ℕ) (a : ℕ) (bs : List Bool) : Prop :=
  ∀ i (hi : i < bs.length), decide (mem (a + i) ≠ 0) = bs[i]

namespace BitsAt

theorem nil (mem : ℕ → ℕ) (a : ℕ) : BitsAt mem a [] := fun _ hi => absurd hi (Nat.not_lt_zero _)

theorem singleton {mem : ℕ → ℕ} {a : ℕ} {b : Bool} (h : decide (mem a ≠ 0) = b) :
    BitsAt mem a [b] := by
  intro i hi
  have hi0 : i = 0 := by simp at hi; omega
  subst hi0; simpa using h

theorem append {mem : ℕ → ℕ} {a : ℕ} {bs₁ bs₂ : List Bool}
    (h₁ : BitsAt mem a bs₁) (h₂ : BitsAt mem (a + bs₁.length) bs₂) :
    BitsAt mem a (bs₁ ++ bs₂) := by
  intro i hi
  by_cases hlt : i < bs₁.length
  · rw [List.getElem_append_left hlt]
    exact h₁ i hlt
  · rw [List.getElem_append_right (by omega)]
    have h2 := h₂ (i - bs₁.length) (by simp at hi; omega)
    rwa [show a + bs₁.length + (i - bs₁.length) = a + i by omega] at h2

theorem cons {mem : ℕ → ℕ} {a : ℕ} {b : Bool} {bs : List Bool}
    (hb : decide (mem a ≠ 0) = b) (hbs : BitsAt mem (a + 1) bs) :
    BitsAt mem a (b :: bs) :=
  BitsAt.append (BitsAt.singleton hb) hbs

theorem congr {mem mem' : ℕ → ℕ} {a : ℕ} {bs : List Bool}
    (h : BitsAt mem a bs) (hm : AgreeOn mem mem' a bs.length) :
    BitsAt mem' a bs := by
  intro i hi
  rw [hm (a + i) (by omega) (by omega)]
  exact h i hi

end BitsAt

/-- If cell `B` holds `bs.length` and `BitsAt mem (B + 1) bs`, then `rawOutput mem B = bs`. -/
theorem rawOutput_eq_of_bitsAt {mem : ℕ → ℕ} {B : ℕ} {bs : List Bool}
    (hlen : mem B = bs.length) (hbits : BitsAt mem (B + 1) bs) :
    rawOutput mem B = bs := by
  unfold rawOutput
  rw [hlen]
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp only [List.getElem_map, List.getElem_range]
    exact hbits i hi₂

/-! ### Small vertex sets (`n ≤ 1`) -/

/-- When `n ≤ 1`, every permutation of `Fin n` is the identity, so the empty list generates
`autGroup G`. -/
theorem autGroup_closure_nil_of_le_one {n : ℕ} (G : SimpleGraph (Fin n)) (hn : n ≤ 1) :
    Subgroup.closure {g : Equiv.Perm (Fin n) | g ∈ ([] : List _)} = autGroup G := by
  ext σ
  have hsub : Subsingleton (Fin n) := ⟨fun a b => Fin.ext (by omega)⟩
  have h1 : σ = 1 := Subsingleton.elim σ 1
  subst h1
  simp

end GI.Turing
