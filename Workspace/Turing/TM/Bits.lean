/-
Binary digit representation and self-delimiting encodings for simulating the stack machine on a
Turing machine with alphabet `Bool`.

A natural number `v` is represented by its binary digits `bits v : List Bool`, lowest digit first,
with no trailing `false`. Its length equals `GI.Machine.len v`. On a stack, a digit list `bs` is
encoded as `encDigits bs`: each digit `b` becomes `[true, b]`, followed by a terminating `false`.
This makes every encoded number nonempty and self-delimiting.

This file also gives pure functional specifications of binary addition (`addBitsRaw`) and
subtraction (`subBitsRaw`) on digit lists, along with the unary encoding `encRet` used for return
addresses.
-/
module

public import Workspace.Turing.SM
import Mathlib.Data.Nat.Log

@[expose] public section

namespace GI.Turing.TM

open GI.Machine (len)

/-- Binary digits of a natural number, least significant bit first, with `bits 0 = []`. -/
def bits : ℕ → List Bool
  | 0 => []
  | n + 1 => decide ((n + 1) % 2 = 1) :: bits ((n + 1) / 2)

/-- Value of a list of binary digits, least significant bit first. -/
def ofBits : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * ofBits bs

/-- A digit list is canonical if it does not end in `false`. -/
def Canonical (bs : List Bool) : Prop :=
  bs.getLast? ≠ some false

/-- Strip leading `false` entries from a list of booleans. -/
def stripLeadingFalse : List Bool → List Bool
  | false :: bs => stripLeadingFalse bs
  | bs => bs

/-- Self-delimiting encoding of a digit list on a `Bool` stack: each digit `b` is written as
`true, b`, followed by a terminating `false`. -/
def encDigits : List Bool → List Bool
  | [] => [false]
  | b :: bs => true :: b :: encDigits bs

/-- Encoding of a natural number on a `Bool` stack. -/
def encNat (v : ℕ) : List Bool :=
  encDigits (bits v)

/-- Encoding of a stack of natural numbers on a `Bool` stack. -/
def encStack (l : List ℕ) : List Bool :=
  (l.map encNat).flatten

/-- Unary encoding of a return address on a `Bool` stack: `r` copies of `true` then `false`. -/
def encRet (r : ℕ) : List Bool :=
  List.replicate r true ++ [false]

/-- Encoding of the return stack on a `Bool` stack. -/
def encRetStack (rs : List ℕ) : List Bool :=
  (rs.map encRet).flatten

theorem bits_zero : bits 0 = [] := by
  rw [bits]

theorem bits_eq_cons {n : ℕ} (hn : n ≠ 0) :
    bits n = decide (n % 2 = 1) :: bits (n / 2) := by
  cases n with
  | zero => exact absurd rfl hn
  | succ m => rw [bits]

theorem bits_eq_nil_iff {n : ℕ} : bits n = [] ↔ n = 0 := by
  cases n with
  | zero => simp [bits_zero]
  | succ m => rw [bits_eq_cons (Nat.succ_ne_zero m)]; simp

theorem bits_one : bits 1 = [true] := by
  rw [bits_eq_cons (by decide)]; simp [bits_zero]

theorem bits_two : bits 2 = [false, true] := by
  rw [bits_eq_cons (by decide)]; simp [bits_one]

theorem bits_length (n : ℕ) : (bits n).length = len n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n = 0
    · subst hn; simp [bits_zero, len]
    · rw [bits_eq_cons hn, List.length_cons,
        ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide))]
      by_cases hdiv : n / 2 = 0
      · have h1 : n = 1 := by omega
        subst h1; simp [len]
      · simp only [len, hn, hdiv, ↓reduceIte]
        rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two,
          Nat.log_of_one_lt_of_le (by decide : 1 < 2) (by omega : 2 ≤ n)]

theorem ofBits_bits (n : ℕ) : ofBits (bits n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n = 0
    · subst hn; simp [bits_zero, ofBits]
    · rw [bits_eq_cons hn, ofBits,
        ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide))]
      by_cases hodd : n % 2 = 1 <;> simp [hodd] <;> omega

theorem ofBits_lt_two_pow (bs : List Bool) : ofBits bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [ofBits]
  | cons b bs ih =>
    simp only [ofBits, List.length_cons, Nat.pow_succ]
    cases b <;> simp <;> omega

theorem ofBits_append (as bs : List Bool) :
    ofBits (as ++ bs) = ofBits as + 2 ^ as.length * ofBits bs := by
  induction as with
  | nil => simp [ofBits]
  | cons a as ih =>
    simp only [List.cons_append, ofBits, ih, List.length_cons, Nat.pow_succ]
    have hmul : 2 * (2 ^ as.length * ofBits bs) = 2 ^ as.length * 2 * ofBits bs := by
      rw [← Nat.mul_assoc, Nat.mul_comm 2 (2 ^ as.length)]
    rw [Nat.mul_add, hmul, Nat.add_assoc]

theorem canonical_nil : Canonical [] := by simp [Canonical]

theorem canonical_singleton_true : Canonical [true] := by simp [Canonical]

theorem canonical_cons_of_ne_nil {b : Bool} {bs : List Bool} (hne : bs ≠ [])
    (h : Canonical bs) : Canonical (b :: bs) := by
  simpa [Canonical, List.getLast?_cons_of_ne_nil hne] using h

theorem canonical_tail {b : Bool} {bs : List Bool} (h : Canonical (b :: bs)) : Canonical bs := by
  cases bs with
  | nil => exact canonical_nil
  | cons c cs =>
    simpa [Canonical, List.getLast?_cons_of_ne_nil] using h

theorem canonical_bits (n : ℕ) : Canonical (bits n) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n = 0
    · subst hn; rw [bits_zero]; exact canonical_nil
    · rw [bits_eq_cons hn]
      by_cases hdiv : n / 2 = 0
      · have h1 : n = 1 := by omega
        subst h1
        rw [show decide (1 % 2 = 1) = true by rfl, show 1 / 2 = 0 by rfl, bits_zero]
        exact canonical_singleton_true
      · exact canonical_cons_of_ne_nil (by rwa [ne_eq, bits_eq_nil_iff])
          (ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)))

theorem bits_ofBits {bs : List Bool} (hc : Canonical bs) : bits (ofBits bs) = bs := by
  induction bs with
  | nil => simp [ofBits, bits_zero]
  | cons b bs ih =>
    have hct : Canonical bs := canonical_tail hc
    have hih := ih hct
    by_cases hbs : bs = []
    · subst hbs
      cases b with
      | false => exfalso; exact hc (by simp)
      | true => simp [ofBits, bits_one]
    · have hpos : ofBits bs ≠ 0 := by
        intro hz
        rw [hz, bits_zero] at hih
        exact hbs hih.symm
      have hne : ofBits (b :: bs) ≠ 0 := by
        simp only [ofBits]; cases b <;> simp; omega
      rw [bits_eq_cons hne]
      have hmod : decide (ofBits (b :: bs) % 2 = 1) = b := by
        simp only [ofBits]; cases b <;> simp
      have hdiv : ofBits (b :: bs) / 2 = ofBits bs := by
        simp only [ofBits]; cases b <;> simp; omega
      rw [hmod, hdiv, hih]

theorem bits_double (v : ℕ) :
    bits (2 * v) = if v = 0 then [] else false :: bits v := by
  by_cases hv : v = 0
  · subst hv; simp [bits_zero]
  · have h2v : 2 * v ≠ 0 := by omega
    rw [ite_eq_right_iff.mpr (fun h => absurd h hv), bits_eq_cons h2v]
    have hmod : (2 * v) % 2 = 0 := by omega
    have hdiv : (2 * v) / 2 = v := by omega
    simp [hmod, hdiv]

theorem bits_half (v : ℕ) : bits (v / 2) = (bits v).tail := by
  cases v with
  | zero => simp [bits_zero]
  | succ m => rw [bits_eq_cons (Nat.succ_ne_zero m)]; rfl

theorem mod_two_of_bits {v : ℕ} {b : Bool} {bs : List Bool} (h : bits v = b :: bs) :
    v % 2 = if b then 1 else 0 := by
  have hv : v ≠ 0 := by intro hv; subst hv; rw [bits_zero] at h; cases h
  rw [bits_eq_cons hv] at h
  have hb : b = decide (v % 2 = 1) := (List.cons.inj h).1.symm
  subst hb
  by_cases hodd : v % 2 = 1
  · simp [hodd]
  · simp [hodd]; omega

theorem encNat_zero : encNat 0 = [false] := by
  simp [encNat, bits_zero, encDigits]

theorem encNat_one : encNat 1 = [true, true, false] := by
  simp [encNat, bits_one, encDigits]

theorem encNat_two : encNat 2 = [true, false, true, true, false] := by
  simp [encNat, bits_two, encDigits]

theorem encNat_double {v : ℕ} (hv : v ≠ 0) :
    encNat (2 * v) = true :: false :: encNat v := by
  simp only [encNat, bits_double, hv, ↓reduceIte, encDigits]

theorem encStack_nil : encStack [] = [] := rfl

theorem encStack_cons (v : ℕ) (r : List ℕ) :
    encStack (v :: r) = encNat v ++ encStack r := rfl

theorem encStack_eq_nil_iff {l : List ℕ} : encStack l = [] ↔ l = [] := by
  cases l with
  | nil => simp [encStack]
  | cons v r =>
    simp only [encStack_cons, List.append_eq_nil_iff, List.cons_ne_nil, iff_false]
    intro ⟨hv, _⟩
    cases h : bits v <;> simp [encNat, h, encDigits] at hv

theorem encRetStack_nil : encRetStack [] = [] := rfl

theorem encRetStack_cons (r : ℕ) (rs : List ℕ) :
    encRetStack (r :: rs) = encRet r ++ encRetStack rs := rfl

/-- Leading `false` count stripped by `stripLeadingFalse`. -/
def leadingFalseCount : List Bool → ℕ
  | false :: bs => leadingFalseCount bs + 1
  | _ => 0

theorem stripLeadingFalse_length_add (bs : List Bool) :
    leadingFalseCount bs + (stripLeadingFalse bs).length = bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | false =>
      simp only [leadingFalseCount, stripLeadingFalse, List.length_cons]
      omega
    | true =>
      simp [leadingFalseCount, stripLeadingFalse]

theorem canonical_reverse_stripLeadingFalse (bs : List Bool) :
    Canonical (stripLeadingFalse bs).reverse := by
  induction bs with
  | nil => exact canonical_nil
  | cons b bs ih =>
    cases b with
    | false => exact ih
    | true =>
      simp only [stripLeadingFalse, Canonical, List.reverse_cons, List.getLast?_concat]
      decide

theorem ofBits_reverse_stripLeadingFalse (bs : List Bool) :
    ofBits (stripLeadingFalse bs).reverse = ofBits bs.reverse := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | false =>
      simp only [stripLeadingFalse, ih, List.reverse_cons, ofBits_append, ofBits]
      simp
    | true => rfl

/-- Functional specification of binary addition on digit lists (least significant bit first). -/
def addBitsRaw : List Bool → List Bool → Bool → List Bool
  | [], [], c => if c then [true] else []
  | a :: as, [], c => xor a c :: addBitsRaw as [] (a && c)
  | [], b :: bs, c => xor b c :: addBitsRaw [] bs (b && c)
  | a :: as, b :: bs, c =>
    xor (xor a b) c :: addBitsRaw as bs ((a && b) || (a && c) || (b && c))

theorem ofBits_addBitsRaw (as bs : List Bool) (c : Bool) :
    ofBits (addBitsRaw as bs c) = ofBits as + ofBits bs + c.toNat := by
  induction as generalizing bs c with
  | nil =>
    induction bs generalizing c with
    | nil => cases c <;> simp [addBitsRaw, ofBits]
    | cons b bs ih =>
      simp only [addBitsRaw, ofBits, ih]
      cases b <;> cases c <;> simp <;> omega
  | cons a as iha =>
    cases bs with
    | nil =>
      simp only [addBitsRaw, ofBits, iha]
      cases a <;> cases c <;> simp <;> omega
    | cons b bs =>
      simp only [addBitsRaw, ofBits, iha]
      cases a <;> cases b <;> cases c <;> simp <;> omega

theorem addBitsRaw_ne_nil_of_left {a : Bool} {as bs : List Bool} {c : Bool} :
    addBitsRaw (a :: as) bs c ≠ [] := by
  cases bs <;> simp [addBitsRaw]

theorem addBitsRaw_ne_nil_of_right {as : List Bool} {b : Bool} {bs : List Bool} {c : Bool} :
    addBitsRaw as (b :: bs) c ≠ [] := by
  cases as <;> simp [addBitsRaw]

theorem canonical_addBitsRaw {as bs : List Bool} {c : Bool}
    (ha : Canonical as) (hb : Canonical bs) : Canonical (addBitsRaw as bs c) := by
  induction as generalizing bs c with
  | nil =>
    induction bs generalizing c with
    | nil =>
      cases c <;> simp [addBitsRaw, canonical_nil, canonical_singleton_true]
    | cons b bs ih =>
      simp only [addBitsRaw]
      cases bs with
      | nil =>
        cases b with
        | false => exfalso; exact hb (by simp)
        | true => cases c <;> simp [Canonical, addBitsRaw]
      | cons b' bs' =>
        exact canonical_cons_of_ne_nil addBitsRaw_ne_nil_of_right (ih (canonical_tail hb))
  | cons a as iha =>
    cases bs with
    | nil =>
      simp only [addBitsRaw]
      cases as with
      | nil =>
        cases a with
        | false => exfalso; exact ha (by simp)
        | true => cases c <;> simp [Canonical, addBitsRaw]
      | cons a' as' =>
        exact canonical_cons_of_ne_nil addBitsRaw_ne_nil_of_left
          (iha (canonical_tail ha) canonical_nil)
    | cons b bs =>
      simp only [addBitsRaw]
      cases as with
      | nil =>
        cases bs with
        | nil =>
          cases a with
          | false => exfalso; exact ha (by simp)
          | true =>
            cases b with
            | false => exfalso; exact hb (by simp)
            | true => cases c <;> simp [Canonical, addBitsRaw]
        | cons b' bs' =>
          exact canonical_cons_of_ne_nil addBitsRaw_ne_nil_of_right
            (iha canonical_nil (canonical_tail hb))
      | cons a' as' =>
        exact canonical_cons_of_ne_nil addBitsRaw_ne_nil_of_left
          (iha (canonical_tail ha) (canonical_tail hb))

theorem addBitsRaw_bits (a b : ℕ) :
    addBitsRaw (bits a) (bits b) false = bits (a + b) := by
  have hc := canonical_addBitsRaw (c := false) (canonical_bits a) (canonical_bits b)
  have hval := ofBits_addBitsRaw (bits a) (bits b) false
  rw [ofBits_bits, ofBits_bits] at hval
  simp only [Bool.toNat_false, Nat.add_zero] at hval
  rw [← hval, bits_ofBits hc]

theorem addBitsRaw_length_le (as bs : List Bool) (c : Bool) :
    (addBitsRaw as bs c).length ≤ max as.length bs.length + 1 := by
  induction as generalizing bs c with
  | nil =>
    induction bs generalizing c with
    | nil => cases c <;> simp [addBitsRaw]
    | cons b bs ih =>
      simp only [addBitsRaw, List.length_cons]
      have := ih (b && c)
      simp only [List.length_nil, Nat.zero_max] at this ⊢
      omega
  | cons a as iha =>
    cases bs with
    | nil =>
      simp only [addBitsRaw, List.length_cons, List.length_nil, Nat.max_zero]
      have := iha [] (a && c)
      simp only [List.length_nil, Nat.max_zero] at this
      omega
    | cons b bs =>
      simp only [addBitsRaw, List.length_cons]
      have := iha bs ((a && b) || (a && c) || (b && c))
      omega

/-- Functional specification of binary subtraction on digit lists (least significant bit first),
returning the raw difference bits and the final borrow bit. -/
def subBitsRaw : List Bool → List Bool → Bool → List Bool × Bool
  | [], [], b => ([], b)
  | a :: as, [], b =>
    let r := subBitsRaw as [] (!a && b)
    (xor a b :: r.1, r.2)
  | [], d :: ds, b =>
    let r := subBitsRaw [] ds (d || b)
    (xor d b :: r.1, r.2)
  | a :: as, d :: ds, b =>
    let r := subBitsRaw as ds ((!a && (d || b)) || (d && b))
    (xor (xor a d) b :: r.1, r.2)

theorem subBitsRaw_length (as bs : List Bool) (b : Bool) :
    (subBitsRaw as bs b).1.length = max as.length bs.length := by
  induction as generalizing bs b with
  | nil =>
    induction bs generalizing b with
    | nil => simp [subBitsRaw]
    | cons d ds ih =>
      simp only [subBitsRaw, List.length_cons, ih, List.length_nil, Nat.zero_max]
  | cons a as iha =>
    cases bs with
    | nil =>
      simp only [subBitsRaw, List.length_cons, iha, List.length_nil, Nat.max_zero]
    | cons d ds =>
      simp only [subBitsRaw, List.length_cons, iha]
      omega

theorem ofBits_subBitsRaw (as bs : List Bool) (b : Bool) :
    ofBits (subBitsRaw as bs b).1 + ofBits bs + b.toNat =
      ofBits as + if (subBitsRaw as bs b).2 then 2 ^ (subBitsRaw as bs b).1.length else 0 := by
  have h1 : ∀ x y z : Bool,
      (if xor (xor x y) z then 1 else 0) + (if y then 1 else 0) + z.toNat =
        (if x then 1 else 0) + 2 * ((!x && (y || z)) || (y && z)).toNat := by decide
  have hL : ∀ x z : Bool,
      (if xor x z then 1 else 0) + z.toNat = (if x then 1 else 0) + 2 * (!x && z).toNat := by
    decide
  have hR : ∀ y z : Bool,
      (if xor y z then 1 else 0) + (if y then 1 else 0) + z.toNat = 2 * (y || z).toNat := by
    decide
  induction as generalizing bs b with
  | nil =>
    induction bs generalizing b with
    | nil => cases b <;> simp [subBitsRaw, ofBits]
    | cons d ds ih =>
      simp only [subBitsRaw, ofBits, List.length_cons, Nat.pow_succ]
      have h := ih (d || b)
      have hs := hR d b
      simp only [ofBits] at h ⊢
      cases hbr : (subBitsRaw [] ds (d || b)).2 <;>
        simp only [hbr, ↓reduceIte, Bool.false_eq_true] at h ⊢ <;> omega
  | cons a as iha =>
    cases bs with
    | nil =>
      simp only [subBitsRaw, ofBits, List.length_cons, Nat.pow_succ]
      have h := iha [] (!a && b)
      have hs := hL a b
      simp only [ofBits] at h ⊢
      cases hbr : (subBitsRaw as [] (!a && b)).2 <;>
        simp only [hbr, ↓reduceIte, Bool.false_eq_true] at h ⊢ <;> omega
    | cons d ds =>
      simp only [subBitsRaw, ofBits, List.length_cons, Nat.pow_succ]
      have h := iha ds ((!a && (d || b)) || (d && b))
      have hs := h1 a d b
      cases hbr : (subBitsRaw as ds ((!a && (d || b)) || (d && b))).2 <;>
        simp only [hbr, ↓reduceIte, Bool.false_eq_true] at h ⊢ <;> omega

theorem subBitsRaw_borrow_true (a b : ℕ)
    (h : (subBitsRaw (bits a) (bits b) false).2 = true) : a - b = 0 := by
  have heq := ofBits_subBitsRaw (bits a) (bits b) false
  rw [h, ofBits_bits, ofBits_bits] at heq
  simp only [Bool.toNat_false, Nat.add_zero, ↓reduceIte] at heq
  have hlt := ofBits_lt_two_pow (subBitsRaw (bits a) (bits b) false).1
  omega

theorem subBitsRaw_borrow_false (a b : ℕ)
    (h : (subBitsRaw (bits a) (bits b) false).2 = false) :
    stripLeadingFalse (subBitsRaw (bits a) (bits b) false).1.reverse = (bits (a - b)).reverse := by
  have heq := ofBits_subBitsRaw (bits a) (bits b) false
  rw [h, ofBits_bits, ofBits_bits] at heq
  simp only [Bool.toNat_false, Nat.add_zero, Bool.false_eq_true, ↓reduceIte] at heq
  have hdiff : ofBits (subBitsRaw (bits a) (bits b) false).1 = a - b := by omega
  have hval : ofBits (stripLeadingFalse (subBitsRaw (bits a) (bits b) false).1.reverse).reverse =
      a - b := by
    rw [ofBits_reverse_stripLeadingFalse, List.reverse_reverse, hdiff]
  have hc := canonical_reverse_stripLeadingFalse (subBitsRaw (bits a) (bits b) false).1.reverse
  have hbits := bits_ofBits hc
  rw [hval] at hbits
  rw [← List.reverse_reverse (stripLeadingFalse _), hbits]

end GI.Turing.TM
