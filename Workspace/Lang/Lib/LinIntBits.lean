import Workspace.Lang.Prims.LinNormal

/-! Binary codecs for the signed integer programs. The cited encInt format stores
least-significant bits first. The programs below use natural arithmetic internally,
whose language costs charge bit weights rather than the numerical values. -/
namespace GI.Lang
open GI.Cited (Val encInt)
open GI.Machine (len len_le_iff len_le_self len_mul_le len_add_le)

/-- A Boolean bit represented by a natural value. -/
def linBit (b : Bool) : ℕ := if b then 1 else 0

def linBitsVal (bs : List Bool) : Val := .list (bs.map fun b => .nat (linBit b))

/-- Value of a little-endian bit list. -/
def linBitsNat : List Bool → ℕ
  | [] => 0
  | b :: bs => 2 * linBitsNat bs + linBit b

@[simp] theorem linBitsNat_nil : linBitsNat [] = 0 := rfl
@[simp] theorem linBitsNat_cons (b : Bool) (bs : List Bool) :
    linBitsNat (b :: bs) = 2 * linBitsNat bs + linBit b := rfl

theorem linBitsNat_lt (bs : List Bool) : linBitsNat bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    have hb : linBit b ≤ 1 := by cases b <;> decide
    simp only [linBitsNat_cons, List.length_cons, pow_succ]
    omega

theorem linBitsNat_bits (n : ℕ) : linBitsNat n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn, linBitsNat_cons, ih]
    cases b <;> simp [linBit, Nat.bit]

theorem linBitsVal_wt (bs : List Bool) : (linBitsVal bs).wt ≤ 7 * bs.length + 4 := by
  have h := linWtList (vs := bs.map fun b => .nat (linBit b)) (B := 3) (by
    intro v hv
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hv
    cases b <;> decide)
  simp only [List.length_map] at h
  change (Val.list _).wt ≤ _
  omega

/-- Read bits from position i by recursively decoding the suffix. -/
def linBitsDecodeF (self : ℕ) : Expr :=
  .ite (.arith .lt (arg 1) (.length (arg 0)))
    (.letE (.call self (mk2 (arg 0) (.arith .add (arg 1) (.nat 1))))
      (.arith .add (.arith .mul (.var 1) (.nat 2)) (.get (arg 0) (arg 1))))
    (.nat 0)

def linBitsDecodeCost (L i : ℕ) : ℕ := (L - i + 1) * (1000 * (L + 1) ^ 2)

/-- The decoder costs a polynomial in the length of the bit list. -/
theorem linBitsDecode_spec {P : Program} {f : ℕ}
    (hf : P.funs[f]? = some (linBitsDecodeF f)) (bs : List Bool) (i : ℕ) (hi : i ≤ bs.length) :
    FunDet P f (.list [linBitsVal bs, .nat i]) (.nat (linBitsNat (bs.drop i)))
      (linBitsDecodeCost bs.length i) := by
  generalize hk : bs.length - i = k
  induction k using Nat.strong_induction_on generalizing i with
  | h k ih =>
    have wb := linBitsVal_wt bs
    have wi := wt_nat_le i
    have wa := wt_list2_le (linBitsVal bs) (.nat i)
    have wi1 := wt_nat_le (i + 1)
    have wa1 := wt_list2_le (linBitsVal bs) (.nat (i + 1))
    have wn : (Val.nat (linBitsNat (bs.drop i))).wt ≤ bs.length + 2 := by
      rw [wt_nat]
      have := len_le_iff.mpr (linBitsNat_lt (bs.drop i))
      simp only [List.length_drop] at this
      omega
    have da := Det.arg' (P := P) (vs := [linBitsVal bs, .nat i]) (rest := []) (j := 0) rfl
    have di := Det.arg' (P := P) (vs := [linBitsVal bs, .nat i]) (rest := []) (j := 1) rfl
    have dl := Det.length da
    have dc := Det.arith (op := .lt) di dl
    by_cases hlt : i < bs.length
    · have hrec := ih (bs.length - (i + 1)) (by omega) (i + 1) (by omega) rfl
      have dp := Det.arith (op := .add) di (Det.nat 1)
      have dcall := Det.call (Det.mk2 da dp) hrec
      have da' := Det.arg' (P := P) (vs := [linBitsVal bs, .nat i])
        (rest := [.nat (linBitsNat (bs.drop (i + 1)))]) (j := 0) rfl
      have di' := Det.arg' (P := P) (vs := [linBitsVal bs, .nat i])
        (rest := [.nat (linBitsNat (bs.drop (i + 1)))]) (j := 1) rfl
      have dx := Det.get' da' di' (by
        rw [List.getElem?_map, List.getElem?_eq_getElem hlt]; rfl)
      have dv := Det.var' (P := P)
        (env := [.list [linBitsVal bs, .nat i], .nat (linBitsNat (bs.drop (i + 1)))]) (i := 1) rfl
      have dm := Det.arith (op := .mul) dv (Det.nat 2)
      have ds := Det.arith (op := .add) dm dx
      have heq : linBitsNat (bs.drop i) = linBitsNat (bs.drop (i + 1)) * 2 + linBit bs[i] := by
        conv_lhs => rw [List.drop_eq_getElem_cons hlt, linBitsNat_cons]
        omega
      have wm : (Val.nat (linBitsNat (bs.drop (i + 1)) * 2)).wt ≤ bs.length + 4 := by
        rw [wt_nat]
        have := len_le_iff.mpr (linBitsNat_lt (bs.drop (i + 1)))
        have := len_mul_le (linBitsNat (bs.drop (i + 1))) 2
        simp only [List.length_drop] at *
        have : len 2 = 2 := rfl
        omega
      have wrec : (Val.nat (linBitsNat (bs.drop (i + 1)))).wt ≤ bs.length + 2 := by
        rw [wt_nat]
        have := len_le_iff.mpr (linBitsNat_lt (bs.drop (i + 1)))
        simp only [List.length_drop] at this
        omega
      have wx : (Val.nat (linBit bs[i])).wt ≤ 3 := by cases bs[i] <;> decide
      have dres := Det.ite_pos (e := .nat 0) dc (by simpa using hlt) (Det.letE dcall ds)
      apply FunDet.intro hf
      rw [heq]
      refine dres.mono ?_
      simp only [GI.Machine.BinOp.eval_lt, GI.Machine.BinOp.eval_add,
        GI.Machine.BinOp.eval_mul, List.length_map] at *
      unfold linBitsDecodeCost at *
      rw [← heq] at *
      simp only [if_pos hlt] at *
      have hc : bs.length - i = bs.length - (i + 1) + 1 := by omega
      rw [hc]
      have w1 : (Val.nat 1).wt = 3 := rfl
      nlinarith
    · have hie : i = bs.length := by omega
      subst i
      have dres := Det.ite_zero (t := .letE (.call f (mk2 (arg 0) (.arith .add (arg 1) (.nat 1))))
        (.arith .add (.arith .mul (.var 1) (.nat 2)) (.get (arg 0) (arg 1)))) (by simpa [linBitsVal] using dc) (Det.nat 0)
      apply FunDet.intro hf
      simp only [List.drop_length, linBitsNat_nil]
      refine dres.mono ?_
      simp only [GI.Machine.BinOp.eval_lt, linBitsVal, List.length_map] at *
      unfold linBitsDecodeCost
      have w0 : (Val.nat 0).wt = 2 := rfl
      nlinarith

/-- The machine bit length agrees with the length of Nat.bits. -/
theorem linLenBits (n : ℕ) : len n = n.bits.length := by
  rw [Nat.size_eq_bits_len]
  apply le_antisymm
  · exact len_le_iff.mpr (Nat.lt_size_self n)
  · exact Nat.size_le.mpr (GI.Machine.lt_two_pow_len n)

/-- Append the little-endian bits of the magnitude to an existing bit list. -/
def linBitsEncodeF (self : ℕ) : Expr :=
  .ite (arg 0)
    (.call self (mk2 (.arith .div (arg 0) (.nat 2))
      (.snoc (arg 1) (.arith .mod (arg 0) (.nat 2)))))
    (arg 1)

def linBitsEncodeCost (n : ℕ) (acc : List Bool) : ℕ :=
  (n.bits.length + 1) * (1000 * (acc.length + n.bits.length + 1) ^ 2)

/-- Encoding is polynomial in the bit length, including all copies of the growing list. -/
theorem linBitsEncode_spec {P : Program} {f : ℕ}
    (hf : P.funs[f]? = some (linBitsEncodeF f)) (n : ℕ) (acc : List Bool) :
    FunDet P f (.list [.nat n, linBitsVal acc]) (linBitsVal (acc ++ n.bits))
      (linBitsEncodeCost n acc) := by
  induction n using Nat.binaryRec' generalizing acc with
  | zero =>
    have da := Det.arg' (P := P) (vs := [.nat 0, linBitsVal acc]) (rest := []) (j := 0) rfl
    have dr := Det.arg' (P := P) (vs := [.nat 0, linBitsVal acc]) (rest := []) (j := 1) rfl
    have d := Det.ite_zero (t := .call f (mk2 (.arith .div (arg 0) (.nat 2))
      (.snoc (arg 1) (.arith .mod (arg 0) (.nat 2))))) da dr
    apply FunDet.intro hf
    simp only [Nat.zero_bits, List.append_nil]
    refine d.mono ?_
    have wa := linBitsVal_wt acc
    have ww := wt_list2_le (.nat 0) (linBitsVal acc)
    have w0 : (Val.nat 0).wt = 2 := rfl
    simp only [linBitsEncodeCost, Nat.zero_bits, List.length_nil]
    nlinarith
  | bit b n hn ih =>
    have hb : linBit b ≤ 1 := by cases b <;> decide
    have hbn : Nat.bit b n ≠ 0 := by cases b <;> simp_all [Nat.bit]
    have hmod : Nat.bit b n % 2 = linBit b := by cases b <;> simp [linBit]
    have hdiv : Nat.bit b n / 2 = n := Nat.bit_div_two b n
    have da := Det.arg' (P := P) (vs := [.nat (Nat.bit b n), linBitsVal acc]) (rest := []) (j := 0) rfl
    have dl := Det.arg' (P := P) (vs := [.nat (Nat.bit b n), linBitsVal acc]) (rest := []) (j := 1) rfl
    have dd := Det.arith (op := .div) da (Det.nat 2)
    have dm := Det.arith (op := .mod) da (Det.nat 2)
    have ds := Det.snoc dl dm
    have he : (Val.list ((acc.map fun b => Val.nat (linBit b)) ++ [.nat (linBit b)])) =
        linBitsVal (acc ++ [b]) := by simp [linBitsVal]
    simp only [GI.Machine.BinOp.eval_mod, hmod, he] at ds
    simp only [GI.Machine.BinOp.eval_div, hdiv] at dd
    have dc := Det.call (Det.mk2 dd ds) (ih (acc ++ [b]))
    have d := Det.ite_pos (e := arg 1) da hbn dc
    have ho : (acc ++ [b]) ++ n.bits = acc ++ (Nat.bit b n).bits := by
      rw [Nat.bits_append_bit n b hn, List.append_assoc]
      rfl
    apply FunDet.intro hf
    rw [← ho]
    refine d.mono ?_
    have wacc := linBitsVal_wt acc
    have wnacc := linBitsVal_wt (acc ++ [b])
    have wout := linBitsVal_wt ((acc ++ [b]) ++ n.bits)
    have wni : (Val.nat (Nat.bit b n)).wt = n.bits.length + 3 := by
      rw [wt_nat, linLenBits, Nat.bits_append_bit n b hn, List.length_cons]
    have wn : (Val.nat n).wt = n.bits.length + 2 := by rw [wt_nat, linLenBits]
    have wb : (Val.nat (linBit b)).wt ≤ 3 := by cases b <;> decide
    have wa := wt_list2_le (.nat (Nat.bit b n)) (linBitsVal acc)
    have wna := wt_list2_le (.nat n) (linBitsVal (acc ++ [b]))
    simp only [GI.Machine.BinOp.eval_div, GI.Machine.BinOp.eval_mod, hdiv, hmod, he] at *
    simp only [linBitsEncodeCost, Nat.bits_append_bit n b hn, List.length_cons,
      List.length_nil, List.length_append] at *
    ring_nf at *
    nlinarith

end GI.Lang
