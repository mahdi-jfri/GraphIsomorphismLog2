module

public import Workspace.Impl.VsQTr
public import Workspace.Lang.Lib.LinIntBits

@[expose] public section

/-!
# Binary powers in an encoded monoid

`vsQPowF self mul` on `[c, a, e, r]` returns `a^e * r`, by squaring: it calls the product
function `mul` on `[c, x, y]` (for `x * y`), and itself on `[c, a * a, e / 2, t]` with
`t = a * r` when `e` is odd and `t = r` otherwise.

* `vsQPow_spec`: for any monoid with an encoding of weight at most `B` and a product program of
  cost at most `C`, the result is the encoding of `a^e * r`, at cost at most
  `(bits e + 1) * (3 C + 1000 (c.wt + B + bits e + 10))`.
-/

namespace GI.Impl

open GI.Lang GI.Cited
open GI.Machine (len)

/-- The binary power: on `[c, a, e, r]`, `a^e * r`. -/
def vsQPowF (self mul : ℕ) : Expr :=
  .ite (arg 2)
    (.letE (.call mul (mk3 (arg 0) (arg 1) (arg 1)))
      (.letE (.ite (.arith .mod (arg 2) (.nat 2))
        (.call mul (mk3 (arg 0) (arg 1) (arg 3))) (arg 3))
        (.call self (mk4 (arg 0) (.var 1) (.arith .div (arg 2) (.nat 2)) (.var 2)))))
    (arg 3)

/-- The cost of one level. -/
def vsQPowUnit (cw B C k : ℕ) : ℕ := 3 * C + 1000 * (cw + B + k + 10)

set_option maxHeartbeats 2000000 in
theorem vsQPow_spec {M : Type*} [Monoid M] {P : Program} {f mul : ℕ}
    (hf : P.funs[f]? = some (vsQPowF f mul)) (enc : M → Val) (c : Val) {B C : ℕ}
    (hB : ∀ x, (enc x).wt ≤ B)
    (hm : ∀ x y, FunDet P mul (.list [c, enc x, enc y]) (enc (x * y)) C) (e : ℕ) (a r : M) :
    FunDet P f (.list [c, enc a, .nat e, enc r]) (enc (a ^ e * r))
      ((e.bits.length + 1) * vsQPowUnit c.wt B C e.bits.length) := by
  induction e using Nat.binaryRec' generalizing a r with
  | zero =>
    have de := Det.arg' (P := P) (vs := [c, enc a, .nat 0, enc r]) (rest := []) (j := 2) rfl
    have dr := Det.arg' (P := P) (vs := [c, enc a, .nat 0, enc r]) (rest := []) (j := 3) rfl
    apply FunDet.intro hf
    simp only [pow_zero, one_mul]
    refine (Det.ite_zero de dr).mono ?_
    have wa := hB a
    have wr := hB r
    have wi := wt_list4_le c (enc a) (.nat 0) (enc r)
    have w0 : (Val.nat 0).wt = 2 := rfl
    simp only [vsQPowUnit, Nat.zero_bits, List.length_nil]
    omega
  | bit b e he ih =>
    let s := a * a
    let t := if b then a * r else r
    let V := Val.list [c, enc a, .nat (Nat.bit b e), enc r]
    obtain ⟨k, hk⟩ : ∃ k, e.bits.length = k := ⟨_, rfl⟩
    have hb : Nat.bit b e ≠ 0 := by cases b <;> simp_all [Nat.bit]
    have hmod : Nat.bit b e % 2 = (if b then 1 else 0) := by cases b <;> simp
    have hdiv : Nat.bit b e / 2 = e := Nat.bit_div_two b e
    have hbits : (Nat.bit b e).bits.length = k + 1 := by
      rw [Nat.bits_append_bit e b he, List.length_cons, hk]
    have hu : vsQPowUnit c.wt B C k ≤ vsQPowUnit c.wt B C (k + 1) := by
      unfold vsQPowUnit; omega
    have hrec := ih s t
    rw [hk] at hrec
    replace hrec := hrec.mono (Nat.mul_le_mul_left (k + 1) hu)
    have darg (j : ℕ) (rest : List Val) {v : Val}
        (hv : [c, enc a, .nat (Nat.bit b e), enc r][j]? = some v) :=
      Det.arg' (P := P) (vs := [c, enc a, .nat (Nat.bit b e), enc r]) (rest := rest) (j := j) hv
    have wa := hB a
    have wr := hB r
    have ws := hB s
    have wt := hB t
    have wo := hB (a ^ Nat.bit b e * r)
    have wi := wt_list4_le c (enc a) (.nat (Nat.bit b e)) (enc r)
    have we : (Val.nat (Nat.bit b e)).wt = k + 3 := by rw [wt_nat, linLenBits, hbits]
    have we' : (Val.nat e).wt = k + 2 := by rw [wt_nat, linLenBits, hk]
    have w2 : (Val.nat 2).wt = 4 := rfl
    have w1 : (Val.nat 1).wt = 3 := rfl
    have w0 : (Val.nat 0).wt = 2 := rfl
    have wl3 := wt_list3_le c (enc a) (enc r)
    have wl3' := wt_list3_le c (enc a) (enc a)
    have ds := Det.call (Det.mk3 (darg 0 [] rfl) (darg 1 [] rfl) (darg 1 [] rfl)) (hm a a)
    have dm := Det.arith (op := .mod) (darg 2 [enc s] rfl) (Det.nat 2)
    simp only [GI.Machine.BinOp.eval_mod, hmod] at dm
    have dt : Det P [V, enc s]
        (.ite (.arith .mod (arg 2) (.nat 2)) (.call mul (mk3 (arg 0) (arg 1) (arg 3))) (arg 3))
        (enc t) (C + 100 * (c.wt + B + k + 10)) := by
      cases b with
      | false =>
        have dd := Det.ite_zero (t := .call mul (mk3 (arg 0) (arg 1) (arg 3))) dm
          (darg 3 [enc s] rfl)
        refine dd.mono ?_
        simp only [V, t, Bool.false_eq_true, if_false] at *
        omega
      | true =>
        have dc := Det.call (Det.mk3 (darg 0 [enc s] rfl) (darg 1 [enc s] rfl)
          (darg 3 [enc s] rfl)) (hm a r)
        have dd := Det.ite_pos (e := arg 3) dm (by decide : 1 ≠ 0) dc
        refine dd.mono ?_
        have wt' := hB (a * r)
        simp only [V, t, ↓reduceIte] at *
        omega
    have dd := Det.arith (op := .div) (darg 2 [enc s, enc t] rfl) (Det.nat 2)
    simp only [GI.Machine.BinOp.eval_div, hdiv] at dd
    have dc := Det.call (Det.mk4 (darg 0 [enc s, enc t] rfl)
      (Det.var' (P := P) (env := [V, enc s, enc t]) (i := 1) rfl) dd
      (Det.var' (P := P) (env := [V, enc s, enc t]) (i := 2) rfl)) hrec
    have heq : s ^ e * t = a ^ Nat.bit b e * r := by
      cases b <;> simp only [s, t, ↓reduceIte, Nat.bit_false, Nat.bit_true, Bool.false_eq_true]
      · rw [← pow_two, ← pow_mul]
      · rw [← pow_two, ← pow_mul]
        simp [pow_succ, mul_assoc, Nat.mul_comm]
    rw [heq] at dc
    have db := Det.ite_pos (e := arg 3) (darg 2 [] rfl) hb (Det.letE ds (Det.letE dt dc))
    apply FunDet.intro hf
    refine db.mono ?_
    have wrec := wt_list4_le c (enc s) (.nat e) (enc t)
    have wz := hB (a * a)
    simp only [hbits]
    have e1 : (k + 1 + 1) * vsQPowUnit c.wt B C (k + 1) =
        (k + 1) * vsQPowUnit c.wt B C (k + 1) + vsQPowUnit c.wt B C (k + 1) := by ring
    rw [e1]
    generalize (k + 1) * vsQPowUnit c.wt B C (k + 1) = X at *
    simp only [V, vsQPowUnit] at *
    omega

end GI.Impl
