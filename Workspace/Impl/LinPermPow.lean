module

public import Workspace.Lang.Lib.LinIntBits
public import Workspace.Lang.Lib.Perm

@[expose] public section

/-! Binary permutation powering for the cyclic-prefix relations in A.20. -/
namespace GI.Impl
open GI.Cited GI.Lang

/-- Input [a,e,r], result a^e*r. Each recursive call halves e. -/
def linPermPowF (self comp : ℕ) : Expr :=
  .ite (arg 1)
    (.letE (.call comp (mk2 (arg 0) (arg 0)))
      (.letE (.ite (.arith .mod (arg 1) (.nat 2))
        (.call comp (mk2 (arg 0) (arg 2))) (arg 2))
        (.call self (mk3 (.var 1) (.arith .div (arg 1) (.nat 2)) (.var 2)))))
    (arg 2)

def linPermPowUnit (n L : ℕ) : ℕ := 10 ^ 6 * (n + L + 2) ^ 4
def linPermPowCost (n L : ℕ) : ℕ := (L + 1) * linPermPowUnit n L

set_option maxHeartbeats 2000000 in
theorem linPermPow_spec {P : Program} {f comp n : ℕ}
    (hf : P.funs[f]? = some (linPermPowF f comp))
    (hc : P.HasAt comp (composeFuns comp)) (e : ℕ) (a r : Equiv.Perm (Fin n)) :
    FunDet P f (.list [encPerm a, .nat e, encPerm r]) (encPerm (a ^ e * r))
      (linPermPowCost n e.bits.length) := by
  induction e using Nat.binaryRec' generalizing a r with
  | zero =>
    have de := Det.arg' (P := P) (vs := [encPerm a, .nat 0, encPerm r]) (rest := []) (j := 1) rfl
    have dr := Det.arg' (P := P) (vs := [encPerm a, .nat 0, encPerm r]) (rest := []) (j := 2) rfl
    apply FunDet.intro hf
    simp only [pow_zero, one_mul]
    refine (Det.ite_zero de dr).mono ?_
    have wa := wt_encPerm_le a
    have wr := wt_encPerm_le r
    have wi := wt_list3_le (encPerm a) (.nat 0) (encPerm r)
    have w0 : (Val.nat 0).wt = 2 := rfl
    simp only [linPermPowCost, linPermPowUnit, Nat.zero_bits, List.length_nil]
    ring_nf at *
    omega
  | bit b e he ih =>
    let s := a * a
    let t := if b then a * r else r
    let V := Val.list [encPerm a, .nat (Nat.bit b e), encPerm r]
    let U := linPermPowUnit n (e.bits.length + 1)
    have hb : Nat.bit b e ≠ 0 := by cases b <;> simp_all [Nat.bit]
    have hmod : Nat.bit b e % 2 = (if b then 1 else 0) := by cases b <;> simp
    have hdiv : Nat.bit b e / 2 = e := Nat.bit_div_two b e
    have hbits : (Nat.bit b e).bits.length = e.bits.length + 1 := by
      rw [Nat.bits_append_bit e b he, List.length_cons]
    have hu : linPermPowUnit n e.bits.length ≤ U := by
      unfold linPermPowUnit U
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
    have hs := compose_spec hc a a
    have ht := compose_spec hc a r
    have hrec := (ih s t).mono (Nat.mul_le_mul_left (e.bits.length + 1) hu)
    have darg (j : ℕ) (rest : List Val) {v : Val}
        (hv : [encPerm a, .nat (Nat.bit b e), encPerm r][j]? = some v) :=
      Det.arg' (P := P) (vs := [encPerm a, .nat (Nat.bit b e), encPerm r]) (rest := rest) (j := j) hv
    have ds := Det.call (Det.mk2 (darg 0 [] rfl) (darg 0 [] rfl)) hs
    have dm := Det.arith (op := .mod) (darg 1 [encPerm s] rfl) (Det.nat 2)
    simp only [GI.Machine.BinOp.eval_mod, hmod] at dm
    have dt : Det P [V, encPerm s]
        (.ite (.arith .mod (arg 1) (.nat 2)) (.call comp (mk2 (arg 0) (arg 2))) (arg 2))
        (encPerm t) (100000 * (n + e.bits.length + 2) ^ 3) := by
      cases b with
      | false =>
        have dd := Det.ite_zero (t := .call comp (mk2 (arg 0) (arg 2))) dm (darg 2 [encPerm s] rfl)
        refine dd.mono ?_
        have wa := wt_encPerm_le a
        have wr := wt_encPerm_le r
        have wi := wt_list3_le (encPerm a) (.nat (Nat.bit false e)) (encPerm r)
        have we : (Val.nat (Nat.bit false e)).wt = e.bits.length + 3 := by rw [wt_nat, linLenBits, hbits]
        have w2 : (Val.nat 2).wt = 4 := rfl
        have w0 : (Val.nat 0).wt = 2 := rfl
        simp only [V, t, Bool.false_eq_true, if_false] at *
        ring_nf at *
        omega
      | true =>
        have dc := Det.call (Det.mk2 (darg 0 [encPerm s] rfl) (darg 2 [encPerm s] rfl)) ht
        have dd := Det.ite_pos (e := arg 2) dm (by decide : 1 ≠ 0) dc
        refine dd.mono ?_
        have wa := wt_encPerm_le a
        have wr := wt_encPerm_le r
        have wt := wt_encPerm_le (a * r)
        have wi := wt_list3_le (encPerm a) (.nat (Nat.bit true e)) (encPerm r)
        have wc := wt_list2_le (encPerm a) (encPerm r)
        have we : (Val.nat (Nat.bit true e)).wt = e.bits.length + 3 := by rw [wt_nat, linLenBits, hbits]
        have w2 : (Val.nat 2).wt = 4 := rfl
        have w1 : (Val.nat 1).wt = 3 := rfl
        simp only [V, t, ↓reduceIte, permK] at *
        ring_nf at *
        omega
    have dd := Det.arith (op := .div) (darg 1 [encPerm s, encPerm t] rfl) (Det.nat 2)
    simp only [GI.Machine.BinOp.eval_div, hdiv] at dd
    have dc := Det.call (Det.mk3
      (Det.var' (P := P) (env := [V, encPerm s, encPerm t]) (i := 1) rfl) dd
      (Det.var' (P := P) (env := [V, encPerm s, encPerm t]) (i := 2) rfl)) hrec
    have heq : s ^ e * t = a ^ Nat.bit b e * r := by
      cases b <;> simp only [s, t, ↓reduceIte, Nat.bit_false, Nat.bit_true]
      · rw [← pow_two, ← pow_mul]
        congr 2
      · rw [← pow_two, ← pow_mul]
        simp [pow_succ, mul_assoc, Nat.mul_comm]
    rw [heq] at dc
    have db := Det.ite_pos (e := arg 2) (darg 1 [] rfl) hb (Det.letE ds (Det.letE dt dc))
    apply FunDet.intro hf
    refine db.mono ?_
    have wa := wt_encPerm_le a
    have wr := wt_encPerm_le r
    have ws := wt_encPerm_le s
    have wt := wt_encPerm_le t
    have wo := wt_encPerm_le (a ^ Nat.bit b e * r)
    have wi := wt_list3_le (encPerm a) (.nat (Nat.bit b e)) (encPerm r)
    have wrec := wt_list3_le (encPerm s) (.nat e) (encPerm t)
    have wcomp := wt_list2_le (encPerm a) (encPerm a)
    have we : (Val.nat (Nat.bit b e)).wt = e.bits.length + 3 := by rw [wt_nat, linLenBits, hbits]
    have we' : (Val.nat e).wt = e.bits.length + 2 := by rw [wt_nat, linLenBits]
    have w2 : (Val.nat 2).wt = 4 := rfl
    simp only [linPermPowCost, hbits]
    change _ ≤ (e.bits.length + 1 + 1) * U
    have hunit : 100000 * (n + e.bits.length + 2) ^ 3 +
        100000 * (n + e.bits.length + 2) ^ 3 + 10000 * (n + e.bits.length + 2) ^ 2 ≤ U := by
      unfold U linPermPowUnit
      ring_nf
      omega
    simp only [V, s, U, hbits, permK, linPermPowCost] at *
    ring_nf at *
    omega

end GI.Impl
