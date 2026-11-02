import Workspace.Impl.HNFCells

/-!
# The numbers `K` and `m` of the Hermite program

On `[r, c, A, d]` the program `hnfNumsF` returns `[K, m]` (as integers), where
`T = 1 + Σ |A i j|`, `K = 2 r (r T)^r + 1` (`GI.Proved.hnfK`) and `m = |d| K`. All arithmetic is on
natural numbers (`Det.arith`, which costs the bit length of the result), and the two results are
encoded once at the end.
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved
open GI.Machine (BinOp len len_le_iff)

variable {r c : ℕ}

/-- The encoder of the integer library at `ints`. -/
structure hnfEncAt (P : Program) (ints : ℕ) : Prop where
  enc : P.funs[ints + 3]? = some (linIntEncodeF (ints + 1))
  bits : P.funs[ints + 1]? = some (linBitsEncodeF (ints + 1))

theorem hnfEncAt_of {P : Program} {ints : ℕ} (h : P.HasAt ints (linIntFuns ints)) :
    hnfEncAt P ints where
  enc := by simpa [linIntFuns] using h 3 (by simp [linIntFuns])
  bits := by simpa [linIntFuns] using h 1 (by simp [linIntFuns])

/-- The natural numbers of the program. -/
def hnfTn (A : Matrix (Fin r) (Fin c) ℤ) : ℕ := hnfAbsTot A r + 1
def hnfPn (A : Matrix (Fin r) (Fin c) ℤ) : ℕ := (r * hnfTn A) ^ r
def hnfKn (A : Matrix (Fin r) (Fin c) ℤ) : ℕ := 2 * r * hnfPn A + 1
def hnfMn (A : Matrix (Fin r) (Fin c) ℤ) (d : ℤ) : ℕ := d.natAbs * hnfKn A

theorem hnfKn_eq (A : Matrix (Fin r) (Fin c) ℤ) :
    ((hnfKn A : ℕ) : ℤ) = hnfK r (hnfTn A) := by
  simp [hnfKn, hnfPn, hnfK]

theorem hnf_parts_nat (k : ℕ) : linIntParts (k : ℤ) = .list [.nat k, .nat 0] := by
  simp [linIntParts]

/-- On `[r, c, A, d]`: `[K, m]`. -/
def hnfNumsF (abs pow ints : ℕ) : Expr :=
  .letE (.call abs (mk3 (.nat 0) (arg 2) (.nat 0)))
  (.letE (.arith .add (.var 1) (.nat 1))
  (.letE (.call pow (mk3 (.arith .mul (arg 0) (.var 2)) (arg 2) (.nat 1)))
  (.letE (.arith .add (.arith .mul (.arith .mul (.nat 2) (arg 0)) (.var 3)) (.nat 1))
  (.letE (.call (ints + 2) (arg 3))
  (.letE (.arith .mul (.arith .add (.get (.var 5) (.nat 0)) (.get (.var 5) (.nat 1))) (.var 4))
    (mk2 (.call (ints + 3) (mk2 (.var 4) (.nat 0))) (.call (ints + 3) (mk2 (.var 6) (.nat 0)))))))))

def hnfNumsCost (Y : ℕ) : ℕ :=
  hnfMatAbsCost Y + hnfPowCost (10 * Y + 100) + 3 * linIntCodecCost (10 * Y + 100) +
    1000 * (Y + 10) * (Y + 10)

theorem hnf_le_pow_self {a n : ℕ} (ha : 1 ≤ a) (hn : 1 ≤ n) : a ≤ a ^ n := by
  calc a = a ^ 1 := (pow_one a).symm
    _ ≤ a ^ n := Nat.pow_le_pow_right ha hn

set_option maxHeartbeats 4000000 in
/-- **The numbers `K` and `m`.** -/
theorem hnfNums_spec {P : Program} {abs pow ints f : ℕ} (hD : hnfDecAt P ints) (hE : hnfEncAt P ints)
    (hf : P.funs[f]? = some (hnfNumsF abs pow ints)) (habs : P.HasAt abs (hnfMatAbsFuns abs ints))
    (hpow : P.HasAt pow (hnfPowFuns pow)) (A : Matrix (Fin r) (Fin c) ℤ) (d : ℤ) (hr : 0 < r)
    (hd : d ≠ 0) {B Y : ℕ} (hAB : ∀ i j, (A i j).natAbs ≤ B) (hB : r * (c * B) < 2 ^ Y)
    (hV : (Val.list [.nat r, .nat c, encIntMatrix A, encInt d]).wt ≤ Y)
    (hm : hnfMn A d < 2 ^ Y) :
    FunDet P f (.list [.nat r, .nat c, encIntMatrix A, encInt d])
      (.list [encInt (hnfKn A : ℤ), encInt (hnfMn A d : ℤ)]) (hnfNumsCost Y) := by
  set inp := Val.list [.nat r, .nat c, encIntMatrix A, encInt d] with hinp
  -- the sizes of the numbers
  have hd1 : 1 ≤ d.natAbs := Int.natAbs_pos.mpr hd
  have hT1 : 1 ≤ (hnfTn A) := by unfold hnfTn; omega
  have hrT : 1 ≤ r * (hnfTn A) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hPrT : r * (hnfTn A) ≤ (hnfPn A) := hnf_le_pow_self hrT hr
  have hTrT : (hnfTn A) ≤ r * (hnfTn A) := Nat.le_mul_of_pos_left _ hr
  have hKm : (hnfKn A) ≤ (hnfMn A d) := by unfold hnfMn; exact Nat.le_mul_of_pos_left _ hd1
  have h2rP : 2 * r * (hnfPn A) < (hnfKn A) := by unfold hnfKn; omega
  have hPK : (hnfPn A) < (hnfKn A) := by
    have : (hnfPn A) ≤ 2 * r * (hnfPn A) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have h2r : 2 * r ≤ 2 * r * (hnfPn A) := Nat.le_mul_of_pos_right _ (by omega)
  have hdm : d.natAbs ≤ (hnfMn A d) := by unfold hnfMn; exact Nat.le_mul_of_pos_right _ (by unfold hnfKn; omega)
  have eT : hnfTn A = hnfAbsTot A r + 1 := rfl
  have bS : (Val.nat (hnfAbsTot A r)).wt ≤ Y + 2 := hnf_nat_wt_le (by omega)
  have bT : (Val.nat (hnfTn A)).wt ≤ Y + 2 := hnf_nat_wt_le (by omega)
  have brT : (Val.nat (r * (hnfTn A))).wt ≤ Y + 2 := hnf_nat_wt_le (by omega)
  have bP : (Val.nat (hnfPn A)).wt ≤ Y + 2 := hnf_nat_wt_le (by omega)
  have b2r : (Val.nat (2 * r)).wt ≤ Y + 2 := hnf_nat_wt_le (by omega)
  have b2rP : (Val.nat (2 * r * (hnfPn A))).wt ≤ Y + 2 := hnf_nat_wt_le (by omega)
  have bK : (Val.nat (hnfKn A)).wt ≤ Y + 2 := hnf_nat_wt_le (by omega)
  have bm : (Val.nat (hnfMn A d)).wt ≤ Y + 2 := hnf_nat_wt_le hm
  have bd : (Val.nat d.natAbs).wt ≤ Y + 2 := hnf_nat_wt_le (by omega)
  have bdp : (Val.nat d.toNat).wt ≤ Y + 2 := hnf_nat_wt_le (by have := linIntAbsParts d; omega)
  have bdn : (Val.nat (-d).toNat).wt ≤ Y + 2 := hnf_nat_wt_le (by have := linIntAbsParts d; omega)
  have wA : (encIntMatrix A).wt < Y := lt_of_lt_of_le (wt_le_wt_list (by simp)) hV
  have wd : (encInt d).wt < Y := lt_of_lt_of_le (wt_le_wt_list (by simp)) hV
  have wr : (Val.nat r).wt < Y := lt_of_lt_of_le (wt_le_wt_list (by simp)) hV
  have e0 : (Val.nat 0).wt = 2 := rfl
  have e1 : (Val.nat 1).wt = 3 := rfl
  have e2 : (Val.nat 2).wt = 4 := rfl
  -- step 1: the sum
  have d1 := Det.call (Det.mk3 (Det.nat (P := P) (env := [inp]) 0)
    (Det.arg' (P := P) (vs := [.nat r, .nat c, encIntMatrix A, encInt d]) (rest := []) (j := 2) rfl)
    (Det.nat 0)) (hnfMatAbs_spec hD habs A B Y hAB wA.le hB)
  -- step 2: `(hnfTn A)`
  set env1 := [inp, Val.nat (hnfAbsTot A r)] with henv1
  have d2 : Det P env1 (.arith .add (.var 1) (.nat 1)) (.nat (hnfTn A)) _ :=
    Det.arith (Det.var' (i := 1) rfl) (Det.nat 1)
  -- step 3: `P`
  set env2 := env1 ++ [Val.nat (hnfTn A)] with henv2
  set xs := (List.finRange r).map fun i => linVecVal (A i) with hxs
  have hxl : xs.length = r := by simp [hxs]
  have dq : Det P env2 (.arith .mul (arg 0) (.var 2)) (.nat (r * (hnfTn A))) _ :=
    Det.arith (Det.arg' (vs := [.nat r, .nat c, encIntMatrix A, encInt d]) (rest := [.nat (hnfAbsTot A r), .nat (hnfTn A)])
      (j := 0) rfl) (Det.var' (i := 2) rfl)
  have dA2 : Det P env2 (arg 2) (.list xs) _ :=
    Det.arg' (vs := [.nat r, .nat c, encIntMatrix A, encInt d]) (rest := [.nat (hnfAbsTot A r), .nat (hnfTn A)]) (j := 2) rfl
  have w3 : (Val.list [.nat (r * (hnfTn A)), .list xs, .nat 1]).wt ≤ 10 * Y + 100 := by
    have := wt_list3_le (.nat (r * (hnfTn A))) (.list xs) (.nat 1)
    have e : (Val.list xs).wt = (encIntMatrix A).wt := rfl
    omega
  have hpw := hnfPow_spec hpow (r * (hnfTn A)) xs w3 (by
    rw [hxl]
    calc (r * (hnfTn A)) ^ r = (hnfPn A) := rfl
      _ < 2 ^ Y := by omega
      _ ≤ 2 ^ (10 * Y + 100) := Nat.pow_le_pow_right (by decide) (by omega))
  rw [hxl] at hpw
  have d3 := Det.call (Det.mk3 dq dA2 (Det.nat 1)) hpw
  -- step 4: `(hnfKn A)`
  set env3 := env2 ++ [Val.nat (hnfPn A)] with henv3
  have d4 : Det P env3 (.arith .add (.arith .mul (.arith .mul (.nat 2) (arg 0)) (.var 3)) (.nat 1))
      (.nat (hnfKn A)) _ :=
    Det.arith (Det.arith (Det.arith (Det.nat 2)
      (Det.arg' (vs := [.nat r, .nat c, encIntMatrix A, encInt d]) (rest := [.nat (hnfAbsTot A r), .nat (hnfTn A), .nat (hnfPn A)])
        (j := 0) rfl)) (Det.var' (i := 3) rfl)) (Det.nat 1)
  -- step 5: the parts of `d`
  set env4 := env3 ++ [Val.nat (hnfKn A)] with henv4
  have hdec := linIntDecode_spec hD.dec hD.bits d
  have d5 := Det.call (Det.arg' (P := P) (vs := [.nat r, .nat c, encIntMatrix A, encInt d])
    (rest := [.nat (hnfAbsTot A r), .nat (hnfTn A), .nat (hnfPn A), .nat (hnfKn A)]) (j := 3) rfl) hdec
  -- step 6: `(hnfMn A d)`
  set env5 := env4 ++ [linIntParts d] with henv5
  have dv5 : Det P env5 (.var 5) (.list [.nat d.toNat, .nat (-d).toNat]) _ := Det.var' (i := 5) rfl
  have d6 := Det.arith (op := .mul) (Det.arith (op := .add) (Det.get' dv5 (Det.nat 0) rfl)
    (Det.get' dv5 (Det.nat 1) rfl)) (Det.var' (P := P) (env := env5) (i := 4) rfl)
  have e6 : BinOp.mul.eval (BinOp.add.eval d.toNat (-d).toNat) (hnfKn A) = (hnfMn A d) := by
    simp only [BinOp.eval, hnfMn, ← linIntAbsParts]
  rw [e6] at d6
  -- the output
  set env6 := env5 ++ [Val.nat (hnfMn A d)] with henv6
  have hpK : linIntParts ((hnfKn A) : ℤ) = .list [.nat (hnfKn A), .nat 0] := hnf_parts_nat (hnfKn A)
  have hpm : linIntParts ((hnfMn A d) : ℤ) = .list [.nat (hnfMn A d), .nat 0] := hnf_parts_nat (hnfMn A d)
  have hencK := linIntEncode_spec hE.enc hE.bits ((hnfKn A) : ℤ)
  have hencm := linIntEncode_spec hE.enc hE.bits ((hnfMn A d) : ℤ)
  rw [hpK] at hencK
  rw [hpm] at hencm
  have dK := Det.call (Det.mk2 (Det.var' (P := P) (env := env6) (i := 4) rfl) (Det.nat 0)) hencK
  have dm := Det.call (Det.mk2 (Det.var' (P := P) (env := env6) (i := 6) rfl) (Det.nat 0)) hencm
  have d7 := Det.mk2 dK dm
  have dall := Det.letE d1 (Det.letE d2 (Det.letE d3 (Det.letE d4 (Det.letE d5 (Det.letE d6 d7)))))
  apply FunDet.intro hf
  refine dall.mono ?_
  have eI : (Val.list [Val.nat r, Val.nat c, encIntMatrix A, encInt d]).wt = inp.wt := rfl
  have f1 := wt_list3_le (.nat 0) (encIntMatrix A) (.nat 0)
  have f2 : (Val.nat (BinOp.add.eval (hnfAbsTot A r) 1)).wt = (Val.nat (hnfTn A)).wt := rfl
  have f3 : (Val.nat (BinOp.mul.eval r (hnfTn A))).wt = (Val.nat (r * hnfTn A)).wt := rfl
  have f4 : (Val.nat ((r * hnfTn A) ^ r)).wt = (Val.nat (hnfPn A)).wt := rfl
  have f5 : (Val.nat (BinOp.mul.eval 2 r)).wt = (Val.nat (2 * r)).wt := rfl
  have f6 : (Val.nat (BinOp.mul.eval (2 * r) (hnfPn A))).wt = (Val.nat (2 * r * hnfPn A)).wt := rfl
  have f7 : (Val.nat (BinOp.add.eval (2 * r * hnfPn A) 1)).wt = (Val.nat (hnfKn A)).wt := rfl
  have f8 : (Val.nat (BinOp.add.eval d.toNat (-d).toNat)).wt = (Val.nat d.natAbs).wt := by
    simp only [BinOp.eval, ← linIntAbsParts]
  have f9 : (linIntParts d).wt = (Val.list [Val.nat d.toNat, Val.nat (-d).toNat]).wt := rfl
  have f10 := wt_list2_le (Val.nat d.toNat) (Val.nat (-d).toNat)
  have f11 := wt_list2_le (Val.nat (hnfKn A)) (Val.nat 0)
  have f12 := wt_list2_le (Val.nat (hnfMn A d)) (Val.nat 0)
  have f13 : (encInt (hnfKn A : ℤ)).wt ≤ 20 * (Y + 1) := hnf_wt_int (by simpa using (by omega : hnfKn A < 2 ^ Y))
  have f14 : (encInt (hnfMn A d : ℤ)).wt ≤ 20 * (Y + 1) := hnf_wt_int (by simpa using hm)
  have f15 := wt_list2_le (encInt (hnfKn A : ℤ)) (encInt (hnfMn A d : ℤ))
  have c1 := linIntCodecCost_mono (show (encInt d).wt ≤ 10 * Y + 100 by omega)
  have c2 := linIntCodecCost_mono (show (Val.list [Val.nat (hnfKn A), Val.nat 0]).wt ≤ 10 * Y + 100 by
    omega)
  have c3 := linIntCodecCost_mono (show (Val.list [Val.nat (hnfMn A d), Val.nat 0]).wt ≤
    10 * Y + 100 by omega)
  have hYY : 1000 * (Y + 10) ≤ 1000 * (Y + 10) * (Y + 10) := Nat.le_mul_of_pos_right _ (by omega)
  unfold hnfNumsCost
  omega

end GI.Impl
