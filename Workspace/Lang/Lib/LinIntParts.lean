module

public import Workspace.Lang.Lib.LinIntCodec

@[expose] public section

/-! Arithmetic on canonical natural parts. These are ordinary GI.Lang expressions,
with no arithmetic primitive hypotheses. All bounds use the weights of natural
values, which are their bit lengths plus two. -/
namespace GI.Lang
open GI.Cited (Val)
open GI.Machine (BinOp len len_add_le len_mul_le len_sub_le len_div_le len_mod_le)

/-- Every machine arithmetic operation has an output bit weight bounded by its inputs. -/
theorem linArithWt (op : BinOp) (x y : ℕ) :
    (Val.nat (op.eval x y)).wt ≤ (Val.nat x).wt + (Val.nat y).wt + 1 := by
  cases op with
  | add => simpa only [BinOp.eval_add, wt_nat] using
      (show len (x + y) + 2 ≤ (len x + 2) + (len y + 2) + 1 from by
        have := len_add_le x y; omega)
  | mul => simp only [BinOp.eval_mul, wt_nat]; have := len_mul_le x y; omega
  | sub => simp only [BinOp.eval_sub, wt_nat]; have := len_sub_le x y; omega
  | div => simp only [BinOp.eval_div, wt_nat]; have := len_div_le x y; omega
  | mod => simp only [BinOp.eval_mod, wt_nat]; have := len_mod_le x y; omega
  | lt => simp only [BinOp.eval_lt]; split_ifs <;> simp only [wt_nat, GI.Machine.len_zero, GI.Machine.len_one]; all_goals omega
  | eq => simp only [BinOp.eval_eq]; split_ifs <;> simp only [wt_nat, GI.Machine.len_zero, GI.Machine.len_one]; all_goals omega

/-- Arithmetic cost in terms of a bound on the two operand bit weights. -/
theorem linDetArith {P : Program} {env : List Val} {a b : Expr} {x y ca cb W : ℕ}
    (op : BinOp) (ha : Det P env a (.nat x) ca) (hb : Det P env b (.nat y) cb)
    (hx : (Val.nat x).wt ≤ W) (hy : (Val.nat y).wt ≤ W) :
    Det P env (.arith op a b) (.nat (op.eval x y)) (ca + cb + 2 * W + 2) :=
  (Det.arith ha hb).mono (by have := linArithWt op x y; omega)

/-- Normalize positive and negative contributions by canceling their common part. -/
def linIntNormF : Expr := mk2 (.arith .sub (arg 0) (arg 1)) (.arith .sub (arg 1) (arg 0))

theorem linIntParts_subNat (p n : ℕ) :
    linIntParts ((p : ℤ) - n) = .list [.nat (p - n), .nat (n - p)] := by
  simp only [linIntParts, Int.toNat_sub, neg_sub]

theorem linIntNorm_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some linIntNormF)
    (p n : ℕ) : FunDet P f (.list [.nat p, .nat n]) (linIntParts ((p : ℤ) - n))
      (100 * ((Val.list [.nat p, .nat n]).wt + 1)) := by
  have dp := Det.arg' (P := P) (vs := [.nat p, .nat n]) (rest := []) (j := 0) rfl
  have dn := Det.arg' (P := P) (vs := [.nat p, .nat n]) (rest := []) (j := 1) rfl
  have d1 := Det.arith (op := .sub) dp dn
  have d2 := Det.arith (op := .sub) dn dp
  have w1 : (Val.nat (p - n)).wt ≤ (Val.nat p).wt := by
    simp only [wt_nat]; have := len_sub_le p n; omega
  have w2 : (Val.nat (n - p)).wt ≤ (Val.nat n).wt := by
    simp only [wt_nat]; have := len_sub_le n p; omega
  have wp := wt_le_wt_list (vs := [.nat p, .nat n]) (v := .nat p) (by simp)
  have wn := wt_le_wt_list (vs := [.nat p, .nat n]) (v := .nat n) (by simp)
  have wo := wt_list2_le (.nat (p - n)) (.nat (n - p))
  rw [linIntParts_subNat]
  apply FunDet.intro hf
  refine (Det.mk2 d1 d2).mono ?_
  simp only [BinOp.eval_sub]
  omega

/-- The positive-minus-negative representation determines the integer. -/
theorem linIntParts_difference (z : ℤ) : (z.toNat : ℤ) - (-z).toNat = z := by omega

/-- Canceling the contributions in addition gives the canonical parts of x+y. -/
theorem linIntParts_add (x y : ℤ) :
    linIntParts (x + y) = linIntParts
      (((x.toNat + y.toNat : ℕ) : ℤ) - ((-x).toNat + (-y).toNat : ℕ)) := by
  congr 1
  push_cast
  have := linIntParts_difference x
  have := linIntParts_difference y
  omega

/-- The product has two positive and two negative contributions. -/
theorem linIntParts_mul (x y : ℤ) :
    linIntParts (x * y) = linIntParts
      (((x.toNat * y.toNat + (-x).toNat * (-y).toNat : ℕ) : ℤ) -
       ((x.toNat * (-y).toNat + (-x).toNat * y.toNat : ℕ) : ℤ)) := by
  congr 1
  push_cast
  have hx := linIntParts_difference x
  have hy := linIntParts_difference y
  nlinarith [hx, hy]

/-- Access one natural part of one of the two signed operands. -/
def linPart (i j : ℕ) : Expr := .get (arg i) (.nat j)

def linPartNat (x y : ℤ) (i j : Fin 2) : ℕ :=
  if j.val = 0 then (if i.val = 0 then x else y).toNat
  else (-(if i.val = 0 then x else y)).toNat

@[simp] theorem linPartNat00 (x y : ℤ) : linPartNat x y 0 0 = x.toNat := rfl
@[simp] theorem linPartNat01 (x y : ℤ) : linPartNat x y 0 1 = (-x).toNat := rfl
@[simp] theorem linPartNat10 (x y : ℤ) : linPartNat x y 1 0 = y.toNat := rfl
@[simp] theorem linPartNat11 (x y : ℤ) : linPartNat x y 1 1 = (-y).toNat := rfl

/-- Every part can be read at cost linear in the weight of the two-operand input. -/
theorem linPart_spec {P : Program} (x y : ℤ) (i j : Fin 2) :
    Det P [.list [linIntParts x, linIntParts y]] (linPart i j)
      (.nat (linPartNat x y i j)) (10 * ((Val.list [linIntParts x, linIntParts y]).wt + 1)) := by
  have wx := wt_le_wt_list (vs := [linIntParts x, linIntParts y]) (v := linIntParts x) (by simp)
  have wy := wt_le_wt_list (vs := [linIntParts x, linIntParts y]) (v := linIntParts y) (by simp)
  have wxp := wt_le_wt_list (vs := [.nat x.toNat, .nat (-x).toNat]) (v := .nat x.toNat) (by simp)
  have wxn := wt_le_wt_list (vs := [.nat x.toNat, .nat (-x).toNat]) (v := .nat (-x).toNat) (by simp)
  have wyp := wt_le_wt_list (vs := [.nat y.toNat, .nat (-y).toNat]) (v := .nat y.toNat) (by simp)
  have wyn := wt_le_wt_list (vs := [.nat y.toNat, .nat (-y).toNat]) (v := .nat (-y).toNat) (by simp)
  fin_cases i <;> fin_cases j
  all_goals
    simp [linPartNat]
    apply (Det.get' (Det.arg' (P := P) (vs := [linIntParts x, linIntParts y])
      (rest := []) rfl) (Det.nat _) rfl).mono
    simp only [linIntParts] at *
    omega

/-- Every natural part is smaller in weight than the full two-operand input. -/
theorem linPartWt (x y : ℤ) (i j : Fin 2) :
    (Val.nat (linPartNat x y i j)).wt ≤ (Val.list [linIntParts x, linIntParts y]).wt := by
  have wx := wt_le_wt_list (vs := [linIntParts x, linIntParts y]) (v := linIntParts x) (by simp)
  have wy := wt_le_wt_list (vs := [linIntParts x, linIntParts y]) (v := linIntParts y) (by simp)
  have wxp := wt_le_wt_list (vs := [.nat x.toNat, .nat (-x).toNat]) (v := .nat x.toNat) (by simp)
  have wxn := wt_le_wt_list (vs := [.nat x.toNat, .nat (-x).toNat]) (v := .nat (-x).toNat) (by simp)
  have wyp := wt_le_wt_list (vs := [.nat y.toNat, .nat (-y).toNat]) (v := .nat y.toNat) (by simp)
  have wyn := wt_le_wt_list (vs := [.nat y.toNat, .nat (-y).toNat]) (v := .nat (-y).toNat) (by simp)
  fin_cases i <;> fin_cases j <;> simp [linPartNat]
  all_goals simp only [linIntParts] at *; omega

/-- A uniform bound for the fixed-size natural-parts arithmetic cores. -/
def linIntPartsCost (W : ℕ) : ℕ := 10000 * (W + 1) ^ 2

/-- Add positive contributions and negative contributions, then normalize. -/
def linIntAddPartsF (norm : ℕ) : Expr :=
  .call norm (mk2 (.arith .add (linPart 0 0) (linPart 1 0))
    (.arith .add (linPart 0 1) (linPart 1 1)))

/-- Addition on canonical parts, with polynomial bit cost. -/
theorem linIntAddParts_spec {P : Program} {f norm : ℕ}
    (hf : P.funs[f]? = some (linIntAddPartsF norm))
    (hn : P.funs[norm]? = some linIntNormF) (x y : ℤ) :
    FunDet P f (.list [linIntParts x, linIntParts y]) (linIntParts (x + y))
      (linIntPartsCost (Val.list [linIntParts x, linIntParts y]).wt) := by
  have dP := Det.arith (op := .add) (linPart_spec (P := P) x y 0 0) (linPart_spec x y 1 0)
  have dN := Det.arith (op := .add) (linPart_spec (P := P) x y 0 1) (linPart_spec x y 1 1)
  have d := Det.call (Det.mk2 dP dN)
    (linIntNorm_spec hn (x.toNat + y.toNat) ((-x).toNat + (-y).toNat))
  rw [linIntParts_add]
  apply FunDet.intro hf
  refine d.mono ?_
  have wxp := linPartWt x y 0 0
  have wxn := linPartWt x y 0 1
  have wyp := linPartWt x y 1 0
  have wyn := linPartWt x y 1 1
  simp only [linPartNat00, linPartNat01, linPartNat10, linPartNat11] at wxp wxn wyp wyn
  have wp := linArithWt .add x.toNat y.toNat
  have wn := linArithWt .add (-x).toNat (-y).toNat
  have wop := linArithWt .sub (x.toNat + y.toNat) ((-x).toNat + (-y).toNat)
  have won := linArithWt .sub ((-x).toNat + (-y).toNat) (x.toNat + y.toNat)
  have wi := wt_list2_le (.nat (x.toNat + y.toNat)) (.nat ((-x).toNat + (-y).toNat))
  have wo := wt_list2_le (.nat ((x.toNat + y.toNat) - ((-x).toNat + (-y).toNat)))
    (.nat (((-x).toNat + (-y).toNat) - (x.toNat + y.toNat)))
  simp only [BinOp.eval_add, BinOp.eval_sub, linIntParts_subNat] at *
  unfold linIntPartsCost
  simp only [linPartNat00, linPartNat01, linPartNat10, linPartNat11] at *
  nlinarith

/-- Subtraction exchanges the two contributions of the second operand. -/
theorem linIntParts_sub (x y : ℤ) :
    linIntParts (x - y) = linIntParts
      (((x.toNat + (-y).toNat : ℕ) : ℤ) - ((-x).toNat + y.toNat : ℕ)) := by
  congr 1
  push_cast
  have := linIntParts_difference x
  have := linIntParts_difference y
  omega

/-- Subtract by exchanging the positive and negative contributions of the second operand. -/
def linIntSubPartsF (norm : ℕ) : Expr :=
  .call norm (mk2 (.arith .add (linPart 0 0) (linPart 1 1))
    (.arith .add (linPart 0 1) (linPart 1 0)))

/-- Subtraction on canonical parts, with polynomial bit cost. -/
theorem linIntSubParts_spec {P : Program} {f norm : ℕ}
    (hf : P.funs[f]? = some (linIntSubPartsF norm))
    (hn : P.funs[norm]? = some linIntNormF) (x y : ℤ) :
    FunDet P f (.list [linIntParts x, linIntParts y]) (linIntParts (x - y))
      (linIntPartsCost (Val.list [linIntParts x, linIntParts y]).wt) := by
  have dP := Det.arith (op := .add) (linPart_spec (P := P) x y 0 0) (linPart_spec x y 1 1)
  have dN := Det.arith (op := .add) (linPart_spec (P := P) x y 0 1) (linPart_spec x y 1 0)
  have d := Det.call (Det.mk2 dP dN)
    (linIntNorm_spec hn (x.toNat + (-y).toNat) ((-x).toNat + y.toNat))
  rw [linIntParts_sub]
  apply FunDet.intro hf
  refine d.mono ?_
  have wxp := linPartWt x y 0 0
  have wxn := linPartWt x y 0 1
  have wyp := linPartWt x y 1 1
  have wyn := linPartWt x y 1 0
  simp only [linPartNat00, linPartNat01, linPartNat10, linPartNat11] at wxp wxn wyp wyn
  have wp := linArithWt .add x.toNat (-y).toNat
  have wn := linArithWt .add (-x).toNat y.toNat
  have wop := linArithWt .sub (x.toNat + (-y).toNat) ((-x).toNat + y.toNat)
  have won := linArithWt .sub ((-x).toNat + y.toNat) (x.toNat + (-y).toNat)
  have wi := wt_list2_le (.nat (x.toNat + (-y).toNat)) (.nat ((-x).toNat + y.toNat))
  have wo := wt_list2_le (.nat ((x.toNat + (-y).toNat) - ((-x).toNat + y.toNat)))
    (.nat (((-x).toNat + y.toNat) - (x.toNat + (-y).toNat)))
  simp only [BinOp.eval_add, BinOp.eval_sub, linIntParts_subNat] at *
  unfold linIntPartsCost
  simp only [linPartNat00, linPartNat01, linPartNat10, linPartNat11] at *
  nlinarith

/-- Multiply the two positive and two negative cross terms, then normalize. -/
def linIntMulPartsF (norm : ℕ) : Expr :=
  .call norm (mk2
    (.arith .add (.arith .mul (linPart 0 0) (linPart 1 0))
      (.arith .mul (linPart 0 1) (linPart 1 1)))
    (.arith .add (.arith .mul (linPart 0 0) (linPart 1 1))
      (.arith .mul (linPart 0 1) (linPart 1 0))))

/-- Multiplication on canonical parts, with polynomial bit cost. -/
theorem linIntMulParts_spec {P : Program} {f norm : ℕ}
    (hf : P.funs[f]? = some (linIntMulPartsF norm))
    (hn : P.funs[norm]? = some linIntNormF) (x y : ℤ) :
    FunDet P f (.list [linIntParts x, linIntParts y]) (linIntParts (x * y))
      (linIntPartsCost (Val.list [linIntParts x, linIntParts y]).wt) := by
  have dpp := Det.arith (op := .mul) (linPart_spec (P := P) x y 0 0) (linPart_spec x y 1 0)
  have dnn := Det.arith (op := .mul) (linPart_spec (P := P) x y 0 1) (linPart_spec x y 1 1)
  have dpn := Det.arith (op := .mul) (linPart_spec (P := P) x y 0 0) (linPart_spec x y 1 1)
  have dnp := Det.arith (op := .mul) (linPart_spec (P := P) x y 0 1) (linPart_spec x y 1 0)
  have dp := Det.arith (op := .add) dpp dnn
  have dn := Det.arith (op := .add) dpn dnp
  have d := Det.call (Det.mk2 dp dn) (linIntNorm_spec hn
    (x.toNat * y.toNat + (-x).toNat * (-y).toNat)
    (x.toNat * (-y).toNat + (-x).toNat * y.toNat))
  rw [linIntParts_mul]
  apply FunDet.intro hf
  refine d.mono ?_
  have wxp := linPartWt x y 0 0
  have wxn := linPartWt x y 0 1
  have wyp := linPartWt x y 1 0
  have wyn := linPartWt x y 1 1
  simp only [linPartNat00, linPartNat01, linPartNat10, linPartNat11] at wxp wxn wyp wyn
  have wpp := linArithWt .mul x.toNat y.toNat
  have wnn := linArithWt .mul (-x).toNat (-y).toNat
  have wpn := linArithWt .mul x.toNat (-y).toNat
  have wnp := linArithWt .mul (-x).toNat y.toNat
  have wp := linArithWt .add (x.toNat * y.toNat) ((-x).toNat * (-y).toNat)
  have wn := linArithWt .add (x.toNat * (-y).toNat) ((-x).toNat * y.toNat)
  have wop := linArithWt .sub (x.toNat * y.toNat + (-x).toNat * (-y).toNat)
    (x.toNat * (-y).toNat + (-x).toNat * y.toNat)
  have won := linArithWt .sub (x.toNat * (-y).toNat + (-x).toNat * y.toNat)
    (x.toNat * y.toNat + (-x).toNat * (-y).toNat)
  have wi := wt_list2_le (.nat (x.toNat * y.toNat + (-x).toNat * (-y).toNat))
    (.nat (x.toNat * (-y).toNat + (-x).toNat * y.toNat))
  have wo := wt_list2_le
    (.nat ((x.toNat * y.toNat + (-x).toNat * (-y).toNat) -
      (x.toNat * (-y).toNat + (-x).toNat * y.toNat)))
    (.nat ((x.toNat * (-y).toNat + (-x).toNat * y.toNat) -
      (x.toNat * y.toNat + (-x).toNat * (-y).toNat)))
  simp only [BinOp.eval_add, BinOp.eval_mul, BinOp.eval_sub, linIntParts_subNat] at *
  unfold linIntPartsCost
  simp only [linPartNat00, linPartNat01, linPartNat10, linPartNat11] at *
  nlinarith

/-- Negation swaps the two canonical natural parts. -/
def linIntNegPartsF : Expr := mk2 (arg 1) (arg 0)

theorem linIntNegParts_spec {P : Program} {f : ℕ}
    (hf : P.funs[f]? = some linIntNegPartsF) (z : ℤ) :
    FunDet P f (linIntParts z) (linIntParts (-z))
      (100 * ((linIntParts z).wt + 1)) := by
  have dp := Det.arg' (P := P) (vs := [.nat z.toNat, .nat (-z).toNat]) (rest := []) (j := 0) rfl
  have dn := Det.arg' (P := P) (vs := [.nat z.toNat, .nat (-z).toNat]) (rest := []) (j := 1) rfl
  have wp := wt_le_wt_list (vs := [.nat z.toNat, .nat (-z).toNat]) (v := .nat z.toNat) (by simp)
  have wn := wt_le_wt_list (vs := [.nat z.toNat, .nat (-z).toNat]) (v := .nat (-z).toNat) (by simp)
  have wo := wt_list2_le (.nat (-z).toNat) (.nat z.toNat)
  simp only [linIntParts, neg_neg]
  apply FunDet.intro hf
  refine (Det.mk2 dn dp).mono ?_
  omega

/-- Compare integers by moving the negative parts to the opposite side. -/
def linIntLtPartsF : Expr :=
  .arith .lt (.arith .add (linPart 0 0) (linPart 1 1))
    (.arith .add (linPart 1 0) (linPart 0 1))

theorem linIntLtParts_spec {P : Program} {f : ℕ}
    (hf : P.funs[f]? = some linIntLtPartsF) (x y : ℤ) :
    FunDet P f (.list [linIntParts x, linIntParts y]) (.nat (if x < y then 1 else 0))
      (linIntPartsCost (Val.list [linIntParts x, linIntParts y]).wt) := by
  have dp := Det.arith (op := .add) (linPart_spec (P := P) x y 0 0) (linPart_spec x y 1 1)
  have dn := Det.arith (op := .add) (linPart_spec (P := P) x y 1 0) (linPart_spec x y 0 1)
  have d := Det.arith (op := .lt) dp dn
  have hlt : x.toNat + (-y).toNat < y.toNat + (-x).toNat ↔ x < y := by omega
  simp only [linPartNat00, linPartNat01, linPartNat10, linPartNat11] at d
  simp only [BinOp.eval_add, BinOp.eval_lt, hlt] at d
  apply FunDet.intro hf
  refine d.mono ?_
  have wxp := linPartWt x y 0 0
  have wxn := linPartWt x y 0 1
  have wyp := linPartWt x y 1 0
  have wyn := linPartWt x y 1 1
  simp only [linPartNat00, linPartNat01, linPartNat10, linPartNat11] at wxp wxn wyp wyn
  have wp := linArithWt .add x.toNat (-y).toNat
  have wn := linArithWt .add y.toNat (-x).toNat
  have wb : (Val.nat (if x < y then 1 else 0)).wt ≤ 3 := by split_ifs <;> decide
  simp only [BinOp.eval_add] at wp wn
  unfold linIntPartsCost
  nlinarith

end GI.Lang
