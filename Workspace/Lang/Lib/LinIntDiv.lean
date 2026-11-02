import Workspace.Lang.Lib.LinIntOps

/-! Euclidean signed quotient and remainder. The negative-dividend quotient uses
(n-1)/b+1, so exact divisibility and a nonzero remainder are both handled correctly. -/
namespace GI.Lang
open GI.Cited (Val)
open GI.Machine (BinOp)

/-- A deterministic conditional whose two branches have different known outputs. -/
theorem linDetIte {P : Program} {env : List Val} {c t e : Expr} {n cc ct ce : ℕ} {v w : Val}
    (hc : Det P env c (.nat n) cc) (ht : Det P env t v ct) (he : Det P env e w ce) :
    Det P env (.ite c t e) (if n = 0 then w else v)
      (cc + ct + ce + v.wt + w.wt + 1) := by
  by_cases hn : n = 0
  · subst n
    simp only [↓reduceIte]
    exact (Det.ite_zero hc he).mono (by omega)
  · rw [if_neg hn]
    exact (Det.ite_pos hc hn ht).mono (by omega)

/-- Quotient magnitude for a negative dividend with magnitude n and positive divisor b. -/
def linIntNegQuot (n b : ℕ) : ℕ := (n - 1) / b + 1

/-- The natural-parts result of the signed quotient algorithm. Division by zero gives zero. -/
def linIntDivPartsVal (x y : ℤ) : Val :=
  if y.natAbs = 0 then linIntParts 0 else
    if (-x).toNat = 0 then
      if (-y).toNat = 0 then .list [.nat (x.toNat / y.natAbs), .nat 0]
      else .list [.nat 0, .nat (x.toNat / y.natAbs)]
    else
      if (-y).toNat = 0 then .list [.nat 0, .nat (linIntNegQuot (-x).toNat y.natAbs)]
      else .list [.nat (linIntNegQuot (-x).toNat y.natAbs), .nat 0]

/-- The branch formulas agree with Lean's Euclidean integer division, for either divisor sign. -/
theorem linIntDivPartsVal_eq (x y : ℤ) : linIntDivPartsVal x y = linIntParts (x / y) := by
  cases y with
  | ofNat b =>
    by_cases hb : b = 0
    · subst b; simp [linIntDivPartsVal, linIntParts]
    · cases x with
      | ofNat a => simp [linIntDivPartsVal, linIntParts, hb, ← Int.natCast_ediv]
      | negSucc a =>
        have hd : Int.negSucc a / (b : ℤ) = -((a / b + 1 : ℕ) : ℤ) := by
          rw [Int.negSucc_ediv a (by omega)]
          change -(((a / b : ℕ) : ℤ) + 1) = -((a / b + 1 : ℕ) : ℤ)
          simp
        change linIntDivPartsVal (Int.negSucc a) (b : ℤ) = linIntParts (Int.negSucc a / (b : ℤ))
        rw [hd]
        have hq : ((a : ℤ) / (b : ℤ)).toNat = a / b := rfl
        have hqp : (0 : ℤ) ≤ (a : ℤ) / (b : ℤ) := Int.ediv_nonneg (by omega) (by omega)
        simp [linIntDivPartsVal, linIntParts, linIntNegQuot, hb]
        omega
  | negSucc b =>
    have hy : (Int.negSucc b : ℤ) = -((b + 1 : ℕ) : ℤ) := by omega
    conv_rhs => rw [hy, Int.ediv_neg]
    cases x with
    | ofNat a =>
      change linIntDivPartsVal (Int.ofNat a) (Int.negSucc b) =
        linIntParts (-((a / (b + 1) : ℕ) : ℤ))
      have hq : ((a : ℤ) / ((b + 1 : ℕ) : ℤ)).toNat = a / (b + 1) := rfl
      have hqp : (0 : ℤ) ≤ (a : ℤ) / ((b + 1 : ℕ) : ℤ) := Int.ediv_nonneg (by omega) (by omega)
      simp [linIntDivPartsVal, linIntParts]
      push_cast at hq hqp
      omega
    | negSucc a =>
      have hd : Int.negSucc a / ((b + 1 : ℕ) : ℤ) = -((a / (b + 1) + 1 : ℕ) : ℤ) := by
        rw [Int.negSucc_ediv a (by omega)]
        change -(((a / (b + 1) : ℕ) : ℤ) + 1) = -((a / (b + 1) + 1 : ℕ) : ℤ)
        simp
      rw [hd]
      have hq : ((a : ℤ) / ((b + 1 : ℕ) : ℤ)).toNat = a / (b + 1) := rfl
      have hqp : (0 : ℤ) ≤ (a : ℤ) / ((b + 1 : ℕ) : ℤ) := Int.ediv_nonneg (by omega) (by omega)
      simp [linIntDivPartsVal, linIntParts, linIntNegQuot]
      push_cast at hq hqp
      omega

/-- Absolute divisor, from the canonical parts. -/
def linIntDivAbsE : Expr := .arith .add (linPart 1 0) (linPart 1 1)

def linIntDivPosE : Expr := .arith .div (linPart 0 0) linIntDivAbsE

def linIntDivNegE : Expr :=
  .arith .add (.arith .div (.arith .sub (linPart 0 1) (.nat 1)) linIntDivAbsE) (.nat 1)

/-- Euclidean quotient on canonical natural parts. -/
def linIntDivPartsF : Expr :=
  .ite linIntDivAbsE
    (.ite (linPart 0 1)
      (.ite (linPart 1 1) (mk2 linIntDivNegE (.nat 0)) (mk2 (.nat 0) linIntDivNegE))
      (.ite (linPart 1 1) (mk2 (.nat 0) linIntDivPosE) (mk2 linIntDivPosE (.nat 0))))
    (mk2 (.nat 0) (.nat 0))

set_option maxHeartbeats 2000000 in
/-- Signed Euclidean quotient, with the same polynomial core bound as add and multiply. -/
theorem linIntDivParts_spec {P : Program} {f : ℕ}
    (hf : P.funs[f]? = some linIntDivPartsF) (x y : ℤ) :
    FunDet P f (.list [linIntParts x, linIntParts y]) (linIntParts (x / y))
      (linIntPartsCost (Val.list [linIntParts x, linIntParts y]).wt) := by
  have xp := linPart_spec (P := P) x y 0 0
  have xn := linPart_spec (P := P) x y 0 1
  have yp := linPart_spec (P := P) x y 1 0
  have yn := linPart_spec (P := P) x y 1 1
  have db := Det.arith (op := .add) yp yn
  have dq := Det.arith (op := .div) xp db
  have dn := Det.arith (op := .add)
    (Det.arith (op := .div) (Det.arith (op := .sub) xn (Det.nat 1)) db) (Det.nat 1)
  have d := linDetIte db
    (linDetIte xn
      (linDetIte yn (Det.mk2 dn (Det.nat 0)) (Det.mk2 (Det.nat 0) dn))
      (linDetIte yn (Det.mk2 (Det.nat 0) dq) (Det.mk2 dq (Det.nat 0))))
    (Det.mk2 (Det.nat 0) (Det.nat 0))
  simp only [linPartNat00, linPartNat01, linPartNat10, linPartNat11,
    BinOp.eval_add, BinOp.eval_sub, BinOp.eval_div, ← linIntAbsParts] at d
  change Det P _ (linIntDivPartsF) (linIntDivPartsVal x y) _ at d
  rw [linIntDivPartsVal_eq] at d
  apply FunDet.intro hf
  refine d.mono ?_
  have wxp := linPartWt x y 0 0
  have wxn := linPartWt x y 0 1
  have wyp := linPartWt x y 1 0
  have wyn := linPartWt x y 1 1
  simp only [linPartNat00, linPartNat01, linPartNat10, linPartNat11] at wxp wxn wyp wyn
  have wb := linArithWt .add y.toNat (-y).toNat
  have wq := linArithWt .div x.toNat y.natAbs
  have ws := linArithWt .sub (-x).toNat 1
  have wd := linArithWt .div ((-x).toNat - 1) y.natAbs
  have wn := linArithWt .add (((-x).toNat - 1) / y.natAbs) 1
  have wq0 := wt_list2_le (.nat (x.toNat / y.natAbs)) (.nat 0)
  have w0q := wt_list2_le (.nat 0) (.nat (x.toNat / y.natAbs))
  have wn0 := wt_list2_le (.nat (linIntNegQuot (-x).toNat y.natAbs)) (.nat 0)
  have w0n := wt_list2_le (.nat 0) (.nat (linIntNegQuot (-x).toNat y.natAbs))
  have w00 := wt_list2_le (.nat 0) (.nat 0)
  have w0 : (Val.nat 0).wt = 2 := rfl
  have w1 : (Val.nat 1).wt = 3 := rfl
  simp only [BinOp.eval_add, BinOp.eval_sub, BinOp.eval_div, ← linIntAbsParts,
    linIntNegQuot] at *
  unfold linIntPartsCost
  split_ifs <;> nlinarith

/-- Public quotient on encInt values. Division by zero is defined, as in Lean, to give zero. -/
theorem linIntDiv_spec {P : Program} {f decode core encode bd be : ℕ}
    (hf : P.funs[f]? = some (linIntBinaryF decode core encode))
    (hd : P.funs[decode]? = some (linIntDecodeF bd))
    (hbd : P.funs[bd]? = some (linBitsDecodeF bd))
    (he : P.funs[encode]? = some (linIntEncodeF be))
    (hbe : P.funs[be]? = some (linBitsEncodeF be))
    (hc : P.funs[core]? = some linIntDivPartsF) (x y : ℤ) :
    FunDet P f (.list [GI.Cited.encInt x, GI.Cited.encInt y]) (GI.Cited.encInt (x / y))
      (linIntBinaryCost (Val.list [GI.Cited.encInt x, GI.Cited.encInt y]).wt) :=
  linIntBinary_spec hf hd hbd he hbe x y (x / y) (linIntDivParts_spec hc x y)

end GI.Lang
