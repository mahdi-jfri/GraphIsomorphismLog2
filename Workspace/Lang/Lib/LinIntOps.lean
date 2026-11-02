import Workspace.Lang.Lib.LinIntParts
import Workspace.Lang.Lib.Tabulate

/-! Public signed arithmetic on the cited encInt values. The wrappers decode both
operands, run a proved natural-parts core, and encode the result. No cited arithmetic
hypothesis enters. The deliberately loose cost is a fixed polynomial in input weight. -/
namespace GI.Lang
open GI.Cited (Val encInt)

/-- Codec costs increase with input bit weight. -/
theorem linIntCodecCost_mono {W V : ℕ} (h : W ≤ V) : linIntCodecCost W ≤ linIntCodecCost V := by
  unfold linIntCodecCost
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)

theorem linIntPartsCost_mono {W V : ℕ} (h : W ≤ V) : linIntPartsCost W ≤ linIntPartsCost V := by
  unfold linIntPartsCost
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)

/-- Decode x and y, compute their result in canonical parts, and encode it. -/
def linIntBinaryF (decode core encode : ℕ) : Expr :=
  .letE (.call decode (arg 0))
    (.letE (.call decode (arg 1))
      (.letE (.call core (mk2 (.var 1) (.var 2))) (.call encode (.var 3))))

/-- Budget for the core after decoding two integers of input weight at most W. -/
def linIntCoreBudget (W : ℕ) : ℕ := linIntPartsCost (4 * linIntCodecCost W + 6)

/-- A fixed polynomial (degree 18) in input bit weight. -/
def linIntBinaryCost (W : ℕ) : ℕ :=
  100 * (linIntCodecCost W + linIntCoreBudget W + linIntCodecCost (linIntCoreBudget W) + W + 1)

/-- Composition lemma for a proved natural-parts core. The core premise is discharged
by linIntAddParts_spec, linIntSubParts_spec or linIntMulParts_spec in the public specs. -/
theorem linIntBinary_spec {P : Program} {f decode core encode bd be : ℕ}
    (hf : P.funs[f]? = some (linIntBinaryF decode core encode))
    (hd : P.funs[decode]? = some (linIntDecodeF bd))
    (hbd : P.funs[bd]? = some (linBitsDecodeF bd))
    (he : P.funs[encode]? = some (linIntEncodeF be))
    (hbe : P.funs[be]? = some (linBitsEncodeF be)) (x y z : ℤ)
    (hc : FunDet P core (.list [linIntParts x, linIntParts y]) (linIntParts z)
      (linIntPartsCost (Val.list [linIntParts x, linIntParts y]).wt)) :
    FunDet P f (.list [encInt x, encInt y]) (encInt z)
      (linIntBinaryCost (Val.list [encInt x, encInt y]).wt) := by
  have hx := linIntDecode_spec hd hbd x
  have hy := linIntDecode_spec hd hbd y
  have hz := linIntEncode_spec he hbe z
  have dx := Det.call (Det.arg' (P := P) (vs := [encInt x, encInt y]) (rest := []) (j := 0) rfl) hx
  have dy := Det.call (Det.arg' (P := P) (vs := [encInt x, encInt y])
    (rest := [linIntParts x]) (j := 1) rfl) hy
  have dc := Det.call (Det.mk2
    (Det.var' (P := P) (env := [.list [encInt x, encInt y], linIntParts x, linIntParts y]) (i := 1) rfl)
    (Det.var' (P := P) (env := [.list [encInt x, encInt y], linIntParts x, linIntParts y]) (i := 2) rfl)) hc
  have de := Det.call (Det.var' (P := P)
    (env := [.list [encInt x, encInt y], linIntParts x, linIntParts y, linIntParts z]) (i := 3) rfl) hz
  apply FunDet.intro hf
  refine (Det.letE dx (Det.letE dy (Det.letE dc de))).mono ?_
  have wx := wt_le_wt_list (vs := [encInt x, encInt y]) (v := encInt x) (by simp)
  have wy := wt_le_wt_list (vs := [encInt x, encInt y]) (v := encInt y) (by simp)
  have dxB := linIntCodecCost_mono wx.le
  have dyB := linIntCodecCost_mono wy.le
  have wpx := hx.wt_lt
  have wpy := hy.wt_lt
  have wpz := hc.wt_lt
  have wo := hz.wt_lt
  have wa := wt_list2_le (linIntParts x) (linIntParts y)
  have ha : (Val.list [linIntParts x, linIntParts y]).wt ≤
      4 * linIntCodecCost (Val.list [encInt x, encInt y]).wt + 6 := by omega
  have hC : linIntPartsCost (Val.list [linIntParts x, linIntParts y]).wt ≤
      linIntCoreBudget (Val.list [encInt x, encInt y]).wt := linIntPartsCost_mono ha
  have hE := linIntCodecCost_mono (show (linIntParts z).wt ≤
    linIntCoreBudget (Val.list [encInt x, encInt y]).wt by omega)
  unfold linIntBinaryCost
  omega

/-- Integer addition on encInt values. -/
theorem linIntAdd_spec {P : Program} {f decode core encode bd be norm : ℕ}
    (hf : P.funs[f]? = some (linIntBinaryF decode core encode))
    (hd : P.funs[decode]? = some (linIntDecodeF bd))
    (hbd : P.funs[bd]? = some (linBitsDecodeF bd))
    (he : P.funs[encode]? = some (linIntEncodeF be))
    (hbe : P.funs[be]? = some (linBitsEncodeF be))
    (hc : P.funs[core]? = some (linIntAddPartsF norm))
    (hn : P.funs[norm]? = some linIntNormF) (x y : ℤ) :
    FunDet P f (.list [encInt x, encInt y]) (encInt (x + y))
      (linIntBinaryCost (Val.list [encInt x, encInt y]).wt) :=
  linIntBinary_spec hf hd hbd he hbe x y (x + y) (linIntAddParts_spec hc hn x y)

/-- Integer subtraction on encInt values. -/
theorem linIntSub_spec {P : Program} {f decode core encode bd be norm : ℕ}
    (hf : P.funs[f]? = some (linIntBinaryF decode core encode))
    (hd : P.funs[decode]? = some (linIntDecodeF bd))
    (hbd : P.funs[bd]? = some (linBitsDecodeF bd))
    (he : P.funs[encode]? = some (linIntEncodeF be))
    (hbe : P.funs[be]? = some (linBitsEncodeF be))
    (hc : P.funs[core]? = some (linIntSubPartsF norm))
    (hn : P.funs[norm]? = some linIntNormF) (x y : ℤ) :
    FunDet P f (.list [encInt x, encInt y]) (encInt (x - y))
      (linIntBinaryCost (Val.list [encInt x, encInt y]).wt) :=
  linIntBinary_spec hf hd hbd he hbe x y (x - y) (linIntSubParts_spec hc hn x y)

/-- Integer multiplication on encInt values. -/
theorem linIntMul_spec {P : Program} {f decode core encode bd be norm : ℕ}
    (hf : P.funs[f]? = some (linIntBinaryF decode core encode))
    (hd : P.funs[decode]? = some (linIntDecodeF bd))
    (hbd : P.funs[bd]? = some (linBitsDecodeF bd))
    (he : P.funs[encode]? = some (linIntEncodeF be))
    (hbe : P.funs[be]? = some (linBitsEncodeF be))
    (hc : P.funs[core]? = some (linIntMulPartsF norm))
    (hn : P.funs[norm]? = some linIntNormF) (x y : ℤ) :
    FunDet P f (.list [encInt x, encInt y]) (encInt (x * y))
      (linIntBinaryCost (Val.list [encInt x, encInt y]).wt) :=
  linIntBinary_spec hf hd hbd he hbe x y (x * y) (linIntMulParts_spec hc hn x y)

end GI.Lang
