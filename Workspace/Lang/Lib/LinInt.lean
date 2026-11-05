module

public import Workspace.Lang.Lib.LinIntMod
public import Workspace.Lang.Lib.LinIntTests

@[expose] public section

/-! The installed signed-integer library. There are no primitive hypotheses.
Offsets 11--17 expose add, subtract, multiply, Euclidean quotient, remainder,
strict comparison, and sign, all on the paper's encInt format. -/
namespace GI.Lang
open GI.Cited (Val encInt)

/-- Eighteen function bodies, including both codecs and the arithmetic cores. -/
def linIntFuns (b : ℕ) : List Expr :=
  [linBitsDecodeF b, linBitsEncodeF (b + 1), linIntDecodeF b, linIntEncodeF (b + 1),
    linIntNormF, linIntAddPartsF (b + 4), linIntSubPartsF (b + 4), linIntMulPartsF (b + 4),
    linIntDivPartsF, linIntModPartsF, linIntLtPartsF,
    linIntBinaryF (b + 2) (b + 5) (b + 3), linIntBinaryF (b + 2) (b + 6) (b + 3),
    linIntBinaryF (b + 2) (b + 7) (b + 3), linIntBinaryF (b + 2) (b + 8) (b + 3),
    linIntBinaryF (b + 2) (b + 9) (b + 3), linIntCompareF (b + 2) (b + 10), linIntSignF]

/-- The public function-index contracts of the signed-integer library. -/
structure linIntSpec (P : Program) (b : ℕ) : Prop where
  add : ∀ x y : ℤ, FunDet P (b + 11) (.list [encInt x, encInt y]) (encInt (x + y))
    (linIntBinaryCost (Val.list [encInt x, encInt y]).wt)
  sub : ∀ x y : ℤ, FunDet P (b + 12) (.list [encInt x, encInt y]) (encInt (x - y))
    (linIntBinaryCost (Val.list [encInt x, encInt y]).wt)
  mul : ∀ x y : ℤ, FunDet P (b + 13) (.list [encInt x, encInt y]) (encInt (x * y))
    (linIntBinaryCost (Val.list [encInt x, encInt y]).wt)
  quo : ∀ x y : ℤ, FunDet P (b + 14) (.list [encInt x, encInt y]) (encInt (x / y))
    (linIntBinaryCost (Val.list [encInt x, encInt y]).wt)
  rem : ∀ x y : ℤ, FunDet P (b + 15) (.list [encInt x, encInt y]) (encInt (x % y))
    (linIntBinaryCost (Val.list [encInt x, encInt y]).wt)
  lt : ∀ x y : ℤ, FunDet P (b + 16) (.list [encInt x, encInt y]) (.nat (if x < y then 1 else 0))
    (linIntBinaryCost (Val.list [encInt x, encInt y]).wt)
  sign : ∀ x : ℤ, FunDet P (b + 17) (encInt x) (encInt x.sign) (10000 * ((encInt x).wt + 1) ^ 2)

set_option maxHeartbeats 2000000 in
/-- Installing the concrete bodies proves all public specs, without adding an oracle. -/
theorem linInt_spec {P : Program} {b : ℕ} (h : P.HasAt b (linIntFuns b)) : linIntSpec P b := by
  have h0 := h 0 (by simp [linIntFuns])
  have h1 := h 1 (by simp [linIntFuns])
  have h2 := h 2 (by simp [linIntFuns])
  have h3 := h 3 (by simp [linIntFuns])
  have h4 := h 4 (by simp [linIntFuns])
  have h5 := h 5 (by simp [linIntFuns])
  have h6 := h 6 (by simp [linIntFuns])
  have h7 := h 7 (by simp [linIntFuns])
  have h8 := h 8 (by simp [linIntFuns])
  have h9 := h 9 (by simp [linIntFuns])
  have h10 := h 10 (by simp [linIntFuns])
  have h11 := h 11 (by simp [linIntFuns])
  have h12 := h 12 (by simp [linIntFuns])
  have h13 := h 13 (by simp [linIntFuns])
  have h14 := h 14 (by simp [linIntFuns])
  have h15 := h 15 (by simp [linIntFuns])
  have h16 := h 16 (by simp [linIntFuns])
  have h17 := h 17 (by simp [linIntFuns])
  exact ⟨fun x y => linIntAdd_spec h11 h2 h0 h3 h1 h5 h4 x y,
    fun x y => linIntSub_spec h12 h2 h0 h3 h1 h6 h4 x y,
    fun x y => linIntMul_spec h13 h2 h0 h3 h1 h7 h4 x y,
    fun x y => linIntDiv_spec h14 h2 h0 h3 h1 h8 x y,
    fun x y => linIntMod_spec h15 h2 h0 h3 h1 h9 x y,
    fun x y => linIntCompare_spec h16 h2 h0 h10 x y,
    fun x => linIntSign_spec h17 x⟩

/-- Run both Euclidean operations and return [quotient,remainder]. -/
def linIntDivModF (d m : ℕ) : Expr := mk2 (.call d (.var 0)) (.call m (.var 0))

def linIntDivModCost (W : ℕ) : ℕ := 100 * (linIntBinaryCost W + W + 1)

/-- Quotient and remainder, with their exact encoded values. -/
theorem linIntDivMod_spec {P : Program} {b f : ℕ} (h : linIntSpec P b)
    (hf : P.funs[f]? = some (linIntDivModF (b + 14) (b + 15))) (x y : ℤ) :
    FunDet P f (.list [encInt x, encInt y]) (.list [encInt (x / y), encInt (x % y)])
      (linIntDivModCost (Val.list [encInt x, encInt y]).wt) := by
  have da := Det.var' (P := P) (env := [.list [encInt x, encInt y]]) (i := 0) rfl
  have dq := Det.call da (h.quo x y)
  have dr := Det.call da (h.rem x y)
  apply FunDet.intro hf
  refine (Det.mk2 dq dr).mono ?_
  have wq := (h.quo x y).wt_lt
  have wr := (h.rem x y).wt_lt
  have wo := wt_list2_le (encInt (x / y)) (encInt (x % y))
  unfold linIntDivModCost
  omega

/-- The returned numbers obey the Euclidean identity and remainder bounds. -/
theorem linIntDivMod_law (x y : ℤ) :
    y * (x / y) + x % y = x ∧ (y ≠ 0 → 0 ≤ x % y ∧ x % y < y.natAbs) :=
  ⟨Int.mul_ediv_add_emod x y, fun hy => ⟨Int.emod_nonneg x hy, Int.emod_lt x hy⟩⟩

/-- Zero in encInt is exactly the empty magnitude bit list. -/
theorem linIntBits_zero_iff (z : ℤ) : z.natAbs.bits.length = 0 ↔ z = 0 := by
  rw [← linLenBits, GI.Machine.len_eq_zero, Int.natAbs_eq_zero]

/-- Return 0 for failed exact division, or [1,quotient] for a successful division. -/
def linIntExactF (d m : ℕ) : Expr :=
  .letE (.call m (.var 0))
    (.ite (.length (.get (.var 1) (.nat 1))) (.nat 0) (mk2 (.nat 1) (.call d (.var 0))))

/-- Exact division tests divisibility, including the zero-divisor convention. -/
theorem linIntExact_spec {P : Program} {b f : ℕ} (h : linIntSpec P b)
    (hf : P.funs[f]? = some (linIntExactF (b + 14) (b + 15))) (x y : ℤ) :
    FunDet P f (.list [encInt x, encInt y])
      (if y ∣ x then .list [.nat 1, encInt (x / y)] else .nat 0)
      (linIntDivModCost (Val.list [encInt x, encInt y]).wt) := by
  have da := Det.var' (P := P) (env := [.list [encInt x, encInt y]]) (i := 0) rfl
  have dm := Det.call da (h.rem x y)
  have dl := Det.length (Det.get'
    (Det.var' (P := P) (env := [.list [encInt x, encInt y], encInt (x % y)]) (i := 1) rfl)
    (Det.nat 1) (show [Val.nat (if x % y < 0 then 1 else 0), linBitsVal (x % y).natAbs.bits][1]? =
      some (linBitsVal (x % y).natAbs.bits) from rfl))
  have dq := Det.call (Det.var' (P := P)
    (env := [.list [encInt x, encInt y], encInt (x % y)]) (i := 0) rfl) (h.quo x y)
  have dc := linDetIte dl (Det.nat 0) (Det.mk2 (Det.nat 1) dq)
  have hz : (x % y).natAbs.bits.length = 0 ↔ y ∣ x := by
    rw [linIntBits_zero_iff, Int.dvd_iff_emod_eq_zero]
  simp only [List.length_map, hz] at dc
  apply FunDet.intro hf
  refine (Det.letE dm dc).mono ?_
  have wq := (h.quo x y).wt_lt
  have wr := (h.rem x y).wt_lt
  have wbits := wt_le_wt_list
    (vs := [.nat (if x % y < 0 then 1 else 0), linBitsVal (x % y).natAbs.bits])
    (v := linBitsVal (x % y).natAbs.bits) (by simp)
  have hlen := length_lt_wt_list ((x % y).natAbs.bits.map fun b => Val.nat (linBit b))
  have wo := wt_list2_le (.nat 1) (encInt (x / y))
  have w0 : (Val.nat 0).wt = 2 := rfl
  have w1 : (Val.nat 1).wt = 3 := rfl
  have hwe : (Val.list [.nat (if x % y < 0 then 1 else 0), linBitsVal (x % y).natAbs.bits]).wt =
      (encInt (x % y)).wt := rfl
  rw [hwe] at wbits
  simp only [List.length_map] at hlen ⊢
  unfold linIntDivModCost
  have hbits : (Val.list ((x % y).natAbs.bits.map fun b => Val.nat (linBit b))).wt =
      (linBitsVal (x % y).natAbs.bits).wt := rfl
  rw [hbits] at hlen
  simp only [linBitsVal, linBit, encInt] at *
  by_cases hdiv : y ∣ x
  · simp only [if_pos hdiv]; omega
  · simp only [if_neg hdiv]; omega

/-- A successful exact division supplies an actual integer solution. -/
theorem linIntExact_law (x y : ℤ) (h : y ∣ x) : (x / y) * y = x := Int.ediv_mul_cancel h

end GI.Lang
