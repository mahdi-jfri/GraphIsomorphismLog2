module

public import Workspace.Impl.LinIntPoly
public import Workspace.Cited.AlgoLinear

@[expose] public section

/-! Reduce signed integer coordinates to the canonical residues required by
the vector-stabilizer task. -/
namespace GI.Impl
open GI.Cited GI.Lang

/-- Avoid natural subtraction across zero by adding the modulus first. -/
def linModNat (p : ℕ) (z : ℤ) : ℕ := (z.toNat % p + p - (-z).toNat % p) % p

theorem linModNat_spec {p : ℕ} (hp : 0 < p) (z : ℤ) : linModNat p z = (z : ZMod p).val := by
  have hle : (-z).toNat % p ≤ z.toNat % p + p := by
    have := Nat.mod_lt (-z).toNat hp
    omega
  have hc : ((linModNat p z : ℕ) : ZMod p) = z := by
    rw [linModNat, ZMod.natCast_mod, Nat.cast_sub hle, Nat.cast_add,
      ZMod.natCast_mod, ZMod.natCast_mod, ZMod.natCast_self, add_zero]
    have hh := congrArg (fun a : ℤ => (a : ZMod p)) (linIntParts_difference z)
    simpa only [Int.cast_sub, Int.cast_natCast] using hh
  have hh := congrArg ZMod.val hc
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (show linModNat p z < p from Nat.mod_lt _ hp)] at hh
  exact hh

/-- Input `[p, encInt z]`, output a natural residue. -/
def linModReduceF (decode : ℕ) : Expr :=
  .letE (.call decode (arg 1))
    (.arith .mod
      (.arith .sub (.arith .add (.arith .mod (.get (.var 1) (.nat 0)) (arg 0)) (arg 0))
        (.arith .mod (.get (.var 1) (.nat 1)) (arg 0))) (arg 0))

def linModReduceFuns (b : ℕ) : List Expr :=
  [linModReduceF (b + 3)] ++ linIntFuns (b + 1)

theorem linModReduceFuns_length (b : ℕ) : (linModReduceFuns b).length = 19 := rfl

def linModReduceCost (W : ℕ) : ℕ := 10000 * (W + linIntCodecCost W + 1)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem linModReduce_spec {P : Program} {b p : ℕ} (hp : P.HasAt b (linModReduceFuns b))
    (hpos : 0 < p) (z : ℤ) :
    FunDet P b (.list [.nat p, encInt z]) (.nat (z : ZMod p).val)
      (linModReduceCost (Val.list [.nat p, encInt z]).wt) := by
  let a := Val.list [.nat p, encInt z]
  let W := a.wt
  have hi : P.HasAt (b + 1) (linIntFuns (b + 1)) := hp.block 1 rfl
  have hd : P.funs[b + 3]? = some (linIntDecodeF (b + 1)) := hi 2 (by simp [linIntFuns])
  have hb : P.funs[b + 1]? = some (linBitsDecodeF (b + 1)) := hi 0 (by simp [linIntFuns])
  have hs := linIntDecode_spec hd hb z
  have dz := Det.call (Det.arg' (P := P) (vs := [.nat p, encInt z]) (rest := []) (j := 1) rfl) hs
  have dparts := Det.var' (P := P) (env := [a, linIntParts z]) (i := 1) rfl
  have dp := Det.arg' (P := P) (vs := [.nat p, encInt z]) (rest := [linIntParts z]) (j := 0) rfl
  have d₀ := Det.arith (op := .mod) (Det.get' dparts (Det.nat 0) rfl) dp
  have d₁ := Det.arith (op := .mod) (Det.get' dparts (Det.nat 1) rfl) dp
  have d₂ := Det.arith (op := .add) d₀ dp
  have d₃ := Det.arith (op := .sub) d₂ d₁
  have d₄ := Det.arith (op := .mod) d₃ dp
  have he := (hp.block (gs := [linModReduceF (b + 3)]) 0 rfl).single
  have wz : (encInt z).wt < W := wt_le_wt_list (by simp [a, W])
  have wp : (Val.nat p).wt < W := wt_le_wt_list (by simp [a, W])
  have wparts := hs.wt_lt.le
  have wc := linIntCodecCost_mono wz.le
  have w₀ : (Val.nat z.toNat).wt < (linIntParts z).wt := wt_le_wt_list (by simp [linIntParts])
  have w₁ : (Val.nat (-z).toNat).wt < (linIntParts z).wt := wt_le_wt_list (by simp [linIntParts])
  have wm₀ := linArithWt .mod z.toNat p
  have wm₁ := linArithWt .mod (-z).toNat p
  have wm₂ := linArithWt .add (z.toNat % p) p
  have wm₃ := linArithWt .sub (z.toNat % p + p) ((-z).toNat % p)
  have wm₄ := linArithWt .mod (z.toNat % p + p - (-z).toNat % p) p
  apply FunAll.intro he
  refine (Det.letE dz d₄).post fun cost hc => ⟨?_, ?_⟩
  · exact congrArg Val.nat (linModNat_spec hpos z)
  · change cost ≤ linModReduceCost W
    unfold linModReduceCost
    dsimp only [W, a] at *
    simp only [GI.Machine.BinOp.eval_mod, GI.Machine.BinOp.eval_add,
      GI.Machine.BinOp.eval_sub] at *
    omega

theorem linModReduceCost_poly : PBU (fun _ W _ => linModReduceCost W) := by
  unfold linModReduceCost linIntCodecCost
  norm_poly

end GI.Impl
