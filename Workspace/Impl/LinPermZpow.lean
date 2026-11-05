module

public import Workspace.Impl.LinPermPow
public import Workspace.Lang.Lib.LinIntCodec
public import Workspace.Impl.GenNormPoly

@[expose] public section

/-! Signed binary permutation powers for lifting integer-coordinate
solutions back to the permutation cover. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linPermZpowF (decode inv power : ℕ) : Expr :=
  .letE (.call decode (arg 1))
    (.letE (.ite (.get (.var 1) (.nat 1)) (.call inv (arg 0)) (arg 0))
      (.call power (mk3 (.var 2)
        (.arith .add (.get (.var 1) (.nat 0)) (.get (.var 1) (.nat 1))) (arg 2))))

def linPermZpowFuns (b : ℕ) : List Expr :=
  [linPermZpowF (b + 1) (b + 8) (b + 3), linIntDecodeF (b + 2),
    linBitsDecodeF (b + 2), linPermPowF (b + 3) (b + 4)] ++
    composeFuns (b + 4) ++ invFuns (b + 8)

theorem linPermZpowFuns_length (b : ℕ) : (linPermZpowFuns b).length = 20 := rfl

structure linPermZpowAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linPermZpowF (b + 1) (b + 8) (b + 3))
  decode : P.funs[b + 1]? = some (linIntDecodeF (b + 2))
  bits : P.funs[b + 2]? = some (linBitsDecodeF (b + 2))
  power : P.funs[b + 3]? = some (linPermPowF (b + 3) (b + 4))
  comp : P.HasAt (b + 4) (composeFuns (b + 4))
  inv : P.HasAt (b + 8) (invFuns (b + 8))

theorem linPermZpowAt_of {P : Program} {b : ℕ} (h : P.HasAt b (linPermZpowFuns b)) :
    linPermZpowAt P b where
  entry := (h.block (gs := [linPermZpowF (b + 1) (b + 8) (b + 3)]) 0 rfl).single
  decode := (h.block (gs := [linIntDecodeF (b + 2)]) 1 rfl).single
  bits := (h.block (gs := [linBitsDecodeF (b + 2)]) 2 rfl).single
  power := (h.block (gs := [linPermPowF (b + 3) (b + 4)]) 3 rfl).single
  comp := h.block 4 rfl
  inv := h.block 8 rfl

theorem linPermZpow_value {G : Type*} [Group G] (a : G) (z : ℤ) :
    (if (-z).toNat = 0 then a else a⁻¹) ^ z.natAbs = a ^ z := by
  cases z with
  | ofNat n => simp
  | negSucc n => simp [zpow_negSucc, inv_pow]

def linPermZpowCost (W : ℕ) : ℕ :=
  1000000 * (W + linIntCodecCost W + linPermPowCost W W + invK * (W + 1) ^ 4 + 1)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 5000 in
theorem linPermZpow_spec {P : Program} {b n : ℕ} (h : linPermZpowAt P b)
    (a r : Equiv.Perm (Fin n)) (z : ℤ) :
    let input := Val.list [encPerm a, encInt z, encPerm r]
    FunDet P b input (encPerm (a ^ z * r)) (linPermZpowCost input.wt) := by
  let input := Val.list [encPerm a, encInt z, encPerm r]
  let W := input.wt
  let parts := linIntParts z
  let base := if (-z).toNat = 0 then a else a⁻¹
  let CB := linIntCodecCost W
  let IB := invK * (W + 1) ^ 4
  let PB := linPermPowCost W W
  have wa : (encPerm a).wt < W := wt_le_wt_list (by simp [input, W])
  have wz : (encInt z).wt < W := wt_le_wt_list (by simp [input, W])
  have wr : (encPerm r).wt < W := wt_le_wt_list (by simp [input, W])
  have hn : n ≤ W := by
    have hh := length_lt_wt_list ((List.finRange n).map fun i => Val.nat (a i))
    simp only [List.length_map, List.length_finRange] at hh
    change n < (encPerm a).wt at hh
    omega
  have hL : z.natAbs.bits.length ≤ W := by
    have hh := length_lt_wt_list (z.natAbs.bits.map fun b => Val.nat (linBit b))
    have hzv : encInt z = .list [.nat (if z < 0 then 1 else 0), linBitsVal z.natAbs.bits] := rfl
    have hb : (linBitsVal z.natAbs.bits).wt < (encInt z).wt := by
      rw [hzv]
      exact wt_le_wt_list (by simp)
    simp only [List.length_map] at hh
    change z.natAbs.bits.length < (linBitsVal z.natAbs.bits).wt at hh
    omega
  have hdec := (linIntDecode_spec h.decode h.bits z).mono
    (show linIntCodecCost (encInt z).wt ≤ CB from by
      unfold linIntCodecCost CB
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right wz.le 1) 3))
  have wparts : parts.wt ≤ CB := hdec.wt_lt.le
  have hi := (inv_spec h.inv a).mono
    (show invK * (n + 1) ^ 4 ≤ IB from Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 4))
  have winv : (encPerm a⁻¹).wt ≤ IB := hi.wt_lt.le
  have hp := (linPermPow_spec h.power h.comp z.natAbs base r).mono
    (show linPermPowCost n z.natAbs.bits.length ≤ PB from by
      unfold PB linPermPowCost linPermPowUnit
      gcongr)
  have wout : (encPerm (base ^ z.natAbs * r)).wt ≤ PB := hp.wt_lt.le
  have dc := Det.call (Det.arg' (P := P) (vs := [encPerm a, encInt z, encPerm r])
    (rest := []) (j := 1) rfl) hdec
  have dparts := Det.var' (P := P) (env := [input, parts]) (i := 1) rfl
  have dneg := Det.get' dparts (Det.nat 1) rfl
  have da := Det.arg' (P := P) (vs := [encPerm a, encInt z, encPerm r])
    (rest := [parts]) (j := 0) rfl
  have dinv := Det.call da hi
  have dbase := Det.ite' dneg dinv da
  have he : (if (-z).toNat = 0 then encPerm a else encPerm a⁻¹) = encPerm base := by
    by_cases hz : (-z).toNat = 0 <;> simp [base, hz]
  rw [he] at dbase
  have dp := Det.var' (P := P) (env := [input, parts, encPerm base]) (i := 1) rfl
  have dpos := Det.get' dp (Det.nat 0) rfl
  have dneg' := Det.get' dp (Det.nat 1) rfl
  have dabs := Det.arith (op := .add) dpos dneg'
  simp only [GI.Machine.BinOp.eval_add, ← linIntAbsParts] at dabs
  have db := Det.var' (P := P) (env := [input, parts, encPerm base]) (i := 2) rfl
  have dr := Det.arg' (P := P) (vs := [encPerm a, encInt z, encPerm r])
    (rest := [parts, encPerm base]) (j := 2) rfl
  have dpow := Det.call (Det.mk3 db dabs dr) hp
  have result := Det.letE dc (Det.letE dbase dpow)
  have hbase : base ^ z.natAbs = a ^ z := linPermZpow_value a z
  rw [hbase] at result
  rw [hbase] at wout
  have hmval : max (encPerm a⁻¹).wt (encPerm a).wt ≤ W + IB := max_le (by omega) (by omega)
  have hmcost : max (2 * W + 0 + 5 + IB + (encPerm a⁻¹).wt + 1)
      (2 * W + 0 + 5) ≤ 100 * (W + IB + 1) := max_le (by omega) (by omega)
  have wbase : (encPerm base).wt ≤ W + IB := by
    by_cases hz : (-z).toNat = 0 <;> simp only [base, hz, if_true, if_false] <;> omega
  have wpos : (Val.nat z.toNat).wt < parts.wt := wt_le_wt_list (by simp [parts, linIntParts])
  have wneg : (Val.nat (-z).toNat).wt < parts.wt := wt_le_wt_list (by simp [parts, linIntParts])
  have wabs : (Val.nat z.natAbs).wt ≤ W + 2 := by
    rw [wt_nat, linLenBits]
    omega
  have wargs := wt_list3_le (encPerm base) (.nat z.natAbs) (encPerm r)
  apply FunDet.intro h.entry
  refine result.mono ?_
  change _ ≤ linPermZpowCost W
  unfold linPermZpowCost
  dsimp only [input, W, CB, IB, PB, parts, linIntParts] at *
  omega

theorem linPermZpowCost_poly : PBU (fun _ W _ => linPermZpowCost W) := by
  simp only [linPermZpowCost, linIntCodecCost, linPermPowCost, linPermPowUnit]
  norm_poly

end GI.Impl
