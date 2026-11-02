import Workspace.Impl.LinTrialPrimaryProg
import Workspace.Impl.LinPrimaryDigit

/-! Extract the primary exponent from a positive signed cyclic order. -/
namespace GI.Impl
open GI.Cited GI.Lang
open GI.Machine (len)

def linTrialExponentF (decode trial : ℕ) : Expr :=
  .letE (.call decode (arg 1))
    (.get (.call trial (mk3 (arg 0) (.get (.var 1) (.nat 0))
      (.length (.get (arg 1) (.nat 1))))) (.nat 0))

def linTrialExponentFuns (b : ℕ) : List Expr :=
  [linTrialExponentF (b + 3) (b + 19)] ++ linIntFuns (b + 1) ++ linTrialPrimaryFuns (b + 19)

theorem linTrialExponentFuns_length (b : ℕ) : (linTrialExponentFuns b).length = 22 := rfl

structure linTrialExponentAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linTrialExponentF (b + 3) (b + 19))
  codec : P.HasAt (b + 1) (linIntFuns (b + 1))
  trial : P.HasAt (b + 19) (linTrialPrimaryFuns (b + 19))

theorem linTrialExponentAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linTrialExponentFuns b)) : linTrialExponentAt P b where
  entry := (h.block (gs := [linTrialExponentF (b + 3) (b + 19)]) 0 rfl).single
  codec := h.block 1 rfl
  trial := h.block 19 rfl

def linTrialExponentArg (W : ℕ) : ℕ := 100 * (W + linIntCodecCost W + 1)
def linTrialExponentBudget (W : ℕ) : ℕ := linTrialPrimaryCost (linTrialExponentArg W) W

def linTrialExponentCost (W : ℕ) : ℕ :=
  100000 * (W + linIntCodecCost W + linTrialExponentBudget W + 1)

theorem linTrialExponentCost_mono {W V : ℕ} (h : W ≤ V) :
    linTrialExponentCost W ≤ linTrialExponentCost V := by
  unfold linTrialExponentCost linTrialExponentBudget linTrialExponentArg linTrialPrimaryCost linIntCodecCost
  gcongr

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 5000 in
theorem linTrialExponent_spec {P : Program} {b : ℕ} (h : linTrialExponentAt P b)
    (p n : ℕ) (hp : p.Prime) (hn : 0 < n) :
    FunDet P b (.list [.nat p, encInt (n : ℤ)])
      (.nat (linTrialPrimary p n (len n)).1)
      (linTrialExponentCost (Val.list [.nat p, encInt (n : ℤ)]).wt) := by
  let a := Val.list [.nat p, encInt (n : ℤ)]
  let W := a.wt
  let parts := linIntParts (n : ℤ)
  let z := linTrialPrimary p n (len n)
  have wn : (encInt (n : ℤ)).wt < W := wt_le_wt_list (by simp [a, W])
  have wp : (Val.nat p).wt < W := wt_le_wt_list (by simp [a, W])
  have hl : len n ≤ W := by
    have hh := linEncIntAbs (n : ℤ)
    simp only [Int.natAbs_natCast] at hh
    exact (GI.Machine.len_le_iff.mpr hh).trans wn.le
  have hdecode := (linIntDecode_spec
    (h.codec 2 (by simp [linIntFuns])) (h.codec 0 (by simp [linIntFuns])) (n : ℤ)).mono
    (linIntCodecCost_mono wn.le)
  have wparts : parts.wt ≤ linIntCodecCost W := hdecode.wt_lt.le
  have wnum : (Val.nat n).wt < parts.wt := wt_le_wt_list (by simp [parts, linIntParts])
  have wlen := wt_nat_le (len n)
  have warg : (Val.list [.nat p, .nat n, .nat (len n)]).wt ≤ linTrialExponentArg W := by
    have hh := wt_list3_le (.nat p) (.nat n) (.nat (len n))
    unfold linTrialExponentArg
    omega
  have htrial := (linTrialPrimaryProg_spec h.trial p n (len n) hp.two_le hn).mono (show
    linTrialPrimaryCost (Val.list [.nat p, .nat n, .nat (len n)]).wt (len n) ≤
      linTrialExponentBudget W by
    unfold linTrialExponentBudget linTrialPrimaryCost
    gcongr)
  have wz : (linTrialPrimaryVal z).wt ≤ linTrialExponentBudget W := htrial.wt_lt.le
  have we : (Val.nat z.1).wt < (linTrialPrimaryVal z).wt :=
    wt_le_wt_list (by simp [linTrialPrimaryVal])
  have dn := Det.arg' (P := P) (vs := [.nat p, encInt (n : ℤ)]) (rest := []) (j := 1) rfl
  have dd := Det.call dn hdecode
  have dp := Det.arg' (P := P) (vs := [.nat p, encInt (n : ℤ)]) (rest := [parts]) (j := 0) rfl
  have dv := Det.get' (Det.var' (P := P) (env := [a, parts]) (i := 1) rfl)
    (Det.nat 0) (v := .nat n) (by simp [parts, linIntParts])
  have db := Det.get' (Det.arg' (P := P) (vs := [.nat p, encInt (n : ℤ)])
    (rest := [parts]) (j := 1) rfl) (Det.nat 1) rfl
  have dl := Det.length db
  simp only [List.length_map, ← linLenBits, Int.natAbs_natCast] at dl
  have dt := Det.call (Det.mk3 dp dv dl) htrial
  have dout := Det.get' dt (Det.nat 0) rfl
  apply FunDet.intro h.entry
  refine (Det.letE dd dout).mono ?_
  have wi := wt_list3_le (.nat p) (.nat n) (.nat (len n))
  have wbits := wt_le_wt_list (vs := [.nat 0, linBitsVal n.bits])
    (v := linBitsVal n.bits) (by simp)
  change (linBitsVal n.bits).wt < (encInt (n : ℤ)).wt at wbits
  change _ ≤ linTrialExponentCost W
  unfold linTrialExponentCost
  dsimp only [W, a, parts, z, linTrialExponentBudget, linIntParts, linBitsVal, linBit] at *
  omega

theorem linTrialExponentCost_poly : PBU (fun _ W _ => linTrialExponentCost W) := by
  unfold linTrialExponentCost linTrialExponentBudget linTrialExponentArg linTrialPrimaryCost linIntCodecCost
  norm_poly

end GI.Impl
