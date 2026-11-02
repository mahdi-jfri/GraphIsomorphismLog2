import Workspace.Impl.LinTrialExponent

/-! Return a primary exponent and the corresponding signed cyclic order.
Both the original order and its bit length bound the computation. -/
namespace GI.Impl
open GI.Cited GI.Lang
open GI.Machine (len len_mono)

def linTrialFactorF (exponent power encode : ℕ) : Expr :=
  .letE (.call exponent (.var 0))
    (.letE (.call power (mk2 (arg 0) (.var 1)))
      (.letE (.call encode (mk2 (.var 2) (.nat 0))) (mk2 (.var 1) (.var 3))))

def linTrialFactorFuns (b : ℕ) : List Expr :=
  [linTrialFactorF (b + 1) (b + 23) (b + 5)] ++
    linTrialExponentFuns (b + 1) ++ linNatPowerFuns (b + 23)

theorem linTrialFactorFuns_length (b : ℕ) : (linTrialFactorFuns b).length = 26 := rfl

structure linTrialFactorAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linTrialFactorF (b + 1) (b + 23) (b + 5))
  exponent : linTrialExponentAt P (b + 1)
  power : P.HasAt (b + 23) (linNatPowerFuns (b + 23))

theorem linTrialFactorAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linTrialFactorFuns b)) : linTrialFactorAt P b where
  entry := (h.block (gs := [linTrialFactorF (b + 1) (b + 23) (b + 5)]) 0 rfl).single
  exponent := linTrialExponentAt_of (h.block 1 rfl)
  power := h.block 23 rfl

def linTrialFactorPower (W : ℕ) : ℕ := linNatPowerCost (100 * (W + 1)) W

def linTrialFactorEncode (W : ℕ) : ℕ := linIntCodecCost (100 * (W + 1))

def linTrialFactorCost (W : ℕ) : ℕ := 100000 *
  (W + linTrialExponentCost W + linTrialFactorPower W + linTrialFactorEncode W + 1)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 6000 in
theorem linTrialFactor_spec {P : Program} {b : ℕ} (h : linTrialFactorAt P b)
    (p n : ℕ) (hp : p.Prime) (hn : 0 < n) :
    let e := (linTrialPrimary p n (len n)).1
    FunDet P b (.list [.nat p, encInt (n : ℤ)])
      (.list [.nat e, encInt (p ^ e : ℤ)])
      (linTrialFactorCost (Val.list [.nat p, encInt (n : ℤ)]).wt) := by
  let a := Val.list [.nat p, encInt (n : ℤ)]
  let W := a.wt
  let e := (linTrialPrimary p n (len n)).1
  let q := p ^ e
  have wn : (encInt (n : ℤ)).wt < W := wt_le_wt_list (by simp [a, W])
  have wp : (Val.nat p).wt < W := wt_le_wt_list (by simp [a, W])
  have hl : len n ≤ W := by
    have hh := linEncIntAbs (n : ℤ)
    simp only [Int.natAbs_natCast] at hh
    exact (GI.Machine.len_le_iff.mpr hh).trans wn.le
  have he : e ≤ W := (linTrialPrimary_terminal p n hp hn).2.2.trans hl
  have hq : q ≤ n := by
    obtain ⟨hf, hpos, _, _⟩ := linTrialPrimary_invariant p n hp.two_le hn (len n)
    exact hf ▸ Nat.le_mul_of_pos_right _ hpos
  have we : (Val.nat e).wt ≤ W + 2 := (wt_nat_le e).trans (by omega)
  have wq : (Val.nat q).wt ≤ W + 2 := by
    rw [wt_nat]
    have hh := len_mono hq
    omega
  have wae : (Val.list [.nat p, .nat e]).wt ≤ 100 * (W + 1) := by
    have hh := wt_list2_le (.nat p) (.nat e)
    omega
  have waq : (linIntParts (q : ℤ)).wt ≤ 100 * (W + 1) := by
    have hh := wt_list2_le (.nat q) (.nat 0)
    have hz : (Val.nat 0).wt = 2 := rfl
    simpa only [linIntParts, Int.toNat_natCast, Int.toNat_neg_natCast] using
      (show (Val.list [.nat q, .nat 0]).wt ≤ 100 * (W + 1) by omega)
  have hexp := linTrialExponent_spec h.exponent p n hp hn
  have hpow := (linNatPower_spec h.power p e).mono (show
    linNatPowerCost (Val.list [.nat p, .nat e]).wt e ≤ linTrialFactorPower W by
      unfold linTrialFactorPower linNatPowerCost
      gcongr)
  have henc := (linIntEncode_spec
    (h.exponent.codec 3 (by simp [linIntFuns]))
    (h.exponent.codec 1 (by simp [linIntFuns])) (q : ℤ)).mono (linIntCodecCost_mono waq)
  have wexp := hexp.wt_lt.le
  have wpow := hpow.wt_lt.le
  have wenc := henc.wt_lt.le
  have de := Det.call (Det.var' (P := P) (env := [a]) (i := 0) rfl) hexp
  have dp := Det.arg' (P := P) (vs := [.nat p, encInt (n : ℤ)]) (rest := [.nat e]) (j := 0) rfl
  have dev := Det.var' (P := P) (env := [a, .nat e]) (i := 1) rfl
  have dq := Det.call (Det.mk2 dp dev) hpow
  have dqv := Det.var' (P := P) (env := [a, .nat e, .nat q]) (i := 2) rfl
  have dcarg := Det.mk2 dqv (Det.nat 0)
  have hparts : linIntParts (q : ℤ) = .list [.nat q, .nat 0] := by
    simp [linIntParts]
  have dcarg' := dcarg
  rw [← hparts] at dcarg'
  have dc := Det.call dcarg' henc
  have dout := Det.mk2
    (Det.var' (P := P) (env := [a, .nat e, .nat q, encInt (q : ℤ)]) (i := 1) rfl)
    (Det.var' (P := P) (env := [a, .nat e, .nat q, encInt (q : ℤ)]) (i := 3) rfl)
  apply FunDet.intro h.entry
  refine (Det.letE de (Det.letE dq (Det.letE dc dout))).mono ?_
  have wout := wt_list2_le (.nat e) (encInt (q : ℤ))
  have wpa := wt_list2_le (.nat p) (.nat e)
  have wca := wt_list2_le (.nat q) (.nat 0)
  have hz : (Val.nat 0).wt = 2 := rfl
  change _ ≤ linTrialFactorCost W
  unfold linTrialFactorCost
  dsimp only [a, W, e, q, linTrialFactorPower, linTrialFactorEncode, linIntParts] at *
  omega

theorem linTrialFactorCost_mono {W V : ℕ} (h : W ≤ V) :
    linTrialFactorCost W ≤ linTrialFactorCost V := by
  unfold linTrialFactorCost linTrialExponentCost linTrialExponentBudget linTrialExponentArg
    linTrialFactorPower linTrialFactorEncode linNatPowerCost linTrialPrimaryCost linIntCodecCost
  gcongr

theorem linTrialFactorCost_poly : PBU (fun _ W _ => linTrialFactorCost W) := by
  unfold linTrialFactorCost linTrialExponentCost linTrialExponentBudget linTrialExponentArg
    linTrialFactorPower linTrialFactorEncode linNatPowerCost linTrialPrimaryCost linIntCodecCost
  norm_poly

end GI.Impl
