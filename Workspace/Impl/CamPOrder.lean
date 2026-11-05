module

public import Workspace.Impl.SmallZ

@[expose] public section

/-!
# Step 1 of `camProg`: the order test

`camSmallFuns b` (seven functions) decides, on `[o, n]`, whether `o < n^(1 + ⌊log₂ n⌋)`. This is
the test of the answer `[0]` of `CameronRecognitionTask` (Maróti's case (iii)). It reuses the two
loops of the integer small test (`Workspace/Impl/SmallZ.lean`): `log2Funs` gives `⌊log₂ n⌋`, and
`powFuns` gives `min(n^e, o + 1)` for `e = 1 + ⌊log₂ n⌋`. Then `o < n^e` exactly when
`o < min(n^e, o + 1)`.
-/

namespace GI.Lang

open GI.Machine (BinOp len len_mono len_mul_le len_le_self)
open GI.Cited (Val)

/-- `o < n^e` exactly when `o < min(n^e, o + 1)`. -/
theorem cam_lt_iff_lt_min (o x : ℕ) : o < x ↔ o < min x (o + 1) := by
  constructor
  · intro h; exact lt_min h (Nat.lt_succ_self o)
  · intro h; exact lt_of_lt_of_le h (min_le_left _ _)

/-- The body of the order test, at base `b`. -/
def camSmallBody (b : ℕ) : Expr :=
  .letE (.call (b + 1) (.get (.var 0) (.nat 1)))
    (.letE (.call (b + 4) (mk3 (.get (.var 0) (.nat 0)) (.get (.var 0) (.nat 1))
        (.arith .add (.nat 1) (.get (.var 1) (.nat 0)))))
      (.arith .lt (.get (.var 0) (.nat 0)) (.var 2)))

/-- **The order test**, at base `b` (seven functions). -/
def camSmallFuns (b : ℕ) : List Expr := [camSmallBody b] ++ log2Funs (b + 1) ++ powFuns (b + 4)

/-- The constant of the order test. -/
def camSmallK : ℕ := 100000

/-- **The order test.** On `[o, n]` it returns `1` if `o < n^(1 + ⌊log₂ n⌋)` and `0` otherwise, at
cost at most `camSmallK X²` with `X = wt [o, n] + 2n + 11`. -/
theorem camSmall_spec {P : Program} {b : ℕ} (h : P.HasAt b (camSmallFuns b)) (ord d : ℕ) :
    FunDet P b (.list [.nat ord, .nat d]) (boolVal (decide (ord < d ^ (1 + Nat.log 2 d))))
      (camSmallK * ((Val.list [.nat ord, .nat d]).wt + 2 * d + 11) ^ 2) := by
  simp only [camSmallFuns] at h
  have hbody : P.funs[b]? = some (camSmallBody b) := h.left.left.single
  have hlog : P.HasAt (b + 1) (log2Funs (b + 1)) := h.left.right
  have hpow : P.HasAt (b + 4) (powFuns (b + 4)) := by
    have := h.right; simpa [log2Funs, loopFuns, Nat.add_assoc] using this
  set x := Val.list [.nat ord, .nat d] with hx
  obtain ⟨L, hLd⟩ : ∃ L, Nat.log 2 d = L := ⟨_, rfl⟩
  rw [hLd]
  set m := min (d ^ (1 + L)) (ord + 1)
  have dX := Det.var' (P := P) (env := [x]) (i := 0) rfl
  have dDd := Det.get' dX (Det.nat 1) (show [Val.nat ord, .nat d][1]? = some (.nat d) from rfl)
  have dLog := Det.call dDd (log2_spec hlog d)
  rw [hLd] at dLog
  have dX2 := Det.var' (P := P) (env := [x, .list [.nat L, .nat (2 ^ L)]]) (i := 0) rfl
  have dO2 := Det.get' dX2 (Det.nat 0) (show [Val.nat ord, .nat d][0]? = some (.nat ord) from rfl)
  have dD2 := Det.get' dX2 (Det.nat 1) (show [Val.nat ord, .nat d][1]? = some (.nat d) from rfl)
  have dLg := Det.var' (P := P) (env := [x, .list [.nat L, .nat (2 ^ L)]]) (i := 1) rfl
  have dL := Det.get' dLg (Det.nat 0) (show [Val.nat L, .nat (2 ^ L)][0]? = some (.nat L) from rfl)
  have dE := Det.arith' (op := .add) (Det.nat 1) dL rfl
  have dArg := Det.mk3 dO2 dD2 dE
  have dPow := Det.call dArg (pow_spec hpow ord d (1 + L))
  have dX3 := Det.var' (P := P) (env := [x, .list [.nat L, .nat (2 ^ L)], .nat m]) (i := 0) rfl
  have dO3 := Det.get' dX3 (Det.nat 0) (show [Val.nat ord, .nat d][0]? = some (.nat ord) from rfl)
  have dM := Det.var' (P := P) (env := [x, .list [.nat L, .nat (2 ^ L)], .nat m]) (i := 2) rfl
  have dT := Det.arith (op := .lt) dO3 dM
  have hval : Val.nat (BinOp.eval .lt ord m) = boolVal (decide (ord < d ^ (1 + L))) := by
    simp only [BinOp.eval, boolVal]
    by_cases hle : ord < d ^ (1 + L)
    · rw [if_pos ((cam_lt_iff_lt_min ord _).1 hle), decide_eq_true hle]; rfl
    · rw [if_neg (fun h' => hle ((cam_lt_iff_lt_min ord _).2 h')), decide_eq_false hle]; rfl
  rw [← hval]
  refine FunDet.intro hbody ((Det.letE dLog (Det.letE dPow dT)).mono ?_)
  clear h hbody hlog hpow dX dDd dLog dX2 dO2 dD2 dLg dL dE dArg dPow dX3 dO3 dM dT hval
  have hm1 : m ≤ ord + 1 := min_le_right _ _
  clear_value m
  have hW := x.two_le_size
  have hW' := x.size_le_wt
  have hwd : (Val.nat d).wt < x.wt := wt_le_wt_list (by simp)
  have hwo : (Val.nat ord).wt < x.wt := wt_le_wt_list (by simp)
  have hL : L ≤ d := hLd ▸ Nat.log_le_self 2 d
  have hlg : (Val.list [Val.nat L, Val.nat (2 ^ L)]).wt ≤ 4 * (Val.nat d).wt + 20 := by
    have := wt_log2Acc_le d (d + 4); rwa [log2Acc_final, hLd] at this
  have hwL := wt_nat_le L
  have hw3 := wt_list3_le (Val.nat ord) (Val.nat d) (Val.nat (1 + L))
  have hwe := wt_nat_le (1 + L)
  have lo1 := GI.Machine.len_add_le ord 1
  have lm := len_mono hm1
  have lm2 := len_mono (min_le_right (d ^ (1 + L)) (ord + 1))
  have hl1 : len 1 = 1 := rfl
  have wlt : ∀ y z, (Val.nat (BinOp.eval .lt y z)).wt ≤ 3 := fun y z => by
    simp only [BinOp.eval]; split <;> decide
  have w1 := wlt ord m
  simp only [BinOp.eval, wt_nat] at hwd hwo hwL hwe w1 hw3 hlg ⊢
  have hEL : 1 + L ≤ d + 1 := by omega
  generalize 1 + L = E at *
  set X := x.wt + 2 * d + 11 with hX
  clear_value X
  have hlogc : 1000 * (d + 5) * (5 * (len d + 2) + d + 25) ≤ 5000 * X ^ 2 := by
    have h1 : d + 5 ≤ X := by omega
    have h2 : 5 * (len d + 2) + d + 25 ≤ 5 * X := by omega
    calc 1000 * (d + 5) * (5 * (len d + 2) + d + 25) ≤ 1000 * X * (5 * X) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
      _ = 5000 * X ^ 2 := by ring
  have hpowc : 1000 * (E + 1) * ((Val.list [Val.nat ord, Val.nat d, Val.nat E]).wt + E +
      (len (ord + 1) + 2) + 1) ≤ 6000 * X ^ 2 := by
    have h1 : E + 1 ≤ X := by omega
    have h2 : (Val.list [Val.nat ord, Val.nat d, Val.nat E]).wt + E +
        (len (ord + 1) + 2) + 1 ≤ 6 * X := by omega
    calc _ ≤ 1000 * X * (6 * X) := Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
      _ = 6000 * X ^ 2 := by ring
  have hX10 : 10 ≤ X := by omega
  have hXX : 10 * X ≤ X ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right X hX10
  simp only [loopModK, camSmallK] at *
  generalize X ^ 2 = Y at *
  generalize (Val.list [Val.nat ord, Val.nat d, Val.nat E]).wt = Z at *
  obtain ⟨P1, hP1⟩ : ∃ P1, 1000 * (d + 5) * (5 * (len d + 2) + d + 25) = P1 := ⟨_, rfl⟩
  obtain ⟨P2, hP2⟩ : ∃ P2, 1000 * (E + 1) * (Z + E + (len (ord + 1) + 2) + 1) = P2 := ⟨_, rfl⟩
  rw [hP1] at hlogc ⊢
  rw [hP2] at hpowc ⊢
  clear hP1 hP2
  omega

end GI.Lang
