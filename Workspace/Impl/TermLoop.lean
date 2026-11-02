import Workspace.Impl.TermScr

/-!
# The step function of the row terminal (T1)

The script runner (`Iface.run_spec`, `ScriptRun.lean`) calls a step function on the program
state `st = [kst, u]`, where `u` is the answer of the last call and `kst` is what the step kept:
`kst = [ctx, j, aN, aH]`, with the context `ctx` of the calls (`tmCtx`), the number `j` of
answers so far, and the lists `aN`, `aH` of the answers of the `N`-tests and of the coset calls
before the last one.

`tmStepF` first adds `u` to the right list (`tmAbsN`, `tmAbsH`; nothing when `j = 0`), then

* for `j < 4q²` asks `N`-test number `j`: rows `j / 2q` and `j % 2q` under `N` (entry 3 of the
  context);
* for `4q² ≤ j < 5q²` asks coset call number `j - 4q²`: row `(j - 4q²) / q` of `x` and row
  `(j - 4q²) % q` of `y` under `H` (entry 4);
* for `j = 5q²` returns `[aN, aH]`.

The value of a call is computed by a function `ak` (`tmAskF`, `TermStep.lean`), a hypothesis
here (`tmStep_det`). `tmStepOut` is the result.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)

/-- The `N`-test answers after absorbing the latest answer `u`. -/
def tmAbsN (T4 j : ℕ) (aN : List Val) (u : Val) : List Val :=
  if j = 0 then aN else if j < T4 + 1 then aN ++ [u] else aN

/-- The coset answers after absorbing the latest answer `u`. -/
def tmAbsH (T4 j : ℕ) (aH : List Val) (u : Val) : List Val :=
  if j < T4 + 1 then aH else aH ++ [u]

/-- What the step keeps. -/
def tmKst (ctx : Val) (j : ℕ) (aN aH : List Val) : Val :=
  .list [ctx, .nat j, .list aN, .list aH]

/-- **The body of `tmStepF`**, with the call values computed by `ak`. -/
def tmStepBody (ak : ℕ) : Expr :=
  .letE (.get (.var 0) (.nat 0))
  (.letE (.get (.var 1) (.nat 1))
  (.letE (.get (.var 1) (.nat 0))
  (.letE (.get (.var 3) (.nat 7))
  (.letE (.arith .mul (.arith .mul (.nat 4) (.var 4)) (.var 4))
  (.letE (.ite (.arith .eq (.var 2) (.nat 0)) (.get (.var 1) (.nat 2))
      (.ite (.arith .lt (.var 2) (.arith .add (.var 5) (.nat 1)))
        (.snoc (.get (.var 1) (.nat 2)) (.get (.var 0) (.nat 1))) (.get (.var 1) (.nat 2))))
  (.letE (.ite (.arith .lt (.var 2) (.arith .add (.var 5) (.nat 1))) (.get (.var 1) (.nat 3))
      (.snoc (.get (.var 1) (.nat 3)) (.get (.var 0) (.nat 1))))
  (.letE (mk4 (.var 3) (.arith .add (.var 2) (.nat 1)) (.var 6) (.var 7))
  (.ite (.arith .lt (.var 2) (.var 5))
    (mk4 (.nat 1) (.nat 0) (.call ak (mk4 (.var 3) (.nat 3)
        (.arith .div (.var 2) (.arith .mul (.nat 2) (.var 4)))
        (.arith .mod (.var 2) (.arith .mul (.nat 2) (.var 4))))) (.var 8))
    (.ite (.arith .lt (.var 2) (.arith .add (.var 5) (.arith .mul (.var 4) (.var 4))))
      (mk4 (.nat 1) (.nat 0) (.call ak (mk4 (.var 3) (.nat 4)
          (.arith .div (.arith .sub (.var 2) (.var 5)) (.var 4))
          (.arith .add (.var 4) (.arith .mod (.arith .sub (.var 2) (.var 5)) (.var 4))))) (.var 8))
      (mk2 (.nat 0) (mk2 (.var 6) (.var 7))))))))))))

/-- **The result of the step** on `[[ctx, j, aN, aH], u]`, where `askVal sel a b` is the value of
the call on rows `a`, `b` under the group at entry `sel` of the context. -/
def tmStepOut (askVal : ℕ → ℕ → ℕ → Val) (ctx : Val) (q j : ℕ) (aN aH : List Val) (u : Val) :
    Val :=
  if j < 4 * q ^ 2 then
    .list [.nat 1, .nat 0, askVal 3 (j / (2 * q)) (j % (2 * q)),
      tmKst ctx (j + 1) (tmAbsN (4 * q ^ 2) j aN u) (tmAbsH (4 * q ^ 2) j aH u)]
  else if j < 5 * q ^ 2 then
    .list [.nat 1, .nat 0, askVal 4 ((j - 4 * q ^ 2) / q) (q + (j - 4 * q ^ 2) % q),
      tmKst ctx (j + 1) (tmAbsN (4 * q ^ 2) j aN u) (tmAbsH (4 * q ^ 2) j aH u)]
  else
    .list [.nat 0, .list [.list (tmAbsN (4 * q ^ 2) j aN u), .list (tmAbsH (4 * q ^ 2) j aH u)]]

theorem wt_nat_succ_le (j : ℕ) : (Val.nat (j + 1)).wt ≤ (Val.nat j).wt + 1 := by
  rw [wt_nat, wt_nat]; have := GI.Machine.len_succ_le j; omega

theorem wt_tmAbsN_le (T4 j : ℕ) (aN : List Val) (u : Val) :
    (Val.list (tmAbsN T4 j aN u)).wt ≤ (Val.list aN).wt + 2 * u.wt + 2 := by
  unfold tmAbsN
  split_ifs
  · omega
  · exact wt_list_snoc_le aN u
  · omega

theorem wt_tmAbsH_le (T4 j : ℕ) (aH : List Val) (u : Val) :
    (Val.list (tmAbsH T4 j aH u)).wt ≤ (Val.list aH).wt + 2 * u.wt + 2 := by
  unfold tmAbsH
  split_ifs
  · omega
  · exact wt_list_snoc_le aH u

theorem tm_idx_test {q j : ℕ} (hq : 0 < q) (hj : j < 4 * q ^ 2) :
    j / (2 * q) < 2 * q ∧ j % (2 * q) < 2 * q :=
  ⟨Nat.div_lt_of_lt_mul (by nlinarith), Nat.mod_lt _ (by omega)⟩

theorem tm_idx_coset {q j : ℕ} (hq : 0 < q) (hj : j < 5 * q ^ 2) :
    (j - 4 * q ^ 2) / q < 2 * q ∧ q + (j - 4 * q ^ 2) % q < 2 * q := by
  have h1 : j - 4 * q ^ 2 < q * q := by
    have : q ^ 2 = q * q := by ring
    omega
  exact ⟨by have := Nat.div_lt_of_lt_mul h1; omega, by have := Nat.mod_lt (j - 4 * q ^ 2) hq; omega⟩

theorem wt_tmStepOut_le (askVal : ℕ → ℕ → ℕ → Val) (ctx : Val) {q Ca : ℕ} (hq : 0 < q)
    (haskw : ∀ sel a b, (sel = 3 ∨ sel = 4) → a < 2 * q → b < 2 * q → (askVal sel a b).wt ≤ Ca)
    (j : ℕ) (aN aH : List Val) (u : Val) :
    (tmStepOut askVal ctx q j aN aH u).wt ≤
      2 * Ca + 8 * (tmKst ctx (j + 1) (tmAbsN (4 * q ^ 2) j aN u) (tmAbsH (4 * q ^ 2) j aH u)).wt +
        40 := by
  have w1 : (Val.nat 1).wt ≤ 3 := by decide
  have w0 : (Val.nat 0).wt ≤ 3 := by decide
  have hN : (Val.list (tmAbsN (4 * q ^ 2) j aN u)).wt <
      (tmKst ctx (j + 1) (tmAbsN (4 * q ^ 2) j aN u) (tmAbsH (4 * q ^ 2) j aH u)).wt :=
    wt_le_wt_list (by simp)
  have hH : (Val.list (tmAbsH (4 * q ^ 2) j aH u)).wt <
      (tmKst ctx (j + 1) (tmAbsN (4 * q ^ 2) j aN u) (tmAbsH (4 * q ^ 2) j aH u)).wt :=
    wt_le_wt_list (by simp)
  unfold tmStepOut
  split_ifs with h1 h2
  · obtain ⟨ha, hb⟩ := tm_idx_test hq h1
    have := haskw 3 _ _ (by omega) ha hb
    have := wt_list4_le (.nat 1) (.nat 0) (askVal 3 (j / (2 * q)) (j % (2 * q)))
      (tmKst ctx (j + 1) (tmAbsN (4 * q ^ 2) j aN u) (tmAbsH (4 * q ^ 2) j aH u))
    omega
  · obtain ⟨ha, hb⟩ := tm_idx_coset hq h2
    have := haskw 4 _ _ (by omega) ha hb
    have := wt_list4_le (.nat 1) (.nat 0) (askVal 4 ((j - 4 * q ^ 2) / q) (q + (j - 4 * q ^ 2) % q))
      (tmKst ctx (j + 1) (tmAbsN (4 * q ^ 2) j aN u) (tmAbsH (4 * q ^ 2) j aH u))
    omega
  · have := wt_list2_le (.nat 0) (.list [.list (tmAbsN (4 * q ^ 2) j aN u),
      .list (tmAbsH (4 * q ^ 2) j aH u)])
    have := wt_list2_le (.list (tmAbsN (4 * q ^ 2) j aN u)) (.list (tmAbsH (4 * q ^ 2) j aH u))
    omega

/-- **One step.** On `[[ctx, j, aN, aH], u]` with `j ≤ 5q²`, the step returns `tmStepOut`. `X`
bounds the weight of the program state and `q`; `Ca` bounds the cost and the result of `ak`. -/
theorem tmStep_det {P : Program} {stp ak : ℕ} (hstp : P.funs[stp]? = some (tmStepBody ak))
    (askVal : ℕ → ℕ → ℕ → Val) {Ca : ℕ} (cl : List Val) {q : ℕ}
    (hq7 : cl[7]? = some (.nat q)) (hq : 0 < q)
    (hask : ∀ sel a b, (sel = 3 ∨ sel = 4) → a < 2 * q → b < 2 * q →
      FunDet P ak (.list [.list cl, .nat sel, .nat a, .nat b]) (askVal sel a b) Ca)
    (haskw : ∀ sel a b, (sel = 3 ∨ sel = 4) → a < 2 * q → b < 2 * q → (askVal sel a b).wt ≤ Ca)
    (j : ℕ) (hj : j ≤ 5 * q ^ 2) (aN aH : List Val) (u : Val) {X : ℕ}
    (hX : (Val.list [tmKst (.list cl) j aN aH, u]).wt ≤ X) (hqX : q ≤ X) :
    FunDet P stp (.list [tmKst (.list cl) j aN aH, u]) (tmStepOut askVal (.list cl) q j aN aH u)
      (40 * Ca + 10 ^ 5 * (X + 1) ^ 2) := by
  set ctx := Val.list cl
  set kst := tmKst ctx j aN aH with hkst
  set st := Val.list [kst, u] with hst
  set T4 := 4 * q ^ 2 with hT4
  have hT4' : 4 * q * q = T4 := by rw [hT4]; ring
  set aN' := tmAbsN T4 j aN u
  set aH' := tmAbsH T4 j aH u
  -- weights
  have wk : kst.wt < st.wt := wt_le_wt_list (by simp)
  have wu : u.wt < st.wt := wt_le_wt_list (by simp)
  have wkl : ∀ v ∈ [ctx, .nat j, .list aN, .list aH], v.wt < kst.wt := fun v hv =>
    wt_le_wt_list hv
  have wc := wkl ctx (by simp)
  have wj := wkl (.nat j) (by simp)
  have wN := wkl (.list aN) (by simp)
  have wH := wkl (.list aH) (by simp)
  have wq : (Val.nat q).wt < ctx.wt := wt_le_wt_list (List.mem_of_getElem? hq7)
  have wN' := wt_tmAbsN_le T4 j aN u
  have wH' := wt_tmAbsH_le T4 j aH u
  have wj1 := wt_nat_succ_le j
  have hY : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hqq : q * q ≤ (X + 1) ^ 2 := by
    have : q * q ≤ (X + 1) * (X + 1) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have hq2 : q ^ 2 = q * q := by ring
  have hX' : st.wt ≤ X := hX
  have hstw : (Val.list [kst, u]).wt = st.wt := rfl
  have wT4 := wt_nat_le T4
  have wj0 := wt_nat_le j
  -- the prefix
  have d1 := Det.get' (Det.var' (P := P) (env := [st]) (i := 0) rfl) (Det.nat 0)
    (vs := [kst, u]) (v := kst) rfl
  have d2 := Det.get' (Det.var' (P := P) (env := [st, kst]) (i := 1) rfl) (Det.nat 1)
    (vs := [ctx, .nat j, .list aN, .list aH]) (v := .nat j) rfl
  have d3 := Det.get' (Det.var' (P := P) (env := [st, kst, .nat j]) (i := 1) rfl) (Det.nat 0)
    (vs := [ctx, .nat j, .list aN, .list aH]) (v := ctx) rfl
  have d4 := Det.get' (Det.var' (P := P) (env := [st, kst, .nat j, ctx]) (i := 3) rfl)
    (Det.nat 7) (vs := cl) (v := .nat q) hq7
  set E4 := [st, kst, Val.nat j, ctx, .nat q]
  have d5 := Det.arith' (z := T4) (op := .mul)
    (Det.arith' (op := .mul) (z := 4 * q) (Det.nat (P := P) (env := E4) 4)
      (Det.var' (P := P) (env := E4) (i := 4) rfl) rfl)
    (Det.var' (P := P) (env := E4) (i := 4) rfl) (by simp [GI.Machine.BinOp.eval, hT4'])
  set E5 := E4 ++ [Val.nat T4]
  have dj5 := Det.var' (P := P) (env := E5) (i := 2) (v := .nat j) rfl
  have dk5 := Det.var' (P := P) (env := E5) (i := 1) (v := kst) rfl
  have dT5 := Det.var' (P := P) (env := E5) (i := 5) (v := .nat T4) rfl
  have du5 := Det.get' (Det.var' (P := P) (env := E5) (i := 0) rfl) (Det.nat 1)
    (vs := [kst, u]) (v := u) rfl
  have dlt5 := Det.arith' (op := .lt) dj5 (Det.arith' (op := .add) dT5 (Det.nat 1) (z := T4 + 1) rfl)
    (z := if j < T4 + 1 then 1 else 0) (by simp [GI.Machine.BinOp.eval])
  have dget2 := Det.get' dk5 (Det.nat 2) (vs := [ctx, .nat j, .list aN, .list aH])
    (v := .list aN) rfl
  -- the `N`-test answers
  have d6 : Det P E5 (.ite (.arith .eq (.var 2) (.nat 0)) (.get (.var 1) (.nat 2))
      (.ite (.arith .lt (.var 2) (.arith .add (.var 5) (.nat 1)))
        (.snoc (.get (.var 1) (.nat 2)) (.get (.var 0) (.nat 1))) (.get (.var 1) (.nat 2))))
      (.list aN') (20 * X + 3 * T4 + 3 * j + 200) := by
    by_cases h0 : j = 0
    · have deq := Det.arith' (op := .eq) dj5 (Det.nat 0) (z := 1) (by simp [GI.Machine.BinOp.eval, h0])
      have : aN' = aN := by simp [aN', tmAbsN, h0]
      rw [this]
      exact (Det.ite_pos deq one_ne_zero dget2).mono (by omega)
    · have deq := Det.arith' (op := .eq) dj5 (Det.nat 0) (z := 0) (by simp [GI.Machine.BinOp.eval, h0])
      by_cases h1 : j < T4 + 1
      · have : aN' = aN ++ [u] := by simp [aN', tmAbsN, h0, h1]
        rw [this]
        rw [if_pos h1] at dlt5
        have := wt_list_snoc_le aN u
        exact (Det.ite_zero deq (Det.ite_pos dlt5 one_ne_zero (Det.snoc dget2 du5))).mono
          (by omega)
      · have : aN' = aN := by simp [aN', tmAbsN, h0, h1]
        rw [this]
        rw [if_neg h1] at dlt5
        exact (Det.ite_zero deq (Det.ite_zero dlt5 dget2)).mono (by omega)
  set E6 := E5 ++ [Val.list aN']
  -- the coset answers
  have d7 : Det P E6 (.ite (.arith .lt (.var 2) (.arith .add (.var 5) (.nat 1)))
      (.get (.var 1) (.nat 3)) (.snoc (.get (.var 1) (.nat 3)) (.get (.var 0) (.nat 1))))
      (.list aH') (20 * X + 3 * T4 + 3 * j + 200) := by
    have dj6 := Det.var' (P := P) (env := E6) (i := 2) (v := .nat j) rfl
    have dk6 := Det.var' (P := P) (env := E6) (i := 1) (v := kst) rfl
    have dT6 := Det.var' (P := P) (env := E6) (i := 5) (v := .nat T4) rfl
    have du6 := Det.get' (Det.var' (P := P) (env := E6) (i := 0) rfl) (Det.nat 1)
      (vs := [kst, u]) (v := u) rfl
    have dget3 := Det.get' dk6 (Det.nat 3) (vs := [ctx, .nat j, .list aN, .list aH])
      (v := .list aH) rfl
    by_cases h1 : j < T4 + 1
    · have dlt := Det.arith' (op := .lt) dj6 (Det.arith' (op := .add) dT6 (Det.nat 1)
        (z := T4 + 1) rfl) (z := 1) (by simp [GI.Machine.BinOp.eval, h1])
      have : aH' = aH := by simp [aH', tmAbsH, h1]
      rw [this]
      exact (Det.ite_pos dlt one_ne_zero dget3).mono (by omega)
    · have dlt := Det.arith' (op := .lt) dj6 (Det.arith' (op := .add) dT6 (Det.nat 1)
        (z := T4 + 1) rfl) (z := 0) (by simp [GI.Machine.BinOp.eval, h1])
      have : aH' = aH ++ [u] := by simp [aH', tmAbsH, h1]
      rw [this]
      have := wt_list_snoc_le aH u
      exact (Det.ite_zero dlt (Det.snoc dget3 du6)).mono (by omega)
  set E7 := E6 ++ [Val.list aH']
  -- what the step keeps
  have d8 := Det.mk4 (Det.var' (P := P) (env := E7) (i := 3) (v := ctx) rfl)
    (Det.arith' (op := .add) (Det.var' (P := P) (env := E7) (i := 2) (v := .nat j) rfl)
      (Det.nat 1) (z := j + 1) rfl)
    (Det.var' (P := P) (env := E7) (i := 6) (v := .list aN') rfl)
    (Det.var' (P := P) (env := E7) (i := 7) (v := .list aH') rfl)
  set kst' := Val.list [ctx, .nat (j + 1), .list aN', .list aH']
  have wk' : kst'.wt ≤ 2 * (ctx.wt + (Val.nat (j + 1)).wt + (Val.list aN').wt +
      (Val.list aH').wt) + 8 := wt_list4_le _ _ _ _
  set E8 := E7 ++ [kst']
  have dj8 := Det.var' (P := P) (env := E8) (i := 2) (v := .nat j) rfl
  have dT8 := Det.var' (P := P) (env := E8) (i := 5) (v := .nat T4) rfl
  have dq8 := Det.var' (P := P) (env := E8) (i := 4) (v := .nat q) rfl
  have dc8 := Det.var' (P := P) (env := E8) (i := 3) (v := ctx) rfl
  have dk8 := Det.var' (P := P) (env := E8) (i := 8) (v := kst') rfl
  have hkst' : kst' = tmKst ctx (j + 1) aN' aH' := rfl
  have wN'' : (Val.list aN').wt ≤ (Val.list aN).wt + 2 * u.wt + 2 := wN'
  have wH'' : (Val.list aH').wt ≤ (Val.list aH).wt + 2 * u.wt + 2 := wH'
  have hX3 : (Val.list [kst, u]).wt ≤ X := hX
  have e1 : (Val.list [ctx, .nat j, .list aN, .list aH]).wt = kst.wt := rfl
  have e2 : (Val.list cl).wt = ctx.wt := rfl
  -- the three cases
  have hfin : Det P E8 (.ite (.arith .lt (.var 2) (.var 5))
    (mk4 (.nat 1) (.nat 0) (.call ak (mk4 (.var 3) (.nat 3)
        (.arith .div (.var 2) (.arith .mul (.nat 2) (.var 4)))
        (.arith .mod (.var 2) (.arith .mul (.nat 2) (.var 4))))) (.var 8))
    (.ite (.arith .lt (.var 2) (.arith .add (.var 5) (.arith .mul (.var 4) (.var 4))))
      (mk4 (.nat 1) (.nat 0) (.call ak (mk4 (.var 3) (.nat 4)
          (.arith .div (.arith .sub (.var 2) (.var 5)) (.var 4))
          (.arith .add (.var 4) (.arith .mod (.arith .sub (.var 2) (.var 5)) (.var 4))))) (.var 8))
      (mk2 (.nat 0) (mk2 (.var 6) (.var 7)))))
      (tmStepOut askVal ctx q j aN aH u) (14 * Ca + 5000 * (X + 1) ^ 2) := by
    have hk8 : kst'.wt ≤ 16 * X + 30 := by omega
    have w1 : (Val.nat 1).wt ≤ 3 := by decide
    have w0 : (Val.nat 0).wt ≤ 3 := by decide
    have w3 : (Val.nat 3).wt ≤ 4 := by decide
    have w4 : (Val.nat 4).wt ≤ 5 := by decide
    have hT' : T4 ≤ 4 * (X + 1) ^ 2 := by omega
    have hctxX : ctx.wt ≤ X := by omega
    by_cases h1 : j < T4
    · obtain ⟨ha, hb⟩ := tm_idx_test hq h1
      have dlt := Det.arith' (op := .lt) dj8 dT8 (z := 1) (by simp [GI.Machine.BinOp.eval, h1])
      have d2q := Det.arith' (op := .mul) (Det.nat (P := P) (env := E8) 2) dq8 (z := 2 * q) rfl
      have da := Det.arith' (op := .div) dj8 d2q (z := j / (2 * q)) rfl
      have db := Det.arith' (op := .mod) dj8 d2q (z := j % (2 * q)) rfl
      have dargs := Det.mk4 dc8 (Det.nat 3) da db
      have dcall := Det.call dargs (hask 3 _ _ (by omega) ha hb)
      have dout := Det.mk4 (Det.nat 1) (Det.nat 0) dcall dk8
      have hv : tmStepOut askVal ctx q j aN aH u = .list [.nat 1, .nat 0,
          askVal 3 (j / (2 * q)) (j % (2 * q)), kst'] := by
        simp only [tmStepOut, ← hT4, if_pos h1]; rfl
      rw [hv]
      refine (Det.ite_pos dlt one_ne_zero dout).mono ?_
      have hw := haskw 3 _ _ (by omega) ha hb
      have := wt_list4_le (.nat 1) (.nat 0) (askVal 3 (j / (2 * q)) (j % (2 * q))) kst'
      have := wt_list4_le ctx (.nat 3) (.nat (j / (2 * q))) (.nat (j % (2 * q)))
      have := wt_nat_le (j / (2 * q))
      have := wt_nat_le (j % (2 * q))
      omega
    · by_cases h2 : j < T4 + q * q
      · have h2' : j < 5 * q ^ 2 := by omega
        obtain ⟨ha, hb⟩ := tm_idx_coset hq h2'
        rw [← hT4] at ha hb
        have dlt := Det.arith' (op := .lt) dj8 dT8 (z := 0) (by simp [GI.Machine.BinOp.eval, h1])
        have dlt2 := Det.arith' (op := .lt) dj8 (Det.arith' (op := .add) dT8
          (Det.arith' (op := .mul) dq8 dq8 (z := q * q) rfl) (z := T4 + q * q) rfl) (z := 1)
          (by simp [GI.Machine.BinOp.eval, h2])
        have dsub := Det.arith' (op := .sub) dj8 dT8 (z := j - T4) rfl
        have da := Det.arith' (op := .div) dsub dq8 (z := (j - T4) / q) rfl
        have db := Det.arith' (op := .add) dq8 (Det.arith' (op := .mod) dsub dq8
          (z := (j - T4) % q) rfl) (z := q + (j - T4) % q) rfl
        have dargs := Det.mk4 dc8 (Det.nat 4) da db
        have dcall := Det.call dargs (hask 4 _ _ (by omega) ha hb)
        have dout := Det.mk4 (Det.nat 1) (Det.nat 0) dcall dk8
        have hv : tmStepOut askVal ctx q j aN aH u = .list [.nat 1, .nat 0,
            askVal 4 ((j - T4) / q) (q + (j - T4) % q), kst'] := by
          simp only [tmStepOut, ← hT4, if_neg h1, if_pos h2']; rfl
        rw [hv]
        refine (Det.ite_zero dlt (Det.ite_pos dlt2 one_ne_zero dout)).mono ?_
        have hw := haskw 4 _ _ (by omega) ha hb
        have := wt_list4_le (.nat 1) (.nat 0) (askVal 4 ((j - T4) / q) (q + (j - T4) % q)) kst'
        have := wt_list4_le ctx (.nat 4) (.nat ((j - T4) / q)) (.nat (q + (j - T4) % q))
        have := wt_nat_le ((j - T4) / q)
        have := wt_nat_le (q + (j - T4) % q)
        have := Nat.div_le_self (j - T4) q
        have := Nat.mod_lt (j - T4) hq
        omega
      · have h3 : ¬ j < 5 * q ^ 2 := by omega
        have dlt := Det.arith' (op := .lt) dj8 dT8 (z := 0) (by simp [GI.Machine.BinOp.eval, h1])
        have dlt2 := Det.arith' (op := .lt) dj8 (Det.arith' (op := .add) dT8
          (Det.arith' (op := .mul) dq8 dq8 (z := q * q) rfl) (z := T4 + q * q) rfl) (z := 0)
          (by simp [GI.Machine.BinOp.eval, h2])
        have dout := Det.mk2 (Det.nat 0) (Det.mk2
          (Det.var' (P := P) (env := E8) (i := 6) (v := .list aN') rfl)
          (Det.var' (P := P) (env := E8) (i := 7) (v := .list aH') rfl))
        have hv : tmStepOut askVal ctx q j aN aH u =
            .list [.nat 0, .list [.list aN', .list aH']] := by
          simp only [tmStepOut, ← hT4, if_neg h1, if_neg h3]; rfl
        rw [hv]
        refine (Det.ite_zero dlt (Det.ite_zero dlt2 dout)).mono ?_
        have := wt_list2_le (.list aN') (.list aH')
        have := wt_list2_le (.nat 0) (.list [.list aN', .list aH'])
        omega
  refine FunDet.intro hstp ?_
  unfold tmStepBody
  refine (Det.letE d1 (Det.letE d2 (Det.letE d3 (Det.letE d4 (Det.letE d5 (Det.letE d6
    (Det.letE d7 (Det.letE d8 hfin)))))))).mono ?_
  have wout := wt_tmStepOut_le askVal ctx hq haskw j aN aH u
  have hk' : (tmKst ctx (j + 1) (tmAbsN (4 * q ^ 2) j aN u) (tmAbsH (4 * q ^ 2) j aH u)).wt =
      kst'.wt := rfl
  have hT : T4 ≤ 4 * (X + 1) ^ 2 := by omega
  omega

end GI.Impl
