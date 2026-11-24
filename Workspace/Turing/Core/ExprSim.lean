/-
Simulation proof for expressions and argument lists (`compileExpr` and `compileArgs`).

Evaluating an expression `e` pushes `(evalExpr st e).1` onto stack `E`, preserves all other
stacks, the return stack, the input and the output (`Keeps [E]`), and costs at most
`exprConst ctx M * (listSize Mem + listSize R + 1) * (evalExpr st e).2 ^ 2`, where `M` bounds
the register indices in `e`.
-/
module

public import Workspace.Turing.Core.Compile
public import Workspace.Machine.Run

@[expose] public section

namespace GI.Turing.Core

open GI.Machine (len Expr State evalExpr evalArgs len_evalExpr_le)
open GI.Turing (E Mem memOf listSize Keeps)
open GI.Turing.SM

/-! ### Basic facts about `evalExpr` and `evalArgs` -/

/-- Every expression has evaluation cost at least 1. -/
theorem one_le_evalExpr_cost (st : State) (e : Expr) : 1 ≤ (evalExpr st e).2 := by
  cases e <;> simp [evalExpr] <;> omega

theorem evalArgs_length (st : State) (args : List Expr) :
    (evalArgs st args).1.length = args.length := by
  induction args with
  | nil => rfl
  | cons e es ih => simp [evalArgs, ih]

/-- Size and cost bound for pushing evaluated arguments onto `R`. -/
theorem evalArgs_buildR_bound (st : State) (args : List Expr) (M : ℕ) :
    (len M + 1) * args.length + listSize (evalArgs st args).1 ≤
      (len M + 3) * (evalArgs st args).2 := by
  induction args with
  | nil => simp [evalArgs]
  | cons e es ih =>
    simp only [evalArgs, List.length_cons, listSize_cons, Nat.mul_succ, Nat.mul_add]
    have h1 : 1 ≤ (evalExpr st e).2 := one_le_evalExpr_cost st e
    have h2 : len (evalExpr st e).1 ≤ (evalExpr st e).2 := len_evalExpr_le st e
    have h3 : (len M + 1) * 1 ≤ (len M + 1) * (evalExpr st e).2 := Nat.mul_le_mul_left _ h1
    have h4 : (len M + 3) * (evalExpr st e).2 =
        (len M + 1) * (evalExpr st e).2 + 2 * (evalExpr st e).2 := by ring
    omega

/-! ### Cost constant and quadratic arithmetic helpers -/

/-- Constant factor in the expression evaluation cost bound. -/
def exprConst (ctx : CompilerCtx) (M : ℕ) : ℕ :=
  max ((ctx.cL + 1) * (len M + 1)) (max ctx.cA 1)

theorem one_le_exprConst (ctx : CompilerCtx) (M : ℕ) : 1 ≤ exprConst ctx M :=
  le_trans (le_max_right _ _) (le_max_right _ _)

theorem cA_le_exprConst (ctx : CompilerCtx) (M : ℕ) : ctx.cA ≤ exprConst ctx M :=
  le_trans (le_max_left _ _) (le_max_right _ _)

theorem cL_mul_le_exprConst (ctx : CompilerCtx) (M : ℕ) :
    (ctx.cL + 1) * (len M + 1) ≤ exprConst ctx M :=
  le_max_left _ _

theorem cL_le_exprConst (ctx : CompilerCtx) (M : ℕ) : ctx.cL ≤ exprConst ctx M := by
  have h := cL_mul_le_exprConst ctx M
  have h1 : ctx.cL ≤ (ctx.cL + 1) * (len M + 1) := by
    calc ctx.cL ≤ ctx.cL + 1 := Nat.le_succ _
      _ = (ctx.cL + 1) * 1 := (Nat.mul_one _).symm
      _ ≤ (ctx.cL + 1) * (len M + 1) := Nat.mul_le_mul_left _ (Nat.succ_pos _)
  exact le_trans h1 h

theorem sq_add_sq_le_sq_add (a b : ℕ) : a ^ 2 + b ^ 2 ≤ (a + b) ^ 2 := by
  have : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by ring
  omega

theorem sq_add_sq_add_sq_le_sq_add (a b c : ℕ) : a ^ 2 + b ^ 2 + c ^ 2 ≤ (a + b + c) ^ 2 := by
  have : (a + b + c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + a * c + b * c) := by ring
  omega

theorem le_sq_self (a : ℕ) : a ≤ a ^ 2 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · rw [sq]; exact Nat.le_mul_of_pos_right a ha

/-! ### Expression simulation -/

/-- Running `compileExpr ctx e a` pushes `(evalExpr st e).1` onto `E`, keeps all other stacks,
and costs at most `exprConst ctx M * (listSize Mem + listSize R + 1) * (evalExpr st e).2 ^ 2`. -/
theorem steps_compileExpr (ctx : CompilerCtx) {M : ℕ} {P : Program} {a : ℕ} {cfg : Config}
    {st : State} {e : Expr}
    (hc : CodeAt P a (compileExpr ctx e a)) (hpc : cfg.pc = a)
    (hMem : memOf (cfg.stk Mem) = st.mem) (hR : memOf (cfg.stk R) = st.regs)
    (hM : maxRegExpr e ≤ M) :
    ∃ cfg' S, Steps P cfg cfg' S ∧ cfg'.pc = a + (compileExpr ctx e a).length ∧
      cfg'.stk E = (evalExpr st e).1 :: cfg.stk E ∧
      Keeps [E] cfg cfg' ∧
      S ≤ exprConst ctx M * (listSize (cfg.stk Mem) + listSize (cfg.stk R) + 1) *
        (evalExpr st e).2 ^ 2 := by
  induction e generalizing a cfg with
  | const k =>
    have h0 : P[a]? = some (.push E k) := hc.cons
    obtain ⟨c1, hs1, hpc1, hE1, hk1⟩ := steps_push h0 hpc
    refine ⟨c1, 1 + len k, hs1, by simpa [compileExpr] using hpc1, hE1, hk1, ?_⟩
    simp only [evalExpr]
    have hC := one_le_exprConst ctx M
    have hW : 1 ≤ listSize (cfg.stk Mem) + listSize (cfg.stk R) + 1 := Nat.succ_pos _
    have hsq : 1 + len k ≤ (1 + len k) ^ 2 := le_sq_self (1 + len k)
    have h1 : 1 * 1 * (1 + len k) ≤
        exprConst ctx M * (listSize (cfg.stk Mem) + listSize (cfg.stk R) + 1) *
          (1 + len k) ^ 2 := by
      exact Nat.mul_le_mul (Nat.mul_le_mul hC hW) hsq
    simpa using h1
  | reg r =>
    have h0 : P[a]? = some (.push E r) := hc.cons
    have hLook : CodeAt P (a + 1) (ctx.lookupCode E R (a + 1)) := hc.tail
    obtain ⟨c1, hs1, hpc1, hE1, hk1⟩ := steps_push h0 hpc
    have hR1 : c1.stk R = cfg.stk R := keeps_stk_eq hk1 (by simp [E_ne_R.symm])
    obtain ⟨c2, S2, hs2, hpc2, hE2, hk2, hcost2⟩ :=
      ctx.hLookup E R E_ne_R P (a + 1) c1 r (cfg.stk E) hLook hpc1 hE1
    refine ⟨c2, (1 + len r) + S2, hs1.trans hs2, ?_, ?_, keeps_trans hk1 hk2, ?_⟩
    · simp only [compileExpr, List.length_append, List.length_singleton]; omega
    · rw [hE2, hR1, hR]; rfl
    · rw [hR1] at hcost2
      have hlenr : len r + 1 ≤ len M + 1 := Nat.add_le_add_right (GI.Machine.len_mono hM) 1
      have hSR : listSize (cfg.stk R) + 1 ≤
          listSize (cfg.stk Mem) + listSize (cfg.stk R) + 1 := by omega
      have hC := cL_mul_le_exprConst ctx M
      have ht : 1 ≤ (evalExpr st (.reg r)).2 ^ 2 :=
        le_trans (one_le_evalExpr_cost st (.reg r)) (le_sq_self _)
      calc (1 + len r) + S2
          ≤ (len M + 1) + ctx.cL * (listSize (cfg.stk R) + 1) * (len M + 1) := by
            have h2 : ctx.cL * (listSize (cfg.stk R) + 1) * (len r + 1) ≤
                ctx.cL * (listSize (cfg.stk R) + 1) * (len M + 1) :=
              Nat.mul_le_mul_left _ hlenr
            omega
        _ ≤ (len M + 1) * (listSize (cfg.stk R) + 1) +
            ctx.cL * (listSize (cfg.stk R) + 1) * (len M + 1) := by
            have : len M + 1 ≤ (len M + 1) * (listSize (cfg.stk R) + 1) :=
              Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
            omega
        _ = (ctx.cL + 1) * (len M + 1) * (listSize (cfg.stk R) + 1) := by ring
        _ ≤ exprConst ctx M * (listSize (cfg.stk Mem) + listSize (cfg.stk R) + 1) * 1 := by
            rw [Nat.mul_one]
            exact Nat.mul_le_mul hC hSR
        _ ≤ exprConst ctx M * (listSize (cfg.stk Mem) + listSize (cfg.stk R) + 1) *
            (evalExpr st (.reg r)).2 ^ 2 := Nat.mul_le_mul_left _ ht
  | load addr iha =>
    have hc1 : CodeAt P a (compileExpr ctx addr a) := hc.append_left
    have hc2 : CodeAt P (a + (compileExpr ctx addr a).length)
        (ctx.lookupCode E Mem (a + (compileExpr ctx addr a).length)) := hc.append_right
    obtain ⟨c1, S1, hs1, hpc1, hE1, hk1, hcost1⟩ := iha hc1 hpc hMem hR hM
    have hM1 : c1.stk Mem = cfg.stk Mem := keeps_stk_eq hk1 (by simp [E_ne_Mem.symm])
    obtain ⟨c2, S2, hs2, hpc2, hE2, hk2, hcost2⟩ :=
      ctx.hLookup E Mem E_ne_Mem P _ c1 (evalExpr st addr).1 (cfg.stk E) hc2 hpc1 hE1
    refine ⟨c2, S1 + S2, hs1.trans hs2, ?_, ?_, keeps_trans hk1 hk2, ?_⟩
    · simp only [compileExpr, List.length_append]; omega
    · rw [hE2, hM1, hMem]; rfl
    · rw [hM1] at hcost2
      set W := listSize (cfg.stk Mem) + listSize (cfg.stk R) + 1
      set C := exprConst ctx M
      set ta := (evalExpr st addr).2
      set d := len (evalExpr st addr).1 + 1
      have hS2 : S2 ≤ C * W * d ^ 2 := by
        have h1 : ctx.cL ≤ C := cL_le_exprConst ctx M
        have h2 : listSize (cfg.stk Mem) + 1 ≤ W := by omega
        have h3 : d ≤ d ^ 2 := le_sq_self d
        exact le_trans hcost2 (Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3)
      have hsum : ta + d ≤ (evalExpr st (.load addr)).2 := by simp [evalExpr, ta, d]; omega
      have hsq : ta ^ 2 + d ^ 2 ≤ (evalExpr st (.load addr)).2 ^ 2 :=
        le_trans (sq_add_sq_le_sq_add ta d) (Nat.pow_le_pow_left hsum 2)
      calc S1 + S2 ≤ C * W * ta ^ 2 + C * W * d ^ 2 := Nat.add_le_add hcost1 hS2
        _ = C * W * (ta ^ 2 + d ^ 2) := (Nat.mul_add _ _ _).symm
        _ ≤ C * W * (evalExpr st (.load addr)).2 ^ 2 := Nat.mul_le_mul_left _ hsq
  | bin op e1 e2 ih1 ih2 =>
    have hc12 : CodeAt P a (compileExpr ctx e1 a ++
        compileExpr ctx e2 (a + (compileExpr ctx e1 a).length)) := hc.append_left
    have hc1 : CodeAt P a (compileExpr ctx e1 a) := hc12.append_left
    have hc2 : CodeAt P (a + (compileExpr ctx e1 a).length)
        (compileExpr ctx e2 (a + (compileExpr ctx e1 a).length)) := hc12.append_right
    have hc3 : CodeAt P (a + (compileExpr ctx e1 a).length +
        (compileExpr ctx e2 (a + (compileExpr ctx e1 a).length)).length)
        (ctx.arithCode op E (a + (compileExpr ctx e1 a).length +
        (compileExpr ctx e2 (a + (compileExpr ctx e1 a).length)).length)) := by
      have h := hc.append_right
      simpa [List.length_append, Nat.add_assoc] using h
    have hM1 : maxRegExpr e1 ≤ M := le_trans (le_max_left _ _) hM
    have hM2 : maxRegExpr e2 ≤ M := le_trans (le_max_right _ _) hM
    obtain ⟨c1, S1, hs1, hpc1, hE1, hk1, hcost1⟩ := ih1 hc1 hpc hMem hR hM1
    have hMem1 : c1.stk Mem = cfg.stk Mem := keeps_stk_eq hk1 (by simp [E_ne_Mem.symm])
    have hR1 : c1.stk R = cfg.stk R := keeps_stk_eq hk1 (by simp [E_ne_R.symm])
    obtain ⟨c2, S2, hs2, hpc2, hE2, hk2, hcost2⟩ :=
      ih2 hc2 hpc1 (by rw [hMem1, hMem]) (by rw [hR1, hR]) hM2
    rw [hE1] at hE2
    obtain ⟨c3, S3, hs3, hpc3, hE3, hk3, hcost3⟩ :=
      ctx.hArith op E P _ c2 (evalExpr st e1).1 (evalExpr st e2).1 (cfg.stk E)
        hc3 (by omega) hE2
    refine ⟨c3, S1 + S2 + S3, (hs1.trans hs2).trans hs3, ?_, hE3,
      keeps_trans (keeps_trans hk1 hk2) hk3, ?_⟩
    · simp only [compileExpr, List.length_append]; omega
    · rw [hMem1, hR1] at hcost2
      set W := listSize (cfg.stk Mem) + listSize (cfg.stk R) + 1
      set C := exprConst ctx M
      set t1 := (evalExpr st e1).2
      set t2 := (evalExpr st e2).2
      set d := len (evalExpr st e1).1 + len (evalExpr st e2).1 + 1
      have hS3 : S3 ≤ C * W * d ^ 2 := by
        have h1 : ctx.cA ≤ C := cA_le_exprConst ctx M
        have h2 : 1 ≤ W := Nat.succ_pos _
        have hCW : ctx.cA ≤ C * W := by
          calc ctx.cA ≤ C := h1
            _ = C * 1 := (Nat.mul_one _).symm
            _ ≤ C * W := Nat.mul_le_mul_left _ h2
        exact le_trans hcost3 (Nat.mul_le_mul_right _ hCW)
      have hsum : t1 + t2 + d ≤ (evalExpr st (.bin op e1 e2)).2 := by
        simp [evalExpr, t1, t2, d]; omega
      have hsq : t1 ^ 2 + t2 ^ 2 + d ^ 2 ≤ (evalExpr st (.bin op e1 e2)).2 ^ 2 :=
        le_trans (sq_add_sq_add_sq_le_sq_add t1 t2 d) (Nat.pow_le_pow_left hsum 2)
      calc S1 + S2 + S3
          ≤ C * W * t1 ^ 2 + C * W * t2 ^ 2 + C * W * d ^ 2 :=
            Nat.add_le_add (Nat.add_le_add hcost1 hcost2) hS3
        _ = C * W * (t1 ^ 2 + t2 ^ 2 + d ^ 2) := by ring
        _ ≤ C * W * (evalExpr st (.bin op e1 e2)).2 ^ 2 := Nat.mul_le_mul_left _ hsq

/-! ### Argument list simulation -/

/-- Running `compileArgs ctx args a` pushes `(evalArgs st args).1` onto `E` (first argument on
top), keeps all other stacks, and obeys the same quadratic cost bound. -/
theorem steps_compileArgs (ctx : CompilerCtx) {M : ℕ} {P : Program} {a : ℕ} {cfg : Config}
    {st : State} {args : List Expr}
    (hc : CodeAt P a (compileArgs ctx args a)) (hpc : cfg.pc = a)
    (hMem : memOf (cfg.stk Mem) = st.mem) (hR : memOf (cfg.stk R) = st.regs)
    (hM : maxRegArgs args ≤ M) :
    ∃ cfg' S, Steps P cfg cfg' S ∧ cfg'.pc = a + (compileArgs ctx args a).length ∧
      cfg'.stk E = (evalArgs st args).1 ++ cfg.stk E ∧
      Keeps [E] cfg cfg' ∧
      S ≤ exprConst ctx M * (listSize (cfg.stk Mem) + listSize (cfg.stk R) + 1) *
        (evalArgs st args).2 ^ 2 := by
  induction args generalizing a cfg with
  | nil =>
    exact ⟨cfg, 0, Steps.refl cfg, by simpa [compileArgs] using hpc, rfl,
      keeps_refl [E] cfg, Nat.zero_le _⟩
  | cons e es ih =>
    have hc1 : CodeAt P a (compileArgs ctx es a) := hc.append_left
    have hc2 : CodeAt P (a + (compileArgs ctx es a).length)
        (compileExpr ctx e (a + (compileArgs ctx es a).length)) := hc.append_right
    have hMe : maxRegExpr e ≤ M := le_trans (le_max_left _ _) hM
    have hMes : maxRegArgs es ≤ M := le_trans (le_max_right _ _) hM
    obtain ⟨c1, S1, hs1, hpc1, hE1, hk1, hcost1⟩ := ih hc1 hpc hMem hR hMes
    have hMem1 : c1.stk Mem = cfg.stk Mem := keeps_stk_eq hk1 (by simp [E_ne_Mem.symm])
    have hR1 : c1.stk R = cfg.stk R := keeps_stk_eq hk1 (by simp [E_ne_R.symm])
    obtain ⟨c2, S2, hs2, hpc2, hE2, hk2, hcost2⟩ :=
      steps_compileExpr ctx hc2 hpc1 (by rw [hMem1, hMem]) (by rw [hR1, hR]) hMe
    refine ⟨c2, S1 + S2, hs1.trans hs2, ?_, ?_, keeps_trans hk1 hk2, ?_⟩
    · simp only [compileArgs, List.length_append]; omega
    · rw [hE2, hE1]; rfl
    · rw [hMem1, hR1] at hcost2
      set W := listSize (cfg.stk Mem) + listSize (cfg.stk R) + 1
      set C := exprConst ctx M
      have hsq : (evalArgs st es).2 ^ 2 + (evalExpr st e).2 ^ 2 ≤
          ((evalExpr st e).2 + (evalArgs st es).2) ^ 2 := by
        rw [Nat.add_comm (evalExpr st e).2]
        exact sq_add_sq_le_sq_add _ _
      calc S1 + S2
          ≤ C * W * (evalArgs st es).2 ^ 2 + C * W * (evalExpr st e).2 ^ 2 :=
            Nat.add_le_add hcost1 hcost2
        _ = C * W * ((evalArgs st es).2 ^ 2 + (evalExpr st e).2 ^ 2) := (Nat.mul_add _ _ _).symm
        _ ≤ C * W * (evalArgs st (e :: es)).2 ^ 2 := Nat.mul_le_mul_left _ hsq

end GI.Turing.Core
