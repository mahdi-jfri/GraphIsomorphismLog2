/-
Simulation proof for statements (`compileStmt`) and procedure epilogues.

By induction on `fuel` in `GI.Machine.exec`, we prove that running `compileStmt` from a stack
machine configuration matching `st` on `Mem` and `R` reaches either the end of the statement's
code (on `.normal`) or the procedure epilogue `ep` with the return value pushed onto `E` (on
`.returned v`). It keeps all stacks other than `E`, `Mem`, and `R` (including the caller frame
stack `F` and the return stack `rs`), grows `Mem` and `R` linearly in the RAM cost `c`, and pays
at most `stmtConst ctx M * (listSize Mem + listSize R + (len M + 3) * c + 1) * c ^ 2`.
-/
module

public import Workspace.Turing.Core.ExprSim

@[expose] public section

namespace GI.Turing.Core

open GI.Machine (len Expr Stmt State Outcome evalExpr evalArgs exec len_evalExpr_le)
open GI.Turing (E Mem memOf listSize Keeps)
open GI.Turing.SM

/-- All procedures of `p` sit at `procAddr f` inside `P`. -/
def ProcsAt (ctx : CompilerCtx) (P : Program) (procAddr : ℕ → ℕ) (p : GI.Machine.Program) : Prop :=
  ∀ (f : ℕ) (body : Stmt), p.procs[f]? = some body →
    CodeAt P (procAddr f) (compileProc ctx procAddr body (procAddr f))

/-- Constant factor in the statement simulation cost bound. -/
def stmtConst (ctx : CompilerCtx) (M : ℕ) : ℕ :=
  max (exprConst ctx M) 20

theorem exprConst_le_stmtConst (ctx : CompilerCtx) (M : ℕ) :
    exprConst ctx M ≤ stmtConst ctx M :=
  le_max_left _ _

theorem twenty_le_stmtConst (ctx : CompilerCtx) (M : ℕ) : 20 ≤ stmtConst ctx M :=
  le_max_right _ _

/-! ### Arithmetic helpers for combining cost bounds -/

private theorem stmt_cost_one {K W c t d : ℕ} (ht : t + 1 ≤ c) (hd : d ≤ K * W) :
    K * W * t ^ 2 + d ≤ K * W * c ^ 2 := by
  have h1 : t ^ 2 + 1 ≤ (t + 1) ^ 2 := by
    have : (t + 1) ^ 2 = t ^ 2 + 1 + 2 * t := by ring
    omega
  have hsq : t ^ 2 + 1 ≤ c ^ 2 := le_trans h1 (Nat.pow_le_pow_left ht 2)
  calc K * W * t ^ 2 + d ≤ K * W * t ^ 2 + K * W := Nat.add_le_add_left hd _
    _ = K * W * (t ^ 2 + 1) := by ring
    _ ≤ K * W * c ^ 2 := Nat.mul_le_mul_left _ hsq

private theorem stmt_cost_two {K W c t₁ t₂ d : ℕ} (ht : t₁ + t₂ + 1 ≤ c) (hd : d ≤ K * W) :
    K * W * t₁ ^ 2 + K * W * t₂ ^ 2 + d ≤ K * W * c ^ 2 := by
  have h1 : t₁ ^ 2 + t₂ ^ 2 + 1 ≤ (t₁ + t₂ + 1) ^ 2 := by
    simpa using sq_add_sq_add_sq_le_sq_add t₁ t₂ 1
  have hsq : t₁ ^ 2 + t₂ ^ 2 + 1 ≤ c ^ 2 := le_trans h1 (Nat.pow_le_pow_left ht 2)
  calc K * W * t₁ ^ 2 + K * W * t₂ ^ 2 + d
      ≤ K * W * t₁ ^ 2 + K * W * t₂ ^ 2 + K * W := Nat.add_le_add_left hd _
    _ = K * W * (t₁ ^ 2 + t₂ ^ 2 + 1) := by ring
    _ ≤ K * W * c ^ 2 := Nat.mul_le_mul_left _ hsq

private theorem stmt_cost_three {K W c t₁ t₂ t₃ d : ℕ}
    (ht : t₁ + t₂ + t₃ + 1 ≤ c) (hd : d ≤ K * W) :
    K * W * t₁ ^ 2 + K * W * t₂ ^ 2 + K * W * t₃ ^ 2 + d ≤ K * W * c ^ 2 := by
  have h1 : t₁ ^ 2 + t₂ ^ 2 + t₃ ^ 2 + 1 ≤ (t₁ + t₂ + t₃ + 1) ^ 2 := by
    have : (t₁ + t₂ + t₃ + 1) ^ 2 =
        t₁ ^ 2 + t₂ ^ 2 + t₃ ^ 2 + 1 + 2 * (t₁ * t₂ + t₁ * t₃ + t₂ * t₃ + t₁ + t₂ + t₃) := by ring
    omega
  have hsq : t₁ ^ 2 + t₂ ^ 2 + t₃ ^ 2 + 1 ≤ c ^ 2 := le_trans h1 (Nat.pow_le_pow_left ht 2)
  calc K * W * t₁ ^ 2 + K * W * t₂ ^ 2 + K * W * t₃ ^ 2 + d
      ≤ K * W * t₁ ^ 2 + K * W * t₂ ^ 2 + K * W * t₃ ^ 2 + K * W := Nat.add_le_add_left hd _
    _ = K * W * (t₁ ^ 2 + t₂ ^ 2 + t₃ ^ 2 + 1) := by ring
    _ ≤ K * W * c ^ 2 := Nat.mul_le_mul_left _ hsq

private theorem expr_to_stmt_cost {ctx : CompilerCtx} {M S Msz Rsz c t : ℕ}
    (h : S ≤ exprConst ctx M * (Msz + Rsz + 1) * t ^ 2) :
    S ≤ stmtConst ctx M * (Msz + Rsz + (len M + 3) * c + 1) * t ^ 2 := by
  have h1 : exprConst ctx M ≤ stmtConst ctx M := exprConst_le_stmtConst ctx M
  have h2 : Msz + Rsz + 1 ≤ Msz + Rsz + (len M + 3) * c + 1 := by omega
  exact le_trans h (Nat.mul_le_mul_right _ (Nat.mul_le_mul h1 h2))

/-- Length of `o.retVal` is at most the cost of the run producing `o`. -/
theorem len_retVal_le {p : GI.Machine.Program} {fuel : ℕ} {s : Stmt} {st st' : State}
    {o : Outcome} {c : ℕ} (h : exec p fuel s st = some (o, st', c)) :
    len o.retVal ≤ c := by
  cases o with
  | normal => simp [GI.Machine.Outcome.retVal, GI.Machine.len_zero]
  | returned w => exact GI.Machine.Runs.len_returned_le ⟨fuel, h⟩

/-- Target program counter after a statement finishes with outcome `o`. -/
@[simp] def outcomePc (normalPc ep : ℕ) : Outcome → ℕ
  | .normal => normalPc
  | .returned _ => ep

/-- Contents of stack `E` after a statement finishes with outcome `o`. -/
@[simp] def outcomeE (stkE : List ℕ) : Outcome → List ℕ
  | .normal => stkE
  | .returned v => v :: stkE

/-! ### Procedure epilogue helper -/

/-- From the end of a compiled procedure body (either at `pos + bodyLen` on `.normal` or at `ep`
on `.returned v`), finish the procedure: push `0` if normal, empty `R`, and `ret` to `retAddr`. -/
theorem steps_procEpilogue (ctx : CompilerCtx) {P : Program} {procAddr : ℕ → ℕ}
    {body : Stmt} {pos retAddr : ℕ} {rs₀ stkE₀ : List ℕ} {o : Outcome} {cfg : Config}
    (hc : CodeAt P pos (compileProc ctx procAddr body pos))
    (hpc : cfg.pc = outcomePc
      (pos + (compileStmt ctx procAddr (procEpilogue ctx body pos) body pos).length)
      (procEpilogue ctx body pos) o)
    (hE : cfg.stk E = outcomeE stkE₀ o)
    (hrs : cfg.rs = retAddr :: rs₀) :
    ∃ cfg' S, Steps P cfg cfg' S ∧ cfg'.pc = retAddr ∧
      cfg'.stk E = o.retVal :: stkE₀ ∧ cfg'.stk R = [] ∧
      cfg'.stk Mem = cfg.stk Mem ∧ cfg'.stk F = cfg.stk F ∧
      (∀ t, t ∉ [E, Mem, R] → cfg'.stk t = cfg.stk t) ∧
      cfg'.rs = rs₀ ∧ cfg'.inp = cfg.inp ∧ cfg'.out = cfg.out ∧
      S ≤ 3 * listSize (cfg.stk R) + 3 := by
  set ep := procEpilogue ctx body pos
  set cBody := compileStmt ctx procAddr ep body pos
  have hlenBody : pos + cBody.length + 1 = ep := by
    change pos + (compileStmt ctx procAddr ep body pos).length + 1 =
      pos + (compileStmt ctx (fun _ => 0) 0 body pos).length + 1
    rw [compileStmt_length_eq ctx procAddr (fun _ => 0) ep 0 body pos]
  have hc123 : CodeAt P pos ((cBody ++ [.push E 0]) ++ emptyR ep) := hc.append_left
  have hc12 : CodeAt P pos (cBody ++ [.push E 0]) := hc123.append_left
  have hcPush : P[pos + cBody.length]? = some (.push E 0) := hc12.append_right.cons
  have hcEmp : CodeAt P ep (emptyR ep) := by
    have h := hc123.append_right
    simp only [List.length_append, List.length_singleton] at h
    rwa [← Nat.add_assoc, hlenBody] at h
  have hcRet : P[ep + 3]? = some .ret := by
    have h := hc.append_right
    simp only [List.length_append, List.length_singleton, emptyR_length] at h
    have heq : pos + (cBody.length + 1 + 3) = ep + 3 := by omega
    rw [heq] at h
    exact h.cons
  -- Reach `ep` with `o.retVal :: stkE₀` on `E` and cost at most 1.
  have hAtEp : ∃ c1 S1, Steps P cfg c1 S1 ∧ c1.pc = ep ∧
      c1.stk E = o.retVal :: stkE₀ ∧ Keeps [E] cfg c1 ∧ S1 ≤ 1 := by
    cases o with
    | normal =>
      obtain ⟨c1, hs1, hpc1, hE1, hk1⟩ := steps_push hcPush hpc
      refine ⟨c1, 1 + len 0, hs1, by omega, by rw [hE1, hE]; rfl, hk1,
        by simp [GI.Machine.len_zero]⟩
    | returned v =>
      exact ⟨cfg, 0, Steps.refl cfg, hpc, hE, keeps_refl [E] cfg, Nat.zero_le 1⟩
  obtain ⟨c1, S1, hs1, hpc1, hE1, hk1, hcost1⟩ := hAtEp
  have hR1 : c1.stk R = cfg.stk R := keeps_stk_eq hk1 (by simp [E_ne_R.symm])
  obtain ⟨c2, S2, hs2, hpc2, hR2, hk2, hcost2⟩ := steps_emptyR hcEmp hpc1
  have hrs2 : c2.rs = retAddr :: rs₀ := by rw [hk2.2.1, hk1.2.1, hrs]
  obtain ⟨c3, hs3, hpc3, hrs3, hstk3, hinp3, hout3⟩ := steps_ret hcRet hpc2 hrs2
  refine ⟨c3, S1 + S2 + 1, (hs1.trans hs2).trans hs3, hpc3, ?_, ?_, ?_, ?_, ?_, hrs3, ?_, ?_, ?_⟩
  · rw [hstk3, keeps_stk_eq hk2 (by simp [E_ne_R]), hE1]
  · rw [hstk3, hR2]
  · rw [hstk3, keeps_stk_eq hk2 (by simp [Mem_ne_R]), keeps_stk_eq hk1 (by simp [E_ne_Mem.symm])]
  · rw [hstk3, keeps_stk_eq hk2 (by simp [R_ne_F.symm]), keeps_stk_eq hk1 (by simp [E_ne_F.symm])]
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ht
    rw [hstk3, keeps_stk_eq hk2 (by simp [ht.2.2]), keeps_stk_eq hk1 (by simp [ht.1])]
  · rw [hinp3, hk2.2.2.1, hk1.2.2.1]
  · rw [hout3, hk2.2.2.2, hk1.2.2.2]
  · rw [hR1] at hcost2; omega

/-! ### Main statement simulation theorem -/

/-- Every successful execution of a statement `s` of program `p` is simulated by `compileStmt`
with the stated stack, size, and cost guarantees. -/
theorem steps_compileStmt (ctx : CompilerCtx) {M : ℕ} {P : Program} {procAddr : ℕ → ℕ}
    {p : GI.Machine.Program} {fuel : ℕ} {s : Stmt} {st st' : State} {o : Outcome} {c : ℕ}
    {a ep : ℕ} {cfg : Config}
    (hprocs : ProcsAt ctx P procAddr p)
    (hpM : maxRegProg p ≤ M) (hsM : maxRegStmt s ≤ M)
    (hc : CodeAt P a (compileStmt ctx procAddr ep s a)) (hpc : cfg.pc = a)
    (hMem : memOf (cfg.stk Mem) = st.mem) (hR : memOf (cfg.stk R) = st.regs)
    (hexec : exec p fuel s st = some (o, st', c)) :
    ∃ cfg' S, Steps P cfg cfg' S ∧
      cfg'.pc = outcomePc (a + (compileStmt ctx procAddr ep s a).length) ep o ∧
      cfg'.stk E = outcomeE (cfg.stk E) o ∧
      memOf (cfg'.stk Mem) = st'.mem ∧
      memOf (cfg'.stk R) = st'.regs ∧
      Keeps [E, Mem, R] cfg cfg' ∧
      listSize (cfg'.stk Mem) ≤ listSize (cfg.stk Mem) + c ∧
      listSize (cfg'.stk R) ≤ listSize (cfg.stk R) + (len M + 2) * c ∧
      S ≤ stmtConst ctx M *
        (listSize (cfg.stk Mem) + listSize (cfg.stk R) + (len M + 3) * c + 1) * c ^ 2 := by
  induction fuel generalizing s st st' o c a ep cfg with
  | zero => simp [exec] at hexec
  | succ f ih =>
    cases s with
    | nop =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl, rfl⟩ := hexec
      exact ⟨cfg, 0, Steps.refl cfg, by simpa [compileStmt] using hpc, rfl, hMem, hR,
        keeps_refl _ cfg, Nat.le_add_right _ _, Nat.le_add_right _ _, Nat.zero_le _⟩
    | assign r e =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl, rfl⟩ := hexec
      have hrM : r ≤ M := le_trans (le_max_left _ _) hsM
      have heM : maxRegExpr e ≤ M := le_trans (le_max_right _ _) hsM
      set ce := compileExpr ctx e a
      have hce : CodeAt P a ce := hc.append_left
      have htail : CodeAt P (a + ce.length) [.move E R, .push R r] := hc.append_right
      have hMove : P[a + ce.length]? = some (.move E R) := htail.cons
      have hPush : P[a + ce.length + 1]? = some (.push R r) := htail.tail.cons
      obtain ⟨c1, S1, hs1, hpc1, hE1, hk1, hcost1⟩ :=
        steps_compileExpr ctx hce hpc hMem hR heM
      obtain ⟨c2, hs2, hpc2, hE2, hR2, hk2⟩ := steps_move E_ne_R hMove hpc1 hE1
      obtain ⟨c3, hs3, hpc3, hR3, hk3⟩ := steps_push hPush hpc2
      have hMem1 : c1.stk Mem = cfg.stk Mem := keeps_stk_eq hk1 (by simp [E_ne_Mem.symm])
      have hR1 : c1.stk R = cfg.stk R := keeps_stk_eq hk1 (by simp [E_ne_R.symm])
      have hMem3 : c3.stk Mem = cfg.stk Mem := by
        rw [keeps_stk_eq hk3 (by simp [Mem_ne_R]),
          keeps_stk_eq hk2 (by simp [E_ne_Mem.symm, Mem_ne_R]), hMem1]
      have hR3' : c3.stk R = r :: (evalExpr st e).1 :: cfg.stk R := by rw [hR3, hR2, hR1]
      have hlenr : len r ≤ len M := GI.Machine.len_mono hrM
      have hlene : len (evalExpr st e).1 ≤ (evalExpr st e).2 := len_evalExpr_le st e
      refine ⟨c3, S1 + (1 + len (evalExpr st e).1) + (1 + len r),
        (hs1.trans hs2).trans hs3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [compileStmt, List.length_append, List.length_cons, List.length_nil]
        change c3.pc = a + (ce.length + 2); omega
      · rw [keeps_stk_eq hk3 (by simp [E_ne_R]), hE2]; rfl
      · rw [hMem3, hMem]
      · rw [hR3', memOf_cons_cons, hR]
      · exact keeps_trans
          (keeps_trans (keeps_mono (by simp) hk1)
            (keeps_mono (by intro t ht; simp at ht ⊢; tauto) hk2))
          (keeps_mono (by simp) hk3)
      · rw [hMem3]; omega
      · rw [hR3']
        simp only [listSize_cons]
        have : (len M + 2) * ((evalExpr st e).2 + 1) =
            (len M + 2) * (evalExpr st e).2 + (len M + 2) := Nat.mul_succ _ _
        have : (evalExpr st e).2 ≤ (len M + 2) * (evalExpr st e).2 :=
          Nat.le_mul_of_pos_left _ (by omega)
        omega
      · set W := listSize (cfg.stk Mem) + listSize (cfg.stk R) +
            (len M + 3) * ((evalExpr st e).2 + 1) + 1
        set K := stmtConst ctx M
        have hS1' : S1 ≤ K * W * (evalExpr st e).2 ^ 2 := expr_to_stmt_cost hcost1
        have hK : 20 ≤ K := twenty_le_stmtConst ctx M
        have hd : (1 + len (evalExpr st e).1) + (1 + len r) ≤ K * W := by
          have h1 : (1 + len (evalExpr st e).1) + (1 + len r) ≤ W := by
            have : (len M + 3) * ((evalExpr st e).2 + 1) =
                (len M + 3) * (evalExpr st e).2 + (len M + 3) := Nat.mul_succ _ _
            have : (evalExpr st e).2 ≤ (len M + 3) * (evalExpr st e).2 :=
              Nat.le_mul_of_pos_left _ (by omega)
            omega
          exact le_trans h1 (Nat.le_mul_of_pos_left _ (by omega))
        have hsum := stmt_cost_one (K := K) (W := W) (c := (evalExpr st e).2 + 1)
          (t := (evalExpr st e).2) (d := (1 + len (evalExpr st e).1) + (1 + len r)) le_rfl hd
        omega
    | store addr val =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl, rfl⟩ := hexec
      have haM : maxRegExpr addr ≤ M := le_trans (le_max_left _ _) hsM
      have hvM : maxRegExpr val ≤ M := le_trans (le_max_right _ _) hsM
      set c1 := compileExpr ctx addr a
      set c2 := compileExpr ctx val (a + c1.length)
      have hc12 : CodeAt P a (c1 ++ c2) := hc.append_left
      have hc1 : CodeAt P a c1 := hc12.append_left
      have hc2 : CodeAt P (a + c1.length) c2 := hc12.append_right
      have htail : CodeAt P (a + c1.length + c2.length) [.move E Mem, .move E Mem] := by
        simpa [List.length_append, Nat.add_assoc] using hc.append_right
      have hM1 : P[a + c1.length + c2.length]? = some (.move E Mem) := htail.cons
      have hM2 : P[a + c1.length + c2.length + 1]? = some (.move E Mem) := htail.tail.cons
      obtain ⟨k1, S1, hs1, hpc1, hE1, hk1, hcost1⟩ :=
        steps_compileExpr ctx hc1 hpc hMem hR haM
      have hMem1 : k1.stk Mem = cfg.stk Mem := keeps_stk_eq hk1 (by simp [E_ne_Mem.symm])
      have hR1 : k1.stk R = cfg.stk R := keeps_stk_eq hk1 (by simp [E_ne_R.symm])
      obtain ⟨k2, S2, hs2, hpc2, hE2, hk2, hcost2⟩ :=
        steps_compileExpr ctx hc2 hpc1 (by rw [hMem1, hMem]) (by rw [hR1, hR]) hvM
      rw [hE1] at hE2
      obtain ⟨k3, hs3, hpc3, hE3, hMem3, hk3⟩ := steps_move E_ne_Mem hM1 (by omega) hE2
      obtain ⟨k4, hs4, hpc4, hE4, hMem4, hk4⟩ := steps_move E_ne_Mem hM2 hpc3 hE3
      have hMem2 : k2.stk Mem = cfg.stk Mem := by rw [keeps_stk_eq hk2 (by simp [E_ne_Mem.symm]), hMem1]
      have hMem4' : k4.stk Mem = (evalExpr st addr).1 :: (evalExpr st val).1 :: cfg.stk Mem := by
        rw [hMem4, hMem3, hMem2]
      have hR4 : k4.stk R = cfg.stk R := by
        rw [keeps_stk_eq hk4 (by simp [E_ne_R.symm, Mem_ne_R.symm]),
          keeps_stk_eq hk3 (by simp [E_ne_R.symm, Mem_ne_R.symm]),
          keeps_stk_eq hk2 (by simp [E_ne_R.symm]), hR1]
      have hta : 1 ≤ (evalExpr st addr).2 := one_le_evalExpr_cost st addr
      have htv : 1 ≤ (evalExpr st val).2 := one_le_evalExpr_cost st val
      set cTot := (evalExpr st addr).2 + (evalExpr st val).2 + 1 +
          len (evalExpr st addr).1 + len (evalExpr st val).1
      refine ⟨k4, S1 + S2 + (1 + len (evalExpr st val).1) + (1 + len (evalExpr st addr).1),
        ((hs1.trans hs2).trans hs3).trans hs4, ?_, hE4, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [compileStmt, List.length_append, List.length_cons, List.length_nil]
        change k4.pc = a + (c1.length + c2.length + 2); omega
      · rw [hMem4', memOf_cons_cons, hMem]
      · rw [hR4, hR]
      · exact keeps_trans
          (keeps_trans (keeps_mono (by simp) hk1) (keeps_mono (by simp) hk2))
          (keeps_trans (keeps_mono (by intro t ht; simp at ht ⊢; tauto) hk3)
            (keeps_mono (by intro t ht; simp at ht ⊢; tauto) hk4))
      · rw [hMem4']; simp only [listSize_cons]; omega
      · rw [hR4]; omega
      · rw [hMem1, hR1] at hcost2
        set W := listSize (cfg.stk Mem) + listSize (cfg.stk R) + (len M + 3) * cTot + 1
        set K := stmtConst ctx M
        have hS1' : S1 ≤ K * W * (evalExpr st addr).2 ^ 2 := expr_to_stmt_cost hcost1
        have hS2' : S2 ≤ K * W * (evalExpr st val).2 ^ 2 := expr_to_stmt_cost hcost2
        have hK : 20 ≤ K := twenty_le_stmtConst ctx M
        have hd : (1 + len (evalExpr st val).1) + (1 + len (evalExpr st addr).1) ≤ K * W := by
          have h1 : (1 + len (evalExpr st val).1) + (1 + len (evalExpr st addr).1) ≤ cTot := by
            omega
          have h2 : cTot ≤ W := by
            have : cTot ≤ (len M + 3) * cTot := Nat.le_mul_of_pos_left _ (by omega)
            omega
          exact le_trans (le_trans h1 h2) (Nat.le_mul_of_pos_left _ (by omega))
        have hsum := stmt_cost_two (K := K) (W := W) (c := cTot)
          (t₁ := (evalExpr st addr).2) (t₂ := (evalExpr st val).2)
          (d := (1 + len (evalExpr st val).1) + (1 + len (evalExpr st addr).1)) (by omega) hd
        exact le_trans (by omega) hsum
    | seq s t =>
      simp only [exec] at hexec
      have hs1M : maxRegStmt s ≤ M := le_trans (le_max_left _ _) hsM
      have ht1M : maxRegStmt t ≤ M := le_trans (le_max_right _ _) hsM
      set c1 := compileStmt ctx procAddr ep s a
      set c2 := compileStmt ctx procAddr ep t (a + c1.length)
      have hc1 : CodeAt P a c1 := hc.append_left
      have hc2 : CodeAt P (a + c1.length) c2 := hc.append_right
      cases h1 : exec p f s st with
      | none => simp [h1] at hexec
      | some res1 =>
        rw [h1] at hexec
        obtain ⟨o1, st1, cost1⟩ := res1
        cases o1 with
        | returned v =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hexec
          obtain ⟨rfl, rfl, rfl⟩ := hexec
          obtain ⟨k1, S1, hs1, hpc1, hE1, hMem1, hR1, hk1, hszM1, hszR1, hcost1⟩ :=
            ih hs1M hc1 hpc hMem hR h1
          refine ⟨k1, S1, hs1, hpc1, hE1, hMem1, hR1, hk1, by omega, ?_, ?_⟩
          · have : (len M + 2) * cost1 ≤ (len M + 2) * (cost1 + 1) :=
              Nat.mul_le_mul_left _ (Nat.le_succ _)
            omega
          · set K := stmtConst ctx M
            have hW : listSize (cfg.stk Mem) + listSize (cfg.stk R) + (len M + 3) * cost1 + 1 ≤
                listSize (cfg.stk Mem) + listSize (cfg.stk R) + (len M + 3) * (cost1 + 1) + 1 := by
              have : (len M + 3) * cost1 ≤ (len M + 3) * (cost1 + 1) :=
                Nat.mul_le_mul_left _ (Nat.le_succ _)
              omega
            have hsq : cost1 ^ 2 ≤ (cost1 + 1) ^ 2 := Nat.pow_le_pow_left (Nat.le_succ _) 2
            exact le_trans hcost1 (Nat.mul_le_mul (Nat.mul_le_mul_left K hW) hsq)
        | normal =>
          simp only at hexec
          cases h2 : exec p f t st1 with
          | none => simp [h2] at hexec
          | some res2 =>
            rw [h2] at hexec
            obtain ⟨o2, st2, cost2⟩ := res2
            simp only [Option.some.injEq, Prod.mk.injEq] at hexec
            obtain ⟨rfl, rfl, rfl⟩ := hexec
            obtain ⟨k1, S1, hs1, hpc1, hE1, hMem1, hR1, hk1, hszM1, hszR1, hcost1⟩ :=
              ih hs1M hc1 hpc hMem hR h1
            obtain ⟨k2, S2, hs2, hpc2, hE2, hMem2, hR2, hk2, hszM2, hszR2, hcost2⟩ :=
              ih ht1M hc2 hpc1 hMem1 hR1 h2
            refine ⟨k2, S1 + S2, hs1.trans hs2, ?_, ?_, hMem2, hR2,
              keeps_trans hk1 hk2, ?_, ?_, ?_⟩
            · cases o2 with
              | normal =>
                simp only [outcomePc, compileStmt, List.length_append] at hpc2 ⊢
                change k2.pc = a + c1.length + c2.length at hpc2
                change k2.pc = a + (c1.length + c2.length); omega
              | returned v => exact hpc2
            · cases o2 with
              | normal => simp only [outcomeE] at hE1 hE2 ⊢; rw [hE2, hE1]
              | returned v => simp only [outcomeE] at hE1 hE2 ⊢; rw [hE2, hE1]
            · omega
            · have : (len M + 2) * cost1 + (len M + 2) * cost2 ≤
                  (len M + 2) * (cost1 + cost2 + 1) := by
                rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
              omega
            · set W := listSize (cfg.stk Mem) + listSize (cfg.stk R) +
                  (len M + 3) * (cost1 + cost2 + 1) + 1
              set K := stmtConst ctx M
              have hW1 : listSize (cfg.stk Mem) + listSize (cfg.stk R) + (len M + 3) * cost1 + 1 ≤
                  W := by
                have : (len M + 3) * cost1 ≤ (len M + 3) * (cost1 + cost2 + 1) :=
                  Nat.mul_le_mul_left _ (by omega)
                omega
              have hW2 : listSize (k1.stk Mem) + listSize (k1.stk R) + (len M + 3) * cost2 + 1 ≤
                  W := by
                have : (len M + 3) * (cost1 + cost2) ≤ (len M + 3) * (cost1 + cost2 + 1) :=
                  Nat.mul_le_mul_left _ (by omega)
                have hmul : cost1 + (len M + 2) * cost1 = (len M + 3) * cost1 := by ring
                have hadd : (len M + 3) * cost1 + (len M + 3) * cost2 =
                    (len M + 3) * (cost1 + cost2) := (Nat.mul_add _ _ _).symm
                omega
              have hS1' : S1 ≤ K * W * cost1 ^ 2 :=
                le_trans hcost1 (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left K hW1))
              have hS2' : S2 ≤ K * W * cost2 ^ 2 :=
                le_trans hcost2 (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left K hW2))
              have hsum := stmt_cost_two (K := K) (W := W) (c := cost1 + cost2 + 1)
                (t₁ := cost1) (t₂ := cost2) (d := 0) le_rfl (Nat.zero_le _)
              omega
    | cond e s t =>
      simp only [exec] at hexec
      have heM : maxRegExpr e ≤ M := le_trans (le_max_left _ _) hsM
      have hs1M : maxRegStmt s ≤ M :=
        le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hsM)
      have ht1M : maxRegStmt t ≤ M :=
        le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hsM)
      set ce := compileExpr ctx e a
      set cs := compileStmt ctx procAddr ep s (a + ce.length + 1)
      set ct := compileStmt ctx procAddr ep t (a + ce.length + 1 + cs.length + 1)
      set endAddr := a + ce.length + 1 + cs.length + 1 + ct.length
      have hc1234 : CodeAt P a (((ce ++ [.jz E (a + ce.length + 1 + cs.length + 1)]) ++ cs) ++
          [.jmp endAddr]) := hc.append_left
      have hc123 : CodeAt P a ((ce ++ [.jz E (a + ce.length + 1 + cs.length + 1)]) ++ cs) :=
        hc1234.append_left
      have hc12 : CodeAt P a (ce ++ [.jz E (a + ce.length + 1 + cs.length + 1)]) :=
        hc123.append_left
      have hce : CodeAt P a ce := hc12.append_left
      have hJz : P[a + ce.length]? = some (.jz E (a + ce.length + 1 + cs.length + 1)) :=
        hc12.append_right.cons
      have hcs : CodeAt P (a + ce.length + 1) cs := by
        simpa [List.length_append, List.length_singleton, Nat.add_assoc] using hc123.append_right
      have hJmp : P[a + ce.length + 1 + cs.length]? = some (.jmp endAddr) := by
        have h := hc1234.append_right.cons
        have heq : a + ((ce ++ [Instr.jz E (a + ce.length + 1 + cs.length + 1)]) ++ cs).length =
            a + ce.length + 1 + cs.length := by
          simp [List.length_append]; omega
        rwa [heq] at h
      have hct : CodeAt P (a + ce.length + 1 + cs.length + 1) ct := by
        have h := hc.append_right
        convert h using 1
        simp only [List.length_append, List.length_singleton]
        change a + ce.length + 1 + cs.length + 1 = a + (ce.length + 1 + cs.length + 1)
        omega
      have hEnd : a + (compileStmt ctx procAddr ep (.cond e s t) a).length = endAddr := by
        simp only [compileStmt, List.length_append, List.length_singleton]
        change a + (ce.length + 1 + cs.length + 1 + ct.length) = endAddr; omega
      cases hbr : exec p f (if (evalExpr st e).1 = 0 then t else s) st with
      | none => simp [hbr] at hexec
      | some res =>
        rw [hbr] at hexec
        obtain ⟨ob, st1, costb⟩ := res
        simp only [Option.some.injEq, Prod.mk.injEq] at hexec
        obtain ⟨rfl, rfl, rfl⟩ := hexec
        obtain ⟨k1, S1, hs1, hpc1, hE1, hk1, hcost1⟩ :=
          steps_compileExpr ctx hce hpc hMem hR heM
        obtain ⟨k2, hs2, hpc2, hE2, hk2⟩ := steps_jz hJz hpc1 hE1
        have hMem2 : k2.stk Mem = cfg.stk Mem := by
          rw [keeps_stk_eq hk2 (by simp [E_ne_Mem.symm]),
            keeps_stk_eq hk1 (by simp [E_ne_Mem.symm])]
        have hR2 : k2.stk R = cfg.stk R := by
          rw [keeps_stk_eq hk2 (by simp [E_ne_R.symm]),
            keeps_stk_eq hk1 (by simp [E_ne_R.symm])]
        have hk12 : Keeps [E, Mem, R] cfg k2 :=
          keeps_mono (by simp) (keeps_trans hk1 hk2)
        have hlene : len (evalExpr st e).1 ≤ (evalExpr st e).2 := len_evalExpr_le st e
        set cTot := (evalExpr st e).2 + costb + 1
        set W := listSize (cfg.stk Mem) + listSize (cfg.stk R) + (len M + 3) * cTot + 1
        set K := stmtConst ctx M
        have hK : 20 ≤ K := twenty_le_stmtConst ctx M
        have hW2 : listSize (k2.stk Mem) + listSize (k2.stk R) + (len M + 3) * costb + 1 ≤ W := by
          rw [hMem2, hR2]
          have : (len M + 3) * costb ≤ (len M + 3) * cTot := Nat.mul_le_mul_left _ (by omega)
          omega
        by_cases hv : (evalExpr st e).1 = 0
        · simp only [hv, ↓reduceIte] at hbr hpc2
          obtain ⟨k3, S3, hs3, hpc3, hE3, hMem3, hR3, hk3, hszM3, hszR3, hcost3⟩ :=
            ih ht1M hct hpc2 (by rw [hMem2, hMem]) (by rw [hR2, hR]) hbr
          refine ⟨k3, S1 + (1 + len (evalExpr st e).1) + S3,
            (hs1.trans hs2).trans hs3, ?_, ?_, hMem3, hR3, keeps_trans hk12 hk3, ?_, ?_, ?_⟩
          · cases ob with
            | normal => rw [hEnd]; exact hpc3
            | returned v => exact hpc3
          · cases ob <;> simp only [hE3, hE2]
          · rw [hMem2] at hszM3; omega
          · rw [hR2] at hszR3
            have : (len M + 2) * costb ≤ (len M + 2) * cTot := Nat.mul_le_mul_left _ (by omega)
            omega
          · have hS1' : S1 ≤ K * W * (evalExpr st e).2 ^ 2 := expr_to_stmt_cost hcost1
            have hS3' : S3 ≤ K * W * costb ^ 2 :=
              le_trans hcost3 (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left K hW2))
            have hd : 1 + len (evalExpr st e).1 ≤ K * W := by
              have h1 : 1 + len (evalExpr st e).1 ≤ cTot := by omega
              have h2 : cTot ≤ W := by
                have : cTot ≤ (len M + 3) * cTot := Nat.le_mul_of_pos_left _ (by omega)
                omega
              exact le_trans (le_trans h1 h2) (Nat.le_mul_of_pos_left _ (by omega))
            have hsum := stmt_cost_two (K := K) (W := W) (c := cTot)
              (t₁ := (evalExpr st e).2) (t₂ := costb) (d := 1 + len (evalExpr st e).1) le_rfl hd
            exact le_trans (by omega) hsum
        · simp only [hv, ↓reduceIte] at hbr hpc2
          obtain ⟨k3, S3, hs3, hpc3, hE3, hMem3, hR3, hk3, hszM3, hszR3, hcost3⟩ :=
            ih hs1M hcs hpc2 (by rw [hMem2, hMem]) (by rw [hR2, hR]) hbr
          have hS1' : S1 ≤ K * W * (evalExpr st e).2 ^ 2 := expr_to_stmt_cost hcost1
          have hS3' : S3 ≤ K * W * costb ^ 2 :=
            le_trans hcost3 (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left K hW2))
          cases ob with
          | returned v =>
            refine ⟨k3, S1 + (1 + len (evalExpr st e).1) + S3,
              (hs1.trans hs2).trans hs3, hpc3, by rw [hE3, hE2], hMem3, hR3,
              keeps_trans hk12 hk3, ?_, ?_, ?_⟩
            · rw [hMem2] at hszM3; omega
            · rw [hR2] at hszR3
              have : (len M + 2) * costb ≤ (len M + 2) * cTot := Nat.mul_le_mul_left _ (by omega)
              omega
            · have hd : 1 + len (evalExpr st e).1 ≤ K * W := by
                have h1 : 1 + len (evalExpr st e).1 ≤ cTot := by omega
                have h2 : cTot ≤ W := by
                  have : cTot ≤ (len M + 3) * cTot := Nat.le_mul_of_pos_left _ (by omega)
                  omega
                exact le_trans (le_trans h1 h2) (Nat.le_mul_of_pos_left _ (by omega))
              have hsum := stmt_cost_two (K := K) (W := W) (c := cTot)
                (t₁ := (evalExpr st e).2) (t₂ := costb) (d := 1 + len (evalExpr st e).1) le_rfl hd
              exact le_trans (by omega) hsum
          | normal =>
            obtain ⟨k4, hs4, hpc4, hk4⟩ := steps_jmp hJmp hpc3
            refine ⟨k4, S1 + (1 + len (evalExpr st e).1) + S3 + 1,
              ((hs1.trans hs2).trans hs3).trans hs4, by rw [hEnd]; exact hpc4,
              by rw [keeps_stk_eq hk4 (by simp), hE3, hE2],
              by rw [keeps_stk_eq hk4 (by simp), hMem3],
              by rw [keeps_stk_eq hk4 (by simp), hR3],
              keeps_trans (keeps_trans hk12 hk3) (keeps_mono (by simp) hk4), ?_, ?_, ?_⟩
            · rw [keeps_stk_eq hk4 (by simp)]; rw [hMem2] at hszM3; omega
            · rw [keeps_stk_eq hk4 (by simp)]; rw [hR2] at hszR3
              have : (len M + 2) * costb ≤ (len M + 2) * cTot := Nat.mul_le_mul_left _ (by omega)
              omega
            · have hd : (1 + len (evalExpr st e).1) + 1 ≤ K * W := by
                have h1 : (1 + len (evalExpr st e).1) + 1 ≤ cTot + 1 := by omega
                have h2 : cTot + 1 ≤ W := by
                  have : cTot ≤ (len M + 3) * cTot := Nat.le_mul_of_pos_left _ (by omega)
                  omega
                exact le_trans (le_trans h1 h2) (Nat.le_mul_of_pos_left _ (by omega))
              have hsum := stmt_cost_two (K := K) (W := W) (c := cTot)
                (t₁ := (evalExpr st e).2) (t₂ := costb)
                (d := (1 + len (evalExpr st e).1) + 1) le_rfl hd
              exact le_trans (by omega) hsum
    | loop e body =>
      simp only [exec] at hexec
      have heM : maxRegExpr e ≤ M := le_trans (le_max_left _ _) hsM
      have hbM : maxRegStmt body ≤ M := le_trans (le_max_right _ _) hsM
      set ce := compileExpr ctx e a
      set cb := compileStmt ctx procAddr ep body (a + ce.length + 1)
      set endAddr := a + ce.length + 1 + cb.length + 1
      have hc123 : CodeAt P a ((ce ++ [.jz E endAddr]) ++ cb) := hc.append_left
      have hc12 : CodeAt P a (ce ++ [.jz E endAddr]) := hc123.append_left
      have hce : CodeAt P a ce := hc12.append_left
      have hJz : P[a + ce.length]? = some (.jz E endAddr) := hc12.append_right.cons
      have hcb : CodeAt P (a + ce.length + 1) cb := by
        simpa [List.length_append, List.length_singleton, Nat.add_assoc] using hc123.append_right
      have hJmp : P[a + ce.length + 1 + cb.length]? = some (.jmp a) := by
        have h := hc.append_right.cons
        convert h using 2
        simp only [List.length_append, List.length_singleton]
        change a + ce.length + 1 + cb.length = a + (ce.length + 1 + cb.length)
        omega
      have hEnd : a + (compileStmt ctx procAddr ep (.loop e body) a).length = endAddr := by
        simp only [compileStmt, List.length_append, List.length_singleton]
        change a + (ce.length + 1 + cb.length + 1) = endAddr; omega
      obtain ⟨k1, S1, hs1, hpc1, hE1, hk1, hcost1⟩ :=
        steps_compileExpr ctx hce hpc hMem hR heM
      obtain ⟨k2, hs2, hpc2, hE2, hk2⟩ := steps_jz hJz hpc1 hE1
      have hMem2 : k2.stk Mem = cfg.stk Mem := by
        rw [keeps_stk_eq hk2 (by simp [E_ne_Mem.symm]),
          keeps_stk_eq hk1 (by simp [E_ne_Mem.symm])]
      have hR2 : k2.stk R = cfg.stk R := by
        rw [keeps_stk_eq hk2 (by simp [E_ne_R.symm]),
          keeps_stk_eq hk1 (by simp [E_ne_R.symm])]
      have hk12 : Keeps [E, Mem, R] cfg k2 :=
        keeps_mono (by simp) (keeps_trans hk1 hk2)
      have hlene : len (evalExpr st e).1 ≤ (evalExpr st e).2 := len_evalExpr_le st e
      by_cases hv : (evalExpr st e).1 = 0
      · simp only [hv, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hexec hpc2
        obtain ⟨rfl, rfl, rfl⟩ := hexec
        refine ⟨k2, S1 + (1 + len (evalExpr st e).1), hs1.trans hs2,
          by rw [hEnd]; exact hpc2, hE2, by rw [hMem2, hMem], by rw [hR2, hR], hk12,
          by rw [hMem2]; omega, by rw [hR2]; omega, ?_⟩
        set cTot := (evalExpr st e).2 + 1
        set W := listSize (cfg.stk Mem) + listSize (cfg.stk R) + (len M + 3) * cTot + 1
        set K := stmtConst ctx M
        have hK : 20 ≤ K := twenty_le_stmtConst ctx M
        have hS1' : S1 ≤ K * W * (evalExpr st e).2 ^ 2 := expr_to_stmt_cost hcost1
        have hd : 1 + len (evalExpr st e).1 ≤ K * W := by
          have h1 : 1 + len (evalExpr st e).1 ≤ cTot := by omega
          have h2 : cTot ≤ W := by
            have : cTot ≤ (len M + 3) * cTot := Nat.le_mul_of_pos_left _ (by omega)
            omega
          exact le_trans (le_trans h1 h2) (Nat.le_mul_of_pos_left _ (by omega))
        have hsum := stmt_cost_one (K := K) (W := W) (c := cTot)
          (t := (evalExpr st e).2) (d := 1 + len (evalExpr st e).1) le_rfl hd
        exact le_trans (by omega) hsum
      · simp only [hv, ↓reduceIte] at hexec hpc2
        cases hb : exec p f body st with
        | none => simp [hb] at hexec
        | some resb =>
          rw [hb] at hexec
          obtain ⟨ob, stb, costb⟩ := resb
          cases ob with
          | returned w =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hexec
            obtain ⟨rfl, rfl, rfl⟩ := hexec
            obtain ⟨k3, S3, hs3, hpc3, hE3, hMem3, hR3, hk3, hszM3, hszR3, hcost3⟩ :=
              ih hbM hcb hpc2 (by rw [hMem2, hMem]) (by rw [hR2, hR]) hb
            refine ⟨k3, S1 + (1 + len (evalExpr st e).1) + S3,
              (hs1.trans hs2).trans hs3, hpc3, by rw [hE3, hE2], hMem3, hR3,
              keeps_trans hk12 hk3, ?_, ?_, ?_⟩
            · rw [hMem2] at hszM3; omega
            · rw [hR2] at hszR3
              have : (len M + 2) * costb ≤ (len M + 2) * ((evalExpr st e).2 + costb + 1) :=
                Nat.mul_le_mul_left _ (by omega)
              omega
            · set cTot := (evalExpr st e).2 + costb + 1
              set W := listSize (cfg.stk Mem) + listSize (cfg.stk R) + (len M + 3) * cTot + 1
              set K := stmtConst ctx M
              have hK : 20 ≤ K := twenty_le_stmtConst ctx M
              have hS1' : S1 ≤ K * W * (evalExpr st e).2 ^ 2 := expr_to_stmt_cost hcost1
              have hW2 : listSize (k2.stk Mem) + listSize (k2.stk R) +
                  (len M + 3) * costb + 1 ≤ W := by
                rw [hMem2, hR2]
                have : (len M + 3) * costb ≤ (len M + 3) * cTot := Nat.mul_le_mul_left _ (by omega)
                omega
              have hS3' : S3 ≤ K * W * costb ^ 2 :=
                le_trans hcost3 (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left K hW2))
              have hd : 1 + len (evalExpr st e).1 ≤ K * W := by
                have h1 : 1 + len (evalExpr st e).1 ≤ cTot := by omega
                have h2 : cTot ≤ W := by
                  have : cTot ≤ (len M + 3) * cTot := Nat.le_mul_of_pos_left _ (by omega)
                  omega
                exact le_trans (le_trans h1 h2) (Nat.le_mul_of_pos_left _ (by omega))
              have hsum := stmt_cost_two (K := K) (W := W) (c := cTot)
                (t₁ := (evalExpr st e).2) (t₂ := costb) (d := 1 + len (evalExpr st e).1) le_rfl hd
              exact le_trans (by omega) hsum
          | normal =>
            simp only at hexec
            cases hr : exec p f (.loop e body) stb with
            | none => simp [hr] at hexec
            | some resr =>
              rw [hr] at hexec
              obtain ⟨or_, str, costr⟩ := resr
              simp only [Option.some.injEq, Prod.mk.injEq] at hexec
              obtain ⟨rfl, rfl, rfl⟩ := hexec
              obtain ⟨k3, S3, hs3, hpc3, hE3, hMem3, hR3, hk3, hszM3, hszR3, hcost3⟩ :=
                ih hbM hcb hpc2 (by rw [hMem2, hMem]) (by rw [hR2, hR]) hb
              obtain ⟨k4, hs4, hpc4, hk4⟩ := steps_jmp hJmp hpc3
              have hMem4 : k4.stk Mem = k3.stk Mem := keeps_stk_eq hk4 (by simp)
              have hR4 : k4.stk R = k3.stk R := keeps_stk_eq hk4 (by simp)
              have hE4 : k4.stk E = cfg.stk E := by rw [keeps_stk_eq hk4 (by simp), hE3, hE2]; rfl
              obtain ⟨k5, S5, hs5, hpc5, hE5, hMem5, hR5, hk5, hszM5, hszR5, hcost5⟩ :=
                ih hsM hc hpc4 (by rw [hMem4, hMem3]) (by rw [hR4, hR3]) hr
              refine ⟨k5, S1 + (1 + len (evalExpr st e).1) + S3 + 1 + S5,
                (((hs1.trans hs2).trans hs3).trans hs4).trans hs5, hpc5, ?_, hMem5, hR5,
                keeps_trans (keeps_trans (keeps_trans hk12 hk3) (keeps_mono (by simp) hk4)) hk5,
                ?_, ?_, ?_⟩
              · cases or_ <;> simp only [hE5, hE4]
              · rw [hMem4] at hszM5; rw [hMem2] at hszM3; omega
              · rw [hR4] at hszR5; rw [hR2] at hszR3
                have : (len M + 2) * costb + (len M + 2) * costr ≤
                    (len M + 2) * ((evalExpr st e).2 + costb + costr + 1) := by
                  rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
                omega
              · set cTot := (evalExpr st e).2 + costb + costr + 1
                set W := listSize (cfg.stk Mem) + listSize (cfg.stk R) + (len M + 3) * cTot + 1
                set K := stmtConst ctx M
                have hK : 20 ≤ K := twenty_le_stmtConst ctx M
                have hS1' : S1 ≤ K * W * (evalExpr st e).2 ^ 2 := expr_to_stmt_cost hcost1
                have hW2 : listSize (k2.stk Mem) + listSize (k2.stk R) +
                    (len M + 3) * costb + 1 ≤ W := by
                  rw [hMem2, hR2]
                  have : (len M + 3) * costb ≤ (len M + 3) * cTot :=
                    Nat.mul_le_mul_left _ (by omega)
                  omega
                have hS3' : S3 ≤ K * W * costb ^ 2 :=
                  le_trans hcost3 (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left K hW2))
                have hW4 : listSize (k4.stk Mem) + listSize (k4.stk R) +
                    (len M + 3) * costr + 1 ≤ W := by
                  rw [hMem4, hR4]
                  rw [hMem2] at hszM3; rw [hR2] at hszR3
                  have hmul : costb + (len M + 2) * costb = (len M + 3) * costb := by ring
                  have hadd : (len M + 3) * costb + (len M + 3) * costr =
                      (len M + 3) * (costb + costr) := (Nat.mul_add _ _ _).symm
                  have : (len M + 3) * (costb + costr) ≤ (len M + 3) * cTot :=
                    Nat.mul_le_mul_left _ (by omega)
                  omega
                have hS5' : S5 ≤ K * W * costr ^ 2 :=
                  le_trans hcost5 (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left K hW4))
                have hd : (1 + len (evalExpr st e).1) + 1 ≤ K * W := by
                  have h1 : (1 + len (evalExpr st e).1) + 1 ≤ cTot + 1 := by omega
                  have h2 : cTot + 1 ≤ W := by
                    have : cTot ≤ (len M + 3) * cTot := Nat.le_mul_of_pos_left _ (by omega)
                    omega
                  exact le_trans (le_trans h1 h2) (Nat.le_mul_of_pos_left _ (by omega))
                have hsum := stmt_cost_three (K := K) (W := W) (c := cTot)
                  (t₁ := (evalExpr st e).2) (t₂ := costb) (t₃ := costr)
                  (d := (1 + len (evalExpr st e).1) + 1) le_rfl hd
                exact le_trans (by omega) hsum
    | call r g args =>
      simp only [exec] at hexec
      cases hg : p.procs[g]? with
      | none => simp [hg] at hexec
      | some body =>
        rw [hg] at hexec
        dsimp only at hexec
        cases hb : exec p f body
            { mem := st.mem, regs := fun i => (evalArgs st args).1.getD i 0 } with
        | none => rw [hb] at hexec; simp at hexec
        | some resb =>
          rw [hb] at hexec
          obtain ⟨ob, stb, costb⟩ := resb
          simp only [Option.some.injEq, Prod.mk.injEq] at hexec
          obtain ⟨rfl, rfl, rfl⟩ := hexec
          have hrM : r ≤ M := le_trans (le_max_left _ _) hsM
          have hlenArgsM : args.length ≤ M :=
            le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hsM)
          have hargsM : maxRegArgs args ≤ M :=
            le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hsM)
          have hbodyM : maxRegStmt body ≤ M :=
            le_trans (maxRegProcs_getElem? hg) hpM
          -- Slice `CodeAt` for the 6 parts of `compileStmt (.call r g args)`.
          set cArgs := compileArgs ctx args a
          set cSave := saveR (a + cArgs.length)
          set cBuild := buildRFrom 0 args.length
          set cCall := [Instr.call (procAddr g)]
          set cRest := restoreR (a + cArgs.length + cSave.length + cBuild.length + 1)
          have hc5 : CodeAt P a ((((cArgs ++ cSave) ++ cBuild) ++ cCall) ++ cRest) :=
            hc.append_left
          have hc4 : CodeAt P a (((cArgs ++ cSave) ++ cBuild) ++ cCall) := hc5.append_left
          have hc3 : CodeAt P a ((cArgs ++ cSave) ++ cBuild) := hc4.append_left
          have hc2 : CodeAt P a (cArgs ++ cSave) := hc3.append_left
          have hcArgs : CodeAt P a cArgs := hc2.append_left
          have hcSave : CodeAt P (a + cArgs.length) cSave := hc2.append_right
          have hcBuild : CodeAt P (a + cArgs.length + cSave.length) cBuild := by
            have h := hc3.append_right
            rwa [show a + (cArgs ++ cSave).length = a + cArgs.length + cSave.length by
              simp [List.length_append]; omega] at h
          have hcCall : P[a + cArgs.length + cSave.length + cBuild.length]? =
              some (.call (procAddr g)) := by
            have h := hc4.append_right.cons
            rwa [show a + ((cArgs ++ cSave) ++ cBuild).length =
              a + cArgs.length + cSave.length + cBuild.length by
              simp [List.length_append]; omega] at h
          set retAddr := a + cArgs.length + cSave.length + cBuild.length + 1
          have hcRest : CodeAt P retAddr cRest := by
            have h := hc5.append_right
            rwa [show a + (((cArgs ++ cSave) ++ cBuild) ++ cCall).length = retAddr by
              simp [List.length_append, cCall, retAddr]; omega] at h
          have hcTail : CodeAt P (retAddr + cRest.length) [.move E R, .push R r] := by
            have h := hc.append_right
            rwa [show a + ((((cArgs ++ cSave) ++ cBuild) ++ cCall) ++ cRest).length =
              retAddr + cRest.length by
              simp [List.length_append, cCall, retAddr]; omega] at h
          have hMove : P[retAddr + cRest.length]? = some (.move E R) := hcTail.cons
          have hPush : P[retAddr + cRest.length + 1]? = some (.push R r) := hcTail.tail.cons
          -- Step 1: evaluate arguments onto `E`.
          obtain ⟨k1, S1, hs1, hpc1, hE1, hk1, hcost1⟩ :=
            steps_compileArgs ctx hcArgs hpc hMem hR hargsM
          have hMem1 : k1.stk Mem = cfg.stk Mem := keeps_stk_eq hk1 (by simp [E_ne_Mem.symm])
          have hR1 : k1.stk R = cfg.stk R := keeps_stk_eq hk1 (by simp [E_ne_R.symm])
          have hF1 : k1.stk F = cfg.stk F := keeps_stk_eq hk1 (by simp [E_ne_F.symm])
          -- Step 2: save `R` onto `F`.
          obtain ⟨k2, S2, hs2, hpc2, hR2, hF2, hk2, hcost2⟩ := steps_saveR hcSave hpc1
          have hE2 : k2.stk E = (evalArgs st args).1 ++ cfg.stk E := by
            rw [keeps_stk_eq hk2 (by simp [E_ne_R, E_ne_F]), hE1]
          have hMem2 : k2.stk Mem = cfg.stk Mem := by
            rw [keeps_stk_eq hk2 (by simp [Mem_ne_R, Mem_ne_F]), hMem1]
          -- Step 3: build new `R` from arguments on `E`.
          have hlenVs : (evalArgs st args).1.length = args.length := evalArgs_length st args
          have hcBuild' : CodeAt P (a + cArgs.length + 5)
              (buildRFrom 0 (evalArgs st args).1.length) := by
            rw [hlenVs]; exact hcBuild
          obtain ⟨k3, S3, hs3, hpc3, hE3, hmemR3, hk3, hszR3, hcost3⟩ :=
            steps_buildR (M := M) hcBuild' (by omega) hE2 hR2 (by rw [hlenVs]; exact hlenArgsM)
          have hMem3 : k3.stk Mem = cfg.stk Mem := by
            rw [keeps_stk_eq hk3 (by simp [E_ne_Mem.symm, Mem_ne_R]), hMem2]
          have hF3 : k3.stk F = pushFrame (cfg.stk R) (0 :: cfg.stk F) := by
            rw [keeps_stk_eq hk3 (by simp [E_ne_F.symm, R_ne_F.symm]), hF2, hR1, hF1]
          -- Step 4: `call (procAddr g)`.
          have hpc3' : k3.pc = a + cArgs.length + cSave.length + cBuild.length := by
            simp only [cSave, cBuild, saveR_length, buildRFrom_length]
            rw [hlenVs] at hpc3; omega
          obtain ⟨k4, hs4, hpc4, hrs4, hstk4, hinp4, hout4⟩ := steps_call hcCall hpc3'
          -- Step 5: execute procedure `g`'s body.
          have hcProc : CodeAt P (procAddr g) (compileProc ctx procAddr body (procAddr g)) :=
            hprocs g body hg
          have hcBody : CodeAt P (procAddr g)
              (compileStmt ctx procAddr (procEpilogue ctx body (procAddr g)) body (procAddr g)) :=
            hcProc.append_left.append_left.append_left
          obtain ⟨k5, S5, hs5, hpc5, hE5, hMem5, _, hk5, hszM5, hszR5, hcost5⟩ :=
            ih hbodyM hcBody hpc4
              (by rw [hstk4, hMem3, hMem]) (by rw [hstk4, hmemR3]) hb
          -- Step 6: execute procedure `g`'s epilogue (`push E 0` if normal, `emptyR`, `ret`).
          have hrs5 : k5.rs = retAddr :: cfg.rs := by
            rw [hk5.2.1, hrs4, hk3.2.1, hk2.2.1, hk1.2.1]
          have hE4 : k4.stk E = cfg.stk E := by rw [hstk4, hE3]
          rw [hE4] at hE5
          obtain ⟨k6, S6, hs6, hpc6, hE6, hR6, hMem6, hF6, hoth6, hrs6, hinp6, hout6, hcost6⟩ :=
            steps_procEpilogue ctx hcProc hpc5 hE5 hrs5
          -- Step 7: restore caller's `R` from `F`.
          have hF5 : k5.stk F = pushFrame (cfg.stk R) (0 :: cfg.stk F) := by
            rw [keeps_stk_eq hk5 (by simp [E_ne_F.symm, Mem_ne_F.symm, R_ne_F.symm]), hstk4, hF3]
          obtain ⟨k7, S7, hs7, hpc7, hR7, hF7, hk7, hcost7⟩ :=
            steps_restoreR hcRest hpc6 hR6 (by rw [hF6, hF5])
          -- Step 8: move return value to `R`, push `r` onto `R`.
          have hE7 : k7.stk E = ob.retVal :: cfg.stk E := by
            rw [keeps_stk_eq hk7 (by simp [E_ne_R, E_ne_F]), hE6]
          obtain ⟨k8, hs8, hpc8, hE8, hR8, hk8⟩ := steps_move E_ne_R hMove hpc7 hE7
          obtain ⟨k9, hs9, hpc9, hR9, hk9⟩ := steps_push hPush hpc8
          -- Assemble postconditions.
          have hMem9 : k9.stk Mem = k5.stk Mem := by
            rw [keeps_stk_eq hk9 (by simp [Mem_ne_R]),
              keeps_stk_eq hk8 (by simp [E_ne_Mem.symm, Mem_ne_R]),
              keeps_stk_eq hk7 (by simp [Mem_ne_R, Mem_ne_F]), hMem6]
          have hR9' : k9.stk R = r :: ob.retVal :: cfg.stk R := by rw [hR9, hR8, hR7]
          have hF9 : k9.stk F = cfg.stk F := by
            rw [keeps_stk_eq hk9 (by simp [R_ne_F.symm]),
              keeps_stk_eq hk8 (by simp [E_ne_F.symm, R_ne_F.symm]), hF7]
          have hE9 : k9.stk E = cfg.stk E := by
            rw [keeps_stk_eq hk9 (by simp [E_ne_R]), hE8]
          have hKeeps9 : Keeps [E, Mem, R] cfg k9 := by
            refine ⟨fun t ht => ?_, ?_, ?_, ?_⟩
            · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ht
              by_cases htF : t = F
              · rw [htF, hF9]
              · rw [keeps_stk_eq hk9 (by simp [ht.2.2]),
                  keeps_stk_eq hk8 (by simp [ht.1, ht.2.2]),
                  keeps_stk_eq hk7 (by simp [ht.2.2, htF]),
                  hoth6 t (by simp [ht.1, ht.2.1, ht.2.2]),
                  keeps_stk_eq hk5 (by simp [ht.1, ht.2.1, ht.2.2]),
                  hstk4,
                  keeps_stk_eq hk3 (by simp [ht.1, ht.2.2]),
                  keeps_stk_eq hk2 (by simp [ht.2.2, htF]),
                  keeps_stk_eq hk1 (by simp [ht.1])]
            · rw [hk9.2.1, hk8.2.1, hk7.2.1, hrs6]
            · rw [hk9.2.2.1, hk8.2.2.1, hk7.2.2.1, hinp6, hk5.2.2.1, hinp4,
                hk3.2.2.1, hk2.2.2.1, hk1.2.2.1]
            · rw [hk9.2.2.2, hk8.2.2.2, hk7.2.2.2, hout6, hk5.2.2.2, hout4,
                hk3.2.2.2, hk2.2.2.2, hk1.2.2.2]
          have hlenr : len r ≤ len M := GI.Machine.len_mono hrM
          have hlenw : len ob.retVal ≤ costb := len_retVal_le hb
          have hbuildBound : (len M + 1) * args.length + listSize (evalArgs st args).1 ≤
              (len M + 3) * (evalArgs st args).2 := evalArgs_buildR_bound st args M
          set tArgs := (evalArgs st args).2
          set cTot := tArgs + costb + 1
          set W := listSize (cfg.stk Mem) + listSize (cfg.stk R) + (len M + 3) * cTot + 1
          set K := stmtConst ctx M
          have hK : 20 ≤ K := twenty_le_stmtConst ctx M
          have hS1' : S1 ≤ K * W * tArgs ^ 2 := expr_to_stmt_cost hcost1
          have hR3Bound : listSize (k3.stk R) ≤ (len M + 3) * tArgs := by
            rw [hlenVs] at hszR3; exact le_trans hszR3 hbuildBound
          have hS3Bound : S3 ≤ (len M + 3) * tArgs := by
            rw [hlenVs] at hcost3; exact le_trans hcost3 hbuildBound
          have hW4 : listSize (k4.stk Mem) + listSize (k4.stk R) + (len M + 3) * costb + 1 ≤
              W := by
            rw [hstk4, hstk4, hMem3]
            have h1 : (len M + 3) * tArgs + (len M + 3) * costb =
                (len M + 3) * (tArgs + costb) := (Nat.mul_add _ _ _).symm
            have h2 : (len M + 3) * (tArgs + costb) ≤ (len M + 3) * cTot :=
              Nat.mul_le_mul_left _ (by omega)
            omega
          have hS5' : S5 ≤ K * W * costb ^ 2 :=
            le_trans hcost5 (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left K hW4))
          have hR5Bound : listSize (k5.stk R) ≤ W := by
            rw [hstk4] at hszR5
            have h1 : (len M + 2) * costb ≤ (len M + 3) * costb :=
              Nat.mul_le_mul_right _ (by omega)
            have h2 : (len M + 3) * tArgs + (len M + 3) * costb =
                (len M + 3) * (tArgs + costb) := (Nat.mul_add _ _ _).symm
            have h3 : (len M + 3) * (tArgs + costb) ≤ (len M + 3) * cTot :=
              Nat.mul_le_mul_left _ (by omega)
            omega
          have hS2Bound : S2 ≤ 5 * W := by rw [hR1] at hcost2; omega
          have hS3W : S3 ≤ W := by
            have : (len M + 3) * tArgs ≤ (len M + 3) * cTot := Nat.mul_le_mul_left _ (by omega)
            omega
          have hS6Bound : S6 ≤ 6 * W := by omega
          have hS7Bound : S7 ≤ 4 * W := by omega
          have hMovePush : (1 + len ob.retVal) + (1 + len r) ≤ W := by
            have h1 : (len M + 3) * cTot = (len M + 3) * (tArgs + costb) + (len M + 3) :=
              Nat.mul_succ _ _
            have h2 : costb ≤ (len M + 3) * (tArgs + costb) := by
              calc costb ≤ tArgs + costb := Nat.le_add_left _ _
                _ ≤ (len M + 3) * (tArgs + costb) := Nat.le_mul_of_pos_left _ (by omega)
            omega
          refine ⟨k9,
            S1 + S2 + S3 + 1 + S5 + S6 + S7 + (1 + len ob.retVal) + (1 + len r),
            (((((((hs1.trans hs2).trans hs3).trans hs4).trans hs5).trans hs6).trans hs7).trans
              hs8).trans hs9,
            ?_, hE9, ?_, ?_, hKeeps9, ?_, ?_, ?_⟩
          · simp only [compileStmt, List.length_append, List.length_cons,
              List.length_nil]
            change k9.pc = a + (cArgs.length + cSave.length + cBuild.length + 1 + cRest.length + 2)
            omega
          · rw [hMem9, hMem5]
          · rw [hR9', memOf_cons_cons, hR]
            cases ob <;> rfl
          · rw [hMem9]; rw [hstk4, hMem3] at hszM5; omega
          · rw [hR9']; simp only [listSize_cons]
            have h1 : (len M + 2) * cTot = (len M + 2) * (tArgs + costb) + (len M + 2) :=
              Nat.mul_succ _ _
            have h2 : costb ≤ (len M + 2) * (tArgs + costb) := by
              calc costb ≤ tArgs + costb := Nat.le_add_left _ _
                _ ≤ (len M + 2) * (tArgs + costb) := Nat.le_mul_of_pos_left _ (by omega)
            omega
          · set d := S2 + S3 + 1 + S6 + S7 + (1 + len ob.retVal) + (1 + len r)
            have hd : d ≤ K * W := by
              have h18 : d ≤ 18 * W := by omega
              have h18K : 18 * W ≤ K * W := Nat.mul_le_mul_right W (by omega)
              exact le_trans h18 h18K
            have hsum := stmt_cost_two (K := K) (W := W) (c := cTot)
              (t₁ := tArgs) (t₂ := costb) (d := d) le_rfl hd
            exact le_trans (by omega) hsum
    | ret e =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl, rfl⟩ := hexec
      set ce := compileExpr ctx e a
      have hce : CodeAt P a ce := hc.append_left
      have hJmp : P[a + ce.length]? = some (.jmp ep) := hc.append_right.cons
      obtain ⟨k1, S1, hs1, hpc1, hE1, hk1, hcost1⟩ :=
        steps_compileExpr ctx hce hpc hMem hR hsM
      obtain ⟨k2, hs2, hpc2, hk2⟩ := steps_jmp hJmp hpc1
      have hMem2 : k2.stk Mem = cfg.stk Mem := by
        rw [keeps_stk_eq hk2 (by simp), keeps_stk_eq hk1 (by simp [E_ne_Mem.symm])]
      have hR2 : k2.stk R = cfg.stk R := by
        rw [keeps_stk_eq hk2 (by simp), keeps_stk_eq hk1 (by simp [E_ne_R.symm])]
      refine ⟨k2, S1 + 1, hs1.trans hs2, hpc2, by rw [keeps_stk_eq hk2 (by simp), hE1]; rfl,
        by rw [hMem2, hMem], by rw [hR2, hR],
        keeps_trans (keeps_mono (by simp) hk1) (keeps_mono (by simp) hk2),
        by rw [hMem2]; omega, by rw [hR2]; omega, ?_⟩
      set cTot := (evalExpr st e).2 + 1
      set W := listSize (cfg.stk Mem) + listSize (cfg.stk R) + (len M + 3) * cTot + 1
      set K := stmtConst ctx M
      have hK : 20 ≤ K := twenty_le_stmtConst ctx M
      have hS1' : S1 ≤ K * W * (evalExpr st e).2 ^ 2 := expr_to_stmt_cost hcost1
      have hd : 1 ≤ K * W := by
        have hW : 1 ≤ W := Nat.succ_pos _
        have : 1 * 1 ≤ K * W := Nat.mul_le_mul (by omega) hW
        simpa using this
      have hsum := stmt_cost_one (K := K) (W := W) (c := cTot)
        (t := (evalExpr st e).2) (d := 1) le_rfl hd
      exact le_trans (by omega) hsum

end GI.Turing.Core
