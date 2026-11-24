/-
Main theorem of the core RAM-to-stack-machine simulation:

`GI.Turing.coreSim_of : GI.Turing.ArithBlocks → GI.Turing.LookupBlock → GI.Turing.CoreSim`.

Given arithmetic and lookup code blocks, we assemble a `CompilerCtx`, compile any program `p` of
`Workspace.Statement.Machine` with `compileProgram`, and lift `steps_compileStmt` and
`steps_procEpilogue` to top-level runs `GI.Machine.run`.
-/
module

public import Workspace.Turing.Core.StmtSim

@[expose] public section

namespace GI.Turing

open GI.Machine (len BinOp run exec)
open GI.Turing.SM
open GI.Turing.Core

private theorem binBlock_mono {f : ℕ → ℕ → ℕ} {code : Stk → ℕ → List Instr} {c₁ c₂ : ℕ}
    (h : BinBlock f code c₁) (hle : c₁ ≤ c₂) : BinBlock f code c₂ := by
  intro s P a cfg x y rest hc hpc hs
  obtain ⟨cfg', S, hsteps, hpc', hs', hk, hcost⟩ := h s P a cfg x y rest hc hpc hs
  exact ⟨cfg', S, hsteps, hpc', hs', hk, le_trans hcost (Nat.mul_le_mul_right _ hle)⟩

/-- Every program of `Workspace.Statement.Machine` runs on the stack machine of
`Workspace.Turing.SM` with polynomial cost and memory-stack growth, given arithmetic and lookup
blocks. -/
theorem coreSim_of : ArithBlocks → LookupBlock → CoreSim := by
  intro hArith hLookup p
  obtain ⟨codeAdd, cAdd, hAdd⟩ := hArith .add
  obtain ⟨codeSub, cSub, hSub⟩ := hArith .sub
  obtain ⟨codeMul, cMul, hMul⟩ := hArith .mul
  obtain ⟨codeDiv, cDiv, hDiv⟩ := hArith .div
  obtain ⟨codeMod, cMod, hMod⟩ := hArith .mod
  obtain ⟨codeLt, cLt, hLt⟩ := hArith .lt
  obtain ⟨codeEq, cEq, hEq⟩ := hArith .eq
  obtain ⟨lookupCode, cL, hL⟩ := hLookup
  let cA := max cAdd (max cSub (max cMul (max cDiv (max cMod (max cLt cEq)))))
  let arithCode : BinOp → Stk → ℕ → List Instr
    | .add => codeAdd
    | .sub => codeSub
    | .mul => codeMul
    | .div => codeDiv
    | .mod => codeMod
    | .lt => codeLt
    | .eq => codeEq
  let ctx : CompilerCtx := {
    arithCode := arithCode
    cA := cA
    hArith := fun op => by
      cases op with
      | add => exact binBlock_mono hAdd (le_max_left _ _)
      | sub => exact binBlock_mono hSub (le_trans (le_max_left _ _) (le_max_right _ _))
      | mul =>
        exact binBlock_mono hMul
          (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
      | div =>
        exact binBlock_mono hDiv
          (le_trans (le_max_left _ _)
            (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
      | mod =>
        exact binBlock_mono hMod
          (le_trans (le_max_left _ _)
            (le_trans (le_max_right _ _)
              (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))))
      | lt =>
        exact binBlock_mono hLt
          (le_trans (le_max_left _ _)
            (le_trans (le_max_right _ _)
              (le_trans (le_max_right _ _)
                (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))))
      | eq =>
        exact binBlock_mono hEq
          (le_trans (le_max_right _ _)
            (le_trans (le_max_right _ _)
              (le_trans (le_max_right _ _)
                (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))))
    lookupCode := lookupCode
    cL := cL
    hLookup := hL
  }
  let M := maxRegProg p
  let K := stmtConst ctx M
  refine ⟨compileProgram ctx p, (K + 5) * (len M + 3), 3, ?_⟩
  intro P a cfg fuel mem' r T hc hpc hempty hrun
  -- Unpack `run p (memOf (cfg.stk Mem)) fuel = some (mem', r, T)`.
  unfold run at hrun
  cases fuel with
  | zero => simp [exec] at hrun
  | succ f =>
    simp only [exec, GI.Machine.evalArgs] at hrun
    cases h0 : p.procs[0]? with
    | none => simp [h0] at hrun
    | some body0 =>
      rw [h0] at hrun
      dsimp only at hrun
      cases hb : exec p f body0
          { mem := memOf (cfg.stk Mem), regs := fun i => [].getD i 0 } with
      | none => rw [hb] at hrun; simp at hrun
      | some res0 =>
        rw [hb] at hrun
        obtain ⟨o0, st0, c0⟩ := res0
        simp only [Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, hr_eq, hT_eq⟩ := hrun
        have hr : r = o0.retVal := by
          rw [← hr_eq]
          cases o0 <;> simp [GI.Machine.Outcome.retVal]
        have hT : T = c0 + 1 := by
          have : 0 + c0 + 1 = T := hT_eq
          omega
        -- Locate entry instructions and procedure table in `compileProgram ctx p a`.
        set pa := procAddrOf ctx p (a + 2)
        set endAddr := (procLayout ctx p.procs (a + 2)).2
        have hcEntry : CodeAt P a [.call (pa 0), .jmp endAddr] := hc.append_left
        have hCall0 : P[a]? = some (.call (pa 0)) := hcEntry.cons
        have hJmpEnd : P[a + 1]? = some (.jmp endAddr) := hcEntry.tail.cons
        have hprocs : ProcsAt ctx P pa p := fun g body hg =>
          codeAt_compileProgram_proc ctx p hc hg
        have hcProc0 : CodeAt P (pa 0) (compileProc ctx pa body0 (pa 0)) := hprocs 0 body0 h0
        have hcBody0 : CodeAt P (pa 0)
            (compileStmt ctx pa (procEpilogue ctx body0 (pa 0)) body0 (pa 0)) :=
          hcProc0.append_left.append_left.append_left
        -- Step 1: call procedure 0.
        obtain ⟨k1, hs1, hpc1, hrs1, hstk1, hinp1, hout1⟩ := steps_call hCall0 hpc
        have hR0 : cfg.stk R = [] := hempty R E_ne_R.symm Mem_ne_R.symm
        have hR1 : k1.stk R = [] := by rw [hstk1, hR0]
        have hmemR1 : memOf (k1.stk R) = fun i => [].getD i 0 := by
          rw [hR1]; funext i; simp [memOf_nil]
        -- Step 2: run procedure 0's body.
        obtain ⟨k2, S2, hs2, hpc2, hE2, hMem2, _, hk2, hszM2, hszR2, hcost2⟩ :=
          steps_compileStmt ctx hprocs le_rfl (maxRegProcs_getElem? h0) hcBody0 hpc1
            (by rw [hstk1]) hmemR1 hb
        -- Step 3: run procedure 0's epilogue (`push E 0` if normal, `emptyR`, `ret`).
        have hrs2 : k2.rs = (a + 1) :: cfg.rs := by rw [hk2.2.1, hrs1]
        have hE1 : k1.stk E = cfg.stk E := hstk1 E
        rw [hE1] at hE2
        obtain ⟨k3, S3, hs3, hpc3, hE3, hR3, hMem3, _, hoth3, hrs3, hinp3, hout3, hcost3⟩ :=
          steps_procEpilogue ctx hcProc0 hpc2 hE2 hrs2
        -- Step 4: jump past all compiled procedures to `endAddr`.
        obtain ⟨k4, hs4, hpc4, hk4⟩ := steps_jmp hJmpEnd hpc3
        refine ⟨k4, 1 + S2 + S3 + 1, ((hs1.trans hs2).trans hs3).trans hs4, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [compileProgram_end]; exact hpc4
        · rw [keeps_stk_eq hk4 (by simp), hMem3, hMem2]
        · rw [keeps_stk_eq hk4 (by simp), hE3, hr]
        · refine ⟨fun t ht => ?_, ?_, ?_, ?_⟩
          · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ht
            by_cases htR : t = R
            · rw [htR, keeps_stk_eq hk4 (by simp), hR3, hR0]
            · rw [keeps_stk_eq hk4 (by simp),
                hoth3 t (by simp [ht.1, ht.2, htR]),
                keeps_stk_eq hk2 (by simp [ht.1, ht.2, htR]),
                hstk1]
          · rw [hk4.2.1, hrs3]
          · rw [hk4.2.2.1, hinp3, hk2.2.2.1, hinp1]
          · rw [hk4.2.2.2, hout3, hk2.2.2.2, hout1]
        · rw [keeps_stk_eq hk4 (by simp), hMem3]
          rw [hstk1] at hszM2
          have h1 : 1 ≤ (K + 5) * (len M + 3) :=
            Nat.mul_pos (by omega) (by omega)
          have h2 : c0 ≤ (T + 1) ^ 3 := by
            have hcube : (T + 1) ^ 3 = (T + 1) * ((T + 1) * (T + 1)) := by ring
            have hle : T + 1 ≤ (T + 1) ^ 3 := by
              rw [hcube]
              exact Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) (by omega))
            omega
          have h3 : (T + 1) ^ 3 ≤ (K + 5) * (len M + 3) * (T + 1) ^ 3 :=
            Nat.le_mul_of_pos_left _ h1
          omega
        · rw [hstk1, hstk1, hR0, listSize_nil] at hcost2
          rw [hstk1, hR0, listSize_nil] at hszR2
          change S2 ≤ K * (listSize (cfg.stk Mem) + 0 + (len M + 3) * c0 + 1) * c0 ^ 2 at hcost2
          change listSize (k2.stk R) ≤ 0 + (len M + 2) * c0 at hszR2
          set N := T + listSize (cfg.stk Mem) + 1
          have hN : 1 ≤ N := by omega
          have hW : listSize (cfg.stk Mem) + 0 + (len M + 3) * c0 + 1 ≤ (len M + 3) * N := by
            have : listSize (cfg.stk Mem) + 1 ≤ (len M + 3) * (listSize (cfg.stk Mem) + 1) :=
              Nat.le_mul_of_pos_left _ (by omega)
            have : (len M + 3) * c0 + (len M + 3) * (listSize (cfg.stk Mem) + 1) =
                (len M + 3) * (c0 + (listSize (cfg.stk Mem) + 1)) := (Nat.mul_add _ _ _).symm
            have : (len M + 3) * (c0 + (listSize (cfg.stk Mem) + 1)) ≤ (len M + 3) * N :=
              Nat.mul_le_mul_left _ (by omega)
            omega
          have hc0sq : c0 ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left (by omega) 2
          have hS2 : S2 ≤ K * (len M + 3) * N ^ 3 := by
            have h1 : S2 ≤ K * ((len M + 3) * N) * N ^ 2 :=
              le_trans hcost2 (Nat.mul_le_mul (Nat.mul_le_mul_left K hW) hc0sq)
            have h2 : K * ((len M + 3) * N) * N ^ 2 = K * (len M + 3) * N ^ 3 := by ring
            omega
          have hS3 : 1 + S3 + 1 ≤ 5 * (len M + 3) * N ^ 3 := by
            have hR2 : listSize (k2.stk R) ≤ (len M + 3) * N := by
              have : (len M + 2) * c0 ≤ (len M + 3) * c0 := Nat.mul_le_mul_right _ (by omega)
              have : (len M + 3) * c0 ≤ (len M + 3) * N := Nat.mul_le_mul_left _ (by omega)
              omega
            have hlin : 1 + (3 * ((len M + 3) * N) + 3) + 1 ≤ 5 * (len M + 3) * N := by
              have h3le : 3 ≤ (len M + 3) * N := by
                calc 3 ≤ len M + 3 := by omega
                  _ ≤ (len M + 3) * N := Nat.le_mul_of_pos_right _ hN
              have h5 : 5 * (len M + 3) * N =
                  3 * ((len M + 3) * N) + 2 * ((len M + 3) * N) := by ring
              omega
            have hpow : N ≤ N ^ 3 := by
              have hcube : N ^ 3 = N * (N * N) := by ring
              rw [hcube]
              exact Nat.le_mul_of_pos_right _ (Nat.mul_pos hN hN)
            have hlin3 : 5 * (len M + 3) * N ≤ 5 * (len M + 3) * N ^ 3 :=
              Nat.mul_le_mul_left _ hpow
            omega
          have hcomb : K * (len M + 3) * N ^ 3 + 5 * (len M + 3) * N ^ 3 =
              (K + 5) * (len M + 3) * N ^ 3 := by ring
          omega

end GI.Turing
