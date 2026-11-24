/-
Compiler from programs of `Workspace.Statement.Machine` to stack machine code
(`Workspace.Turing.SM`).

Given arithmetic blocks (`ArithBlocks`) and a memory lookup block (`LookupBlock`) packaged in
`CompilerCtx`, we compile expressions (`compileExpr`), argument lists (`compileArgs`), statements
(`compileStmt`), procedures (`compileProc`), and whole programs (`compileProgram`).

The code length of a compiled statement depends only on its starting address, not on jump targets
such as procedure addresses or the procedure epilogue (`compileStmt_length_eq`). This lets
`procLayout` compute every procedure's exact starting address in a first pass before emitting
calls in the second pass (`codeAt_compileProcs`).
-/
module

public import Workspace.Turing.Core.SMHelpers

@[expose] public section

namespace GI.Turing.Core

open GI.Machine (len BinOp Expr Stmt)
open GI.Turing (E Mem memOf listSize Keeps BinBlock)
open GI.Turing.SM

/-- Arithmetic and lookup building blocks supplied to the compiler. -/
structure CompilerCtx where
  arithCode : BinOp → Stk → ℕ → List Instr
  cA : ℕ
  hArith : ∀ op, BinBlock op.eval (arithCode op) cA
  lookupCode : Stk → Stk → ℕ → List Instr
  cL : ℕ
  hLookup : ∀ (s m : Stk), s ≠ m →
    ∀ (P : Program) (a : ℕ) (cfg : Config) (x : ℕ) (rest : List ℕ),
      CodeAt P a (lookupCode s m a) → cfg.pc = a → cfg.stk s = x :: rest →
        ∃ cfg' S, Steps P cfg cfg' S ∧ cfg'.pc = a + (lookupCode s m a).length ∧
          cfg'.stk s = memOf (cfg.stk m) x :: rest ∧ Keeps [s] cfg cfg' ∧
          S ≤ cL * (listSize (cfg.stk m) + 1) * (len x + 1)

/-! ### Static bound on register indices and argument counts -/

/-- Largest register index appearing in an expression. -/
def maxRegExpr : Expr → ℕ
  | .const _ => 0
  | .reg r => r
  | .load a => maxRegExpr a
  | .bin _ a b => max (maxRegExpr a) (maxRegExpr b)

/-- Largest register index appearing in a list of expressions. -/
def maxRegArgs : List Expr → ℕ
  | [] => 0
  | e :: es => max (maxRegExpr e) (maxRegArgs es)

/-- Largest register index or argument count appearing in a statement. -/
def maxRegStmt : Stmt → ℕ
  | .nop => 0
  | .assign r e => max r (maxRegExpr e)
  | .store a e => max (maxRegExpr a) (maxRegExpr e)
  | .seq s t => max (maxRegStmt s) (maxRegStmt t)
  | .cond e s t => max (maxRegExpr e) (max (maxRegStmt s) (maxRegStmt t))
  | .loop e b => max (maxRegExpr e) (maxRegStmt b)
  | .call r _ args => max r (max args.length (maxRegArgs args))
  | .ret e => maxRegExpr e

/-- Largest register index or argument count appearing in a list of procedures. -/
def maxRegProcs : List Stmt → ℕ
  | [] => 0
  | s :: rest => max (maxRegStmt s) (maxRegProcs rest)

/-- Largest register index or argument count appearing in a program. -/
def maxRegProg (p : GI.Machine.Program) : ℕ :=
  maxRegProcs p.procs

theorem maxRegProcs_getElem? {procs : List Stmt} {f : ℕ} {body : Stmt}
    (h : procs[f]? = some body) : maxRegStmt body ≤ maxRegProcs procs := by
  induction procs generalizing f with
  | nil => simp at h
  | cons s rest ih =>
    cases f with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact le_max_left _ _
    | succ f' =>
      simp only [List.getElem?_cons_succ] at h
      exact le_trans (ih h) (le_max_right _ _)

/-! ### Compilation of expressions, statements, and programs -/

/-- Compile an expression placed at address `a`: pushes its value onto `E`. -/
def compileExpr (ctx : CompilerCtx) : Expr → ℕ → List Instr
  | .const k, _ => [.push E k]
  | .reg r, a => [.push E r] ++ ctx.lookupCode E R (a + 1)
  | .load addr, a =>
    let c1 := compileExpr ctx addr a
    c1 ++ ctx.lookupCode E Mem (a + c1.length)
  | .bin op e1 e2, a =>
    let c1 := compileExpr ctx e1 a
    let c2 := compileExpr ctx e2 (a + c1.length)
    c1 ++ c2 ++ ctx.arithCode op E (a + c1.length + c2.length)

/-- Compile an argument list placed at address `a`: evaluates in reverse so that the first
argument ends up on top of `E`. -/
def compileArgs (ctx : CompilerCtx) : List Expr → ℕ → List Instr
  | [], _ => []
  | e :: es, a =>
    let c1 := compileArgs ctx es a
    c1 ++ compileExpr ctx e (a + c1.length)

/-- Compile a statement placed at address `a`, using `procAddr` for procedure calls and `ep` as
the epilogue target for `ret`. -/
def compileStmt (ctx : CompilerCtx) (procAddr : ℕ → ℕ) (ep : ℕ) : Stmt → ℕ → List Instr
  | .nop, _ => []
  | .assign r e, a =>
    compileExpr ctx e a ++ [.move E R, .push R r]
  | .store addr val, a =>
    let c1 := compileExpr ctx addr a
    let c2 := compileExpr ctx val (a + c1.length)
    c1 ++ c2 ++ [.move E Mem, .move E Mem]
  | .seq s t, a =>
    let c1 := compileStmt ctx procAddr ep s a
    c1 ++ compileStmt ctx procAddr ep t (a + c1.length)
  | .cond e s t, a =>
    let ce := compileExpr ctx e a
    let cs := compileStmt ctx procAddr ep s (a + ce.length + 1)
    let ct := compileStmt ctx procAddr ep t (a + ce.length + 1 + cs.length + 1)
    ce ++ [.jz E (a + ce.length + 1 + cs.length + 1)] ++ cs ++
      [.jmp (a + ce.length + 1 + cs.length + 1 + ct.length)] ++ ct
  | .loop e body, a =>
    let ce := compileExpr ctx e a
    let cb := compileStmt ctx procAddr ep body (a + ce.length + 1)
    ce ++ [.jz E (a + ce.length + 1 + cb.length + 1)] ++ cb ++ [.jmp a]
  | .call r f args, a =>
    let cArgs := compileArgs ctx args a
    let cSave := saveR (a + cArgs.length)
    let cBuild := buildRFrom 0 args.length
    let cCall := [.call (procAddr f)]
    let cRest := restoreR (a + cArgs.length + cSave.length + cBuild.length + 1)
    cArgs ++ cSave ++ cBuild ++ cCall ++ cRest ++ [.move E R, .push R r]
  | .ret e, a =>
    compileExpr ctx e a ++ [.jmp ep]

/-- The compiled length of a statement depends only on its placement address `a`, not on
`procAddr` or `ep`. -/
theorem compileStmt_length_eq (ctx : CompilerCtx) (pa₁ pa₂ : ℕ → ℕ) (ep₁ ep₂ : ℕ)
    (s : Stmt) (a : ℕ) :
    (compileStmt ctx pa₁ ep₁ s a).length = (compileStmt ctx pa₂ ep₂ s a).length := by
  induction s generalizing a with
  | nop => rfl
  | assign r e => rfl
  | store addr val => rfl
  | seq s t ihs iht =>
    simp only [compileStmt, List.length_append]
    rw [ihs a, iht (a + (compileStmt ctx pa₂ ep₂ s a).length)]
  | cond e s t ihs iht =>
    simp only [compileStmt, List.length_append, List.length_singleton]
    have hs := ihs (a + (compileExpr ctx e a).length + 1)
    rw [hs, iht (a + (compileExpr ctx e a).length + 1 +
      (compileStmt ctx pa₂ ep₂ s (a + (compileExpr ctx e a).length + 1)).length + 1)]
  | loop e body ihb =>
    simp only [compileStmt, List.length_append, List.length_singleton]
    rw [ihb (a + (compileExpr ctx e a).length + 1)]
  | call r f args =>
    simp only [compileStmt, List.length_append, saveR_length,
      buildRFrom_length, restoreR_length, List.length_cons, List.length_nil]
  | ret e =>
    simp only [compileStmt, List.length_append, List.length_singleton]

/-- Epilogue address for a procedure `body` placed at `pos`. -/
def procEpilogue (ctx : CompilerCtx) (body : Stmt) (pos : ℕ) : ℕ :=
  pos + (compileStmt ctx (fun _ => 0) 0 body pos).length + 1

/-- Code length of a procedure `body` placed at `pos`. -/
def procLen (ctx : CompilerCtx) (body : Stmt) (pos : ℕ) : ℕ :=
  (compileStmt ctx (fun _ => 0) 0 body pos).length + 5

/-- Compile a procedure `body` placed at `pos`: run `body`, push default return value `0`,
empty `R`, and return. -/
def compileProc (ctx : CompilerCtx) (procAddr : ℕ → ℕ) (body : Stmt) (pos : ℕ) : List Instr :=
  let ep := procEpilogue ctx body pos
  compileStmt ctx procAddr ep body pos ++ [.push E 0] ++ emptyR ep ++ [.ret]

theorem compileProc_length (ctx : CompilerCtx) (procAddr : ℕ → ℕ) (body : Stmt) (pos : ℕ) :
    (compileProc ctx procAddr body pos).length = procLen ctx body pos := by
  simp only [compileProc, procLen, List.length_append, List.length_singleton, emptyR_length]
  rw [compileStmt_length_eq ctx procAddr (fun _ => 0) (procEpilogue ctx body pos) 0 body pos]

/-- First pass: compute the starting address of each procedure in `procs` starting from `pos`,
together with the end address after the last procedure. -/
def procLayout (ctx : CompilerCtx) : List Stmt → ℕ → List ℕ × ℕ
  | [], pos => ([], pos)
  | body :: rest, pos =>
    let next := pos + procLen ctx body pos
    let res := procLayout ctx rest next
    (pos :: res.1, res.2)

/-- Lookup the starting address of procedure `f` in `p` when procedures start at `base`. -/
def procAddrOf (ctx : CompilerCtx) (p : GI.Machine.Program) (base : ℕ) (f : ℕ) : ℕ :=
  (procLayout ctx p.procs base).1.getD f 0

/-- Compile a list of procedures consecutively starting from `pos`. -/
def compileProcs (ctx : CompilerCtx) (procAddr : ℕ → ℕ) : List Stmt → ℕ → List Instr
  | [], _ => []
  | body :: rest, pos =>
    let c := compileProc ctx procAddr body pos
    c ++ compileProcs ctx procAddr rest (pos + c.length)

theorem compileProcs_length (ctx : CompilerCtx) (procAddr : ℕ → ℕ) (procs : List Stmt) (pos : ℕ) :
    pos + (compileProcs ctx procAddr procs pos).length = (procLayout ctx procs pos).2 := by
  induction procs generalizing pos with
  | nil => simp [compileProcs, procLayout]
  | cons body rest ih =>
    simp only [compileProcs, procLayout, List.length_append]
    rw [compileProc_length ctx procAddr body pos]
    rw [← Nat.add_assoc]
    exact ih (pos + procLen ctx body pos)

/-- Every procedure `procs[f]? = some body` sits at its layout address in `compileProcs`. -/
theorem codeAt_compileProcs (ctx : CompilerCtx) (procAddr : ℕ → ℕ) {P : Program}
    {procs : List Stmt} {pos f : ℕ} {body : Stmt}
    (hc : CodeAt P pos (compileProcs ctx procAddr procs pos))
    (hf : procs[f]? = some body) :
    ∃ addr, (procLayout ctx procs pos).1[f]? = some addr ∧
      CodeAt P addr (compileProc ctx procAddr body addr) := by
  induction procs generalizing pos f with
  | nil => simp at hf
  | cons b rest ih =>
    cases f with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
      subst hf
      refine ⟨pos, by simp [procLayout], ?_⟩
      exact hc.append_left
    | succ f' =>
      simp only [List.getElem?_cons_succ] at hf
      have hc' : CodeAt P (pos + procLen ctx b pos)
          (compileProcs ctx procAddr rest (pos + procLen ctx b pos)) := by
        have h := hc.append_right
        rwa [compileProc_length ctx procAddr b pos] at h
      obtain ⟨addr, haddr, hcode⟩ := ih hc' hf
      exact ⟨addr, by simpa [procLayout] using haddr, hcode⟩

/-- Compile a full program `p` placed at address `a`: call procedure 0, jump past all
procedures, followed by all compiled procedures. -/
def compileProgram (ctx : CompilerCtx) (p : GI.Machine.Program) (a : ℕ) : List Instr :=
  let pa := procAddrOf ctx p (a + 2)
  let endAddr := (procLayout ctx p.procs (a + 2)).2
  [.call (pa 0), .jmp endAddr] ++ compileProcs ctx pa p.procs (a + 2)

theorem compileProgram_end (ctx : CompilerCtx) (p : GI.Machine.Program) (a : ℕ) :
    a + (compileProgram ctx p a).length = (procLayout ctx p.procs (a + 2)).2 := by
  simp only [compileProgram, List.length_append, List.length_cons, List.length_nil]
  rw [show a + (2 + (compileProcs ctx (procAddrOf ctx p (a + 2)) p.procs (a + 2)).length) =
    (a + 2) + (compileProcs ctx (procAddrOf ctx p (a + 2)) p.procs (a + 2)).length by omega]
  exact compileProcs_length ctx _ p.procs (a + 2)

/-- Every procedure of `p` sits at `procAddrOf ctx p (a + 2)` inside `compileProgram ctx p a`. -/
theorem codeAt_compileProgram_proc (ctx : CompilerCtx) (p : GI.Machine.Program) {P : Program}
    {a f : ℕ} {body : Stmt}
    (hc : CodeAt P a (compileProgram ctx p a)) (hf : p.procs[f]? = some body) :
    let pa := procAddrOf ctx p (a + 2)
    CodeAt P (pa f) (compileProc ctx pa body (pa f)) := by
  intro pa
  have hprocs : CodeAt P (a + 2) (compileProcs ctx pa p.procs (a + 2)) :=
    hc.append_right
  obtain ⟨addr, haddr, hcode⟩ := codeAt_compileProcs ctx pa hprocs hf
  have hpa : pa f = addr := by
    simp only [pa, procAddrOf]
    rw [List.getD_eq_getElem?_getD, haddr]
    rfl
  rwa [hpa]

end GI.Turing.Core
