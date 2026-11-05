/-
The machine model behind the running-time claim. This file is part of the trusted statement:
a reader must check it to know what the main theorem says.

A program is a list of procedures, and procedure 0 is the entry point. The machine has one
global memory `ℕ → ℕ`, and each running procedure has its own registers `ℕ → ℕ`. This is the
standard log-cost RAM (Cook and Reckhow, 1973) with procedure calls added. Every operation
costs one plus the number of binary digits of each number it reads or writes, so large numbers
are not free. Log-cost RAMs and multitape Turing machines simulate each other with polynomial
overhead, so a bound of the form `exp (O ((log n) ^ 2))` means the same in both models.

Calls pass single numbers in and out. Memory is shared and never copied, so a call does no
hidden work, and every call costs at least one.
-/
module

public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.List.GetD

@[expose] public section

namespace GI.Machine

/-- Binary operations on natural numbers. Comparisons give 1 for true and 0 for false.
Subtraction stops at 0, and division or remainder by 0 gives 0, as for `ℕ` in Lean. -/
inductive BinOp
  | add | sub | mul | div | mod | lt | eq
  deriving DecidableEq, Repr

/-- The value of a binary operation. -/
def BinOp.eval : BinOp → ℕ → ℕ → ℕ
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a / b
  | .mod, a, b => a % b
  | .lt, a, b => if a < b then 1 else 0
  | .eq, a, b => if a = b then 1 else 0

/-- Expressions. `reg r` reads register `r` of the running procedure, and `load a` reads the
memory cell whose address is the value of `a`. -/
inductive Expr
  | const (k : ℕ)
  | reg (r : ℕ)
  | load (addr : Expr)
  | bin (op : BinOp) (a b : Expr)
  deriving Repr

/-- Statements.
* `assign r e` puts the value of `e` in register `r`.
* `store a e` puts the value of `e` in the memory cell at the value of `a`.
* `cond e s t` runs `s` if `e` is nonzero and `t` otherwise.
* `loop e s` runs `s` while `e` is nonzero.
* `call r f args` runs procedure `f`. Its registers start with the values of `args` in
  registers `0, 1, …` and 0 everywhere else. Its return value goes to register `r`.
* `ret e` ends the running procedure with the value of `e`. A procedure that ends without
  `ret` returns 0. -/
inductive Stmt
  | nop
  | assign (r : ℕ) (e : Expr)
  | store (addr val : Expr)
  | seq (s t : Stmt)
  | cond (e : Expr) (s t : Stmt)
  | loop (e : Expr) (body : Stmt)
  | call (r : ℕ) (f : ℕ) (args : List Expr)
  | ret (e : Expr)
  deriving Repr

/-- A program: the bodies of its procedures. Procedure 0 is the entry point. -/
structure Program where
  procs : List Stmt
  deriving Repr

/-- The memory and the registers of the running procedure. -/
structure State where
  mem : ℕ → ℕ
  regs : ℕ → ℕ

/-- The number of binary digits of `v`, with `len 0 = 0`. Reading or writing `v` costs this
much on top of the unit cost of the operation. -/
def len (v : ℕ) : ℕ :=
  if v = 0 then 0 else Nat.log2 v + 1

/-- The value of an expression and the cost of computing it. A constant, a register read, a
memory read and an operation each cost one plus the lengths of the numbers they handle: the
constant, the register value, the address and the value read, or the two operands. -/
def evalExpr (st : State) : Expr → ℕ × ℕ
  | .const k => (k, 1 + len k)
  | .reg r => (st.regs r, 1 + len (st.regs r))
  | .load a =>
    let va := evalExpr st a
    (st.mem va.1, va.2 + 1 + len va.1 + len (st.mem va.1))
  | .bin op a b =>
    let va := evalExpr st a
    let vb := evalExpr st b
    (op.eval va.1 vb.1, va.2 + vb.2 + 1 + len va.1 + len vb.1)

/-- The values of a list of expressions and the total cost of computing them. -/
def evalArgs (st : State) : List Expr → List ℕ × ℕ
  | [] => ([], 0)
  | e :: es =>
    let v := evalExpr st e
    let vs := evalArgs st es
    (v.1 :: vs.1, v.2 + vs.2)

/-- How a statement ended: normally, or by `ret` with a value. -/
inductive Outcome
  | normal
  | returned (v : ℕ)
  deriving DecidableEq, Repr

/-- Run statement `s` of program `p` from state `st`. The result is how the statement ended,
the new state, and the cost. Every statement costs one plus the cost of the expressions it
evaluates and of the statements it runs; a `store` also pays for the lengths of the address
and the value.

`fuel` only bounds the depth of the run, so that this function terminates. A run that needs
more fuel gives `none`, and so does a call to a procedure that does not exist. Extra fuel never
changes a result (`GI.Machine.exec_fuel_mono`), so the cost does not depend on the fuel. -/
def exec (p : Program) : ℕ → Stmt → State → Option (Outcome × State × ℕ)
  | 0, _, _ => none
  | fuel + 1, s, st =>
    match s with
    | .nop => some (.normal, st, 1)
    | .assign r e =>
      let v := evalExpr st e
      some (.normal, { st with regs := Function.update st.regs r v.1 }, v.2 + 1)
    | .store a e =>
      let va := evalExpr st a
      let ve := evalExpr st e
      some (.normal, { st with mem := Function.update st.mem va.1 ve.1 },
        va.2 + ve.2 + 1 + len va.1 + len ve.1)
    | .seq s t =>
      match exec p fuel s st with
      | none => none
      | some (.returned v, st', c) => some (.returned v, st', c + 1)
      | some (.normal, st', c) =>
        match exec p fuel t st' with
        | none => none
        | some (o, st'', c') => some (o, st'', c + c' + 1)
    | .cond e s t =>
      let v := evalExpr st e
      match exec p fuel (if v.1 = 0 then t else s) st with
      | none => none
      | some (o, st', c) => some (o, st', v.2 + c + 1)
    | .loop e body =>
      let v := evalExpr st e
      if v.1 = 0 then some (.normal, st, v.2 + 1) else
      match exec p fuel body st with
      | none => none
      | some (.returned w, st', c) => some (.returned w, st', v.2 + c + 1)
      | some (.normal, st', c) =>
        match exec p fuel (.loop e body) st' with
        | none => none
        | some (o, st'', c') => some (o, st'', v.2 + c + c' + 1)
    | .call r f args =>
      let vs := evalArgs st args
      match p.procs[f]? with
      | none => none
      | some body =>
        match exec p fuel body { mem := st.mem, regs := fun i => vs.1.getD i 0 } with
        | none => none
        | some (o, st', c) =>
          let w := match o with
            | .returned w => w
            | .normal => 0
          some (.normal, { mem := st'.mem, regs := Function.update st.regs r w }, vs.2 + c + 1)
    | .ret e =>
      let v := evalExpr st e
      some (.returned v.1, st, v.2 + 1)

/-- Run program `p` on memory `mem` by calling procedure 0 with no arguments. The result is the
final memory, the value that procedure 0 returned, and the total cost. -/
def run (p : Program) (mem : ℕ → ℕ) (fuel : ℕ) : Option ((ℕ → ℕ) × ℕ × ℕ) :=
  match exec p fuel (.call 0 0 []) { mem := mem, regs := fun _ => 0 } with
  | none => none
  | some (_, st, c) => some (st.mem, st.regs 0, c)

end GI.Machine
