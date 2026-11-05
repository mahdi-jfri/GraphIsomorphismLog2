/-
The compiler from `GI.Lang` to the machine of `Workspace.Statement.Machine`.

**Memory.** Values live in a heap, in the cell format of `GI.Cited.Val`. Register 0 holds the
heap pointer `hp`, the first free cell. Every cell below `hp` that belongs to a live value stays
fixed; nothing is assumed about the cells at and above `hp`.

**Registers.** Register 1 is scratch. The compiled code of an expression gets a context `ctx`,
the list of registers that hold the addresses of the environment values, and a first free
register `t`. It may write registers 0, 1 and `t, t + 1, …`, and keeps registers `2, …, t - 1`.

**Contract.** The code of `e`, started with `hp` in register 0, writes the value of `e` at `hp`
and moves `hp` just past it. It writes only at or above the old `hp`. Each construct computes its
subexpressions one after another on top of the heap and then moves its result down to the old
`hp`; moves always go downward, so a forward copy is correct.

**Program.** Procedure 0 is the copy procedure `GI.Machine.copyBody`, procedure `1 + f` is user
function `f`, and the primitives' programs follow, each shifted to its offset (`primOff`). A user
function is called with registers 0 and 2 holding the heap pointer and the address of its
argument, and returns its final heap pointer; its result lies at the heap pointer it started
with.
-/
module

public import Workspace.Lang.Syntax
public import Workspace.Machine.Procs.Copy

@[expose] public section

namespace GI.Lang

open GI.Machine (Stmt Outcome State WP Runs len copyBody)

/-- Machine expressions. -/
abbrev MExpr := GI.Machine.Expr

/-- Register `r` gets the number of cells of the value at the address in register `a`: 2 for a
number, and three plus the count in the third cell for a list. -/
def sizeInto (r a : ℕ) : Stmt :=
  .cond (.load (.reg a)) (.assign r (.load (.reg a + 2) + 3)) (.assign r 2)

/-- Copy `len` cells from `src` to `dst` with procedure 0. -/
def copyCall (src dst n : MExpr) : Stmt := .call 1 0 [src, dst, n]

/-- Move the address in register `a` past the value stored there, using register `s`. -/
def skipStep (a s : ℕ) : Stmt := sizeInto s a ;; .assign a (.reg a + .reg s)

/-- The code of an expression, for context `ctx` and first free register `t`. `po j` is the
procedure index of primitive `j`. -/
def compE (po : ℕ → ℕ) : List ℕ → ℕ → Expr → Stmt
  | ctx, t, .var i =>
    sizeInto t (ctx.getD i 0) ;; copyCall (.reg (ctx.getD i 0)) (.reg 0) (.reg t) ;;
    .assign 0 (.reg 0 + .reg t)
  | _, _, .nat k =>
    .store (.reg 0) 0 ;; .store (.reg 0 + 1) (.const k) ;; .assign 0 (.reg 0 + 2)
  | ctx, t, .arith op a b =>
    .assign t (.reg 0) ;; compE po ctx (t + 1) a ;; compE po ctx (t + 1) b ;;
    .store (.reg t + 1) (.bin op (.load (.reg t + 1)) (.load (.reg t + 3))) ;;
    .assign 0 (.reg t + 2)
  | _, _, .nil =>
    .store (.reg 0) 1 ;; .store (.reg 0 + 1) 0 ;; .store (.reg 0 + 2) 0 ;; .assign 0 (.reg 0 + 3)
  | ctx, t, .snoc l e =>
    .assign t (.reg 0) ;; compE po ctx (t + 1) l ;; .assign (t + 1) (.reg 0) ;;
    compE po ctx (t + 2) e ;;
    .store (.reg t + 1) (.load (.reg t + 1) + 1) ;;
    .store (.reg t + 2) (.load (.reg t + 2) + (.reg 0 - .reg (t + 1)))
  | ctx, t, .length l =>
    .assign t (.reg 0) ;; compE po ctx (t + 1) l ;; .store (.reg t) 0 ;; .assign 0 (.reg t + 2)
  | ctx, t, .get l i =>
    .assign t (.reg 0) ;; compE po ctx (t + 1) l ;; compE po ctx (t + 1) i ;;
    .assign (t + 1) (.load (.reg 0 - 1)) ;; .assign (t + 2) (.reg t + 3) ;;
    Stmt.forUp (t + 3) (t + 1) (skipStep (t + 2) (t + 4)) ;;
    sizeInto (t + 4) (t + 2) ;; copyCall (.reg (t + 2)) (.reg t) (.reg (t + 4)) ;;
    .assign 0 (.reg t + .reg (t + 4))
  | ctx, t, .isNat e =>
    .assign t (.reg 0) ;; compE po ctx (t + 1) e ;;
    .store (.reg t + 1) (1 - .load (.reg t)) ;; .store (.reg t) 0 ;; .assign 0 (.reg t + 2)
  | ctx, t, .ite c th el =>
    .assign t (.reg 0) ;; compE po ctx (t + 1) c ;; .assign 0 (.reg t) ;;
    .cond (.load (.reg t + 1)) (compE po ctx (t + 1) th) (compE po ctx (t + 1) el)
  | ctx, t, .letE e body =>
    .assign t (.reg 0) ;; compE po ctx (t + 1) e ;; .assign (t + 1) (.reg 0) ;;
    compE po (ctx ++ [t]) (t + 2) body ;;
    copyCall (.reg (t + 1)) (.reg t) (.reg 0 - .reg (t + 1)) ;;
    .assign 0 (.reg t + (.reg 0 - .reg (t + 1)))
  | ctx, t, .call f a =>
    .assign t (.reg 0) ;; compE po ctx (t + 1) a ;;
    .call (t + 1) (1 + f) [.reg 0, 0, .reg t] ;;
    copyCall (.reg 0) (.reg t) (.reg (t + 1) - .reg 0) ;;
    .assign 0 (.reg t + (.reg (t + 1) - .reg 0))
  | ctx, t, .prim j a =>
    .assign t (.reg 0) ;; compE po ctx (t + 1) a ;;
    .call (t + 1) (po j) [.reg t] ;; sizeInto (t + 2) (t + 1) ;;
    copyCall (.reg (t + 1)) (.reg t) (.reg (t + 2)) ;; .assign 0 (.reg t + .reg (t + 2))

/-- The procedure of a user function: its argument's address is in register 2. It returns the
final heap pointer. -/
def funBody (po : ℕ → ℕ) (body : Expr) : Stmt := compE po [2] 3 body ;; .ret (.reg 0)

/-- The programs of the primitives, one after another, the first at offset `off`. -/
def primsCode : ℕ → List Prim → List Stmt
  | _, [] => []
  | off, p :: ps => p.prog.shifted off ++ primsCode (off + p.prog.procs.length) ps

/-- The procedure index of primitive `j`. -/
def primOff (P : Program) (j : ℕ) : ℕ :=
  1 + P.funs.length + ((P.prims.take j).map fun p => p.prog.procs.length).sum

/-- The compiled program. -/
def compile (P : Program) : GI.Machine.Program :=
  ⟨copyBody :: P.funs.map (funBody (primOff P)) ++ primsCode (1 + P.funs.length) P.prims⟩

end GI.Lang
