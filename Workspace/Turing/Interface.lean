/-
The parts of the proof that the main theorem holds for Turing machines, as named statements.

The proof runs the program of `GI.Statement.GraphIsomorphismInDegreeTime` on a Turing machine in
three steps.

1. A program `wrap p` of the machine of `Workspace.Statement.Machine` reads the input bits from
   memory in the layout `GI.Turing.rawInput`, runs `p`, and writes the output bits in the layout
   `GI.Turing.rawOutput`.
2. Every such program runs on the stack machine of `Workspace.Turing.SM` with a polynomial
   slowdown (`GI.Turing.SimulatesRAM`).
3. Every stack machine program runs on a Turing machine with a polynomial slowdown
   (`GI.Turing.SimulatesSM`).

Step 2 is split further. The stack machine keeps the memory as a list of address-value pairs on
stack `GI.Turing.Mem` (`GI.Turing.memOf`). `GI.Turing.CoreSim` runs a program on that memory.
`GI.Turing.FrontEnd` and `GI.Turing.BackEnd` move the input and the output between the memory and
the input and output bits. `GI.Turing.ArithBlocks` and `GI.Turing.LookupBlock` are pieces of
stack machine code that the simulation uses: arithmetic, and reading a cell of the memory.

Each piece of code is a function of the index `a` where it is placed, since its jumps go to
indices inside it. A specification says what the code does when it is placed at `a` in any
program and run from index `a`: it reaches the index just after it, with the stated effect and
cost.
-/
module

public import Workspace.Turing.SM
public import Workspace.Statement.Degree
public import Workspace.Statement.Turing

@[expose] public section

namespace GI.Turing

open GI.Machine (len run BinOp)
open GI.Turing.SM

/-- The stack for evaluation. -/
abbrev E : Stk := 0

/-- The stack that holds the memory. -/
abbrev Mem : Stk := 1

/-- The input bits `x` in memory: cell 0 holds the number of bits, cell `i + 1` holds 1 or 0 for
bit `i`, and every other cell holds 0. -/
def rawInput (x : List Bool) (a : ℕ) : ℕ :=
  if a = 0 then x.length else if x.getD (a - 1) false then 1 else 0

/-- The output bits in memory at address `B`: cell `B` holds the number `L` of bits, and bit `i`
is `true` when cell `B + 1 + i` is not 0, for `i < L`. -/
def rawOutput (mem : ℕ → ℕ) (B : ℕ) : List Bool :=
  (List.range (mem B)).map fun i => decide (mem (B + 1 + i) ≠ 0)

/-- The memory that a list `[a₁, v₁, a₂, v₂, …]` of address-value pairs stands for: cell `x`
holds the value of the first pair with address `x`, and 0 if there is none. A new pair on top
overrides older pairs with the same address. -/
def memOf : List ℕ → ℕ → ℕ
  | a :: v :: rest, x => if a = x then v else memOf rest x
  | _, _ => 0

/-- The size of a stack of numbers on a Turing machine: each number takes its binary digits and
one separator. -/
def listSize (l : List ℕ) : ℕ :=
  (l.map fun v => len v + 1).sum

/-- `c'` agrees with `c` on every stack not in `ss`, on the return stack, on the input and on the
output. -/
def Keeps (ss : List Stk) (c c' : Config) : Prop :=
  (∀ t, t ∉ ss → c'.stk t = c.stk t) ∧ c'.rs = c.rs ∧ c'.inp = c.inp ∧ c'.out = c.out

/-- Code `code s a`, placed at `a`, replaces the top two numbers `y, x` of stack `s` (`y` on top)
by `f x y`, keeps everything else, and costs at most `c * (len x + len y + 1) ^ 2`. -/
def BinBlock (f : ℕ → ℕ → ℕ) (code : Stk → ℕ → List Instr) (c : ℕ) : Prop :=
  ∀ (s : Stk) (P : Program) (a : ℕ) (cfg : Config) (x y : ℕ) (rest : List ℕ),
    CodeAt P a (code s a) → cfg.pc = a → cfg.stk s = y :: x :: rest →
      ∃ cfg' S, Steps P cfg cfg' S ∧ cfg'.pc = a + (code s a).length ∧
        cfg'.stk s = f x y :: rest ∧ Keeps [s] cfg cfg' ∧ S ≤ c * (len x + len y + 1) ^ 2

/-- Code for each operation of the machine of `Workspace.Statement.Machine`. -/
def ArithBlocks : Prop :=
  ∀ op : BinOp, ∃ code : Stk → ℕ → List Instr, ∃ c : ℕ, BinBlock op.eval code c

/-- Code `code s m a`, placed at `a`, for stacks `s ≠ m`: it replaces the top `x` of stack `s` by
the value of cell `x` in the memory that stack `m` stands for, and keeps everything else. Its
cost is at most `c * (listSize (stack m) + 1) * (len x + 1)`. -/
def LookupBlock : Prop :=
  ∃ code : Stk → Stk → ℕ → List Instr, ∃ c : ℕ, ∀ (s m : Stk), s ≠ m →
    ∀ (P : Program) (a : ℕ) (cfg : Config) (x : ℕ) (rest : List ℕ),
      CodeAt P a (code s m a) → cfg.pc = a → cfg.stk s = x :: rest →
        ∃ cfg' S, Steps P cfg cfg' S ∧ cfg'.pc = a + (code s m a).length ∧
          cfg'.stk s = memOf (cfg.stk m) x :: rest ∧ Keeps [s] cfg cfg' ∧
          S ≤ c * (listSize (cfg.stk m) + 1) * (len x + 1)

/-- Code `code a`, placed at `a`, started with stack `Mem` empty: it reads the input `x` and
leaves on `Mem` a list that stands for `rawInput x`, of size at most `c * (x.length + 1) ^ 2`.
It keeps the other stacks, the return stack and the output, and its cost is at most
`c * (x.length + 1) ^ 2`. -/
def FrontEnd : Prop :=
  ∃ code : ℕ → List Instr, ∃ c : ℕ, ∀ (P : Program) (a : ℕ) (cfg : Config),
    CodeAt P a (code a) → cfg.pc = a → cfg.stk Mem = [] →
      ∃ cfg' S, Steps P cfg cfg' S ∧ cfg'.pc = a + (code a).length ∧
        memOf (cfg'.stk Mem) = rawInput cfg.inp ∧
        listSize (cfg'.stk Mem) ≤ c * (cfg.inp.length + 1) ^ 2 ∧
        (∀ t, t ≠ Mem → cfg'.stk t = cfg.stk t) ∧ cfg'.rs = cfg.rs ∧ cfg'.out = cfg.out ∧
        S ≤ c * (cfg.inp.length + 1) ^ 2

/-- Code `code a`, placed at `a`, started with `B` on top of stack `E`: it appends
`rawOutput mem B` to the output, where `mem` is the memory that stack `Mem` stands for. Its cost
is at most `c * (mem B + listSize (stack Mem) + len B + 1) ^ 3`. -/
def BackEnd : Prop :=
  ∃ code : ℕ → List Instr, ∃ c : ℕ,
    ∀ (P : Program) (a : ℕ) (cfg : Config) (B : ℕ) (rest : List ℕ),
      CodeAt P a (code a) → cfg.pc = a → cfg.stk E = B :: rest →
        ∃ cfg' S, Steps P cfg cfg' S ∧ cfg'.pc = a + (code a).length ∧
          cfg'.out = cfg.out ++ rawOutput (memOf (cfg.stk Mem)) B ∧
          S ≤ c * (memOf (cfg.stk Mem) B + listSize (cfg.stk Mem) + len B + 1) ^ 3

/-- The simulation of a program `p` of the machine of `Workspace.Statement.Machine`. Code
`code a`, placed at `a`, started with every stack other than `E` and `Mem` empty: if `p`, run on
the memory that stack `Mem` stands for, finishes with memory `mem'`, return value `r` and cost
`T`, then the code ends with `Mem` standing for `mem'` and with `r` pushed onto `E`. It keeps
the other stacks, the return stack, the input and the output. Its cost is polynomial in `T` and
in the size of `Mem`, and it adds at most a polynomial in `T` to the size of `Mem`. -/
def CoreSim : Prop :=
  ∀ p : GI.Machine.Program, ∃ code : ℕ → List Instr, ∃ c k : ℕ,
    ∀ (P : Program) (a : ℕ) (cfg : Config) (fuel : ℕ) (mem' : ℕ → ℕ) (r T : ℕ),
      CodeAt P a (code a) → cfg.pc = a → (∀ t, t ≠ E → t ≠ Mem → cfg.stk t = []) →
      run p (memOf (cfg.stk Mem)) fuel = some (mem', r, T) →
        ∃ cfg' S, Steps P cfg cfg' S ∧ cfg'.pc = a + (code a).length ∧
          memOf (cfg'.stk Mem) = mem' ∧ cfg'.stk E = r :: cfg.stk E ∧
          Keeps [E, Mem] cfg cfg' ∧
          listSize (cfg'.stk Mem) ≤ listSize (cfg.stk Mem) + c * (T + 1) ^ k ∧
          S ≤ c * (T + listSize (cfg.stk Mem) + 1) ^ k

/-- **Step 2.** Every program of the machine of `Workspace.Statement.Machine` runs on the stack
machine: if it finishes on the input `x` in the layout `rawInput x` with cost `T`, the stack
machine program halts on `x` with the output that the program left in memory, at a cost
polynomial in `T`, in the length of `x` and in the length of the output. -/
def SimulatesRAM : Prop :=
  ∀ p : GI.Machine.Program, ∃ P : Program, ∃ c k : ℕ,
    ∀ (x : List Bool) (fuel : ℕ) (mem' : ℕ → ℕ) (B T : ℕ),
      run p (rawInput x) fuel = some (mem', B, T) →
        ∃ S, Halts P x (rawOutput mem' B) S ∧ S ≤ c * (T + x.length + mem' B + 2) ^ k

/-- **Step 3.** Every stack machine program runs on a Turing machine of Mathlib with bits as
input and output alphabets, in time quadratic in the cost of the run and the length of the
input. -/
def SimulatesSM : Prop :=
  ∀ P : Program, ∃ M : Turing.TM2ComputableAux Bool Bool, ∃ c : ℕ,
    ∀ (x y : List Bool) (S : ℕ), Halts P x y S →
      Nonempty (Turing.TM2OutputsInTime M.tm (x.map M.inputAlphabet.symm)
        (some (y.map M.outputAlphabet.symm)) (c * (S + x.length + 1) ^ 2))

end GI.Turing
