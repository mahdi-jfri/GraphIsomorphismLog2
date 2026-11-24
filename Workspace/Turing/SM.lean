/-
A stack machine between the machine of `Workspace.Statement.Machine` and Mathlib's Turing
machines.

The machine has eight stacks of numbers, a stack of return addresses, the unread input bits and
the output bits written so far. A program is a list of instructions, and the program counter
says which one runs next. Each instruction touches only the tops of the stacks, and it costs one
plus the binary length of each number it reads or writes. These are the properties that make the
machine easy to run on a Turing machine (`GI.Turing.SimulatesSM`): there, a number is a block of
binary digits on a stack, and each instruction takes time linear in its cost.

The arithmetic is only `add`, `sub`, `double`, `half` and `parity`. Multiplication, division and
comparisons are programs of this machine (`GI.Turing.ArithBlocks`).
-/
module

public import Workspace.Statement.Machine

@[expose] public section

namespace GI.Turing.SM

open GI.Machine (len)

/-- The eight stacks of numbers. -/
abbrev Stk : Type := Fin 8

/-- The instructions. A jump target is the index of an instruction in the program.
* `push s k` pushes the constant `k` onto stack `s`.
* `pop s` removes the top of `s`.
* `copy s t` pushes a copy of the top of `s` onto `t`. With `s = t` it duplicates the top.
* `move s t` moves the top of `s` onto `t`.
* `add s t` and `sub s t` need `s ≠ t`. They pop `b` from `t` and replace the top `a` of `s` by
  `a + b` or `a - b` (which stops at 0).
* `double s`, `half s` and `parity s` replace the top `v` of `s` by `2 * v`, `v / 2` and `v % 2`.
* `jz s l` pops `v` from `s` and jumps to `l` if `v = 0`.
* `jmp l` jumps to `l`. `jnil s l` jumps to `l` if `s` is empty, and pops nothing.
* `call l` pushes the index of the next instruction onto the return stack and jumps to `l`.
  `ret` pops an index from the return stack and jumps to it.
* `read s` pushes the next input bit onto `s` (1 for `true`, 0 for `false`) and removes it from
  the input. At the end of the input it pushes 2.
* `write s` pops `v` from `s` and appends the bit `v ≠ 0` to the output.
* `halt` stops the machine. -/
inductive Instr
  | push (s : Stk) (k : ℕ)
  | pop (s : Stk)
  | copy (s t : Stk)
  | move (s t : Stk)
  | add (s t : Stk)
  | sub (s t : Stk)
  | double (s : Stk)
  | half (s : Stk)
  | parity (s : Stk)
  | jz (s : Stk) (l : ℕ)
  | jmp (l : ℕ)
  | jnil (s : Stk) (l : ℕ)
  | call (l : ℕ)
  | ret
  | read (s : Stk)
  | write (s : Stk)
  | halt
  deriving DecidableEq, Repr

/-- A program: its instructions, numbered from 0. -/
abbrev Program : Type := List Instr

/-- A configuration: the program counter, the stacks of numbers (top first), the return stack,
the unread input and the output written so far. -/
structure Config where
  pc : ℕ
  stk : Stk → List ℕ
  rs : List ℕ
  inp : List Bool
  out : List Bool

/-- The start on input `x`: instruction 0, every stack empty, nothing written. -/
def init (x : List Bool) : Config :=
  { pc := 0, stk := fun _ => [], rs := [], inp := x, out := [] }

/-- Run one instruction. The result is the next configuration and the cost of the instruction,
or `none` if the instruction is `halt` or cannot run (it pops an empty stack, or it is `add` or
`sub` with `s = t`). -/
def exec1 (c : Config) : Instr → Option (Config × ℕ)
  | .push s k => some ({ c with pc := c.pc + 1, stk := Function.update c.stk s (k :: c.stk s) },
      1 + len k)
  | .pop s => match c.stk s with
    | v :: r => some ({ c with pc := c.pc + 1, stk := Function.update c.stk s r }, 1 + len v)
    | [] => none
  | .copy s t => match c.stk s with
    | v :: _ => some ({ c with pc := c.pc + 1, stk := Function.update c.stk t (v :: c.stk t) },
        1 + len v)
    | [] => none
  | .move s t => match c.stk s with
    | v :: r =>
      let st := Function.update c.stk s r
      some ({ c with pc := c.pc + 1, stk := Function.update st t (v :: st t) }, 1 + len v)
    | [] => none
  | .add s t => if s = t then none else match c.stk s, c.stk t with
    | a :: r, b :: r' =>
      some ({ c with
        pc := c.pc + 1
        stk := Function.update (Function.update c.stk t r') s ((a + b) :: r) },
        1 + len a + len b)
    | _, _ => none
  | .sub s t => if s = t then none else match c.stk s, c.stk t with
    | a :: r, b :: r' =>
      some ({ c with
        pc := c.pc + 1
        stk := Function.update (Function.update c.stk t r') s ((a - b) :: r) },
        1 + len a + len b)
    | _, _ => none
  | .double s => match c.stk s with
    | v :: r => some ({ c with pc := c.pc + 1, stk := Function.update c.stk s (2 * v :: r) },
        1 + len v)
    | [] => none
  | .half s => match c.stk s with
    | v :: r => some ({ c with pc := c.pc + 1, stk := Function.update c.stk s (v / 2 :: r) },
        1 + len v)
    | [] => none
  | .parity s => match c.stk s with
    | v :: r => some ({ c with pc := c.pc + 1, stk := Function.update c.stk s (v % 2 :: r) },
        1 + len v)
    | [] => none
  | .jz s l => match c.stk s with
    | v :: r => some ({ c with
        pc := if v = 0 then l else c.pc + 1
        stk := Function.update c.stk s r }, 1 + len v)
    | [] => none
  | .jmp l => some ({ c with pc := l }, 1)
  | .jnil s l => some ({ c with pc := (if c.stk s = [] then l else c.pc + 1) }, 1)
  | .call l => some ({ c with pc := l, rs := (c.pc + 1) :: c.rs }, 1)
  | .ret => match c.rs with
    | r :: rs => some ({ c with pc := r, rs := rs }, 1)
    | [] => none
  | .read s => match c.inp with
    | b :: x => some ({ c with
        pc := c.pc + 1
        stk := Function.update c.stk s ((if b then 1 else 0) :: c.stk s)
        inp := x }, 1)
    | [] => some ({ c with pc := c.pc + 1, stk := Function.update c.stk s (2 :: c.stk s) }, 1)
  | .write s => match c.stk s with
    | v :: r => some ({ c with
        pc := c.pc + 1
        stk := Function.update c.stk s r
        out := c.out ++ [decide (v ≠ 0)] }, 1 + len v)
    | [] => none
  | .halt => none

/-- One step of program `P`: run the instruction at the program counter. There is no step if the
program counter is past the end of the program. -/
def step (P : Program) (c : Config) : Option (Config × ℕ) :=
  match P[c.pc]? with
  | some i => exec1 c i
  | none => none

/-- `Steps P c c' S`: program `P` goes from `c` to `c'` in zero or more steps of total cost
`S`. -/
inductive Steps (P : Program) : Config → Config → ℕ → Prop
  | refl (c : Config) : Steps P c c 0
  | step {c c₁ c' : Config} {s S : ℕ} : step P c = some (c₁, s) → Steps P c₁ c' S →
      Steps P c c' (s + S)

/-- `Halts P x y S`: started on input `x`, program `P` reaches a `halt` instruction at total cost
`S`, and the output at that point is `y`. -/
def Halts (P : Program) (x y : List Bool) (S : ℕ) : Prop :=
  ∃ c, Steps P (init x) c S ∧ P[c.pc]? = some .halt ∧ c.out = y

/-- `code` sits in `P` from index `a` on. -/
def CodeAt (P : Program) (a : ℕ) (code : List Instr) : Prop :=
  ∀ i (h : i < code.length), P[a + i]? = some code[i]

namespace Steps

variable {P : Program}

theorem trans {c₁ c₂ c₃ : Config} {S T : ℕ} (h₁ : Steps P c₁ c₂ S) (h₂ : Steps P c₂ c₃ T) :
    Steps P c₁ c₃ (S + T) := by
  induction h₁ with
  | refl => simpa using h₂
  | step hs _ ih => rw [Nat.add_assoc]; exact .step hs (ih h₂)

theorem single {c c' : Config} {s : ℕ} (h : SM.step P c = some (c', s)) : Steps P c c' s := by
  simpa using Steps.step h (.refl c')

/-- A run whose cost is given by an equation. -/
theorem cast {c c' : Config} {S T : ℕ} (h : Steps P c c' S) (e : S = T) : Steps P c c' T :=
  e ▸ h

end Steps

theorem step_eq {P : Program} {c : Config} {i : Instr} (h : P[c.pc]? = some i) :
    step P c = exec1 c i := by
  simp [step, h]

namespace CodeAt

variable {P : Program} {a : ℕ}

theorem get {code : List Instr} (h : CodeAt P a code) {i : ℕ} (hi : i < code.length) :
    P[a + i]? = some code[i] := h i hi

theorem append_left {c₁ c₂ : List Instr} (h : CodeAt P a (c₁ ++ c₂)) : CodeAt P a c₁ :=
  fun i hi => by
    have := h i (by simp; omega)
    simpa [List.getElem_append_left hi] using this

theorem append_right {c₁ c₂ : List Instr} (h : CodeAt P a (c₁ ++ c₂)) :
    CodeAt P (a + c₁.length) c₂ := fun i hi => by
  have := h (c₁.length + i) (by simp; omega)
  rw [← Nat.add_assoc] at this
  simpa using this

theorem append {c₁ c₂ : List Instr} (h₁ : CodeAt P a c₁) (h₂ : CodeAt P (a + c₁.length) c₂) :
    CodeAt P a (c₁ ++ c₂) := fun i hi => by
  by_cases hi' : i < c₁.length
  · simpa [List.getElem_append_left hi'] using h₁ i hi'
  · have := h₂ (i - c₁.length) (by simp at hi; omega)
    rw [show a + c₁.length + (i - c₁.length) = a + i by omega] at this
    simpa [List.getElem_append_right (by omega : c₁.length ≤ i)] using this

theorem cons {i : Instr} {code : List Instr} (h : CodeAt P a (i :: code)) : P[a]? = some i := by
  have h0 := h 0 (Nat.succ_pos _)
  rw [Nat.add_zero] at h0
  exact h0

theorem tail {i : Instr} {code : List Instr} (h : CodeAt P a (i :: code)) :
    CodeAt P (a + 1) code :=
  append_right (c₁ := [i]) h

theorem self (P : Program) : CodeAt P 0 P := fun i hi => by simp [hi]

end CodeAt

end GI.Turing.SM
