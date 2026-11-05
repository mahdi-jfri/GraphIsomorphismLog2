/-
How a cited algorithm is stated. Every algorithm from the literature that the proof uses is
stated as `∃ p, PolyTimeAt t p` for a task `t`, and this statement is proved in the library.

A task says how an instance is laid out in memory and which outputs are correct. A program solves
it in polynomial time if, wherever the caller places the instance, one call to the program's
procedure 0 with the base address as its argument returns the address of a correct output, keeps
every cell below the base address, and costs at most a polynomial in the size of the instance and
the length of the base address. The cells at and above the base address, apart from the instance,
may hold anything, so a caller can place an instance just above its own data and call the program
as a subroutine.

Such a statement is true for every algorithm that the literature proves to run in polynomial time,
provided the task is set up as described in `GI.Cited.Task`: a Turing machine or a RAM running the
algorithm can be simulated on the machine of `Workspace.Statement.Machine` with every address
shifted by the base address, at a polynomial overhead.
-/
module

public import Workspace.Statement.Machine

@[expose] public section

namespace GI.Cited

open GI.Machine

/-- A computational task, given by its memory layout.
* `size x` is the number of cells that instance `x` occupies.
* `Input x b mem` says that `mem` holds `x` in the cells `b, …, b + size x - 1`. It must depend only
  on those cells, and it must bound every cell value by a polynomial in `size x`.
* `Output x mem r` says that `mem` holds a correct output for `x`, starting at address `r`. Every
  instance must have a correct output, of size polynomial in `size x`.

Lean does not check these requirements. They are what makes `∃ p, PolyTimeAt t p` true for a
polynomial-time algorithm. -/
structure Task (α : Type) where
  size : α → ℕ
  Input : α → ℕ → (ℕ → ℕ) → Prop
  Output : α → (ℕ → ℕ) → ℕ → Prop

/-- Program `p` solves task `t` in polynomial time, wherever the instance lies in memory. There are
constants `c, k` such that for every instance `x`, base address `b`, and memory `mem` holding `x` at
`b`, calling procedure 0 of `p` with argument `b` finishes, and then:
* every cell below `b` is unchanged;
* the returned address `r` is at least `b`, and the memory holds a correct output at `r`;
* the cost is at most `c * (size x + len b + 2) ^ k`.

The registers of the calling state all hold `b`, so the call `.call 0 0 [.reg 0]` passes `b`; the
returned address lands in register 0. -/
def PolyTimeAt {α : Type} (t : Task α) (p : Program) : Prop :=
  ∃ c k : ℕ, ∀ (x : α) (b : ℕ) (mem : ℕ → ℕ), t.Input x b mem →
    ∃ fuel o st cost,
      exec p fuel (.call 0 0 [.reg 0]) { mem := mem, regs := fun _ => b } = some (o, st, cost) ∧
      (∀ a < b, st.mem a = mem a) ∧
      b ≤ st.regs 0 ∧ t.Output x st.mem (st.regs 0) ∧
      cost ≤ c * (t.size x + len b + 2) ^ k

end GI.Cited
