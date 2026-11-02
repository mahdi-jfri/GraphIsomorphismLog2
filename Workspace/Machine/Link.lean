/-
Linking programs, and cited algorithms as subroutines.

A program `p` can be placed inside a bigger program `q` at offset `k`: procedure `i` of `p`
becomes procedure `i + k` of `q`, with every `call` inside it shifted by `k`
(`GI.Machine.Stmt.shift`). `GI.Machine.Embeds q p k` says that `q` contains such a copy. Then
every run of `p` is a run of `q` with the same outcome, state and cost
(`GI.Machine.Runs.shift`), so `call r k args` in `q` behaves as `call r 0 args` in `p`.

The main use is `GI.Machine.PolyTimeWith.wp_call`: a program `p` with `GI.Cited.PolyTimeAt t p`,
embedded in `q` at offset `k`, gives a rule for `call r k [e]` in `q`. If `e` evaluates to `b`
and the memory holds an instance `x` at `b`, the call finishes, keeps the memory below `b`, puts
the address of a correct output in register `r`, changes no other register, and costs at most
the polynomial bound plus the cost of `e`.
-/
import Workspace.Machine.Loops
import Workspace.Cited.Algorithm

namespace GI.Machine

/-- Add `k` to the index of every procedure called by the statement. -/
def Stmt.shift (k : ℕ) : Stmt → Stmt
  | .nop => .nop
  | .assign r e => .assign r e
  | .store a e => .store a e
  | .seq s t => .seq (s.shift k) (t.shift k)
  | .cond e s t => .cond e (s.shift k) (t.shift k)
  | .loop e s => .loop e (s.shift k)
  | .call r f args => .call r (f + k) args
  | .ret e => .ret e

@[simp] theorem Stmt.shift_zero (s : Stmt) : s.shift 0 = s := by
  induction s <;> simp_all [Stmt.shift]

theorem Stmt.shift_shift (s : Stmt) (k m : ℕ) : (s.shift k).shift m = s.shift (k + m) := by
  induction s <;> simp_all [Stmt.shift, Nat.add_assoc]

@[simp] theorem Stmt.writes_shift (s : Stmt) (k r : ℕ) : (s.shift k).Writes r ↔ s.Writes r := by
  induction s <;> simp_all [Stmt.shift, Stmt.Writes]

/-- The procedures of `p` with every call shifted by `k`: the copy of `p` to place at offset
`k` of a bigger program. -/
def Program.shifted (p : Program) (k : ℕ) : List Stmt := p.procs.map (Stmt.shift k)

/-- `q` contains a copy of `p` at offset `k`: procedure `i` of `p`, with its calls shifted by
`k`, is procedure `i + k` of `q`. -/
def Embeds (q p : Program) (k : ℕ) : Prop :=
  ∀ i body, p.procs[i]? = some body → q.procs[i + k]? = some (body.shift k)

namespace Embeds

theorem refl (p : Program) : Embeds p p 0 := by
  intro i body h; simpa using h

/-- The standard way to embed: the procedures of `q` are some list `A`, then the copy of `p`
at offset `A.length`, then anything. -/
theorem of_append {q p : Program} {A B : List Stmt}
    (h : q.procs = A ++ p.shifted A.length ++ B) : Embeds q p A.length := by
  intro i body hb
  have hi : i < p.procs.length := (List.getElem?_eq_some_iff.mp hb).1
  rw [h, List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel,
    List.getElem?_append_left (by simpa [Program.shifted] using hi)]
  simp [Program.shifted, hb]

theorem trans {q p r : Program} {k m : ℕ} (h₁ : Embeds q p k) (h₂ : Embeds r q m) :
    Embeds r p (k + m) := by
  intro i body hb
  have := h₂ _ _ (h₁ i body hb)
  rw [Stmt.shift_shift, Nat.add_assoc] at this
  exact this

end Embeds

/-- Running a shifted statement in a program that embeds `p` gives the same result as in `p`. -/
theorem exec_shift {q p : Program} {k : ℕ} (hq : Embeds q p k) {fuel : ℕ} {s : Stmt}
    {st : State} {res : Outcome × State × ℕ} (h : exec p fuel s st = some res) :
    exec q fuel (s.shift k) st = some res := by
  induction fuel generalizing s st res with
  | zero => simp [exec] at h
  | succ f ih =>
    cases s with
    | nop => simpa [exec, Stmt.shift] using h
    | assign r e => simpa [exec, Stmt.shift] using h
    | store a e => simpa [exec, Stmt.shift] using h
    | ret e => simpa [exec, Stmt.shift] using h
    | seq s t =>
      simp only [exec, Stmt.shift] at h ⊢
      cases h1 : exec p f s st with
      | none => simp [h1] at h
      | some r1 =>
        rw [ih h1]
        rw [h1] at h
        obtain ⟨o, st', c⟩ := r1
        cases o with
        | returned v => exact h
        | normal =>
          simp only at h ⊢
          cases h2 : exec p f t st' with
          | none => simp [h2] at h
          | some r2 => rw [ih h2]; rw [h2] at h; exact h
    | cond e s t =>
      simp only [exec, Stmt.shift] at h ⊢
      cases h1 : exec p f (if (evalExpr st e).1 = 0 then t else s) st with
      | none => simp [h1] at h
      | some r1 =>
        have : exec q f (if (evalExpr st e).1 = 0 then t.shift k else s.shift k) st =
            some r1 := by
          split_ifs with he
          · rw [if_pos he] at h1; exact ih h1
          · rw [if_neg he] at h1; exact ih h1
        rw [this]; rw [h1] at h; exact h
    | loop e body =>
      simp only [exec, Stmt.shift] at h ⊢
      split_ifs at h ⊢ with hv
      · exact h
      · cases h1 : exec p f body st with
        | none => simp [h1] at h
        | some r1 =>
          rw [ih h1]
          rw [h1] at h
          obtain ⟨o, st', c⟩ := r1
          cases o with
          | returned w => exact h
          | normal =>
            simp only at h ⊢
            cases h2 : exec p f (.loop e body) st' with
            | none => simp [h2] at h
            | some r2 =>
              have := ih h2
              simp only [Stmt.shift] at this
              rw [this]; rw [h2] at h; exact h
    | call r g args =>
      simp only [exec, Stmt.shift] at h ⊢
      cases hb : p.procs[g]? with
      | none => simp [hb] at h
      | some body =>
        rw [hb] at h
        rw [hq g body hb]
        simp only at h ⊢
        cases h1 : exec p f body
            { mem := st.mem, regs := fun i => (evalArgs st args).1.getD i 0 } with
        | none => rw [h1] at h; simp at h
        | some r1 => rw [ih h1]; rw [h1] at h; exact h

theorem Runs.shift {q p : Program} {k : ℕ} (hq : Embeds q p k) {s : Stmt} {st st' : State}
    {o : Outcome} {c : ℕ} (h : Runs p s st o st' c) : Runs q (s.shift k) st o st' c := by
  obtain ⟨fuel, h⟩ := h
  exact ⟨fuel, exec_shift hq h⟩

theorem WP.shift {q p : Program} {k : ℕ} (hq : Embeds q p k) {s : Stmt} {st : State}
    {Q : Outcome → State → ℕ → Prop} (h : WP p s st Q) : WP q (s.shift k) st Q := by
  obtain ⟨o, st', c, hr, hQ⟩ := h
  exact ⟨o, st', c, hr.shift hq, hQ⟩

/-- A specification of procedure `f` of `p` holds for procedure `f + k` of any program that
embeds `p` at offset `k`. -/
theorem ProcSpec.shift {q p : Program} {k f : ℕ} (hq : Embeds q p k)
    {P : (ℕ → ℕ) → (ℕ → ℕ) → Prop} {Q : (ℕ → ℕ) → (ℕ → ℕ) → (ℕ → ℕ) → ℕ → ℕ → Prop}
    (h : ProcSpec p f P Q) : ProcSpec q (f + k) P Q := by
  intro args mem hP
  obtain ⟨body, hb, hw⟩ := h args mem hP
  exact ⟨body.shift k, hq f body hb, hw.shift hq⟩

/-- Inverting a run of `call`. -/
theorem Runs.call_inv {p : Program} {r f : ℕ} {args : List Expr} {st st' : State}
    {o : Outcome} {c : ℕ} (h : Runs p (.call r f args) st o st' c) :
    ∃ body o' st'' c', p.procs[f]? = some body ∧
      Runs p body { mem := st.mem, regs := fun i => (evalArgs st args).1.getD i 0 } o' st'' c' ∧
      o = .normal ∧ st' = { mem := st''.mem, regs := Function.update st.regs r o'.retVal } ∧
      c = (evalArgs st args).2 + c' + 1 := by
  obtain ⟨fuel, h⟩ := h
  cases fuel with
  | zero => simp [exec] at h
  | succ f' =>
    simp only [exec] at h
    cases hb : p.procs[f]? with
    | none => simp [hb] at h
    | some body =>
      rw [hb] at h
      simp only at h
      cases h1 : exec p f' body
          { mem := st.mem, regs := fun i => (evalArgs st args).1.getD i 0 } with
      | none => rw [h1] at h; simp at h
      | some r1 =>
        rw [h1] at h
        obtain ⟨o', st'', c'⟩ := r1
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨body, o', st'', c', rfl, ⟨f', h1⟩, rfl, ?_, rfl⟩
        cases o' <;> rfl

/-! ### Cited algorithms as subroutines -/

open GI.Cited

/-- `GI.Cited.PolyTimeAt` with its two constants given: the cost is at most
`c * (size x + len b + 2) ^ d`. -/
def PolyTimeWith {α : Type} (t : GI.Cited.Task α) (p : Program) (c d : ℕ) : Prop :=
  ∀ (x : α) (b : ℕ) (mem : ℕ → ℕ), t.Input x b mem →
    ∃ fuel o st cost,
      exec p fuel (.call 0 0 [.reg 0]) { mem := mem, regs := fun _ => b } = some (o, st, cost) ∧
      (∀ a < b, st.mem a = mem a) ∧
      b ≤ st.regs 0 ∧ t.Output x st.mem (st.regs 0) ∧
      cost ≤ c * (t.size x + len b + 2) ^ d

theorem polyTimeAt_iff {α : Type} (t : GI.Cited.Task α) (p : Program) :
    PolyTimeAt t p ↔ ∃ c d, PolyTimeWith t p c d := Iff.rfl

/-- The postcondition of a call to a cited algorithm, at the call `call r k [e]`: `b` is the
base address, `st` the state before the call. The call ends normally; it changes no register
other than `r`; it keeps every cell below `b`; register `r` holds an address at least `b` where
a correct output lies; the length of that address is at most the cost; and the cost is at most
`c * (size x + len b + 2) ^ d` plus `extra` (the cost of evaluating the argument). -/
structure CallPost {α : Type} (t : GI.Cited.Task α) (c d : ℕ) (x : α) (b r extra : ℕ) (st : State)
    (o : Outcome) (st' : State) (cost : ℕ) : Prop where
  normal : o = .normal
  regs : ∀ r', r' ≠ r → st'.regs r' = st.regs r'
  below : ∀ a < b, st'.mem a = st.mem a
  ge : b ≤ st'.regs r
  output : t.Output x st'.mem (st'.regs r)
  len_le : len (st'.regs r) ≤ cost
  cost_le : cost ≤ c * (t.size x + len b + 2) ^ d + extra

/-- **A cited algorithm as a subroutine.** If `p` solves `t` within `c * (size + len b + 2) ^ d`
and `q` embeds `p` at offset `k`, then in `q` the statement `call r k [e]` solves the instance
at the address `e` evaluates to. -/
theorem PolyTimeWith.wp_call {α : Type} {t : GI.Cited.Task α} {p : Program} {c d : ℕ}
    (hp : PolyTimeWith t p c d) {q : Program} {k : ℕ} (hq : Embeds q p k) {st : State}
    {r : ℕ} {e : Expr} {x : α} (hx : t.Input x (evalExpr st e).1 st.mem) :
    WP q (.call r k [e]) st
      (CallPost t c d x (evalExpr st e).1 r (evalExpr st e).2 st) := by
  set b := (evalExpr st e).1 with hb
  obtain ⟨fuel, o, st₁, cost, hrun, hbelow, hge, hout, hcost⟩ := hp x b st.mem hx
  obtain ⟨body, o', st'', c', hbody, hr, rfl, rfl, rfl⟩ := Runs.call_inv ⟨fuel, hrun⟩
  have hr' := hr.shift hq
  have hbody' := hq 0 body hbody
  rw [Nat.zero_add] at hbody'
  have hcall := Runs.call (r := r) (args := [e]) (st := st) hbody' (by simpa using hr')
  refine WP.intro hcall ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r' hr'
    simp [Function.update_of_ne hr']
  · intro a ha; exact hbelow a ha
  · simpa using hge
  · simpa using hout
  · simp only [Function.update_self]
    cases o' with
    | normal => simp [len_zero]
    | returned w =>
      have := hr.len_returned_le
      simp only [Outcome.retVal_returned, evalArgs_cons, evalArgs_nil]
      omega
  · simp only [evalArgs_cons, evalArgs_nil, evalExpr_reg] at hcost ⊢
    omega

/-- The same with `PolyTimeAt`: there are constants `c, d` that work for every embedding and
every call. -/
theorem PolyTimeAt.wp_call {α : Type} {t : GI.Cited.Task α} {p : Program} (hp : PolyTimeAt t p) :
    ∃ c d : ℕ, ∀ (q : Program) (k : ℕ), Embeds q p k → ∀ (st : State) (r : ℕ) (e : Expr)
      (x : α), t.Input x (evalExpr st e).1 st.mem →
      WP q (.call r k [e]) st (CallPost t c d x (evalExpr st e).1 r (evalExpr st e).2 st) := by
  obtain ⟨c, d, h⟩ := hp
  exact ⟨c, d, fun q k hq st r e x hx => PolyTimeWith.wp_call h hq hx⟩

end GI.Machine
