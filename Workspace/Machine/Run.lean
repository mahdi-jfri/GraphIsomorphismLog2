/-
Fuel-free semantics of the machine of `Workspace.Statement.Machine`.

`GI.Machine.Runs p s st o st' c` says that statement `s` of program `p`, started in state `st`,
finishes with outcome `o`, state `st'` and cost `c`, for some amount of fuel. Runs are
deterministic (`GI.Machine.Runs.det`), and there is one lemma building a run for each form of
statement. The program logic of `Workspace.Machine.Logic` is built on these lemmas.

We also prove two facts used later: a returned value has length at most the cost of the run
that returns it (`GI.Machine.Runs.len_returned_le`), and the registers that a statement never
writes keep their values (`GI.Machine.Runs.regs_eq_of_not_writes`).
-/
module

public import Workspace.Machine.Len

@[expose] public section

namespace GI.Machine

theorem State.ext' {a b : State} (h1 : a.mem = b.mem) (h2 : a.regs = b.regs) : a = b := by
  cases a; cases b; simp_all

theorem State.eta' (st : State) : ({ mem := st.mem, regs := st.regs } : State) = st := rfl

/-- The value a procedure gives back when it ends with outcome `o`: the value of its `ret`, or 0
if it ends without `ret`. -/
def Outcome.retVal : Outcome → ℕ
  | .returned w => w
  | .normal => 0

@[simp] theorem Outcome.retVal_returned (w : ℕ) : (Outcome.returned w).retVal = w := rfl
@[simp] theorem Outcome.retVal_normal : Outcome.normal.retVal = 0 := rfl

/-- Statement `s` of program `p`, started in state `st`, finishes with outcome `o`, state `st'`
and cost `c`. -/
def Runs (p : Program) (s : Stmt) (st : State) (o : Outcome) (st' : State) (c : ℕ) : Prop :=
  ∃ fuel, exec p fuel s st = some (o, st', c)

namespace Runs

variable {p : Program} {s t body : Stmt} {st st' st'' : State} {o o' : Outcome} {c c' : ℕ}

theorem mono_fuel {fuel fuel' : ℕ} {res : Outcome × State × ℕ}
    (h : exec p fuel s st = some res) (hle : fuel ≤ fuel') : exec p fuel' s st = some res :=
  exec_fuel_mono h hle

/-- Runs are deterministic: the outcome, final state and cost are fixed by the start. -/
theorem det (h₁ : Runs p s st o st' c) (h₂ : Runs p s st o' st'' c') :
    o = o' ∧ st' = st'' ∧ c = c' := by
  obtain ⟨f₁, h₁⟩ := h₁
  obtain ⟨f₂, h₂⟩ := h₂
  have e₁ := mono_fuel h₁ (le_max_left f₁ f₂)
  rw [mono_fuel h₂ (le_max_right f₁ f₂)] at e₁
  simp only [Option.some.injEq, Prod.mk.injEq] at e₁
  exact ⟨e₁.1.symm, e₁.2.1.symm, e₁.2.2.symm⟩

theorem nop : Runs p .nop st .normal st 1 := ⟨1, rfl⟩

theorem assign (r : ℕ) (e : Expr) :
    Runs p (.assign r e) st .normal
      { st with regs := Function.update st.regs r (evalExpr st e).1 } ((evalExpr st e).2 + 1) :=
  ⟨1, rfl⟩

theorem store (a e : Expr) :
    Runs p (.store a e) st .normal
      { st with mem := Function.update st.mem (evalExpr st a).1 (evalExpr st e).1 }
      ((evalExpr st a).2 + (evalExpr st e).2 + 1 + len (evalExpr st a).1 +
        len (evalExpr st e).1) :=
  ⟨1, rfl⟩

theorem ret (e : Expr) :
    Runs p (.ret e) st (.returned (evalExpr st e).1) st ((evalExpr st e).2 + 1) :=
  ⟨1, rfl⟩

theorem seq_normal (h₁ : Runs p s st .normal st' c) (h₂ : Runs p t st' o st'' c') :
    Runs p (.seq s t) st o st'' (c + c' + 1) := by
  obtain ⟨f₁, h₁⟩ := h₁
  obtain ⟨f₂, h₂⟩ := h₂
  refine ⟨max f₁ f₂ + 1, ?_⟩
  simp only [exec, mono_fuel h₁ (le_max_left f₁ f₂), mono_fuel h₂ (le_max_right f₁ f₂)]

theorem seq_returned {v : ℕ} (h₁ : Runs p s st (.returned v) st' c) :
    Runs p (.seq s t) st (.returned v) st' (c + 1) := by
  obtain ⟨f₁, h₁⟩ := h₁
  exact ⟨f₁ + 1, by simp only [exec, h₁]⟩

theorem cond {e : Expr}
    (h : Runs p (if (evalExpr st e).1 = 0 then t else s) st o st' c) :
    Runs p (.cond e s t) st o st' ((evalExpr st e).2 + c + 1) := by
  obtain ⟨f, h⟩ := h
  exact ⟨f + 1, by simp only [exec, h]⟩

theorem cond_true {e : Expr} (he : (evalExpr st e).1 ≠ 0) (h : Runs p s st o st' c) :
    Runs p (.cond e s t) st o st' ((evalExpr st e).2 + c + 1) :=
  cond (by rw [if_neg he]; exact h)

theorem cond_false {e : Expr} (he : (evalExpr st e).1 = 0) (h : Runs p t st o st' c) :
    Runs p (.cond e s t) st o st' ((evalExpr st e).2 + c + 1) :=
  cond (by rw [if_pos he]; exact h)

theorem loop_exit {e : Expr} (he : (evalExpr st e).1 = 0) :
    Runs p (.loop e body) st .normal st ((evalExpr st e).2 + 1) :=
  ⟨1, by simp only [exec, he, if_true]⟩

theorem loop_returned {e : Expr} {w : ℕ} (he : (evalExpr st e).1 ≠ 0)
    (h : Runs p body st (.returned w) st' c) :
    Runs p (.loop e body) st (.returned w) st' ((evalExpr st e).2 + c + 1) := by
  obtain ⟨f, h⟩ := h
  exact ⟨f + 1, by simp only [exec, he, if_false, h]⟩

theorem loop_step {e : Expr} (he : (evalExpr st e).1 ≠ 0)
    (h₁ : Runs p body st .normal st' c) (h₂ : Runs p (.loop e body) st' o st'' c') :
    Runs p (.loop e body) st o st'' ((evalExpr st e).2 + c + c' + 1) := by
  obtain ⟨f₁, h₁⟩ := h₁
  obtain ⟨f₂, h₂⟩ := h₂
  refine ⟨max f₁ f₂ + 1, ?_⟩
  simp only [exec, he, if_false, mono_fuel h₁ (le_max_left f₁ f₂),
    mono_fuel h₂ (le_max_right f₁ f₂)]

theorem call {r f : ℕ} {args : List Expr} (hf : p.procs[f]? = some body)
    (h : Runs p body { mem := st.mem, regs := fun i => (evalArgs st args).1.getD i 0 } o st' c) :
    Runs p (.call r f args) st .normal
      { mem := st'.mem, regs := Function.update st.regs r o.retVal }
      ((evalArgs st args).2 + c + 1) := by
  obtain ⟨fu, h⟩ := h
  refine ⟨fu + 1, ?_⟩
  simp only [exec, hf, h]
  cases o <;> rfl

end Runs

/-! ### The length of computed values -/

/-- The length of the value of an expression is at most its cost. -/
theorem len_evalExpr_le (st : State) (e : Expr) : len (evalExpr st e).1 ≤ (evalExpr st e).2 := by
  induction e with
  | const k => simp [evalExpr]
  | reg r => simp [evalExpr]
  | load a _ => simp only [evalExpr]; omega
  | bin op a b iha ihb =>
    simp only [evalExpr]
    have : len (op.eval (evalExpr st a).1 (evalExpr st b).1) ≤
        len (evalExpr st a).1 + len (evalExpr st b).1 + 1 := by
      cases op <;> simp only [BinOp.eval]
      · exact len_add_le_add _ _
      · exact le_trans (len_sub_le _ _) (by omega)
      · exact le_trans (len_mul_le _ _) (by omega)
      · exact le_trans (len_div_le _ _) (by omega)
      · exact le_trans (len_mod_le _ _) (by omega)
      · exact le_trans (len_ite_le_one _) (by omega)
      · exact le_trans (len_ite_le_one _) (by omega)
    omega

/-- A value returned by a run has length at most the cost of the run. -/
theorem Runs.len_returned_le {p : Program} {s : Stmt} {st st' : State} {w c : ℕ}
    (h : Runs p s st (.returned w) st' c) : len w ≤ c := by
  obtain ⟨fuel, h⟩ := h
  induction fuel generalizing s st st' w c with
  | zero => simp [exec] at h
  | succ f ih =>
    cases s with
    | nop => simp [exec] at h
    | assign r e => simp [exec] at h
    | store a e => simp [exec] at h
    | ret e =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq, Outcome.returned.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact le_trans (len_evalExpr_le st e) (by omega)
    | call r g args =>
      simp only [exec] at h
      split at h
      · simp at h
      · split at h
        · simp at h
        · simp at h
    | seq s t =>
      simp only [exec] at h
      split at h
      · simp at h
      · rename_i heq
        simp only [Option.some.injEq, Prod.mk.injEq, Outcome.returned.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact le_trans (ih heq) (by omega)
      · split at h
        · simp at h
        · rename_i heq _ _ _ heq2
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact le_trans (ih heq2) (by omega)
    | cond e s t =>
      simp only [exec] at h
      split at h
      · simp at h
      · rename_i heq
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact le_trans (ih heq) (by omega)
    | loop e body =>
      simp only [exec] at h
      split_ifs at h
      · simp at h
      · split at h
        · simp at h
        · rename_i heq
          simp only [Option.some.injEq, Prod.mk.injEq, Outcome.returned.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact le_trans (ih heq) (by omega)
        · split at h
          · simp at h
          · rename_i heq _ _ _ heq2
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact le_trans (ih heq2) (by omega)

/-! ### Registers that a statement never writes -/

/-- `s.Writes r`: statement `s` contains an `assign` to register `r` or a `call` whose result
goes to register `r`. Other registers keep their values (`Runs.regs_eq_of_not_writes`). -/
def Stmt.Writes : Stmt → ℕ → Prop
  | .nop, _ => False
  | .assign r' _, r => r = r'
  | .store _ _, _ => False
  | .seq s t, r => s.Writes r ∨ t.Writes r
  | .cond _ s t, r => s.Writes r ∨ t.Writes r
  | .loop _ s, r => s.Writes r
  | .call r' _ _, r => r = r'
  | .ret _, _ => False

instance Stmt.decWrites : (s : Stmt) → (r : ℕ) → Decidable (s.Writes r)
  | .nop, _ => isFalse id
  | .assign r' _, r => inferInstanceAs (Decidable (r = r'))
  | .store _ _, _ => isFalse id
  | .seq s t, r =>
    have := Stmt.decWrites s r; have := Stmt.decWrites t r
    inferInstanceAs (Decidable (_ ∨ _))
  | .cond _ s t, r =>
    have := Stmt.decWrites s r; have := Stmt.decWrites t r
    inferInstanceAs (Decidable (_ ∨ _))
  | .loop _ s, r => Stmt.decWrites s r
  | .call r' _ _, r => inferInstanceAs (Decidable (r = r'))
  | .ret _, _ => isFalse id

/-- A register that the statement never writes keeps its value. -/
theorem Runs.regs_eq_of_not_writes {p : Program} {s : Stmt} {st st' : State} {o : Outcome}
    {c r : ℕ} (h : Runs p s st o st' c) (hw : ¬ s.Writes r) : st'.regs r = st.regs r := by
  obtain ⟨fuel, h⟩ := h
  induction fuel generalizing s st st' o c with
  | zero => simp [exec] at h
  | succ f ih =>
    cases s with
    | nop =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2.1]
    | assign r' e =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2.1]
      simp only [Stmt.Writes] at hw
      simp [Function.update_of_ne hw]
    | store a e =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2.1]
    | ret e =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2.1]
    | call r' g args =>
      simp only [Stmt.Writes] at hw
      simp only [exec] at h
      split at h
      · simp at h
      · split at h
        · simp at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.2.1]
          simp [Function.update_of_ne hw]
    | seq s t =>
      simp only [Stmt.Writes, not_or] at hw
      simp only [exec] at h
      split at h
      · simp at h
      · rename_i heq
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.2.1]
        exact ih hw.1 heq
      · split at h
        · simp at h
        · rename_i heq _ _ _ _ heq2
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.2.1, ih hw.2 heq2, ih hw.1 heq]
    | cond e s t =>
      simp only [Stmt.Writes, not_or] at hw
      simp only [exec] at h
      split at h
      · simp at h
      · rename_i heq
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.2.1]
        split_ifs at heq
        · exact ih hw.2 heq
        · exact ih hw.1 heq
    | loop e body =>
      simp only [exec] at h
      split_ifs at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.2.1]
      · split at h
        · simp at h
        · rename_i heq
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.2.1]
          exact ih (by simpa [Stmt.Writes] using hw) heq
        · split at h
          · simp at h
          · rename_i heq _ _ _ _ heq2
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            rw [← h.2.1, ih hw heq2, ih (by simpa [Stmt.Writes] using hw) heq]

/-! ### Statements that do not write memory -/

/-- `s.ReadOnly`: statement `s` contains no `store` and no `call`, so it never changes the
memory (`Runs.mem_eq_of_readOnly`). -/
def Stmt.ReadOnly : Stmt → Prop
  | .nop => True
  | .assign _ _ => True
  | .store _ _ => False
  | .seq s t => s.ReadOnly ∧ t.ReadOnly
  | .cond _ s t => s.ReadOnly ∧ t.ReadOnly
  | .loop _ s => s.ReadOnly
  | .call _ _ _ => False
  | .ret _ => True

instance Stmt.decReadOnly : (s : Stmt) → Decidable s.ReadOnly
  | .nop => isTrue trivial
  | .assign _ _ => isTrue trivial
  | .store _ _ => isFalse id
  | .seq s t =>
    have := Stmt.decReadOnly s; have := Stmt.decReadOnly t
    inferInstanceAs (Decidable (_ ∧ _))
  | .cond _ s t =>
    have := Stmt.decReadOnly s; have := Stmt.decReadOnly t
    inferInstanceAs (Decidable (_ ∧ _))
  | .loop _ s => Stmt.decReadOnly s
  | .call _ _ _ => isFalse id
  | .ret _ => isTrue trivial

/-- A statement without `store` and `call` keeps the memory. -/
theorem Runs.mem_eq_of_readOnly {p : Program} {s : Stmt} {st st' : State} {o : Outcome}
    {c : ℕ} (h : Runs p s st o st' c) (hs : s.ReadOnly) : st'.mem = st.mem := by
  obtain ⟨fuel, h⟩ := h
  induction fuel generalizing s st st' o c with
  | zero => simp [exec] at h
  | succ f ih =>
    cases s with
    | nop =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2.1]
    | assign r' e =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2.1]
    | store a e => exact absurd hs id
    | ret e =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2.1]
    | call r' g args => exact absurd hs id
    | seq s t =>
      simp only [exec] at h
      split at h
      · simp at h
      · rename_i heq
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.2.1]
        exact ih hs.1 heq
      · split at h
        · simp at h
        · rename_i heq _ _ _ _ heq2
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.2.1, ih hs.2 heq2, ih hs.1 heq]
    | cond e s t =>
      simp only [exec] at h
      split at h
      · simp at h
      · rename_i heq
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.2.1]
        split_ifs at heq
        · exact ih hs.2 heq
        · exact ih hs.1 heq
    | loop e body =>
      simp only [exec] at h
      split_ifs at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.2.1]
      · split at h
        · simp at h
        · rename_i heq
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.2.1]
          exact ih (s := body) hs heq
        · split at h
          · simp at h
          · rename_i heq _ _ _ _ heq2
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            rw [← h.2.1, ih hs heq2, ih (s := body) hs heq]

end GI.Machine
