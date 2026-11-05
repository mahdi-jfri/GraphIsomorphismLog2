/-
A program logic for the machine, in weakest-precondition style.

`GI.Machine.WP p s st Q` says that statement `s` of program `p`, started in state `st`,
finishes, and its outcome, final state and exact cost satisfy `Q`. Since runs are deterministic
(`GI.Machine.Runs.det`), this is the same as saying that the unique run satisfies `Q`. A cost
bound is a postcondition of the form `c ≤ B`.

There is one rule for each form of statement (`WP.nop`, `WP.assign`, `WP.store`, `WP.seq`,
`WP.cond`, `WP.loop`, `WP.call`, `WP.ret`), plus the consequence rule `WP.mono`, rules with cost
bounds instead of exact costs, and procedure specifications (`GI.Machine.ProcSpec`) with the
rule `WP.call_spec`. The loop rule takes an invariant, which may mention the cost spent so far,
and a decreasing measure.

A typical proof applies the rules backwards (`refine WP.seq' _ ?_ ?_`), lets `simp` evaluate the
expressions, and proves the cost bound with `omega` or `nlinarith`.
-/
module

public import Workspace.Machine.Expr

@[expose] public section

namespace GI.Machine

/-- Statement `s` of `p`, started in `st`, finishes, and the outcome, final state and cost
satisfy `Q`. -/
def WP (p : Program) (s : Stmt) (st : State) (Q : Outcome → State → ℕ → Prop) : Prop :=
  ∃ o st' c, Runs p s st o st' c ∧ Q o st' c

namespace WP

variable {p : Program} {s t body : Stmt} {st : State} {Q Q' : Outcome → State → ℕ → Prop}

/-- A `WP` fact pins down the run: any run of `s` from `st` satisfies `Q`. -/
theorem of_runs {o : Outcome} {st' : State} {c : ℕ} (h : WP p s st Q)
    (hr : Runs p s st o st' c) : Q o st' c := by
  obtain ⟨o₁, st₁, c₁, h₁, hq⟩ := h
  obtain ⟨rfl, rfl, rfl⟩ := Runs.det h₁ hr
  exact hq

theorem intro {o : Outcome} {st' : State} {c : ℕ} (hr : Runs p s st o st' c)
    (hq : Q o st' c) : WP p s st Q := ⟨o, st', c, hr, hq⟩

/-- The consequence rule. -/
theorem mono (h : WP p s st Q) (hQ : ∀ o st' c, Q o st' c → Q' o st' c) : WP p s st Q' := by
  obtain ⟨o, st', c, hr, hq⟩ := h
  exact ⟨o, st', c, hr, hQ _ _ _ hq⟩

theorem and (h₁ : WP p s st Q) (h₂ : WP p s st Q') : WP p s st (fun o st' c => Q o st' c ∧ Q' o st' c) := by
  obtain ⟨o, st', c, hr, hq⟩ := h₁
  exact ⟨o, st', c, hr, hq, h₂.of_runs hr⟩

theorem nop (h : Q .normal st 1) : WP p .nop st Q := ⟨_, _, _, Runs.nop, h⟩

theorem assign {r : ℕ} {e : Expr}
    (h : Q .normal { st with regs := Function.update st.regs r (evalExpr st e).1 }
      ((evalExpr st e).2 + 1)) :
    WP p (.assign r e) st Q := ⟨_, _, _, Runs.assign r e, h⟩

theorem store {a e : Expr}
    (h : Q .normal { st with mem := Function.update st.mem (evalExpr st a).1 (evalExpr st e).1 }
      ((evalExpr st a).2 + (evalExpr st e).2 + 1 + len (evalExpr st a).1 +
        len (evalExpr st e).1)) :
    WP p (.store a e) st Q := ⟨_, _, _, Runs.store a e, h⟩

theorem ret {e : Expr} (h : Q (.returned (evalExpr st e).1) st ((evalExpr st e).2 + 1)) :
    WP p (.ret e) st Q := ⟨_, _, _, Runs.ret e, h⟩

/-- The general rule for `seq`: the first statement may return early. -/
theorem seq
    (h : WP p s st (fun o st' c => match o with
      | .normal => WP p t st' (fun o' st'' c' => Q o' st'' (c + c' + 1))
      | .returned v => Q (.returned v) st' (c + 1))) :
    WP p (.seq s t) st Q := by
  obtain ⟨o, st', c, hr, hq⟩ := h
  cases o with
  | normal =>
    obtain ⟨o', st'', c', hr', hq'⟩ := hq
    exact ⟨_, _, _, Runs.seq_normal hr hr', hq'⟩
  | returned v => exact ⟨_, _, _, Runs.seq_returned hr, hq⟩

/-- The rule for `seq` when the first statement ends normally, with an intermediate
condition `R` on the state and cost after it. -/
theorem seq' (R : State → ℕ → Prop) (h₁ : WP p s st (fun o st' c => o = .normal ∧ R st' c))
    (h₂ : ∀ st' c, R st' c → WP p t st' (fun o st'' c' => Q o st'' (c + c' + 1))) :
    WP p (.seq s t) st Q := by
  apply seq
  refine h₁.mono ?_
  rintro o st' c ⟨rfl, hR⟩
  exact h₂ st' c hR

theorem cond {e : Expr}
    (h : WP p (if (evalExpr st e).1 = 0 then t else s) st
      (fun o st' c => Q o st' ((evalExpr st e).2 + c + 1))) :
    WP p (.cond e s t) st Q := by
  obtain ⟨o, st', c, hr, hq⟩ := h
  exact ⟨_, _, _, Runs.cond hr, hq⟩

theorem cond_true {e : Expr} (he : (evalExpr st e).1 ≠ 0)
    (h : WP p s st (fun o st' c => Q o st' ((evalExpr st e).2 + c + 1))) :
    WP p (.cond e s t) st Q :=
  cond (by rw [if_neg he]; exact h)

theorem cond_false {e : Expr} (he : (evalExpr st e).1 = 0)
    (h : WP p t st (fun o st' c => Q o st' ((evalExpr st e).2 + c + 1))) :
    WP p (.cond e s t) st Q :=
  cond (by rw [if_pos he]; exact h)

/-- The loop rule. `I st a` is the invariant at the start of an iteration in state `st`, after
the loop has spent cost `a`. Each iteration that ends normally keeps the invariant and lowers
the measure `μ`. The cost of the whole loop is the cost spent when the test fails, plus that
test. -/
theorem loop {e : Expr} (I : State → ℕ → Prop) (μ : State → ℕ) (h0 : I st 0)
    (hstep : ∀ st' a, I st' a → (evalExpr st' e).1 ≠ 0 →
      WP p body st' (fun o st'' c => match o with
        | .normal => I st'' (a + (evalExpr st' e).2 + c + 1) ∧ μ st'' < μ st'
        | .returned w => Q (.returned w) st'' (a + (evalExpr st' e).2 + c + 1)))
    (hexit : ∀ st' a, I st' a → (evalExpr st' e).1 = 0 →
      Q .normal st' (a + (evalExpr st' e).2 + 1)) :
    WP p (.loop e body) st Q := by
  suffices H : ∀ m st' a, μ st' = m → I st' a →
      WP p (.loop e body) st' (fun o st'' c => Q o st'' (a + c)) by
    have := H _ st 0 rfl h0
    simpa using this
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro st' a hm hI
    by_cases he : (evalExpr st' e).1 = 0
    · refine ⟨_, _, _, Runs.loop_exit he, ?_⟩
      have := hexit st' a hI he
      simpa [Nat.add_assoc] using this
    · obtain ⟨o, st'', c, hr, hq⟩ := hstep st' a hI he
      cases o with
      | returned w =>
        refine ⟨_, _, _, Runs.loop_returned he hr, ?_⟩
        simpa [Nat.add_assoc] using hq
      | normal =>
        obtain ⟨hI', hμ⟩ := hq
        obtain ⟨o', st''', c', hr', hq'⟩ :=
          ih (μ st'') (hm ▸ hμ) st'' _ rfl hI'
        refine ⟨_, _, _, Runs.loop_step he hr hr', ?_⟩
        have hc : a + ((evalExpr st' e).2 + c + c' + 1) =
            a + (evalExpr st' e).2 + c + 1 + c' := by omega
        show Q o' st''' (a + ((evalExpr st' e).2 + c + c' + 1))
        rw [hc]
        exact hq'

theorem call {r f : ℕ} {args : List Expr} (hf : p.procs[f]? = some body)
    (h : WP p body { mem := st.mem, regs := fun i => (evalArgs st args).1.getD i 0 }
      (fun o st' c => Q .normal { mem := st'.mem, regs := Function.update st.regs r o.retVal }
        ((evalArgs st args).2 + c + 1))) :
    WP p (.call r f args) st Q := by
  obtain ⟨o, st', c, hr, hq⟩ := h
  exact ⟨_, _, _, Runs.call hf hr, hq⟩

/-! ### Rules with cost bounds

These rules ask for the postcondition at every cost up to a bound, instead of at the exact
cost. The bounds come from `Expr.cost_le`. -/

theorem assign_le {r : ℕ} {e : Expr} {M : ℕ} (hv : e.ValsLe st M)
    (h : ∀ c ≤ (e.size + 1) * (2 * len M + 1),
      Q .normal { st with regs := Function.update st.regs r (evalExpr st e).1 } c) :
    WP p (.assign r e) st Q :=
  assign (h _ (by have := Expr.cost_le hv; rw [Nat.add_mul]; omega))

theorem store_le {a e : Expr} {M : ℕ} (ha : a.ValsLe st M) (he : e.ValsLe st M)
    (haM : (evalExpr st a).1 ≤ M) (heM : (evalExpr st e).1 ≤ M)
    (h : ∀ c ≤ (a.size + e.size + 1) * (2 * len M + 1),
      Q .normal { st with mem := Function.update st.mem (evalExpr st a).1 (evalExpr st e).1 } c) :
    WP p (.store a e) st Q := by
  apply store
  apply h
  have h1 := Expr.cost_le ha
  have h2 := Expr.cost_le he
  have h3 := len_mono haM
  have h4 := len_mono heM
  simp only [Nat.add_mul]
  omega

theorem ret_le {e : Expr} {M : ℕ} (hv : e.ValsLe st M)
    (h : ∀ c ≤ (e.size + 1) * (2 * len M + 1), Q (.returned (evalExpr st e).1) st c) :
    WP p (.ret e) st Q :=
  ret (h _ (by have := Expr.cost_le hv; rw [Nat.add_mul]; omega))

/-- `seq` with cost bounds: if the first statement ends normally at cost at most `B₁` with
condition `R`, and the second, from any state satisfying `R`, satisfies `Q` at every cost up to
`B₂`, then `Q` holds for the whole statement at every cost up to `B₁ + B₂ + 1`. -/
theorem seq_le (R : State → Prop) (B₁ B₂ : ℕ)
    (h₁ : WP p s st (fun o st' c => o = .normal ∧ R st' ∧ c ≤ B₁))
    (h₂ : ∀ st', R st' → WP p t st' (fun o st'' c' => c' ≤ B₂ ∧ Q o st'' c'))
    (hQ : ∀ o st'' c, c ≤ B₁ + B₂ + 1 → (∃ c', c' ≤ B₂ ∧ Q o st'' c') → Q' o st'' c) :
    WP p (.seq s t) st Q' := by
  refine seq' (fun st' c => R st' ∧ c ≤ B₁) (h₁.mono ?_) ?_
  · rintro o st' c ⟨rfl, h, hc⟩; exact ⟨rfl, h, hc⟩
  · rintro st' c ⟨hR, hc⟩
    refine (h₂ st' hR).mono ?_
    rintro o st'' c' ⟨hc', hq⟩
    exact hQ _ _ _ (by omega) ⟨c', hc', hq⟩

end WP

/-! ### Procedure specifications -/

/-- Procedure `f` of `p` meets a specification. For all registers `args` (the arguments, with
0 in the unused registers) and memory `mem` satisfying `P`, the body of `f` finishes, and the
new memory `mem'`, the returned value `w` and the cost `c` of the body satisfy
`Q args mem mem' w c`. A `call` adds the cost of its arguments plus one (`WP.call_spec`). -/
def ProcSpec (p : Program) (f : ℕ) (P : (ℕ → ℕ) → (ℕ → ℕ) → Prop)
    (Q : (ℕ → ℕ) → (ℕ → ℕ) → (ℕ → ℕ) → ℕ → ℕ → Prop) : Prop :=
  ∀ args mem, P args mem → ∃ body, p.procs[f]? = some body ∧
    WP p body { mem := mem, regs := args } (fun o st' c => Q args mem st'.mem o.retVal c)

namespace ProcSpec

variable {p : Program} {f : ℕ} {P P' : (ℕ → ℕ) → (ℕ → ℕ) → Prop}
  {Q Q' : (ℕ → ℕ) → (ℕ → ℕ) → (ℕ → ℕ) → ℕ → ℕ → Prop}

/-- Build a specification from the body. -/
theorem of_body {body : Stmt} (hf : p.procs[f]? = some body)
    (h : ∀ args mem, P args mem →
      WP p body { mem := mem, regs := args } (fun o st' c => Q args mem st'.mem o.retVal c)) :
    ProcSpec p f P Q := fun args mem hP => ⟨body, hf, h args mem hP⟩

theorem mono (h : ProcSpec p f P Q) (hP : ∀ args mem, P' args mem → P args mem)
    (hQ : ∀ args mem mem' w c, P' args mem → Q args mem mem' w c → Q' args mem mem' w c) :
    ProcSpec p f P' Q' := by
  intro args mem hP'
  obtain ⟨body, hb, hw⟩ := h args mem (hP _ _ hP')
  exact ⟨body, hb, hw.mono fun o st' c hq => hQ _ _ _ _ _ hP' hq⟩

end ProcSpec

/-- The rule for calling a procedure with a specification. -/
theorem WP.call_spec {p : Program} {st : State} {Q : Outcome → State → ℕ → Prop} {r f : ℕ}
    {args : List Expr} {P : (ℕ → ℕ) → (ℕ → ℕ) → Prop}
    {S : (ℕ → ℕ) → (ℕ → ℕ) → (ℕ → ℕ) → ℕ → ℕ → Prop} (hs : ProcSpec p f P S)
    (hP : P (fun i => (evalArgs st args).1.getD i 0) st.mem)
    (h : ∀ mem' w c, S (fun i => (evalArgs st args).1.getD i 0) st.mem mem' w c →
      Q .normal { mem := mem', regs := Function.update st.regs r w }
        ((evalArgs st args).2 + c + 1)) :
    WP p (.call r f args) st Q := by
  obtain ⟨body, hb, hw⟩ := hs _ _ hP
  exact WP.call hb (hw.mono fun o st' c hq => h _ _ _ hq)

end GI.Machine
