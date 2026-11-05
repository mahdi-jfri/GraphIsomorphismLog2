/-
Two common loop shapes with ready-made rules.

* `WP.forUp_store`: the loop `forUp i n (.store a e)` writes `val k` at `addr k` for each round
  `k`. If the addresses are distinct and the expressions read only cells not yet written, the
  final memory holds `val k` at `addr k` and is unchanged elsewhere.
* `Stmt.checkAll i n f e` and `WP.checkAll`: test `e` for `i = 0, …, N - 1` and set the flag
  register `f` to 0 when a test fails. The memory does not change, and at the end the flag is
  unchanged if every test passed and 0 otherwise.
-/
module

public import Workspace.Machine.Layout

@[expose] public section

namespace GI.Machine

/-- The cost of `store a e` in state `st`. -/
def storeCost (st : State) (a e : Expr) : ℕ :=
  (evalExpr st a).2 + (evalExpr st e).2 + 1 + len (evalExpr st a).1 + len (evalExpr st e).1

theorem storeCost_le {st : State} {a e : Expr} {M : ℕ} (ha : a.ValsLe st M) (he : e.ValsLe st M)
    (haM : (evalExpr st a).1 ≤ M) (heM : (evalExpr st e).1 ≤ M) :
    storeCost st a e ≤ (a.size + e.size + 1) * (2 * len M + 1) := by
  have h1 := Expr.cost_le ha
  have h2 := Expr.cost_le he
  have h3 := len_mono haM
  have h4 := len_mono heM
  unfold storeCost
  simp only [Nat.add_mul]
  omega

/-- Registers equal to `update regs i k` agree with `regs` off `i`. -/
theorem regs_eq_update {regs regs' : ℕ → ℕ} {i k : ℕ} (hi : regs' i = k)
    (h : ∀ r, r ≠ i → regs' r = regs r) : regs' = Function.update regs i k := by
  funext r
  by_cases hr : r = i
  · subst hr; simp [hi]
  · rw [Function.update_of_ne hr, h r hr]

/-- The rule for a loop that stores `val k` at `addr k` in round `k`. The addresses must be
distinct for `k < N`. When round `k` starts, the registers are those of `st` with `i = k`, and
the memory agrees with `st` except at the addresses already written; there the expressions
must give `addr k` and `val k`, and the store must cost at most `T`. -/
theorem WP.forUp_store {p : Program} {st : State} {Q : Outcome → State → ℕ → Prop}
    {i n : ℕ} {a e : Expr} (hin : i ≠ n) (addr val : ℕ → ℕ) (T : ℕ)
    (hinj : ∀ j k, j < st.regs n → k < st.regs n → addr j = addr k → j = k)
    (heval : ∀ k st', k < st.regs n → st'.regs = Function.update st.regs i k →
      (∀ x, (∀ j < k, x ≠ addr j) → st'.mem x = st.mem x) →
      (evalExpr st' a).1 = addr k ∧ (evalExpr st' e).1 = val k ∧ storeCost st' a e ≤ T)
    (hQ : ∀ mem' c, (∀ k < st.regs n, mem' (addr k) = val k) →
      (∀ x, (∀ k < st.regs n, x ≠ addr k) → mem' x = st.mem x) →
      c ≤ st.regs n * (T + 11 + 6 * len (st.regs n)) + 7 + 4 * len (st.regs n) →
      Q .normal { mem := mem', regs := Function.update st.regs i (st.regs n) } c) :
    WP p (Stmt.forUp i n (.store a e)) st Q := by
  set N := st.regs n
  let I : ℕ → State → Prop := fun k st' => (∀ r, r ≠ i → st'.regs r = st.regs r) ∧
    (∀ j < k, st'.mem (addr j) = val j) ∧ (∀ x, (∀ j < k, x ≠ addr j) → st'.mem x = st.mem x)
  refine WP.forUp_const hin (by simp [Stmt.Writes]) (by simp [Stmt.Writes]) I T ?_ ?_ ?_ ?_
  · rintro k st' v ⟨h1, h2, h3⟩
    exact ⟨fun r hr => by simp [Function.update_of_ne hr, h1 r hr], h2, h3⟩
  · exact ⟨fun _ _ => rfl, fun j hj => absurd hj (Nat.not_lt_zero _), fun _ _ => rfl⟩
  · rintro k st' hk ⟨h1, h2, h3⟩ hik _
    obtain ⟨ha, he, hc⟩ := heval k st' hk (regs_eq_update hik h1) h3
    apply WP.store
    refine ⟨rfl, ⟨h1, ?_, ?_⟩, ?_⟩
    · intro j hj
      simp only [ha, he, Function.update_apply]
      split_ifs with hjk
      · rw [hinj j k (by omega) hk hjk]
      · exact h2 j (by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
          · exact h
          · exact absurd (congrArg addr h) hjk)
    · intro x hx
      simp only [ha, he, Function.update_apply]
      rw [if_neg (hx k (by omega))]
      exact h3 x (fun j hj => hx j (by omega))
    · exact hc
  · rintro st' c ⟨h1, h2, h3⟩ hi _ hc
    have hst : st' = { mem := st'.mem, regs := Function.update st.regs i N } :=
      State.ext' rfl (regs_eq_update hi h1)
    rw [hst]
    exact hQ st'.mem c h2 h3 hc

/-- Test `e` for `i = 0, …, N - 1`, where `N` is the value of register `n`, and set register `f`
to 0 whenever a test gives 0. -/
def Stmt.checkAll (i n f : ℕ) (e : Expr) : Stmt :=
  Stmt.forUp i n (.cond e .nop (.assign f (.const 0)))

@[simp] theorem Stmt.writes_checkAll (i n f r : ℕ) (e : Expr) :
    (Stmt.checkAll i n f e).Writes r ↔ r = i ∨ r = f := by
  simp [Stmt.checkAll, Stmt.Writes]

/-- The rule for `checkAll`. In round `k` the registers other than `i` and `f` are those of
`st`, register `i` is `k`, and the memory is that of `st`; there `e` must be nonzero exactly
when `P k` holds, and cost at most `T`. At the end the memory and the other registers are
unchanged, register `i` is `N`, and register `f` keeps its value if `P k` holds for all `k < N`
and is 0 otherwise. -/
theorem WP.checkAll {p : Program} {st : State} {Q : Outcome → State → ℕ → Prop}
    {i n f : ℕ} {e : Expr} (hin : i ≠ n) (hif : i ≠ f) (hfn : f ≠ n)
    (P : ℕ → Prop) [DecidablePred P] (T : ℕ)
    (heval : ∀ k st', k < st.regs n → st'.mem = st.mem →
      (∀ r, r ≠ i → r ≠ f → st'.regs r = st.regs r) → st'.regs i = k →
      ((evalExpr st' e).1 ≠ 0 ↔ P k) ∧ (evalExpr st' e).2 ≤ T)
    (hQ : ∀ st' c, st'.mem = st.mem → (∀ r, r ≠ i → r ≠ f → st'.regs r = st.regs r) →
      st'.regs i = st.regs n →
      st'.regs f = (if ∀ k < st.regs n, P k then st.regs f else 0) →
      c ≤ st.regs n * (T + 14 + 6 * len (st.regs n)) + 7 + 4 * len (st.regs n) →
      Q .normal st' c) :
    WP p (Stmt.checkAll i n f e) st Q := by
  set N := st.regs n
  let I : ℕ → State → Prop := fun k st' => st'.mem = st.mem ∧
    (∀ r, r ≠ i → r ≠ f → st'.regs r = st.regs r) ∧
    st'.regs f = (if ∀ j < k, P j then st.regs f else 0)
  refine WP.forUp_const hin (by simp [Stmt.Writes, hif]) (by simp [Stmt.Writes, hfn.symm]) I
    (T + 3) ?_ ?_ ?_ ?_
  · rintro k st' v ⟨h1, h2, h3⟩
    refine ⟨h1, fun r hr hrf => by simp [Function.update_of_ne hr, h2 r hr hrf], ?_⟩
    simp [Function.update_of_ne (Ne.symm hif), h3]
  · refine ⟨rfl, fun _ _ _ => rfl, ?_⟩
    simp
  · rintro k st' hk ⟨h1, h2, h3⟩ hik _
    obtain ⟨hP, hT⟩ := heval k st' hk h1 h2 hik
    apply WP.cond
    by_cases hPk : P k
    · rw [if_neg (hP.mpr hPk)]
      apply WP.nop
      refine ⟨rfl, ⟨h1, h2, ?_⟩, by omega⟩
      rw [h3]
      congr 1
      apply propext
      constructor
      · intro h j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h' | h'
        · exact h j h'
        · exact h' ▸ hPk
      · intro h j hj; exact h j (by omega)
    · have h0 : (evalExpr st' e).1 = 0 := by
        by_contra h; exact hPk (hP.mp h)
      rw [if_pos h0]
      apply WP.assign
      refine ⟨rfl, ⟨h1, fun r hr hrf => by simp [Function.update_of_ne hrf, h2 r hr hrf], ?_⟩, ?_⟩
      · simp only [evalExpr_const, Function.update_self]
        rw [if_neg]
        intro h; exact hPk (h k (by omega))
      · simp [len_zero]; omega
  · rintro st' c ⟨h1, h2, h3⟩ hi _ hc
    exact hQ st' c h1 h2 hi h3 hc

end GI.Machine
