/-
Counting loops and other conveniences on top of `Workspace.Machine.Logic`.

* `WP.frame_reg`: a register that a statement never writes keeps its value.
* `Stmt.forUp i n body` runs `body` for register `i = 0, 1, …, N - 1`, where `N` is the value of
  register `n`. The rule `WP.forUp` needs an invariant `I k st` after `k` rounds and a cost bound
  `B k` for round `k`; the whole loop costs at most `∑ k < N, (B k + 11 + 6 len N) + 7 + 4 len N`.
  `WP.forUp_const` is the case of a constant bound `B`.
* `s ;; t` is notation for `Stmt.seq s t`.
-/
import Workspace.Machine.Logic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace GI.Machine

/-- `s ;; t` runs `s`, then `t`. -/
infixr:20 " ;; " => Stmt.seq

/-- A register that the statement never writes keeps its value. -/
theorem WP.frame_reg {p : Program} {s : Stmt} {st : State} {Q : Outcome → State → ℕ → Prop}
    {r : ℕ} (h : WP p s st Q) (hw : ¬ s.Writes r) :
    WP p s st (fun o st' c => Q o st' c ∧ st'.regs r = st.regs r) := by
  obtain ⟨o, st', c, hr, hq⟩ := h
  exact ⟨o, st', c, hr, hq, hr.regs_eq_of_not_writes hw⟩

/-- `forUp i n body`: set register `i` to 0, and while `i` is below register `n`, run `body` and
add one to `i`. -/
def Stmt.forUp (i n : ℕ) (body : Stmt) : Stmt :=
  .assign i (.const 0) ;;
  .loop (.bin .lt (.reg i) (.reg n)) (body ;; .assign i (.bin .add (.reg i) (.const 1)))

@[simp] theorem Stmt.writes_forUp (i n r : ℕ) (body : Stmt) :
    (Stmt.forUp i n body).Writes r ↔ r = i ∨ body.Writes r := by
  simp [Stmt.forUp, Stmt.Writes]; tauto

open Finset in
/-- The rule for a counting loop. `I k st` holds after `k` rounds. Round `k` runs `body` from a
state with `i = k`, `n = N` and `I k`, ends normally with `I (k + 1)`, and costs at most `B k`.
The invariant must not depend on register `i` (`hI`), and `body` must not write `i` or `n`. -/
theorem WP.forUp {p : Program} {body : Stmt} {st : State} {Q : Outcome → State → ℕ → Prop}
    {i n : ℕ} (hin : i ≠ n) (hwi : ¬ body.Writes i) (hwn : ¬ body.Writes n)
    (I : ℕ → State → Prop) (B : ℕ → ℕ)
    (hI : ∀ k st' v, I k st' → I k { st' with regs := Function.update st'.regs i v })
    (h0 : I 0 st)
    (hstep : ∀ k st', k < st.regs n → I k st' → st'.regs i = k → st'.regs n = st.regs n →
      WP p body st' (fun o st'' c => o = .normal ∧ I (k + 1) st'' ∧ c ≤ B k))
    (hQ : ∀ st' c, I (st.regs n) st' → st'.regs i = st.regs n → st'.regs n = st.regs n →
      c ≤ ∑ k ∈ range (st.regs n), (B k + 11 + 6 * len (st.regs n)) + 7 +
        4 * len (st.regs n) → Q .normal st' c) :
    WP p (Stmt.forUp i n body) st Q := by
  set N := st.regs n with hN
  set S : ℕ → ℕ := fun k => ∑ j ∈ range k, (B j + 11 + 6 * len N) with hS
  -- The invariant of the `loop`: `k` rounds done, cost at most `S k`.
  let J : State → ℕ → Prop := fun st' a => ∃ k, k ≤ N ∧ st'.regs i = k ∧ st'.regs n = N ∧
    I k st' ∧ a ≤ S k
  refine WP.seq' (fun st' c => J st' 0 ∧ c = 2) ?_ ?_
  · apply WP.assign
    refine ⟨rfl, ⟨0, Nat.zero_le _, by simp, by simp [Function.update_of_ne hin.symm, hN], hI _ _ _ h0,
      by simp⟩, by simp [len_zero]⟩
  rintro st₁ c₁ ⟨hJ, rfl⟩
  refine WP.loop (Q := fun o st'' c' => Q o st'' (2 + c' + 1)) J
    (fun st' => N - st'.regs i) hJ ?_ ?_
  · rintro st' a ⟨k, hkN, hik, hnN, hIk, ha⟩ htest
    have hk : k < N := by
      simp only [evalExpr_bin, evalExpr_reg, BinOp.eval_lt, hik, hnN] at htest
      by_contra h; simp [h] at htest
    have hb := (hstep k st' hk hIk hik hnN).frame_reg hwi |>.frame_reg hwn
    refine WP.seq' (fun st'' c => I (k + 1) st'' ∧ c ≤ B k ∧ st''.regs i = k ∧
      st''.regs n = N) (hb.mono ?_) ?_
    · rintro o st'' c ⟨⟨⟨rfl, h1, h2⟩, h3⟩, h4⟩
      exact ⟨rfl, h1, h2, h3.trans hik, h4.trans hnN⟩
    rintro st'' c ⟨hI1, hc, hi'', hn''⟩
    apply WP.assign
    simp only [evalExpr_bin, evalExpr_reg, evalExpr_const, BinOp.eval_add, BinOp.eval_lt, hik,
      hnN, hi'', if_pos hk, len_one]
    refine ⟨⟨k + 1, hk, by simp, by simp [Function.update_of_ne hin.symm, hn''],
      hI _ _ _ hI1, ?_⟩, by simp [Function.update_self]; omega⟩
    have hlk := len_mono hk.le
    have hsum : S (k + 1) = S k + (B k + 11 + 6 * len N) := by
      simp only [hS, sum_range_succ]
    rw [hsum]
    omega
  · rintro st' a ⟨k, hkN, hik, hnN, hIk, ha⟩ htest
    have hk : k = N := by
      simp only [evalExpr_bin, evalExpr_reg, BinOp.eval_lt, hik, hnN] at htest
      by_contra h; have : k < N := by omega
      simp [this] at htest
    subst hk
    simp only [evalExpr_bin, evalExpr_reg, BinOp.eval_lt, hik, hnN]
    exact hQ st' _ hIk hik hnN (by simp only [hS] at ha; omega)

open Finset in
/-- `WP.forUp` with the same cost bound `B` for every round. -/
theorem WP.forUp_const {p : Program} {body : Stmt} {st : State}
    {Q : Outcome → State → ℕ → Prop}
    {i n : ℕ} (hin : i ≠ n) (hwi : ¬ body.Writes i) (hwn : ¬ body.Writes n)
    (I : ℕ → State → Prop) (B : ℕ)
    (hI : ∀ k st' v, I k st' → I k { st' with regs := Function.update st'.regs i v })
    (h0 : I 0 st)
    (hstep : ∀ k st', k < st.regs n → I k st' → st'.regs i = k → st'.regs n = st.regs n →
      WP p body st' (fun o st'' c => o = .normal ∧ I (k + 1) st'' ∧ c ≤ B))
    (hQ : ∀ st' c, I (st.regs n) st' → st'.regs i = st.regs n → st'.regs n = st.regs n →
      c ≤ st.regs n * (B + 11 + 6 * len (st.regs n)) + 7 + 4 * len (st.regs n) →
      Q .normal st' c) :
    WP p (Stmt.forUp i n body) st Q :=
  WP.forUp hin hwi hwn I (fun _ => B) hI h0 hstep
    (fun st' c h1 h2 h3 hc => hQ st' c h1 h2 h3 (by simpa [sum_const, card_range] using hc))

end GI.Machine

namespace GI.Machine

/-- Every register that the statement never writes keeps its value. -/
theorem WP.frame_regs {p : Program} {s : Stmt} {st : State} {Q : Outcome → State → ℕ → Prop}
    (h : WP p s st Q) :
    WP p s st (fun o st' c => Q o st' c ∧ ∀ r, ¬ s.Writes r → st'.regs r = st.regs r) := by
  obtain ⟨o, st', c, hr, hq⟩ := h
  exact ⟨o, st', c, hr, hq, fun r hw => hr.regs_eq_of_not_writes hw⟩

/-- A statement without `store` and `call` keeps the memory. -/
theorem WP.frame_mem {p : Program} {s : Stmt} {st : State} {Q : Outcome → State → ℕ → Prop}
    (h : WP p s st Q) (hs : s.ReadOnly) :
    WP p s st (fun o st' c => Q o st' c ∧ st'.mem = st.mem) := by
  obtain ⟨o, st', c, hr, hq⟩ := h
  exact ⟨o, st', c, hr, hq, hr.mem_eq_of_readOnly hs⟩

end GI.Machine
