module

public import Workspace.Impl.ScriptRun

@[expose] public section

/-!
# A step function that moves until it asks

Between two recursive calls the certificate phase passes through positions that ask nothing:
rounds with an empty increment, the closure at the end of a round, the end of a string and of a
test set. The script runner (`Iface.run_specC`) wants each step to return either the result or
one call. So the step function is a loop: it applies a *move* function `mv` and repeats while
the move says "continue".

A move returns one of

* `[0, out]` or `[1, code, arg, kst]`: what the step returns (`StepPostC`);
* `[2, st']`: go on from the program state `st'`.

`stepOKC_of_move`: if every move from a program state of measure `m` either meets `StepPostC` or
continues to a program state of a smaller measure that stands for a subset of the candidate
scripts, then the loop meets `StepOKC`, at cost at most `(M + 1)` times the cost of one move
plus overhead, where `M` bounds the measures. This is the well-founded induction on the number
of remaining positions that the plan asked for.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang
open GI.Cited (Val)

/-- **The loop of moves**, placed at index `d`, with the move function `mv`. -/
def cpLoopBody (d mv : ℕ) : Expr :=
  .letE (.call mv (.var 0))
    (.ite (.arith .eq (.get (.var 1) (.nat 0)) (.nat 2))
      (.call d (.get (.var 1) (.nat 1)))
      (.var 1))

/-- The cost of one round of the loop, for moves of cost at most `Bm` on program states of
weight at most `Bw`. -/
def cpLoopC (Bm Bw : ℕ) : ℕ := 20 * Bm + 2 * Bw + 60

theorem cp_stepPostC_head {μ : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ} {α : Type}
    {Out : α → Val → Prop} {Rep : Val → Set (Script α) → ℕ → Prop} {Ss : Set (Script α)}
    {f : ℕ} {w : Val} (h : Iface.StepPostC μ Out Rep Ss f w) :
    ∃ j rest, w = .list (.nat j :: rest) ∧ j < 2 := by
  rcases h with ⟨a, out, rfl, -⟩ | ⟨-, m, Ω', C', T, k', e', c', arg, kst, Ks, -, -, rfl, -⟩
  · exact ⟨0, _, rfl, by omega⟩
  · exact ⟨1, _, rfl, by omega⟩

/-- **The loop meets `StepOKC`.** -/
theorem stepOKC_of_move {Pg : Program} {d mv : ℕ} (hd : Pg.funs[d]? = some (cpLoopBody d mv))
    {μ : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ} {α : Type} {Out : α → Val → Prop}
    {Rep' : ℕ → Val → Set (Script α) → ℕ → Prop} {Bm Bw M : ℕ}
    (hmv : ∀ m st Ss f, Rep' m st Ss f → FunAll Pg mv st (fun w c => c ≤ Bm ∧
      (Iface.StepPostC μ Out (fun st Ss f => ∃ m, Rep' m st Ss f) Ss f w ∨
        ∃ m' st' Ss', m' < m ∧ Ss' ⊆ Ss ∧ Rep' m' st' Ss' f ∧ w = .list [.nat 2, st'])))
    (hwt : ∀ m st Ss f, Rep' m st Ss f → st.wt ≤ Bw)
    (hM : ∀ m st Ss f, Rep' m st Ss f → m ≤ M) :
    Iface.StepOKC Pg d μ Out (fun st Ss f => ∃ m, Rep' m st Ss f)
      ((M + 1) * cpLoopC Bm Bw + Bw) := by
  refine ⟨fun st Ss f ⟨m, hst⟩ => ?_, fun st Ss f ⟨m, hst⟩ => by
    have := hwt m st Ss f hst; nlinarith⟩
  -- The cost of the loop from a state of measure `m`.
  suffices key : ∀ m st Ss f, Rep' m st Ss f → FunAll Pg d st (fun w c =>
      c ≤ (m + 1) * cpLoopC Bm Bw ∧ w.wt < Bm ∧
        Iface.StepPostC μ Out (fun st Ss f => ∃ m, Rep' m st Ss f) Ss f w) by
    refine (key m st Ss f hst).mono fun w c ⟨hc, _, hp⟩ => ⟨?_, hp⟩
    have := hM m st Ss f hst
    have : (m + 1) * cpLoopC Bm Bw ≤ (M + 1) * cpLoopC Bm Bw :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  intro st Ss f hst
  have hwst := hwt m st Ss f hst
  refine FunAll.intro hd ?_
  unfold cpLoopBody
  refine EvalAll.letE (Ra := fun w cw => cw ≤ st.wt + 2 * Bm + 2 ∧ w.wt < Bm ∧
      (Iface.StepPostC μ Out (fun st Ss f => ∃ m, Rep' m st Ss f) Ss f w ∨
        ∃ m' st' Ss', m' < m ∧ Ss' ⊆ Ss ∧ Rep' m' st' Ss' f ∧ w = .list [.nat 2, st']))
    (EvalAll.call_funAll (Det.var' (P := Pg) (env := [st]) (i := 0) rfl) fun v ca h => ?_) ?_
  · obtain ⟨rfl, hca⟩ := h
    exact (hmv m _ Ss f hst).wt_lt.mono fun w c ⟨⟨hc, hp⟩, hwc⟩ => ⟨by omega, by omega, hp⟩
  rintro w cw ⟨hcw, hww, hp | ⟨m', st', Ss', hm', hsub, hst', rfl⟩⟩
  · -- The move returned what the step returns.
    obtain ⟨j, rest, rfl, hj⟩ := cp_stepPostC_head hp
    set w := Val.list (.nat j :: rest) with hw
    have dh := Det.get' (Det.var' (P := Pg) (env := [st, w]) (i := 1) (v := w) rfl) (Det.nat 0)
      (v := .nat j) rfl
    have dt := Det.arith' (op := .eq) dh (Det.nat 2) (z := 0) (by
      simp only [GI.Machine.BinOp.eval]; rw [if_neg (by omega)])
    have dv := Det.var' (P := Pg) (env := [st, w]) (i := 1) (v := w) rfl
    refine (Det.ite_zero (t := .call d (.get (.var 1) (.nat 1))) dt dv).post fun c hc =>
      ⟨?_, hww, hp⟩
    have : (Val.nat j).wt ≤ j + 2 := wt_nat_le j
    have : (Val.nat j).wt < w.wt := wt_le_wt_list (by simp)
    unfold cpLoopC
    nlinarith
  · -- The move continues from `st'`.
    have hwst' := hwt m' st' Ss' f hst'
    set w := Val.list [.nat 2, st'] with hw
    have dh := Det.get' (Det.var' (P := Pg) (env := [st, w]) (i := 1) (v := w) rfl) (Det.nat 0)
      (v := .nat 2) rfl
    have dt := Det.arith' (op := .eq) dh (Det.nat 2) (z := 1) (by
      simp [GI.Machine.BinOp.eval])
    have ds := Det.get' (Det.var' (P := Pg) (env := [st, w]) (i := 1) (v := w) rfl) (Det.nat 1)
      (v := st') rfl
    refine EvalAll.ite dt (fun _ _ h => ⟨_, h.1⟩) fun x cc hx => ?_
    obtain ⟨hx, hcc⟩ := hx
    cases hx
    simp only [one_ne_zero, if_false]
    refine EvalAll.call_funAll ds fun v ca h => ?_
    obtain ⟨hv, hca⟩ := h
    rw [hv]
    refine (ihm m' hm' _ Ss' f hst').mono fun out cr ⟨hcr, hwo, hp⟩ =>
      ⟨?_, hwo, stepPostC_mono_set' hsub hp⟩
    have : (Val.nat 2).wt ≤ 4 := wt_nat_le 2
    have : st'.wt < w.wt := wt_le_wt_list (by simp)
    have hw2 : w.wt ≤ 2 * ((Val.nat 2).wt + st'.wt) + 6 := wt_list2_le _ _
    have : (m' + 1) * cpLoopC Bm Bw ≤ m * cpLoopC Bm Bw := Nat.mul_le_mul_right _ (by omega)
    have e : (m + 1) * cpLoopC Bm Bw = m * cpLoopC Bm Bw + cpLoopC Bm Bw := by ring
    unfold cpLoopC at *
    omega
where
  /-- `stepPostC_mono_set`, restated here to keep this file free of the certificate phase. -/
  stepPostC_mono_set' {μ : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ} {β : Type}
    {Out : β → Val → Prop} {Rep : Val → Set (Script β) → ℕ → Prop}
    {Ss Ss' : Set (Script β)} (hS : Ss ⊆ Ss') {f : ℕ} {w : Val}
    (h : Iface.StepPostC μ Out Rep Ss f w) : Iface.StepPostC μ Out Rep Ss' f w := by
    rcases h with ⟨a, out, hw, ho, hm⟩ | ⟨hf, m, Ω', C', T, k', e', c', arg, kst, Ks, hc', hm, hw,
      hcan, hg, hlt, hKs, hKS, hrep⟩
    · exact Or.inl ⟨a, out, hw, ho, hS hm⟩
    · exact Or.inr ⟨hf, m, Ω', C', T, k', e', c', arg, kst, Ks, hc', hm, hw, hcan, hg, hlt, hKs,
        fun k hk => hS (hKS k hk), hrep⟩

end GI.Impl
