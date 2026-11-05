module

public import Workspace.Impl.Cases

@[expose] public section

/-!
# The threshold step of `Continue`

Algorithm 5: "if `|Ω| ≤ N^γ` then return `Solve(Ω, G, x, y)`". The step function calls the
function of `Solve` on its own input value: a canonical value of the state is a state value, so
it is a valid input of `Solve`. The result is the answer of `Run.threshold`.

The call `Solve` on the same state is smaller in the termination measure, because `|dom| ≤ N^γ`
is less than `N` (the phase size is above `N₀ ≥ 1`, and `γ < 1`).

Cost: reading the input (`wt v + 1`), the call, and returning its answer (`wt u + 1`). The
setup of the `Solve` child is its excess `K₀ (wt v + 1)^d₀ ≤ K₀ (stateW + 1)^d₀`, which is its
`charge` in `childCost`. So the step needs `W ≥ stateW + ansW + 2` at threshold nodes.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val)
open scoped Pointwise

/-- The body of the threshold step: call `Solve` on the input. -/
def thresholdBody (F : Funs) : Expr := .call F.solve (.var 0)

namespace Iface

variable (I : Iface) (Pg : Program) (F : Funs)

/-- The work bound that the threshold step needs at its nodes. -/
def ThresholdW : Prop :=
  ∀ nd : Node P₀, nd.run.kind = .threshold →
    ((stateW (Nat.card nd.Ω) nd.S + ansW (Nat.card nd.Ω) + 2 : ℕ) : ℝ) ≤ I.W nd

/-- A `Continue` call at or below the threshold is larger in the measure than `Solve` on the
same state. -/
theorem mlt_threshold {Ω C : Type} {S : State Ω C} (hg : Good P₀ .cont S)
    (hs : (S.size : ℝ) ≤ (S.N : ℝ) ^ P₀.γ) : MLt (measure P₀ .solve S) (measure P₀ .cont S) := by
  obtain ⟨hN, -, -⟩ := hg
  have hN2 : 2 ≤ S.N := by have := P₀_terminating.N₀_pos; omega
  have hlt := size_lt_of_rpow hN2 P₀_terminating.γ_lt hs
  rw [mlt_iff]
  left
  exact hlt

/-- **The threshold step meets its specification.** -/
theorem thresholdSpec {f : ℕ} (hf : Pg.funs[f]? = some (thresholdBody F)) (hW : I.ThresholdW) :
    I.ThresholdSpec Pg F f := by
  intro Ω C S k e c hc v hv hg hP ih
  have hv' : Canon e c v S := hv
  have hcall := ih .solve S trivial (mlt_threshold hg hP) k e c hc v hv'.stateVal
  refine FunAll.intro hf (EvalAll.call_funAll (Det.var' (P := Pg) (env := [v]) (i := 0) rfl)
    fun v' ca h => ?_)
  obtain ⟨hvv, hca⟩ := h
  rw [hvv]
  refine hcall.mono fun u cs ⟨A, L, r, hL, hA, hcs⟩ => ?_
  have hL' : L = none := hL
  subst hL'
  refine ⟨A, none, Run.threshold hP r, rfl, by simp [Run.kind], hA, ?_⟩
  have hk := card_eq e
  have hwv := hv'.wt_le
  have hu := hA.wt_le
  have hWn := hW (Run.threshold hP r).node rfl
  simp only [Run.node] at hWn
  rw [hk] at hWn
  have hown : ((stateW k S + ansW k + 2 : ℕ) : ℝ) ≤ I.own .cont (Run.threshold hP r) v := by
    simp only [own, reduceCtorEq, if_false]
    exact hWn.trans (le_max_right _ _)
  have hch : I.childCost (Run.threshold hP r) =
      r.total I.work + (I.K₀ : ℝ) * ((stateW k S : ℝ) + 1) ^ I.d₀ := by
    simp only [childCost, Run.children, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, charge, if_true, hk]
  rw [hch]
  simp only [excess, if_true] at hcs
  have hpow : ((v.wt : ℝ) + 1) ^ I.d₀ ≤ ((stateW k S : ℝ) + 1) ^ I.d₀ := by
    have : (v.wt : ℝ) ≤ stateW k S := by exact_mod_cast hwv
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have hK : (0 : ℝ) ≤ I.K₀ := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left hpow hK
  have hrest : ((ca + cs + u.wt + 1 : ℕ) : ℝ) ≤ ((stateW k S + ansW k + 2 : ℕ) : ℝ) + cs := by
    have h1 : ca + u.wt + 1 ≤ stateW k S + ansW k + 2 := by omega
    have h2 : ((ca + u.wt + 1 : ℕ) : ℝ) ≤ ((stateW k S + ansW k + 2 : ℕ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h2 ⊢
    linarith
  linarith

end Iface

end GI.Impl
