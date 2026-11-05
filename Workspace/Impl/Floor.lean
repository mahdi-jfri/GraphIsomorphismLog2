module

public import Workspace.Impl.Cases
public import Workspace.Lang.Lib.Tabulate

@[expose] public section

/-!
# The floor reset of `Continue`

Algorithm 5: "if the active column floor has been entered then clear the row record and floor
mode; set `h ← 2`", and continue with the general dispatcher on the same core. In the recursion
this is `Run.floorReset`: one `Continue` child on `S.floorCleared`, the state with the same core,
hierarchy and phase size, no row record, floor mode off and `h = 2`.

The step function rewrites three entries of its input value (the row record becomes `[]`, the
floor flag `0`, the counter `2`) and calls `Continue` on the result. A canonical value of `S`
becomes a canonical value of `S.floorCleared`, since the other entries are unchanged.

The child is smaller in the termination measure: the entry `3 [floor] + h` drops from at least
`3` to `2`, and the entries before it are equal.

Cost: reading the ten entries and building the new list (at most `50 wt v + 600`), the call,
and returning its answer (`wt u + 1`). So the step needs `W ≥ 50 stateW + ansW + 700` at
floor-reset nodes (`Iface.FloorW`), a polynomial in `k ≤ N` and the numbers of the state.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val)
open scoped Pointwise

/-- The new state value of the floor reset: entries `6, 7, 8` of the input become `[]`, `0`,
`2`. -/
def floorArg : Expr :=
  Expr.mkList [arg 0, arg 1, arg 2, arg 3, arg 4, arg 5, .nil, .nat 0, .nat 2, arg 9]

/-- The body of the floor reset: call `Continue` on the cleared state. -/
def floorBody (F : Funs) : Expr := .call F.cont floorArg

/-- The cleared state value. -/
def floorVal (k : ℕ) (gv dv xv yv hv : Val) (N : ℕ) : Val :=
  .list [.nat k, gv, dv, xv, yv, hv, .list [], boolVal false, .nat 2, .nat N]

theorem floorArg_det {P : Program} {k N : ℕ} {gv dv xv yv hv rv fv hh : Val} :
    Det P [.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]] floorArg
      (floorVal k gv dv xv yv hv N)
      (50 * (Val.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]).wt + 600) := by
  have h2 := sum_wt_lt_wt_list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]
  have hw' : (floorVal k gv dv xv yv hv N).wt ≤
      2 * (Val.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]).wt + 34 := by
    have h1 := wt_list_le [.nat k, gv, dv, xv, yv, hv, .list [], boolVal false, .nat 2, .nat N]
    have e1 : (Val.list []).wt = 4 := by simp
    have e2 : (boolVal false).wt = 2 := by simp [wt_nat, GI.Machine.len_zero]
    have e3 : (Val.nat 2).wt ≤ 4 := wt_nat_le 2
    simp only [floorVal, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_cons, List.length_nil] at h1 h2 ⊢
    omega
  generalize hW : (Val.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]).wt = W at hw' ⊢
  have ha : ∀ j (hj : j < 10), Det P [.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]]
      (arg j) [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N][j] (W + W + 20) := fun j hj =>
    (Det.arg (P := P) (rest := []) (j := j) (by simp; omega)).mono (by omega)
  have hps := Det.mkList (P := P) (env := [.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]])
    (c := 2 * W + 20)
    [(arg 0, .nat k), (arg 1, gv), (arg 2, dv), (arg 3, xv), (arg 4, yv), (arg 5, hv),
      (.nil, .list []), (.nat 0, .nat 0), (.nat 2, .nat 2), (arg 9, .nat N)] (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (ha 0 (by omega)).mono (by omega)
      · exact (ha 1 (by omega)).mono (by omega)
      · exact (ha 2 (by omega)).mono (by omega)
      · exact (ha 3 (by omega)).mono (by omega)
      · exact (ha 4 (by omega)).mono (by omega)
      · exact (ha 5 (by omega)).mono (by omega)
      · exact Det.nil.mono (by omega)
      · exact (Det.nat 0).mono (by omega)
      · exact (Det.nat 2).mono (by omega)
      · exact (ha 9 (by omega)).mono (by omega))
  simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil] at hps
  refine hps.mono ?_
  have : (Val.list [.nat k, gv, dv, xv, yv, hv, .list [], .nat 0, .nat 2, .nat N]).wt ≤
      2 * W + 34 := hw'
  omega

namespace Iface

variable (I : Iface) (Pg : Program) (F : Funs)

/-- The work bound that the floor reset needs at its nodes. -/
def FloorW : Prop :=
  ∀ nd : Node P₀, nd.run.kind = .floorReset →
    ((50 * stateW (Nat.card nd.Ω) nd.S + ansW (Nat.card nd.Ω) + 700 : ℕ) : ℝ) ≤ I.W nd

/-- A `Continue` call at a column floor is larger in the measure than `Continue` on the cleared
state. -/
theorem mlt_floor {Ω C : Type} {S : State Ω C} (hfl : S.FloorEntered) :
    MLt (measure P₀ .cont S.floorCleared) (measure P₀ .cont S) := by
  have hfl1 : flInd S = 1 := by simp [flInd, hfl.1]
  have hfl0 : flInd S.floorCleared = 0 := by simp [flInd, State.floorCleared]
  have h1 : S.floorCleared.N = S.N := rfl
  have h2 : S.floorCleared.size = S.size := rfl
  have h3 : S.floorCleared.sigma P₀.κ = S.sigma P₀.κ := rfl
  have h4 : rhoNat S.floorCleared.hier = rhoNat S.hier := rfl
  have h5 : S.floorCleared.h = 2 := rfl
  have h6 : trInd S.floorCleared = trInd S := rfl
  rw [mlt_iff]
  simp only [GI.Algorithm.measure, major, solveInd, stageInd, true_and, lt_self_iff_false, false_or]
  omega

/-- A canonical value of `S` with three entries rewritten is a canonical value of the cleared
state. -/
theorem canon_floorCleared {Ω C : Type} {k : ℕ} {e : Ω ≃ Fin k} {c : C → ℕ} {v : Val}
    {S : State Ω C} (hv : Canon e c v S) :
    ∃ gv dv xv yv hv rv, v = .list [.nat k, gv, dv, xv, yv, hv, rv, boolVal S.floor, .nat S.h,
      .nat S.N] ∧ Canon e c (floorVal k gv dv xv yv hv S.N) S.floorCleared := by
  obtain ⟨gv, dv, xv, yv, hv', rv, hg, hd, hx, hy, hh, hr, rfl⟩ := hv.val
  refine ⟨gv, dv, xv, yv, hv', rv, rfl, ⟨⟨gv, dv, xv, yv, hv', .list [], hg, hd, hx, hy, hh,
    rfl, rfl⟩, hv.colors, hv.fits, hv.small.reset rfl rfl rfl⟩⟩

/-- **The floor reset meets its specification.** -/
theorem floorSpec {f : ℕ} (hf : Pg.funs[f]? = some (floorBody F)) (hW : I.FloorW) :
    I.FloorSpec Pg F f := by
  intro Ω C S k e c hc v hv hg hP ih
  have hv' : Canon e c v S := hv
  obtain ⟨hs, htr, hfl⟩ := hP
  obtain ⟨gv, dv, xv, yv, hv0, rv, hvv, hcan⟩ := canon_floorCleared hv'
  have hg' : Good P₀ .cont S.floorCleared := hg
  have hcall := ih .cont S.floorCleared hg' (mlt_floor hfl) k e c hc _ hcan
  have hwv := hv'.wt_le
  have hwv' := hwv
  rw [hvv] at hwv'
  refine FunAll.intro hf (EvalAll.call_funAll (hvv ▸ floorArg_det) fun v' ca h => ?_)
  obtain ⟨hvv', hca⟩ := h
  rw [hvv']
  refine hcall.mono fun u cs ⟨A, L, r, hL, hA, hcs⟩ => ?_
  have hL' : L = none := hL
  subst hL'
  refine ⟨A, none, Run.floorReset (S' := S.floorCleared) hs htr hfl ⟨rfl, rfl, rfl, rfl⟩ rfl rfl
    rfl rfl rfl r, rfl, by simp [Run.kind], hA, ?_⟩
  have hk := card_eq e
  have hu := hA.wt_le
  have hWn := hW (Run.floorReset (S' := S.floorCleared) hs htr hfl ⟨rfl, rfl, rfl, rfl⟩ rfl rfl
    rfl rfl rfl r).node rfl
  simp only [Run.node] at hWn
  rw [hk] at hWn
  have hown : ((50 * stateW k S + ansW k + 700 : ℕ) : ℝ) ≤
      I.own .cont (Run.floorReset (S' := S.floorCleared) hs htr hfl ⟨rfl, rfl, rfl, rfl⟩ rfl rfl
        rfl rfl rfl r) v := by
    simp only [own, reduceCtorEq, if_false]
    exact hWn.trans (le_max_right _ _)
  have hch : I.childCost (Run.floorReset (S' := S.floorCleared) hs htr hfl ⟨rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl r) = r.total I.work := by
    simp only [childCost, Run.children, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, charge, reduceCtorEq, if_false]
  rw [hch]
  simp only [excess, reduceCtorEq, if_false, add_zero] at hcs
  have hrest : ((ca + cs + u.wt + 1 : ℕ) : ℝ) ≤ ((50 * stateW k S + ansW k + 700 : ℕ) : ℝ) + cs := by
    have h1 : ca + u.wt + 1 ≤ 50 * stateW k S + ansW k + 700 := by omega
    have h2 : ((ca + u.wt + 1 : ℕ) : ℝ) ≤ ((50 * stateW k S + ansW k + 700 : ℕ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h2 ⊢
    linarith
  linarith

end Iface

end GI.Impl
