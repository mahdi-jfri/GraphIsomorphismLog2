import Workspace.Assembly.Build
import Workspace.Assembly.Convert
import Workspace.Assembly.Final

/-!
# The wrapper of Algorithm 1 (obligation (b))

`wrapperFuns b fs` is a block of 55 functions at base `b`:

* `b`: the body `mainBody (b + 1) fs (b + 35)` of the main function;
* `b + 1, …, b + 34`: the builder `buildFuns (b + 1)` (`Workspace/Assembly/Build.lean`);
* `b + 35, …, b + 54`: the converter `convFuns (b + 35)` (`Workspace/Assembly/Convert.lean`).

Any program that holds this block meets obligation (b) for every index `fs` of the solver
(`graphWrapper_of_hasAt`). So the final theorem needs only obligations (a) and (c)
(`final_of_solve`).
-/

namespace GI.Assembly

open GI.Algorithm GI.Lang GI.Paper

/-- **The wrapper**: the main body, the builder and the converter, at base `b`. -/
def wrapperFuns (b fs : ℕ) : List Expr :=
  [mainBody (b + 1) fs (b + 35)] ++ buildFuns (b + 1) ++ convFuns (b + 35)

theorem length_wrapperFuns (b fs : ℕ) : (wrapperFuns b fs).length = 55 := by
  simp only [wrapperFuns, List.length_append, length_buildFuns, length_convFuns,
    List.length_singleton]

/-- **Obligation (b)** holds for every program that holds the wrapper at `b`. -/
theorem graphWrapper_of_hasAt {P : Program} {b fs : ℕ} (h : P.HasAt b (wrapperFuns b fs)) :
    GraphWrapper P b fs := by
  simp only [wrapperFuns] at h
  have hm := h.left.left.single
  have hb := h.left.right
  have hc := h.right
  simp only [List.length_singleton, List.length_append, length_buildFuns] at hb hc
  rw [show b + (1 + 34) = b + 35 by omega] at hc
  exact ⟨b + 1, b + 35, hm, buildSpec_of_hasAt hb, convertSpec_of_hasAt hc⟩

/-- **The final theorem from the solver.** If a program holds the wrapper at `b`, and its
function `fs` implements `solve` with a work function `w` that meets the work bounds, then
graph isomorphism is in quasipolynomial time. -/
theorem final_of_solve {Pg : Program} {b fs : ℕ} {w : Node P₀ → ℝ}
    (h : Pg.HasAt b (wrapperFuns b fs)) (ha : Implements .solve Pg fs w) (hc : WorkBound w) :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime :=
  final_of_axioms ha (graphWrapper_of_hasAt h) hc

end GI.Assembly
