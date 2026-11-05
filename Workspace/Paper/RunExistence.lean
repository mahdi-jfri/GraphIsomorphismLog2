module

public import Workspace.Algorithm.Existence
public import Workspace.Paper.Algorithm

@[expose] public section

/-!
# Every state has a run of the recursion

Lemma 6.1 (`GI.Paper.lem_main_correctness`) is about the runs of `GI.Algorithm.Run`. This
file states that runs exist: given the subroutine data of Algorithms 4 and 5
(`GI.Algorithm.Supply`), the parameter inequalities of Section 6
(`GI.Algorithm.Params.Terminating`), Maróti's theorem (`GI.Cited.MarotiPrimitive`, which makes
the dispatcher's cases exhaustive) and `a ≥ 128` (the enumeration exponent, Section A.5), `Solve` has a run on every state of a finite
position set. The termination argument is in `Workspace/Algorithm/Existence.lean`.
-/

namespace GI.Paper

open GI.Algorithm

/-- **The recursion terminates on every input.** Given the subroutine data and the
parameter inequalities, `Solve` has a run on every state `S` of a finite position set,
and by Lemma 6.1 every such run returns the full transporter
`{g ∈ G : y(g v) = x(v) for all v ∈ dom}`. -/
theorem run_exists {P : Params} (hP : P.Terminating) (hM : GI.Cited.MarotiPrimitive)
    (ha : 128 ≤ P.a) (Su : Supply P) {Ω C : Type} [Finite Ω]
    (S : State Ω C) :
    Nonempty (Run P .solve S none S.answer) ∧
      ∀ {A : Set (Equiv.Perm Ω)}, Run P .solve S none A →
        A = {g | g ∈ S.G ∧ ∀ v ∈ S.dom, S.y (g v) = S.x v} :=
  ⟨exists_run_solve hP hM ha Su S, fun r => lem_main_correctness_all r⟩

end GI.Paper
