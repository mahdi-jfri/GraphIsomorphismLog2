import Workspace.Algorithm.PhaseTree
import Workspace.Paper.RunningTime

/-!
# Lemma 7.1 for the runs of the recursion

`GI.Paper.lem_main_phase_bound` is proved for an abstract phase tree. Here it is applied
to the phase tree of the runs of `GI.Algorithm.Run` (`GI.Algorithm.phaseTree`), whose
hypotheses are proved in `Workspace/Algorithm/PhaseTree.lean` except the two cost
fields, which stay hypotheses until stage 2 defines the cost of a run.
-/

namespace GI.Paper

open GI.Algorithm

variable {P : Params}

/-- **Lemma 7.1 for the runs of the recursion** (`lem:main-phase-bound`). Fix the
constants of Section 7.5 (`cc`), compatible with the parameters of the run, and a phase
size `N` above the base size. Suppose the cost of the vertices of the phase tree obeys
the two cost hypotheses of Lemma 7.1 ("An ordinary threshold leaf has cost at most
`K_N`" and the node toll; stage 2). Then the inherited recursion of the phase
terminates, and a `Continue` run that starts a phase (counter `h = 2`, as set by
`Solve`) costs at most `K_N W(S)`, where `W` is the weighted majorant of eq.
`main-weight` at the resources of its state. -/
theorem lem_main_phase_bound_run {cc : ChargingConstants} (hc : Compat P cc) (cT : ℝ)
    (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n) {N : ℕ} (hN6 : 6 ≤ (N : ℝ) ^ cc.γ)
    (hN2 : 2 ≤ (N : ℝ) ^ (cc.γ * cc.D - cc.a)) (cost : PNode P → ℝ)
    (leaf_cost : ∀ v, (phaseTree P N cost).kind v = .leaf →
      cost v ≤ phaseToll cT cc.γ F N)
    (toll : ∀ v, (phaseTree P N cost).kind v ≠ .leaf →
      cost v ≤ (N : ℝ) ^ cc.a * phaseToll cT cc.γ F N +
        (((phaseTree P N cost).kind v).children.map cost).sum) :
    WellFounded (fun u v => u ∈ ((phaseTree P N cost).kind v).children) ∧
    ∀ {Ω C : Type} [Finite Ω] {S : State Ω C} {A : Set (Equiv.Perm Ω)}
      (r : Run P .cont S none A), S.N = N → S.h = 2 →
      cost (Leaf.ofRun r).toP ≤ phaseToll cT cc.γ F N * (S.res P.κ).W cc.A cc.B cc.D := by
  have hT := phaseTree_hyp hc hN6 _ leaf_cost toll
  obtain ⟨hwf, hbound⟩ := lem_main_phase_bound cc (phaseTree P N cost) N cT F hF hN6 hN2 hT
  refine ⟨hwf, fun {Ω C} _ {S A} r hSN hh => ?_⟩
  have hinv : (Leaf.ofRun r).toP.Inv N :=
    { fin := ‹_›
      N_eq := hSN
      mode := by simp [Leaf.toP, Leaf.ofRun]
      virt := fun a h => by simp [Leaf.toP, Leaf.ofRun] at h
      orbit_h := fun _ _ => hh }
  have := hbound (Leaf.ofRun r).toP
  rwa [phaseTree_state_of hinv] at this

end GI.Paper
