import Workspace.Impl.AggBodyRun

/-!
# The continuations of a round are allowed calls

`LiftAndContinue` calls `Continue` on the child `lcChild S E₀ τ sel ⌊βq⌋` of each overcoset
`(σ, E₀)` that the item phase returns. The program may make this call only if the induction
hypothesis covers it: the child must be `Good` for `Continue` and below the round in the
measure. This is the argument of `exists_run_aux` (case `aggregate`) in
`Workspace/Algorithm/Existence.lean`, for one overcoset of the round's exact result:

* the group `π⁻¹(E₀)` has the cap `⌊βq⌋` on the selected interval (`child_hierInv`), so the
  child keeps the invariant `HierInv`;
* the child has the same domain, `N`, `ρ`, floor mode and `h`, a smaller or equal `σ`, and a
  smaller sum of interval bounds (`capUpdate`, `capSum_lt`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm
open scoped Pointwise

variable {Ω C : Type}

/-- **A continuation of the round may be made**: for an overcoset of the round's exact result,
the child of `LiftAndContinue` is `Good` for `Continue` and below the round in the measure. -/
theorem as_child_good_mlt [Finite Ω] {S : State Ω C} (hgood : Good P₀ .giant S)
    (L : SuppliedLabels S) (hq₀ : P₀.q₀ ≤ L.q) (Ag : Aggregation P₀ S L.toGiantLabels)
    (hsel : Ag.sel.val = L.sel.val) (o : LcOver L.q)
    (ho : abOv L.toGiantLabels o ∈ Ag.script.evalExact.overs) (τ : Perm Ω) :
    Good P₀ .cont (lcChild S o.2.1 τ L.sel (abCap L.toGiantLabels)) ∧
      MLt (measure P₀ .cont (lcChild S o.2.1 τ L.sel (abCap L.toGiantLabels)))
        (measure P₀ .giant S) := by
  obtain ⟨hN, hsN, htr, hth, hhi, -⟩ := hgood
  have hP := P₀_terminating
  have hκ := hP.κ_five
  have htr1 := trInd_of S htr
  set child := lcChild S o.2.1 τ L.sel (abCap L.toGiantLabels) with hchild
  have hhier : child.hier = Ag.newHier (abOv L.toGiantLabels o) := by
    rw [hchild, lcChild_hier, ← hsel]
    exact lcHier_eq_newHier S Ag _
  have hinv : child.HierInv := by
    show HierInv child.G child.dom child.hier
    rw [hhier]
    exact Ag.child_hierInv hsel hhi ho
  refine ⟨⟨hN, hsN, hinv⟩, ?_⟩
  have hcu := Ag.capUpdate (abOv L.toGiantLabels o) ho
  have hσ : child.sigma P₀.κ ≤ S.sigma P₀.κ :=
    State.sigma_le_of hκ (L.toGiantLabels.lift_le o.2.1) le_rfl
  have hρ : rhoNat child.hier = rhoNat S.hier := by
    rw [hhier]
    have h1 : (rhoNat (Ag.newHier (abOv L.toGiantLabels o)) : ℝ) = rhoNat S.hier := by
      rw [rhoNat_cast, rhoNat_cast]; exact hcu.rho_eq
    exact_mod_cast h1
  have hc := hcu.capSum_lt hP.β_lt (Nat.lt_of_lt_of_le hP.q₀_pos hq₀)
  have htrj := trInd_le child
  rw [mlt_iff]
  simp only [Algorithm.measure, major, solveInd, stageInd, true_and, lt_self_iff_false, false_or]
  have h1 : child.size = S.size := rfl
  have hk := lc_keep S L.con o.2.1 L.sel (abCap L.toGiantLabels)
  have hfl : child.floor = S.floor := State.restrict_floor_of _ _ _ _ _ _ hk
  have h3 : flInd child = flInd S := by simp only [flInd, hfl]
  have h4 : child.h = S.h := State.restrict_h_of _ _ _ _ _ _ hk
  have h5 : capSum child.hier = capSum (Ag.newHier (abOv L.toGiantLabels o)) := by rw [hhier]
  have hNc : child.N = S.N := rfl
  omega

end GI.Impl
