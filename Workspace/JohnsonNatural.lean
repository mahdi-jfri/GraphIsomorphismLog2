import Workspace.JohnsonOrbits
import Workspace.JohnsonEntropy

namespace GI.Johnson

/-- Exactly the natural symmetric-group induction hypothesis used in A.7.
The small degrees are handled separately by the proved small-degree theorem. -/
def NaturalActionBound (cutoff : ℕ) (C B : ℝ) (m : ℕ) : Prop :=
  ∀ (r : ℕ), 3 ≤ r → r ≤ m → ∀ a : Fin r,
    (sigma cutoff a (⊤ : Subgroup (Equiv.Perm (Fin r))) : ℝ) ≤ C * Real.log (r : ℝ) - B

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
/-- The stated natural-action hypothesis supplies the fresh budget on every
actual subgroup orbit, using the proved faithful-orbit and relabel invariances. -/
theorem natural_bound_on_orbit {cutoff : ℕ} {C B : ℝ} (hcutoff : 5 ≤ cutoff)
    (natural : NaturalActionBound cutoff C B (Fintype.card α))
    (H : Subgroup (Equiv.Perm α)) (a : α) (hsize : 3 ≤ (orbitFinset H a).card) :
    (sigma cutoff a H : ℝ) ≤ C * Real.log ((orbitFinset H a).card : ℝ) - B := by
  classical
  let r := (orbitFinset H a).card
  let e : ActiveOrbit H a ≃ Fin r := Fintype.equivFinOfCardEq (orbitFinset_card H a).symm
  have hs := sigma_relabel cutoff e (faithfulOrbitImage H a) (activeOrbitBase H a)
  rw [← sigma_faithfulOrbit cutoff H a] at hs
  have hm := sigma_subgroup_mono hcutoff (e (activeOrbitBase H a))
    (show (faithfulOrbitImage H a).map (relabelPerm e).toMonoidHom ≤ ⊤ from le_top)
  rw [← hs] at hm
  have hmReal : (sigma cutoff a H : ℝ) ≤
      (sigma cutoff (e (activeOrbitBase H a)) (⊤ : Subgroup (Equiv.Perm (Fin r))) : ℝ) := by
    exact_mod_cast hm
  exact hmReal.trans (natural r hsize (orbitFinset H a).card_le_univ _)

omit [DecidableEq α] in
theorem orbitFinset_top (a : α) : orbitFinset (⊤ : Subgroup (Equiv.Perm α)) a = Finset.univ := by
  classical
  apply Finset.eq_univ_iff_forall.mpr
  intro b
  exact mem_orbitFinset.mpr ⟨⟨Equiv.swap a b, Subgroup.mem_top _⟩, Equiv.swap_apply_left a b⟩

end GI.Johnson
