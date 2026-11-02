import Workspace.CertificateTermination

/-!
# Lockstep: a marked-window transporter conjugates the two endpoint procedures

Paper, Appendix A, `sec:certificates`, "Ordered comparisons and equivariance":

"Every representative conjugates `A_i` to the other endpoint group ...
Therefore it maps affected sets, the extra orbit union, and stopping tests to the
corresponding objects at the other endpoint."

"An empty partial comparison cannot revive at the final windows. Any map
satisfying (comparison) maps the initial empty windows to one another.
Inductively it conjugates the endpoint groups, hence maps the next window; its
agreement on the final marked strings restricts to agreement there. It must
belong to every earlier comparison coset."

This file proves these claims for two generic test data `(P, phi)` and
`(P', phi')` that `g` carries to each other (`Compat`).
-/

namespace GI.Endpoint

open Equiv Equiv.Perm

variable {V C Q Q' : Type*} [Group Q] [Group Q'] [DecidableEq V] [Fintype V]
  {P P' : Subgroup (Perm V)} {phi : P →* Q} {phi' : P' →* Q'} {g : Perm V} {θ : Q ≃* Q'}

/-- **Lockstep.** If `g` carries the test data and agrees with the two strings on
the window `W_t`, then for every `j ≤ t` it conjugates `A_j` to `A'_j` and maps
`W_j` to `W'_j`. -/
theorem stage_cmap (hc : Compat phi phi' g θ) {x y : V → C} {t : ℕ}
    (hxy : ∀ v ∈ win phi x t, y (g v) = x v) :
    ∀ j ≤ t, grp phi' y j = cmap g (grp phi x j) ∧ win phi' y j = wmap g (win phi x j) := by
  intro j
  induction j with
  | zero =>
    intro _
    exact ⟨hc.cmap_P.symm, by simp [win_zero]⟩
  | succ j ih =>
    intro hj
    obtain ⟨hA, hW⟩ := ih (by omega)
    have hinc : inc phi' y j = wmap g (inc phi x j) := by
      simp only [inc]
      rw [hA, hW, hc.increment_cmap]
    have htr : Transports (mask x (inc phi x j)) (mask y (wmap g (inc phi x j))) g := by
      rw [transports_mask_iff]
      exact ⟨fun v => apply_mem_wmap, fun v hv => hxy v (inc_subset_win phi x (by omega) hv)⟩
    refine ⟨?_, ?_⟩
    · rw [grp_succ, grp_succ, hinc, hA, automorphisms_cmap htr]
    · rw [win_succ, win_succ, hinc, hW]
      exact (Finset.map_union _ _).symm

/-- A transporter of the final marked strings at stage `t` belongs to every
earlier lockstep comparison coset: it transports the marked strings at every
stage `j ≤ t`, and the two procedures run in lockstep up to `t`. -/
theorem lockstep_of_transports (hc : Compat phi phi' g θ) {x y : V → C} {t : ℕ}
    (hg : Transports (mask x (win phi x t)) (mask y (win phi' y t)) g) :
    ∀ j ≤ t, grp phi' y j = cmap g (grp phi x j) ∧ win phi' y j = wmap g (win phi x j) ∧
      Transports (mask x (win phi x j)) (mask y (win phi' y j)) g := by
  have hxy : ∀ v ∈ win phi x t, y (g v) = x v := ((transports_mask_iff _ _ _ _ _).1 hg).2
  intro j hj
  obtain ⟨hA, hW⟩ := stage_cmap hc hxy j hj
  refine ⟨hA, hW, ?_⟩
  rw [transports_mask_iff, hW]
  exact ⟨fun v => apply_mem_wmap, fun v hv => hxy v (win_mono phi x hj hv)⟩

/-- Under lockstep the stopping tests agree. -/
theorem stopped_iff_of_lockstep (hc : Compat phi phi' g θ) {x y : V → C} {j : ℕ}
    (hA : grp phi' y j = cmap g (grp phi x j)) (hW : win phi' y j = wmap g (win phi x j)) :
    Stopped phi' (grp phi' y j) (win phi' y j) ↔ Stopped phi (grp phi x j) (win phi x j) := by
  rw [hA, hW, hc.stopped_iff]

/-- Under lockstep the full tests agree. -/
theorem full_iff_of_lockstep (hc : Compat phi phi' g θ) {x y : V → C} {j : ℕ}
    (hA : grp phi' y j = cmap g (grp phi x j)) :
    Full phi' (grp phi' y j) ↔ Full phi (grp phi x j) := by
  rw [hA, hc.full_iff]

/-- **Parent isomorphisms.** If `g` carries the test data and transports `x` to `y`
on all of `Ω`, the two procedures correspond at every stage. -/
theorem stage_cmap_of_transports (hc : Compat phi phi' g θ) {x y : V → C}
    (hg : Transports x y g) (t : ℕ) :
    grp phi' y t = cmap g (grp phi x t) ∧ win phi' y t = wmap g (win phi x t) :=
  stage_cmap (t := t) hc (fun v _ => hg v) t le_rfl

end GI.Endpoint
