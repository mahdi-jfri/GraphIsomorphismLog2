module

public import Workspace.Algorithm.DomainRestriction
public import Workspace.Paper.LocalCertificates

@[expose] public section

/-!
# The local-test calls are charged calls (Lemma 4.1 on the domain of a state)

Lemma 4.1 (`GI.Paper.lem_main_local_test`) is stated for a group `G` transitive on a whole
finite type. A state has a domain inside `Ω`. We apply the lemma to the faithful image
`G|_dom` of a transitive state on its domain (`Workspace/Algorithm/DomainRestriction.lean`),
with a supplied alternating label map `π : G|_dom → Alt(Γ)` and a test set `T` of
`|T| = κ` labels.

The calls of the local test are `Continue` calls under the kernel group `N_t` of a stage on
the increment window `V_t` (Algorithm 2, `CheckNewWindow`). In `Ω` such a call runs under
the lift of `N_t` (the elements of `G` whose restriction lies in `N_t`) on part of the lifted
window. Clause 2 of Lemma 4.1 gives the two call types `(s, σ) ↦ (s/κ, σ)` and
`(s, σ) ↦ (s, σ - κ)`. With `θ κ ≥ 1` both are of the types of `ChargedCall`.

The certificate colors `x` are any coloring of the domain. The label map is supplied on the
faithful image: if the state's own label map `S.G → Alt(Γ)` does not factor through the
restriction to the domain, this lemma does not apply to it.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.Endpoint GI.LocalGroups

variable {P : Params} {Ω C C' C₀ Γ : Type} [Fintype Γ] [DecidableEq Γ]

/-- **The local-test calls are charged calls** (Lemma 4.1, clause 2, applied to the
faithful image of a transitive state on its domain). Let `π : G|_dom → Alt(Γ)` be a label
map, `T` a test set with `|T| = κ ≥ 5`, `x` a coloring of the domain, and `t` a stage of
the endpoint procedure. An inherited call `T'` with the parent's phase and hierarchy, under
the lift of the stage kernel `N_t`, on part of the lifted increment `V_t`, is a charged
call, provided `θ κ ≥ 1` (so that `s/κ ≤ θ s`). -/
theorem ChargedCall.of_local_test [Finite Ω] [DecidableEq Ω] {S : State Ω C} [Fintype S.dom]
    (htr : S.Transitive)
    (π : S.domGroup →* alternatingGroup Γ) (x : S.dom → C₀) (T : Finset Γ) (hk5 : 5 ≤ T.card)
    (hκ : P.κ = T.card) (hθ : 1 ≤ P.θ * T.card) (t : ℕ) {T' : State Ω C'}
    (hN : T'.N = S.N) (hhier : T'.hier = S.hier)
    (hG : T'.G = S.liftGroup (kernelIn (phiT S.domGroup π T) (grp (phiT S.domGroup π T) x t)))
    (hdom : T'.dom ⊆ Subtype.val '' (inc (phiT S.domGroup π T) x t : Set S.dom)) :
    ChargedCall P S T' := by
  haveI := State.domGroup_pretransitive htr
  set Nt := kernelIn (phiT S.domGroup π T) (grp (phiT S.domGroup π T) x t) with hNt_def
  have hNt : Nt ≤ S.domGroup :=
    inf_le_left.trans ((grp_le _ x t).trans Pgrp_le)
  refine ⟨hN, hG ▸ State.liftGroup_le _, fun v hv => ?_, hhier, fun v hv => ?_⟩
  · obtain ⟨w, -, rfl⟩ := hdom hv
    exact w.2
  obtain ⟨w, hw, rfl⟩ := hdom hv
  -- Clause 2 of Lemma 4.1 at the point `w` of the increment.
  have hcall := (GI.Paper.lem_main_local_test S.domGroup w π T.card hk5).2.1 x T rfl t w hw
  have hcard : Nat.card (orb T'.G w) = Nat.card (orb Nt w) := by
    rw [hG, State.card_orb_liftGroup hNt w.2]
  have hsize : Fintype.card S.dom = S.size := (Nat.card_eq_fintype_card).symm
  have hσ : GI.sigma P.κ (w : Ω) T'.G =
      GI.sigma P.κ (GI.activeOrbitBase Nt w) (GI.faithfulOrbitImage Nt w) := by
    haveI : Fintype (GI.ActiveOrbit Nt w) := Fintype.ofFinite _
    rw [hG, State.sigma_liftGroup P.κ hNt w.2, GI.sigma_faithfulOrbit]
  have hσS : GI.sigma P.κ w S.domGroup ≤ S.sigma P.κ := by
    rw [← State.sigma_domGroup P.κ w.2]
    exact S.sigma_point_le P.κ w.2
  rw [← hκ, ← hNt_def] at hcall
  rcases hcall with ⟨h1, h2⟩ | ⟨_, h2⟩
  · -- Type `(s, σ) ↦ (s/κ, σ)`: the orbit has at most `s/κ ≤ θ s` points.
    left
    rw [hcard]
    have h1' : (T.card : ℝ) * Nat.card (orb Nt w) ≤ S.size := by
      rw [← hsize]; exact_mod_cast hκ ▸ h1
    have hk0 : (0 : ℝ) < T.card := by exact_mod_cast (show 0 < T.card by omega)
    have hc0 : (0 : ℝ) ≤ Nat.card (orb Nt w) := Nat.cast_nonneg _
    have hθ0 : 0 < P.θ := by
      by_contra h
      push Not at h
      nlinarith
    nlinarith
  · -- Type `(s, σ) ↦ (s, σ - κ)`: `σ` drops by `κ`.
    right
    rw [hσ]
    omega

end GI.Algorithm
