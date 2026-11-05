module

public import Workspace.Impl.VsHPcMath
public import Workspace.Impl.VsQTSot

@[expose] public section

/-!
# The orbit of a tuple of pieces is small

If every entry of a tuple `ys₀` of local subspaces is some `X i`, the orbit of `ys₀` under
`⟨hs⟩` has at most `|H̄ : vsMStab X|` points (`vsH_tup_orbit`).
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst} {s : VsQSt I}

/-- The tuple moved by a local unit. -/
noncomputable def vsHTPhi (ys : VsQTup s) (u : (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ) :
    VsQTup s :=
  ys.map fun U => U.map (u : Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))

theorem vsQTAct_eq (hs : VsQStOK s) {g : Perm (Fin I.n)} (hg : g ∈ gens s.hs) (ys : VsQTup s) :
    vsQTAct s g ys = vsHTPhi ys (vsPRho hs g) := by
  unfold vsQTAct vsHTPhi
  rw [vsPRho_of hs hg, vsQRho_eq_toLin' hs hg]

set_option backward.isDefEq.respectTransparency false in
/-- **The orbit of a tuple of pieces.** -/
theorem vsH_tup_orbit [Fact I.p.Prime] (hs : VsQStOK s) {ι : Type*}
    {X : ι → Submodule (ZMod I.p) (Fin (vsQD s) → ZMod I.p)} {ys₀ : VsQTup s}
    (hX : ∀ U ∈ ys₀, ∃ i, U = X i) :
    (vsQOrb (vsQTAct s) s.hs ys₀).ncard ≤ (vsMStab X).relIndex (vsPBar hs (gens s.hs)) := by
  classical
  set Cb := vsPBar hs (gens s.hs)
  set Z := vsMStab X
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  haveI : Finite (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p)) := Module.finite_of_finite (ZMod I.p)
  have hconst : ∀ u v : Cb, (QuotientGroup.mk u : Cb ⧸ Z.subgroupOf Cb) = QuotientGroup.mk v →
      vsHTPhi ys₀ u = vsHTPhi ys₀ v := by
    intro u v huv
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at huv
    set z := ((u⁻¹ * v : Cb) : (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ)
    have hv : (v : (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ) = u * z := by simp [z]
    unfold vsHTPhi
    refine List.map_congr_left fun U hU => ?_
    obtain ⟨i, rfl⟩ := hX U hU
    rw [hv, Units.val_mul, Module.End.mul_eq_comp, Submodule.map_comp, huv i]
  let F : Cb ⧸ Z.subgroupOf Cb → VsQTup s :=
    Quotient.lift (fun u : Cb => vsHTPhi ys₀ u) (fun u v h => hconst u v (Quotient.sound h))
  have hsub : vsQOrb (vsQTAct s) s.hs ys₀ ⊆ Set.range F := by
    rintro _ ⟨g, hg, rfl⟩
    have hg' : g ∈ gens s.hs := hg
    refine ⟨QuotientGroup.mk ⟨vsPRho hs g, vsPRho_mem_vsPBar hs hg' hg'⟩, ?_⟩
    show vsHTPhi ys₀ (vsPRho hs g) = _
    rw [vsQTAct_eq hs hg']
  calc (vsQOrb (vsQTAct s) s.hs ys₀).ncard ≤ (Set.range F).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ Nat.card (Cb ⧸ Z.subgroupOf Cb) := by
      rw [← Set.image_univ, ← Set.ncard_univ]
      exact Set.ncard_image_le (Set.toFinite _)
    _ = Z.relIndex Cb := rfl

end GI.Impl
