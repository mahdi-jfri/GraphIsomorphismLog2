import Workspace.CleanComplementOldRows
import Workspace.CleanComplementEven
import Workspace.CleanComplementTransport

/-! Combine the old-block construction and the localized even extension in
the original supplied group. The only local inputs are actual localized elements. -/
namespace GI.CleanEvenAssembly
open CleanEvenCoordinates
variable {J V : Type*} [Fintype J] [DecidableEq J]
variable {G : Subgroup (Equiv.Perm V)}
variable {A : CleanBlockAction G (Option (Option (J × Bool)))}
variable (d : LocalizedBlockPair A) (hcard : 5 ≤ Fintype.card (Option (Option (J × Bool))))

noncomputable def oldAction : CleanBlockAction
    (CleanBlockAction.relabeledGroup (G := G) (CleanOldRows.coordinates d hcard).symm)
    (Option (Option (J × Bool))) :=
  A.relabel (CleanOldRows.coordinates d hcard).symm

theorem oldAction_label
    (x : ((CleanOldRows.system d hcard).Center × Option (J × Bool)) ⊕ CleanOldRows.New (A := A)) :
    (oldAction d hcard).label x = blockLabel x := CleanOldRows.coordinates_label d hcard x

theorem old_mem (p : alternatingGroup (Option (J × Bool))) :
    oldHom p.val ∈ CleanBlockAction.relabeledGroup (G := G) (CleanOldRows.coordinates d hcard).symm := by
  refine ⟨CleanOldRows.lift d hcard p.val, CleanOldRows.pure_mem d hcard p, ?_⟩
  apply Equiv.ext
  intro x
  change (CleanOldRows.coordinates d hcard).symm
    (CleanOldRows.coordinates d hcard (oldHom p.val
      ((CleanOldRows.coordinates d hcard).symm (CleanOldRows.coordinates d hcard x)))) = _
  rw [(CleanOldRows.coordinates d hcard).symm_apply_apply,
    (CleanOldRows.coordinates d hcard).symm_apply_apply]

variable {a b c : Option (J × Bool)}
variable (u : CleanEvenConstruction.ExtraLift (oldAction d hcard) a b c)
variable (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)

noncomputable def coordinates :
    (CleanOldRows.system d hcard).Center × Option (Option (J × Bool)) ≃ V :=
  (CleanEvenConstruction.coords (oldAction_label d hcard) u hab hbc).trans
    (CleanOldRows.coordinates d hcard)

theorem coordinates_label (x : (CleanOldRows.system d hcard).Center)
    (i : Option (Option (J × Bool))) : A.label (coordinates d hcard u hab hbc (x, i)) = i := by
  change A.label (CleanOldRows.coordinates d hcard
    (CleanEvenConstruction.coords (oldAction_label d hcard) u hab hbc (x, i))) = _
  rw [CleanOldRows.coordinates_label]
  cases i <;> rfl

include hac in
theorem pure_mem (p : alternatingGroup (Option (Option (J × Bool)))) :
    coordinatePureLift (coordinates d hcard u hab hbc) p.val ∈ G := by
  have hn := CleanEvenConstruction.pure_mem (oldAction_label d hcard) u hab hac hbc (old_mem d hcard) p
  obtain ⟨q, hq, hqe⟩ := hn
  have he : coordinatePureLift (coordinates d hcard u hab hbc) p.val =
      relabelPerm (CleanOldRows.coordinates d hcard)
        (coordinatePureLift (CleanEvenConstruction.coords (oldAction_label d hcard) u hab hbc) p.val) := by
    rfl
  rw [he, ← hqe]
  have hc : relabelPerm (CleanOldRows.coordinates d hcard)
      (relabelPerm (CleanOldRows.coordinates d hcard).symm q) = q := by
    apply Equiv.ext
    intro x
    change CleanOldRows.coordinates d hcard ((CleanOldRows.coordinates d hcard).symm
      (q (CleanOldRows.coordinates d hcard ((CleanOldRows.coordinates d hcard).symm x)))) = q x
    rw [(CleanOldRows.coordinates d hcard).apply_symm_apply,
      (CleanOldRows.coordinates d hcard).apply_symm_apply]
  change relabelPerm (CleanOldRows.coordinates d hcard)
    (relabelPerm (CleanOldRows.coordinates d hcard).symm q) ∈ G
  rw [hc]
  exact hq

noncomputable def sectionHom : alternatingGroup (Option (Option (J × Bool))) →* G :=
  CleanBlockAction.cleanSection (coordinates d hcard u hab hbc) (pure_mem d hcard u hab hac hbc)

theorem top_section (p : alternatingGroup (Option (Option (J × Bool)))) :
    A.top (sectionHom d hcard u hab hac hbc p) = p :=
  A.top_cleanSection (coordinates d hcard u hab hbc) (CleanOldRows.system d hcard).centerBase
    (coordinates_label d hcard u hab hbc) (pure_mem d hcard u hab hac hbc) p

theorem section_pure (p : alternatingGroup (Option (Option (J × Bool))))
    (x : (CleanOldRows.system d hcard).Center) (i : Option (Option (J × Bool))) :
    (sectionHom d hcard u hab hac hbc p).val (coordinates d hcard u hab hbc (x, i)) =
      coordinates d hcard u hab hbc (x, p.val i) :=
  coordinatePureLift_apply (coordinates d hcard u hab hbc) p.val x i

theorem kernel_complement : A.top.ker.IsComplement' (sectionHom d hcard u hab hac hbc).range :=
  A.cleanRange_isComplement (coordinates d hcard u hab hbc) (CleanOldRows.system d hcard).centerBase
    (coordinates_label d hcard u hab hbc) (pure_mem d hcard u hab hac hbc)

theorem kernel_intersection : A.top.ker ⊓ (sectionHom d hcard u hab hac hbc).range = ⊥ :=
  A.kernel_inf_cleanRange (coordinates d hcard u hab hbc) (CleanOldRows.system d hcard).centerBase
    (coordinates_label d hcard u hab hbc) (pure_mem d hcard u hab hac hbc)

theorem kernel_product (g : G) :
    ∃ k ∈ A.top.ker, ∃ r ∈ (sectionHom d hcard u hab hac hbc).range, k * r = g :=
  A.kernel_mul_cleanRange (coordinates d hcard u hab hbc) (CleanOldRows.system d hcard).centerBase
    (coordinates_label d hcard u hab hbc) (pure_mem d hcard u hab hac hbc) g

noncomputable def rangeEquiv :
    alternatingGroup (Option (Option (J × Bool))) ≃* (sectionHom d hcard u hab hac hbc).range :=
  A.cleanRangeEquiv (coordinates d hcard u hab hbc) (CleanOldRows.system d hcard).centerBase
    (coordinates_label d hcard u hab hbc) (pure_mem d hcard u hab hac hbc)

end GI.CleanEvenAssembly
