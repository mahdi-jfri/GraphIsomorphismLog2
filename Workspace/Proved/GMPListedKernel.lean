module

public import Workspace.Proved.GMPConjLabels

@[expose] public section

/-! # The kernel on listed cosets as a commutator condition -/

namespace GI.Proved

open GI.Impl Equiv

variable {G : Type*} [Group G] {H U V : Subgroup G} {rs : List G}

/-- Fixing every listed coset is the same as centralizing `U` modulo `V`. -/
theorem gmpConjLabelAction_mem_ker (hrs : GmpCosetReps U V rs)
    (hU : GI.Multicoset.Normalizes H U) (hV : GI.Multicoset.Normalizes H V) (h : H) :
    h ∈ (gmpConjLabelAction hrs hU hV).ker ↔
      ∀ u ∈ U, (h : G) * u * (h : G)⁻¹ * u⁻¹ ∈ V := by
  have hlisted : h ∈ (gmpConjLabelAction hrs hU hV).ker ↔
      ∀ r ∈ rs, (h : G) * r * (h : G)⁻¹ * r⁻¹ ∈ V := by
    constructor
    · intro hk r hr
      obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hr
      have hi' : gmpConjLabelAction hrs hU hV h ⟨i, hi⟩ = ⟨i, hi⟩ :=
        congrArg (fun p : Perm (Fin rs.length) => p ⟨i, hi⟩) hk
      have hm := (gmpConjLabelAction_apply_iff hrs hU hV h ⟨i, hi⟩ ⟨i, hi⟩).mp hi'
      simpa only [List.get_eq_getElem, he] using hm
    · intro hk
      apply Equiv.ext
      intro i
      exact (gmpConjLabelAction_apply_iff hrs hU hV h i i).mpr (hk _ (List.get_mem rs i))
  rw [hlisted]
  constructor
  · intro hk u hu
    obtain ⟨r, hr, v, hv, rfl⟩ := hrs.cover u hu
    have hnorm := hV h h.property v hv
    have hrep := hk r hr
    have hp := V.mul_mem (V.mul_mem hnorm hrep) (V.inv_mem hv)
    convert hp using 1 <;> group
  · intro hk r hr
    exact hk r (hrs.sub r hr)

end GI.Proved
