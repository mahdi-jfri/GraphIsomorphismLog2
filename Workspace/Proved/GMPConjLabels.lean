module

public import Workspace.Proved.GMPListedCosets
public import Workspace.MulticosetModel

@[expose] public section

/-! # Conjugation rows encode permutations of the coset labels -/

namespace GI.Proved

open GI.Impl GI.Cited GI.Lang Equiv

variable {G : Type*} [Group G] {H U V : Subgroup G}

/-- The normalization condition supplies an inclusion into the normalizer. -/
theorem gmp_le_normalizer (hU : GI.Multicoset.Normalizes H U) : H ≤ Subgroup.normalizer (U : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · exact hU h hh u
  · intro hu
    have ht := hU h⁻¹ (H.inv_mem hh) (h * u * h⁻¹) hu
    convert ht using 1 <;> group

/-- Conjugation by a normalizing subgroup, even if it does not contain `U`. -/
def gmpNormalizerAction (hU : GI.Multicoset.Normalizes H U) : H →* MulAut U :=
  U.normalizerMonoidHom.comp (Subgroup.inclusion (gmp_le_normalizer hU))

theorem gmpNormalizerAction_apply (hU : GI.Multicoset.Normalizes H U) (h : H) (u : U) :
    (gmpNormalizerAction hU h u : G) = (h : G) * u * (h : G)⁻¹ := rfl

theorem gmpNormalizerAction_preserves (hU : GI.Multicoset.Normalizes H U)
    (hV : GI.Multicoset.Normalizes H V) (h : H) :
    V.subgroupOf U ≤ (V.subgroupOf U).comap (gmpNormalizerAction hU h).toMonoidHom :=
  fun u hu => hV h h.property u hu

noncomputable def gmpConjLabelAction {rs : List G} (hrs : GmpCosetReps U V rs)
    (hU : GI.Multicoset.Normalizes H U) (hV : GI.Multicoset.Normalizes H V) :
    H →* Perm (Fin rs.length) :=
  gmpRepsAutAction hrs (gmpNormalizerAction hU) (gmpNormalizerAction_preserves hU hV)

theorem gmpConjLabelAction_apply_iff {rs : List G} (hrs : GmpCosetReps U V rs)
    (hU : GI.Multicoset.Normalizes H U) (hV : GI.Multicoset.Normalizes H V)
    (h : H) (i j : Fin rs.length) :
    gmpConjLabelAction hrs hU hV h i = j ↔
      (h : G) * rs.get i * (h : G)⁻¹ * (rs.get j)⁻¹ ∈ V :=
  gmpRepsAutAction_apply_iff hrs _ _ h i j

/-- Each integer produced by the coset search is the value of the label permutation. -/
theorem gmpConjLabelAction_index {n : ℕ} {H U V : Subgroup (Perm (Fin n))}
    {rs : List (Perm (Fin n))} (hrs : GmpCosetReps U V rs)
    (hU : GI.Multicoset.Normalizes H U) (hV : GI.Multicoset.Normalizes H V)
    (h : H) (i : Fin rs.length) :
    gmpCosetIndex V rs ((h : Perm (Fin n)) * rs.get i * (h : Perm (Fin n))⁻¹) =
      (gmpConjLabelAction hrs hU hV h i).val := by
  apply gmpCosetIndex_eq hrs
    (hU h h.property _ (hrs.sub _ (List.get_mem rs i)))
    (gmpConjLabelAction hrs hU hV h i).isLt
  exact (gmpConjLabelAction_apply_iff hrs hU hV h i _).mp rfl

/-- The complete computed row is the standard encoding of that permutation. -/
theorem gmpConjLabelAction_encPerm {n : ℕ} {H U V : Subgroup (Perm (Fin n))}
    {rs : List (Perm (Fin n))} (hrs : GmpCosetReps U V rs)
    (hU : GI.Multicoset.Normalizes H U) (hV : GI.Multicoset.Normalizes H V) (h : H) :
    natList (rs.map fun r => gmpCosetIndex V rs ((h : Perm (Fin n)) * r * (h : Perm (Fin n))⁻¹)) =
      encPerm (gmpConjLabelAction hrs hU hV h) := by
  unfold natList encPerm
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.length_map] at hi
    simp only [List.getElem_map, List.getElem_finRange]
    exact congrArg Val.nat (gmpConjLabelAction_index hrs hU hV h ⟨i, hi⟩)

end GI.Proved
