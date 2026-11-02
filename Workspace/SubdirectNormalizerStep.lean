import Workspace.SimpleSubdirect

namespace GI.PrimitiveProducts

variable {S T : Type*} [Group S] [Group T] [IsSimpleGroup S]

/-- A normalizer element supported in the first simple factor belongs to
the subgroup. Otherwise its commutators force it into the trivial center. -/
theorem normalizer_inl_mem (H : Subgroup (S × T))
    (onto : Function.Surjective (Prod.fst ∘ H.subtype))
    (nonabelian : ∃ x y : S, x * y ≠ y * x)
    (s : S) (hs : (s, 1) ∈ (Subgroup.normalizer (H : Set (S × T)))) : (s, 1) ∈ H := by
  letI := Subgroup.normal_goursatFst onto
  rcases (inferInstance : H.goursatFst.Normal).eq_bot_or_eq_top with hb | ht
  · have hcenter : s ∈ Subgroup.center S := by
      apply Subgroup.mem_center_iff.mpr
      intro t
      obtain ⟨h, hh⟩ := onto t
      change h.val.1 = t at hh
      have hconj := (Subgroup.mem_normalizer_iff.mp hs h.val).mp h.property
      have hcomm := H.mul_mem hconj (H.inv_mem h.property)
      change ((s * h.val.1 * s⁻¹) * h.val.1⁻¹,
        (1 * h.val.2 * 1⁻¹) * h.val.2⁻¹) ∈ H at hcomm
      have hk : s * t * s⁻¹ * t⁻¹ ∈ H.goursatFst :=
        Subgroup.mem_goursatFst.mpr (by
          simpa only [Prod.mk_mul_mk, Prod.inv_mk, inv_one, one_mul, mul_one,
            mul_inv_cancel, hh] using hcomm)
      rw [hb, Subgroup.mem_bot] at hk
      exact (commutatorElement_eq_one_iff_mul_comm.mp hk).symm
    rw [simple_center_eq_bot nonabelian, Subgroup.mem_bot] at hcenter
    simpa only [hcenter] using H.one_mem
  · exact Subgroup.mem_goursatFst.mp (by rw [ht]; exact Subgroup.mem_top s)

/-- One-coordinate induction step for the Scott normalizer lemma. The
tail hypothesis is about the actual projection subgroup, and is discharged
by finite-coordinate induction in the next module. -/
theorem normalizer_eq_self_of_simple_first (H : Subgroup (S × T))
    (onto : Function.Surjective (Prod.fst ∘ H.subtype))
    (nonabelian : ∃ x y : S, x * y ≠ y * x)
    (tail : (Subgroup.normalizer (H.map (MonoidHom.snd S T))) = H.map (MonoidHom.snd S T)) :
    (Subgroup.normalizer (H : Set (S × T))) = H := by
  apply le_antisymm _ H.le_normalizer
  intro x hx
  have ht : x.2 ∈ (Subgroup.normalizer (H.map (MonoidHom.snd S T))) :=
    Subgroup.le_normalizer_map (MonoidHom.snd S T) ⟨x, hx, rfl⟩
  rw [tail] at ht
  obtain ⟨h, hh, ht⟩ := ht
  change h.2 = x.2 at ht
  have hx' : x * h⁻¹ ∈ (Subgroup.normalizer (H : Set (S × T))) :=
    (Subgroup.normalizer (H : Set (S × T))).mul_mem hx ((Subgroup.normalizer (H : Set (S × T))).inv_mem (H.le_normalizer hh))
  have htail : (x * h⁻¹).2 = 1 := by
    change x.2 * h.2⁻¹ = 1
    rw [ht, mul_inv_cancel]
  have he : ((x * h⁻¹).1, 1) = x * h⁻¹ := Prod.ext rfl htail.symm
  have hm := normalizer_inl_mem H onto nonabelian (x * h⁻¹).1 (he.symm ▸ hx')
  have hxH : x * h⁻¹ ∈ H := he ▸ hm
  have := H.mul_mem hxH hh
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using this

end GI.PrimitiveProducts

#print axioms GI.PrimitiveProducts.normalizer_inl_mem
#print axioms GI.PrimitiveProducts.normalizer_eq_self_of_simple_first
