import Workspace.SimpleSubdirect

namespace GI.PrimitiveProducts

variable {S T : Type*} [Group S] [Group T]

def secondProjection (H : Subgroup (S × T)) : H →* H.map (MonoidHom.snd S T) where
  toFun h := ⟨h.val.2, ⟨h.val, h.property, rfl⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem secondProjection_surjective (H : Subgroup (S × T)) :
    Function.Surjective (secondProjection H) := by
  intro t
  obtain ⟨x, hx, he⟩ := t.property
  exact ⟨⟨x, hx⟩, Subtype.ext he⟩

theorem secondProjection_injective (H : Subgroup (S × T)) (hk : H.goursatFst = ⊥) :
    Function.Injective (secondProjection H) := by
  intro h k he
  exact snd_injective_of_goursatFst_eq_bot H hk (congrArg Subtype.val he)

noncomputable def secondProjectionEquiv (H : Subgroup (S × T)) (hk : H.goursatFst = ⊥) :
    H ≃* H.map (MonoidHom.snd S T) :=
  MulEquiv.ofBijective (secondProjection H)
    ⟨secondProjection_injective H hk, secondProjection_surjective H⟩

/-- A subgroup with trivial first-coordinate intersection is the graph
of an actual homomorphism from its actual tail projection. -/
noncomputable def projectionGraphHom (H : Subgroup (S × T)) (hk : H.goursatFst = ⊥) :
    H.map (MonoidHom.snd S T) →* S :=
  ((MonoidHom.fst S T).comp H.subtype).comp (secondProjectionEquiv H hk).symm.toMonoidHom

theorem projectionGraphHom_pair_mem (H : Subgroup (S × T)) (hk : H.goursatFst = ⊥)
    (t : H.map (MonoidHom.snd S T)) : (projectionGraphHom H hk t, t.val) ∈ H := by
  let h := (secondProjectionEquiv H hk).symm t
  have ht : h.val.2 = t.val :=
    congrArg Subtype.val ((secondProjectionEquiv H hk).apply_symm_apply t)
  have he : h.val = (projectionGraphHom H hk t, t.val) := Prod.ext rfl ht
  exact he ▸ h.property

theorem card_eq_secondProjection (H : Subgroup (S × T)) (hk : H.goursatFst = ⊥) :
    Nat.card H = Nat.card (H.map (MonoidHom.snd S T)) :=
  Nat.card_congr (secondProjectionEquiv H hk).toEquiv

theorem goursatFst_eq_bot_of_no_full_first [IsSimpleGroup S]
    (H : Subgroup (S × T)) (onto : Function.Surjective (Prod.fst ∘ H.subtype))
    (noFull : ¬ ∀ s : S, (s, 1) ∈ H) : H.goursatFst = ⊥ := by
  letI := Subgroup.normal_goursatFst onto
  rcases (inferInstance : H.goursatFst.Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · apply (noFull ?_).elim
    intro s
    apply Subgroup.mem_goursatFst.mp
    rw [ht]
    exact Subgroup.mem_top s

end GI.PrimitiveProducts

#print axioms GI.PrimitiveProducts.secondProjection
#print axioms GI.PrimitiveProducts.secondProjection_surjective
#print axioms GI.PrimitiveProducts.secondProjection_injective
#print axioms GI.PrimitiveProducts.secondProjectionEquiv
#print axioms GI.PrimitiveProducts.projectionGraphHom
#print axioms GI.PrimitiveProducts.projectionGraphHom_pair_mem
#print axioms GI.PrimitiveProducts.card_eq_secondProjection
#print axioms GI.PrimitiveProducts.goursatFst_eq_bot_of_no_full_first
