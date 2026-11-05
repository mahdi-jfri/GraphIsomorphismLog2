module

public import Workspace.SocleCoordinateNaturality
public import Workspace.NormalizedCoordinateEnvelope

@[expose] public section

namespace GI.PrimitiveCartesian

open GI.RadicalSocle

variable {G V : Type*} [Group G] [Finite G]

noncomputable def normalCoordinateEmbedding (N : Subgroup G)
    (radicalFree : ∀ K : Subgroup N, K.Normal → IsSolvable K → K = ⊥)
    (hsoc : socle N = ⊤) : IntrinsicCoordinates N →* G :=
  N.subtype.comp (intrinsicProductEquiv radicalFree hsoc).toMonoidHom

theorem normalCoordinateEmbedding_injective (N : Subgroup G)
    (radicalFree : ∀ K : Subgroup N, K.Normal → IsSolvable K → K = ⊥)
    (hsoc : socle N = ⊤) :
    Function.Injective (normalCoordinateEmbedding N radicalFree hsoc) :=
  N.subtype_injective.comp (intrinsicProductEquiv radicalFree hsoc).injective

theorem normalCoordinateEmbedding_range (N : Subgroup G)
    (radicalFree : ∀ K : Subgroup N, K.Normal → IsSolvable K → K = ⊥)
    (hsoc : socle N = ⊤) : (normalCoordinateEmbedding N radicalFree hsoc).range = N := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact (intrinsicProductEquiv radicalFree hsoc x).property
  · intro x hx
    refine ⟨(intrinsicProductEquiv radicalFree hsoc).symm ⟨x, hx⟩, ?_⟩
    change ((intrinsicProductEquiv radicalFree hsoc
      ((intrinsicProductEquiv radicalFree hsoc).symm ⟨x, hx⟩)) : G) = x
    rw [MulEquiv.apply_symm_apply]

theorem normalCoordinateEmbedding_conjugation (N : Subgroup G) [N.Normal]
    (radicalFree : ∀ K : Subgroup N, K.Normal → IsSolvable K → K = ⊥)
    (hsoc : socle N = ⊤) (g : G) (x : IntrinsicCoordinates N) :
    normalCoordinateEmbedding N radicalFree hsoc
      (intrinsicCoordinateAut radicalFree hsoc (MulAut.conjNormal (H := N) g) x) =
      g * normalCoordinateEmbedding N radicalFree hsoc x * g⁻¹ := by
  change ((intrinsicProductEquiv radicalFree hsoc
    ((intrinsicProductEquiv radicalFree hsoc).symm
      (MulAut.conjNormal (H := N) g (intrinsicProductEquiv radicalFree hsoc x)))) : G) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

/-- In a primitive physical action, a normal subgroup equal to its socle
has a product point stabilizer as soon as one intrinsic coordinate
projection is proper. Factor permutation and envelope normalization are
derived here from actual conjugation, not supplied as a representation. -/
theorem primitive_normal_product_stabilizer [MulAction G V] [Nontrivial V]
    [MulAction.IsPreprimitive G V] (N : Subgroup G) [N.Normal]
    (radicalFree : ∀ K : Subgroup N, K.Normal → IsSolvable K → K = ⊥)
    (hsoc : socle N = ⊤) (a : V) (i : MinimalNormals N)
    (proper : ((MulAction.stabilizer G a).comap
      (normalCoordinateEmbedding N radicalFree hsoc)).map
        (Pi.evalMonoidHom (fun M : MinimalNormals N => M.val) i) ≠ ⊤) :
    projectionEnvelope ((MulAction.stabilizer G a).comap
      (normalCoordinateEmbedding N radicalFree hsoc)) =
      (MulAction.stabilizer G a).comap (normalCoordinateEmbedding N radicalFree hsoc) :=
  primitive_projectionEnvelope_eq a (normalCoordinateEmbedding N radicalFree hsoc)
    (normalCoordinateEmbedding_injective N radicalFree hsoc)
    (fun g => intrinsicCoordinateAut radicalFree hsoc (MulAut.conjNormal (H := N) g.val))
    (fun g => minimalNormalPerm (MulAut.conjNormal (H := N) g.val))
    (fun g => normalCoordinateEmbedding_conjugation N radicalFree hsoc g.val)
    (fun g => intrinsicCoordinateAut_fibers radicalFree hsoc
      (MulAut.conjNormal (H := N) g.val)) i proper

/-- The actual minimal-normal case discharges both semisimple structural
inputs using the existing radical-free socle theorems. -/
theorem primitive_minimalNormal_product_stabilizer [MulAction G V] [Nontrivial V]
    [MulAction.IsPreprimitive G V]
    (radicalFree : ∀ K : Subgroup G, K.Normal → IsSolvable K → K = ⊥)
    (N : Subgroup G) [N.Normal] (hN : MinimalNormal N) (a : V) (i : MinimalNormals N)
    (proper : ((MulAction.stabilizer G a).comap (normalCoordinateEmbedding N
      (normal_subgroup_radicalFree radicalFree N) (minimalNormal_socle_eq_top hN))).map
        (Pi.evalMonoidHom (fun M : MinimalNormals N => M.val) i) ≠ ⊤) :
    projectionEnvelope ((MulAction.stabilizer G a).comap (normalCoordinateEmbedding N
      (normal_subgroup_radicalFree radicalFree N) (minimalNormal_socle_eq_top hN))) =
      (MulAction.stabilizer G a).comap (normalCoordinateEmbedding N
        (normal_subgroup_radicalFree radicalFree N) (minimalNormal_socle_eq_top hN)) :=
  primitive_normal_product_stabilizer N (normal_subgroup_radicalFree radicalFree N)
    (minimalNormal_socle_eq_top hN) a i proper

end GI.PrimitiveCartesian
