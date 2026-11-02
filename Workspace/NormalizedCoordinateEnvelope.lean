import Workspace.ProjectionEnvelope
import Workspace.StabilizerEnvelope

namespace GI.PrimitiveCartesian

variable {G P V : Type*} [Group G] [Group P]

theorem normalizes_image_of_intertwining (F : P →* G) (H : Subgroup P)
    (e : MulAut P) (g : G) (transport : ∀ x, F (e x) = g * F x * g⁻¹)
    (preserves : H.map e.toMonoidHom = H) : g ∈ (Subgroup.normalizer (H.map F)) := by
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨e y, ?_, transport y⟩
    rw [← preserves]
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, he⟩
    refine ⟨e.symm y, ?_, ?_⟩
    · have hymap : y ∈ H.map e.toMonoidHom := by rw [preserves]; exact hy
      obtain ⟨z, hz, hzy⟩ := hymap
      change e z = y at hzy
      have hez : e.symm y = z := by rw [← hzy]; exact e.symm_apply_apply z
      rwa [hez]
    · apply (MulAut.conj g).injective
      change g * F (e.symm y) * g⁻¹ = g * x * g⁻¹
      rw [← transport, e.apply_symm_apply, he]

theorem stabilizer_coordinates_preserved [MulAction G V] (a : V)
    (F : P →* G) (e : MulAut P) (g : MulAction.stabilizer G a)
    (transport : ∀ x, F (e x) = g.val * F x * g.val⁻¹) :
    ((MulAction.stabilizer G a).comap F).map e.toMonoidHom =
      (MulAction.stabilizer G a).comap F := by
  ext x
  rw [Subgroup.mem_map_equiv]
  change F (e.symm x) ∈ MulAction.stabilizer G a ↔ F x ∈ MulAction.stabilizer G a
  have h := Subgroup.mem_normalizer_iff.mp
    ((MulAction.stabilizer G a).le_normalizer g.property) (F (e.symm x))
  rwa [← transport, e.apply_symm_apply] at h

variable {I : Type*} {S : I → Type*} [∀ i, Group (S i)] [Finite (∀ i, S i)]

/-- Primitivity forces a proper product of coordinate images to equal
the actual stabilizer in the embedded product group. The conjugation
and fiber conditions are supplied by intrinsic socle coordinates in the
next module. -/
theorem primitive_projectionEnvelope_eq [MulAction G V] [Nontrivial V]
    [MulAction.IsPreprimitive G V] (a : V) (F : (∀ i, S i) →* G)
    (injective : Function.Injective F)
    (coordinateAut : MulAction.stabilizer G a → MulAut (∀ i, S i))
    (positions : MulAction.stabilizer G a → Equiv.Perm I)
    (transport : ∀ g x, F (coordinateAut g x) = g.val * F x * g.val⁻¹)
    (fibers : ∀ g i x y, x i = y i →
      coordinateAut g x (positions g i) = coordinateAut g y (positions g i))
    (i : I) (proper : ((MulAction.stabilizer G a).comap F).map
      (Pi.evalMonoidHom S i) ≠ ⊤) :
    projectionEnvelope ((MulAction.stabilizer G a).comap F) =
      (MulAction.stabilizer G a).comap F := by
  let K := (MulAction.stabilizer G a).comap F
  let R := (projectionEnvelope K).map F
  have hRN : R ≤ F.range := Subgroup.map_le_range F (projectionEnvelope K)
  have hinter : F.range ⊓ MulAction.stabilizer G a ≤ R := by
    rw [← Subgroup.map_comap_eq]
    exact Subgroup.map_mono (le_projectionEnvelope K)
  have hnorm : MulAction.stabilizer G a ≤ (Subgroup.normalizer R) := by
    intro g hg
    let h : MulAction.stabilizer G a := ⟨g, hg⟩
    exact normalizes_image_of_intertwining F (projectionEnvelope K) (coordinateAut h) g
      (transport h) (projectionEnvelope_map_eq K (coordinateAut h) (positions h)
        (fibers h) (stabilizer_coordinates_preserved a F (coordinateAut h) h (transport h)))
  have hproper : R ≠ F.range := by
    intro hR
    apply projectionEnvelope_ne_top K i proper
    apply Subgroup.map_injective (f := F) injective
    rw [← MonoidHom.range_eq_map]
    exact hR
  have hR := primitive_proper_envelope_eq a F.range R hRN hinter hnorm hproper
  apply Subgroup.map_injective (f := F) injective
  change R = K.map F
  rw [Subgroup.map_comap_eq]
  exact hR

end GI.PrimitiveCartesian

#print axioms GI.PrimitiveCartesian.normalizes_image_of_intertwining
#print axioms GI.PrimitiveCartesian.stabilizer_coordinates_preserved
#print axioms GI.PrimitiveCartesian.primitive_projectionEnvelope_eq
