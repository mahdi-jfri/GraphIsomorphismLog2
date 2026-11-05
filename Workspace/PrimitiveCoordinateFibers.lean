module

public import Workspace.PrimitiveProductCoordinates
public import Workspace.CosetCoordinateFibers
public import Workspace.RadicalSocleHomogeneous

@[expose] public section

namespace GI.PrimitiveCartesian

open GI.RadicalSocle

variable {G V : Type*} [Group G] [Finite G]

noncomputable abbrev minimalCoordinateEmbedding
    (radicalFree : ∀ K : Subgroup G, K.Normal → IsSolvable K → K = ⊥)
    (N : Subgroup G) [N.Normal] (hN : MinimalNormal N) : IntrinsicCoordinates N →* G :=
  normalCoordinateEmbedding N (normal_subgroup_radicalFree radicalFree N)
    (minimalNormal_socle_eq_top hN)

def normalFactorPositions (N : Subgroup G) [N.Normal] :
    G →* Equiv.Perm (MinimalNormals N) :=
  minimalNormalAction.comp (MulAut.conjNormal (H := N))

theorem normalFactorPositions_transitive
    (radicalFree : ∀ K : Subgroup G, K.Normal → IsSolvable K → K = ⊥)
    (N : Subgroup G) [N.Normal] (hN : MinimalNormal N) (i j : MinimalNormals N) :
    ∃ g : G, normalFactorPositions N g i = j := by
  obtain ⟨g, hg⟩ := minimalNormal_factors_conjugate radicalFree hN i j
  exact ⟨g, Subtype.ext hg⟩

variable [MulAction G V] [FaithfulSMul G V] [Nontrivial V]
  [MulAction.IsPreprimitive G V]

omit [Nontrivial V] in
theorem minimalCoordinate_representatives
    (radicalFree : ∀ K : Subgroup G, K.Normal → IsSolvable K → K = ⊥)
    (N : Subgroup G) [N.Normal] (hN : MinimalNormal N) (a v : V) :
    ∃ x : IntrinsicCoordinates N, minimalCoordinateEmbedding radicalFree N hN x • a = v := by
  let f := intrinsicProductEquiv (normal_subgroup_radicalFree radicalFree N)
    (minimalNormal_socle_eq_top hN)
  letI : MulAction.IsPretransitive N V :=
    GI.PrimitiveStructure.normal_pretransitive N hN.2.1
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N a v
  refine ⟨f.symm n, ?_⟩
  change ((f (f.symm n) : N) : G) • a = v
  rw [f.apply_symm_apply]
  exact hn

theorem primitiveMinimalProductCoordinates_apply
    (radicalFree : ∀ K : Subgroup G, K.Normal → IsSolvable K → K = ⊥)
    (N : Subgroup G) [N.Normal] (hN : MinimalNormal N) (a : V) (i : MinimalNormals N)
    (proper : ((MulAction.stabilizer G a).comap
      (minimalCoordinateEmbedding radicalFree N hN)).map
        (Pi.evalMonoidHom (fun M : MinimalNormals N => M.val) i) ≠ ⊤)
    (x : IntrinsicCoordinates N) (j : MinimalNormals N) :
    primitiveMinimalProductCoordinates radicalFree N hN a i proper
      (minimalCoordinateEmbedding radicalFree N hN x • a) j = QuotientGroup.mk (x j) := by
  letI : MulAction (IntrinsicCoordinates N) V :=
    MulAction.compHom V (minimalCoordinateEmbedding radicalFree N hN)
  letI : MulAction.IsPretransitive (IntrinsicCoordinates N) V := by
    constructor
    exact minimalCoordinate_representatives radicalFree N hN
  unfold primitiveMinimalProductCoordinates
  exact productActionCoordinates_smul a _ _ x j

/-- The actual primitive action permutes its actual coset-coordinate
fibers by the actual conjugation action on minimal normal factors. -/
theorem primitive_minimalNormal_fiber_transport
    (radicalFree : ∀ K : Subgroup G, K.Normal → IsSolvable K → K = ⊥)
    (N : Subgroup G) [N.Normal] (hN : MinimalNormal N) (a : V) (i : MinimalNormals N)
    (proper : ((MulAction.stabilizer G a).comap
      (minimalCoordinateEmbedding radicalFree N hN)).map
        (Pi.evalMonoidHom (fun M : MinimalNormals N => M.val) i) ≠ ⊤)
    (g : G) (j : MinimalNormals N) (v w : V)
    (hvw : primitiveMinimalProductCoordinates radicalFree N hN a i proper v j =
      primitiveMinimalProductCoordinates radicalFree N hN a i proper w j) :
    primitiveMinimalProductCoordinates radicalFree N hN a i proper (g • v)
        (normalFactorPositions N g j) =
      primitiveMinimalProductCoordinates radicalFree N hN a i proper (g • w)
        (normalFactorPositions N g j) :=
  physical_product_fiber_transport a (minimalCoordinateEmbedding radicalFree N hN) _
    (primitiveMinimalProductCoordinates radicalFree N hN a i proper)
    (minimalCoordinate_representatives radicalFree N hN a)
    (primitiveMinimalProductCoordinates_apply radicalFree N hN a i proper)
    (fun g => intrinsicCoordinateAut (normal_subgroup_radicalFree radicalFree N)
      (minimalNormal_socle_eq_top hN) (MulAut.conjNormal (H := N) g))
    (normalFactorPositions N)
    (normalCoordinateEmbedding_conjugation N (normal_subgroup_radicalFree radicalFree N)
      (minimalNormal_socle_eq_top hN))
    (fun g => intrinsicCoordinateAut_fibers (normal_subgroup_radicalFree radicalFree N)
      (minimalNormal_socle_eq_top hN) (MulAut.conjNormal (H := N) g)) g j v w hvw

end GI.PrimitiveCartesian
