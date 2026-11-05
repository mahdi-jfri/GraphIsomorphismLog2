module

public import Workspace.PrimitiveProductStabilizer
public import Workspace.CosetProductCoordinates
public import Workspace.PrimitiveAbelianNormal

@[expose] public section

namespace GI.PrimitiveCartesian

open GI.RadicalSocle

variable {G V : Type*} [Group G] [Finite G] [MulAction G V]
  [FaithfulSMul G V] [Nontrivial V] [MulAction.IsPreprimitive G V]

/-- The proper-projection minimal-normal branch has actual Cartesian
coset coordinates on the physical domain. Its product stabilizer and
transitivity are proved, rather than supplied as structural hypotheses. -/
noncomputable def primitiveMinimalProductCoordinates
    (radicalFree : ∀ K : Subgroup G, K.Normal → IsSolvable K → K = ⊥)
    (N : Subgroup G) [N.Normal] (hN : MinimalNormal N) (a : V) (i : MinimalNormals N)
    (proper : ((MulAction.stabilizer G a).comap (normalCoordinateEmbedding N
      (normal_subgroup_radicalFree radicalFree N) (minimalNormal_socle_eq_top hN))).map
        (Pi.evalMonoidHom (fun M : MinimalNormals N => M.val) i) ≠ ⊤) :
    V ≃ (∀ j : MinimalNormals N, j.val ⧸
      (((MulAction.stabilizer G a).comap (normalCoordinateEmbedding N
        (normal_subgroup_radicalFree radicalFree N) (minimalNormal_socle_eq_top hN))).map
          (Pi.evalMonoidHom (fun M : MinimalNormals N => M.val) j))) := by
  let f := intrinsicProductEquiv (normal_subgroup_radicalFree radicalFree N)
    (minimalNormal_socle_eq_top hN)
  let F := normalCoordinateEmbedding N (normal_subgroup_radicalFree radicalFree N)
    (minimalNormal_socle_eq_top hN)
  let K := (MulAction.stabilizer G a).comap F
  let Q := fun j : MinimalNormals N => K.map
    (Pi.evalMonoidHom (fun M : MinimalNormals N => M.val) j)
  letI : MulAction (IntrinsicCoordinates N) V := MulAction.compHom V F
  letI : MulAction.IsPretransitive N V :=
    GI.PrimitiveStructure.normal_pretransitive N hN.2.1
  letI : MulAction.IsPretransitive (IntrinsicCoordinates N) V := by
    constructor
    intro v w
    obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N v w
    refine ⟨f.symm n, ?_⟩
    change ((f (f.symm n) : N) : G) • v = w
    rw [f.apply_symm_apply]
    exact hn
  have hstab : MulAction.stabilizer (IntrinsicCoordinates N) a = Subgroup.pi Set.univ Q := by
    change K = projectionEnvelope K
    exact (primitive_minimalNormal_product_stabilizer radicalFree N hN a i proper).symm
  exact productActionCoordinates a Q hstab

theorem primitive_minimalNormal_product_degree
    (radicalFree : ∀ K : Subgroup G, K.Normal → IsSolvable K → K = ⊥)
    (N : Subgroup G) [N.Normal] [Fintype (MinimalNormals N)]
    (hN : MinimalNormal N) (a : V) (i : MinimalNormals N)
    (proper : ((MulAction.stabilizer G a).comap (normalCoordinateEmbedding N
      (normal_subgroup_radicalFree radicalFree N) (minimalNormal_socle_eq_top hN))).map
        (Pi.evalMonoidHom (fun M : MinimalNormals N => M.val) i) ≠ ⊤) :
    Nat.card V = ∏ j : MinimalNormals N,
      (((MulAction.stabilizer G a).comap (normalCoordinateEmbedding N
        (normal_subgroup_radicalFree radicalFree N) (minimalNormal_socle_eq_top hN))).map
          (Pi.evalMonoidHom (fun M : MinimalNormals N => M.val) j)).index := by
  rw [Nat.card_congr (primitiveMinimalProductCoordinates radicalFree N hN a i proper),
    Nat.card_pi]
  rfl

end GI.PrimitiveCartesian
