module

public import Workspace.PrimitiveCoordinateFibers
public import Workspace.UniformFiberCoordinates

@[expose] public section

namespace GI.PrimitiveCartesian

open GI.RadicalSocle

variable {G V : Type*} [Group G] [Finite G] [MulAction G V]
  [FaithfulSMul G V] [Nontrivial V] [MulAction.IsPreprimitive G V]

noncomputable def primitiveUniformCoordinates
    (radicalFree : ∀ K : Subgroup G, K.Normal → IsSolvable K → K = ⊥)
    (N : Subgroup G) [N.Normal] (hN : MinimalNormal N) (a : V) (i : MinimalNormals N)
    (proper : ((MulAction.stabilizer G a).comap
      (minimalCoordinateEmbedding radicalFree N hN)).map
        (Pi.evalMonoidHom (fun M : MinimalNormals N => M.val) i) ≠ ⊤) :
    V ≃ (MinimalNormals N → i.val ⧸
      (((MulAction.stabilizer G a).comap (minimalCoordinateEmbedding radicalFree N hN)).map
        (Pi.evalMonoidHom (fun M : MinimalNormals N => M.val) i))) :=
  CartesianCoordinates.uniformCoordinates
    (primitiveMinimalProductCoordinates radicalFree N hN a i proper a)
    (primitiveMinimalProductCoordinates radicalFree N hN a i proper)
    (normalFactorPositions N)
    (primitive_minimalNormal_fiber_transport radicalFree N hN a i proper)
    (normalFactorPositions_transitive radicalFree N hN) i

theorem primitiveUniformCoordinates_fibers
    (radicalFree : ∀ K : Subgroup G, K.Normal → IsSolvable K → K = ⊥)
    (N : Subgroup G) [N.Normal] (hN : MinimalNormal N) (a : V) (i : MinimalNormals N)
    (proper : ((MulAction.stabilizer G a).comap
      (minimalCoordinateEmbedding radicalFree N hN)).map
        (Pi.evalMonoidHom (fun M : MinimalNormals N => M.val) i) ≠ ⊤)
    (g : G) (j : MinimalNormals N) (v w : V)
    (hvw : primitiveUniformCoordinates radicalFree N hN a i proper v j =
      primitiveUniformCoordinates radicalFree N hN a i proper w j) :
    primitiveUniformCoordinates radicalFree N hN a i proper (g • v)
        (normalFactorPositions N g j) =
      primitiveUniformCoordinates radicalFree N hN a i proper (g • w)
        (normalFactorPositions N g j) :=
  CartesianCoordinates.uniformCoordinates_fibers _ _ _ _ _ _ g j v w hvw

theorem primitive_uniform_degree
    (radicalFree : ∀ K : Subgroup G, K.Normal → IsSolvable K → K = ⊥)
    (N : Subgroup G) [N.Normal] (hN : MinimalNormal N) (a : V) (i : MinimalNormals N)
    (proper : ((MulAction.stabilizer G a).comap
      (minimalCoordinateEmbedding radicalFree N hN)).map
        (Pi.evalMonoidHom (fun M : MinimalNormals N => M.val) i) ≠ ⊤) :
    Nat.card V =
      (((MulAction.stabilizer G a).comap (minimalCoordinateEmbedding radicalFree N hN)).map
        (Pi.evalMonoidHom (fun M : MinimalNormals N => M.val) i)).index ^
          Nat.card (MinimalNormals N) := by
  rw [Nat.card_congr (primitiveUniformCoordinates radicalFree N hN a i proper), Nat.card_fun]
  rfl

end GI.PrimitiveCartesian
