import Workspace.RectangleQueries
import Workspace.TransportOutput

namespace GI.Rectangle

variable {α G V C : Type*} [Fintype α] [DecidableEq α] [Group G] [MulAction G V]
variable {φ : G →* alternatingGroup α} {W R : Finset α}

/-- Transform a certified full answer from one physical string query into a
certified full matrix answer. This does not supply the recursive string solver. -/
noncomputable def orderedOutput
    (f : StabilizerQuotient.KernelQuotient φ V (Pairs.OrderedPair α))
    (onto : Function.Surjective φ) (hd : Disjoint W R) {x y : W × R → C} :
    TransportOutput.Answer (orderedPhysicalAction f hd).range
      (x ∘ orderedMap f hd) (y ∘ orderedMap f hd) →
        TransportOutput.Answer (rectangleAction (W := W) (R := R)).range x y :=
  TransportOutput.projectAnswer (orderedProjection f hd)
    (EmbeddedQuotient.permittedProjection_onto f (orderedEmbedding hd) (permitted W R)
      rectangleAction (orderedEmbedding_move hd) onto)
    (orderedMap f hd) (EmbeddedQuotient.map_onto f (orderedEmbedding hd))
    (EmbeddedQuotient.permittedProjection_equivariant f (orderedEmbedding hd)
      (permitted W R) rectangleAction (orderedEmbedding_move hd))

noncomputable def unorderedOutput
    (f : StabilizerQuotient.KernelQuotient φ V (Johnson.SubsetVertex α 2))
    (onto : Function.Surjective φ) (hd : Disjoint W R) {x y : W × R → C} :
    TransportOutput.Answer (unorderedPhysicalAction f hd).range
      (x ∘ unorderedMap f hd) (y ∘ unorderedMap f hd) →
        TransportOutput.Answer (rectangleAction (W := W) (R := R)).range x y :=
  TransportOutput.projectAnswer (unorderedProjection f hd)
    (EmbeddedQuotient.permittedProjection_onto f (unorderedEmbedding hd) (permitted W R)
      rectangleAction (unorderedEmbedding_move hd) onto)
    (unorderedMap f hd) (EmbeddedQuotient.map_onto f (unorderedEmbedding hd))
    (EmbeddedQuotient.permittedProjection_equivariant f (unorderedEmbedding hd)
      (permitted W R) rectangleAction (unorderedEmbedding_move hd))

theorem ordered_strings_constant_on_fibers
    (f : StabilizerQuotient.KernelQuotient φ V (Pairs.OrderedPair α))
    (hd : Disjoint W R) (x : W × R → C) (u v : OrderedPhysical f hd)
    (heq : f.map u.val = f.map v.val) :
    (x ∘ orderedMap f hd) u = (x ∘ orderedMap f hd) v := by
  apply congrArg x
  apply (orderedEmbedding hd).injective
  simpa only [orderedMap, EmbeddedQuotient.embed_map] using heq

theorem unordered_strings_constant_on_fibers
    (f : StabilizerQuotient.KernelQuotient φ V (Johnson.SubsetVertex α 2))
    (hd : Disjoint W R) (x : W × R → C) (u v : UnorderedPhysical f hd)
    (heq : f.map u.val = f.map v.val) :
    (x ∘ unorderedMap f hd) u = (x ∘ unorderedMap f hd) v := by
  apply congrArg x
  apply (unorderedEmbedding hd).injective
  simpa only [unorderedMap, EmbeddedQuotient.embed_map] using heq

end GI.Rectangle
