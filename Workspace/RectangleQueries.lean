module

public import Workspace.PhysicalRectangles
public import Workspace.EmbeddedTransport
public import Workspace.EmbeddedBudget

@[expose] public section

namespace GI.Rectangle

variable {α G V C : Type*} [Fintype α] [DecidableEq α] [Group G] [MulAction G V]
variable {φ : G →* alternatingGroup α} {W R : Finset α}

abbrev OrderedPhysical
    (f : StabilizerQuotient.KernelQuotient φ V (Pairs.OrderedPair α))
    (hd : Disjoint W R) := EmbeddedQuotient.Physical f (orderedEmbedding hd)

abbrev UnorderedPhysical
    (f : StabilizerQuotient.KernelQuotient φ V (Johnson.SubsetVertex α 2))
    (hd : Disjoint W R) := EmbeddedQuotient.Physical f (unorderedEmbedding hd)

def orderedPhysicalAction
    (f : StabilizerQuotient.KernelQuotient φ V (Pairs.OrderedPair α))
    (hd : Disjoint W R) : (permitted W R).comap φ →* Equiv.Perm (OrderedPhysical f hd) :=
  EmbeddedQuotient.action f (orderedEmbedding hd) (permitted W R) rectangleAction
    (orderedEmbedding_move hd)

def unorderedPhysicalAction
    (f : StabilizerQuotient.KernelQuotient φ V (Johnson.SubsetVertex α 2))
    (hd : Disjoint W R) : (permitted W R).comap φ →* Equiv.Perm (UnorderedPhysical f hd) :=
  EmbeddedQuotient.action f (unorderedEmbedding hd) (permitted W R) rectangleAction
    (unorderedEmbedding_move hd)

noncomputable abbrev orderedMap
    (f : StabilizerQuotient.KernelQuotient φ V (Pairs.OrderedPair α))
    (hd : Disjoint W R) := EmbeddedQuotient.map f (orderedEmbedding hd)

noncomputable abbrev unorderedMap
    (f : StabilizerQuotient.KernelQuotient φ V (Johnson.SubsetVertex α 2))
    (hd : Disjoint W R) := EmbeddedQuotient.map f (unorderedEmbedding hd)

noncomputable def orderedProjection
    (f : StabilizerQuotient.KernelQuotient φ V (Pairs.OrderedPair α))
    (hd : Disjoint W R) : (orderedPhysicalAction f hd).range →*
      (rectangleAction (W := W) (R := R)).range :=
  EmbeddedQuotient.permittedProjection f (orderedEmbedding hd) (permitted W R)
    rectangleAction (orderedEmbedding_move hd)

noncomputable def unorderedProjection
    (f : StabilizerQuotient.KernelQuotient φ V (Johnson.SubsetVertex α 2))
    (hd : Disjoint W R) : (unorderedPhysicalAction f hd).range →*
      (rectangleAction (W := W) (R := R)).range :=
  EmbeddedQuotient.permittedProjection f (unorderedEmbedding hd) (permitted W R)
    rectangleAction (unorderedEmbedding_move hd)

theorem ordered_exact_query
    (f : StabilizerQuotient.KernelQuotient φ V (Pairs.OrderedPair α))
    (onto : Function.Surjective φ) (hd : Disjoint W R) (x y : W × R → C) :
    orderedProjection f hd ''
      {p : (orderedPhysicalAction f hd).range |
        Transports (x ∘ orderedMap f hd) (y ∘ orderedMap f hd) p.val} =
      {q : (rectangleAction (W := W) (R := R)).range | Transports x y q.val} :=
  EmbeddedQuotient.exact_permitted_transporter f (orderedEmbedding hd) (permitted W R)
    rectangleAction (orderedEmbedding_move hd) onto x y

theorem unordered_exact_query
    (f : StabilizerQuotient.KernelQuotient φ V (Johnson.SubsetVertex α 2))
    (onto : Function.Surjective φ) (hd : Disjoint W R) (x y : W × R → C) :
    unorderedProjection f hd ''
      {p : (unorderedPhysicalAction f hd).range |
        Transports (x ∘ unorderedMap f hd) (y ∘ unorderedMap f hd) p.val} =
      {q : (rectangleAction (W := W) (R := R)).range | Transports x y q.val} :=
  EmbeddedQuotient.exact_permitted_transporter f (unorderedEmbedding hd) (permitted W R)
    rectangleAction (unorderedEmbedding_move hd) onto x y

section Budget

variable {Ω : Type*} [Fintype Ω] {K : Subgroup (Equiv.Perm Ω)}
variable {ψ : K →* alternatingGroup α}

theorem ordered_query_budget
    (f : StabilizerQuotient.KernelQuotient ψ Ω (Pairs.OrderedPair α))
    (hd : Disjoint W R) [Fintype (OrderedPhysical f hd)]
    {cutoff : ℕ} (hcutoff : 5 ≤ cutoff) (x : OrderedPhysical f hd) :
    sigma cutoff x (orderedPhysicalAction f hd).range ≤ sigma cutoff x.val K :=
  EmbeddedQuotient.physical_budget_le K ψ (permitted W R) f (orderedEmbedding hd)
    rectangleAction (orderedEmbedding_move hd) hcutoff x

theorem unordered_query_budget
    (f : StabilizerQuotient.KernelQuotient ψ Ω (Johnson.SubsetVertex α 2))
    (hd : Disjoint W R) [Fintype (UnorderedPhysical f hd)]
    {cutoff : ℕ} (hcutoff : 5 ≤ cutoff) (x : UnorderedPhysical f hd) :
    sigma cutoff x (unorderedPhysicalAction f hd).range ≤ sigma cutoff x.val K :=
  EmbeddedQuotient.physical_budget_le K ψ (permitted W R) f (unorderedEmbedding hd)
    rectangleAction (unorderedEmbedding_move hd) hcutoff x

end Budget

end GI.Rectangle
