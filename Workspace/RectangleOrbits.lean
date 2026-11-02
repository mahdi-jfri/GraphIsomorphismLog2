import Workspace.RectangleActions
import Workspace.PairCardinalities

namespace GI.Rectangle

open Equiv Equiv.Perm

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {W R : Finset α}

def orderedEmbedding (hd : Disjoint W R) : (W × R) ↪ GI.Pairs.OrderedPair α where
  toFun p := ⟨(p.1.val, p.2.val), cross_ne hd p.1.property p.2.property⟩
  inj' _ _ h := Prod.ext (Subtype.ext (congrArg (fun z => z.val.1) h))
    (Subtype.ext (congrArg (fun z => z.val.2) h))

def unorderedEmbedding (hd : Disjoint W R) : (W × R) ↪ GI.Johnson.SubsetVertex α 2 where
  toFun p := GI.Pairs.unorderedOfOrdered (orderedEmbedding hd p)
  inj' p q h := by
    have hs := congrArg (fun z : GI.Johnson.SubsetVertex α 2 => (z.val : Set α)) h
    simp only [GI.Pairs.unorderedOfOrdered, orderedEmbedding,
      Finset.coe_pair, Function.Embedding.coeFn_mk] at hs
    rcases Set.pair_eq_pair_iff.mp hs with hstraight | hswapped
    · exact Prod.ext (Subtype.ext hstraight.1) (Subtype.ext hstraight.2)
    · exact (cross_ne hd p.1.property q.2.property hswapped.1).elim

def orderedRectangle (hd : Disjoint W R) : Set (GI.Pairs.OrderedPair α) :=
  Set.range (orderedEmbedding hd)

def unorderedRectangle (hd : Disjoint W R) : Set (GI.Johnson.SubsetVertex α 2) :=
  Set.range (unorderedEmbedding hd)

def movePoint (g : permitted W R) (p : W × R) : W × R :=
  (⟨(g.val : Perm α) p.1, (left_mem_iff W R g p.1).mpr p.1.property⟩,
   ⟨(g.val : Perm α) p.2, (right_mem_iff W R g p.2).mpr p.2.property⟩)

theorem orderedEmbedding_move (hd : Disjoint W R) (g : permitted W R) (p : W × R) :
    orderedEmbedding hd (movePoint g p) = g.val • orderedEmbedding hd p := rfl

theorem unorderedEmbedding_move (hd : Disjoint W R) (g : permitted W R) (p : W × R) :
    unorderedEmbedding hd (movePoint g p) = g.val • unorderedEmbedding hd p :=
  GI.Pairs.unorderedOfOrdered_equivariant g.val (orderedEmbedding hd p)

def rectangleAction : permitted W R →* Perm (W × R) where
  toFun g :=
    { toFun := movePoint g
      invFun := movePoint g⁻¹
      left_inv p := by apply Prod.ext <;> apply Subtype.ext <;> simp [movePoint]
      right_inv p := by apply Prod.ext <;> apply Subtype.ext <;> simp [movePoint] }
  map_one' := by ext p <;> rfl
  map_mul' _ _ := by ext p <;> rfl

theorem orderedRectangle_preserved (hd : Disjoint W R) (g : permitted W R)
    (x : GI.Pairs.OrderedPair α) (hx : x ∈ orderedRectangle hd) :
    g.val • x ∈ orderedRectangle hd := by
  obtain ⟨p, rfl⟩ := hx
  exact ⟨movePoint g p, orderedEmbedding_move hd g p⟩

theorem unorderedRectangle_preserved (hd : Disjoint W R) (g : permitted W R)
    (x : GI.Johnson.SubsetVertex α 2) (hx : x ∈ unorderedRectangle hd) :
    g.val • x ∈ unorderedRectangle hd := by
  obtain ⟨p, rfl⟩ := hx
  exact ⟨movePoint g p, unorderedEmbedding_move hd g p⟩

theorem orderedRectangle_transitive (hd : Disjoint W R) (hW : 3 ≤ W.card)
    (x : GI.Pairs.OrderedPair α) (hx : x ∈ orderedRectangle hd)
    (y : GI.Pairs.OrderedPair α) (hy : y ∈ orderedRectangle hd) :
    ∃ g : permitted W R, g.val • x = y := by
  obtain ⟨p, rfl⟩ := hx
  obtain ⟨q, rfl⟩ := hy
  obtain ⟨g, hg₁, hg₂⟩ := exists_permitted_pair_map hd hW p.1.property q.1.property
    p.2.property q.2.property
  exact ⟨g, Subtype.ext (Prod.ext hg₁ hg₂)⟩

theorem unorderedRectangle_transitive (hd : Disjoint W R) (hW : 3 ≤ W.card)
    (x : GI.Johnson.SubsetVertex α 2) (hx : x ∈ unorderedRectangle hd)
    (y : GI.Johnson.SubsetVertex α 2) (hy : y ∈ unorderedRectangle hd) :
    ∃ g : permitted W R, g.val • x = y := by
  obtain ⟨p, rfl⟩ := hx
  obtain ⟨q, rfl⟩ := hy
  obtain ⟨g, hg⟩ := orderedRectangle_transitive hd hW
    (orderedEmbedding hd p) ⟨p, rfl⟩ (orderedEmbedding hd q) ⟨q, rfl⟩
  refine ⟨g, ?_⟩
  change g.val • GI.Pairs.unorderedOfOrdered (orderedEmbedding hd p) =
    GI.Pairs.unorderedOfOrdered (orderedEmbedding hd q)
  rw [← GI.Pairs.unorderedOfOrdered_equivariant, hg]

omit [Fintype α] [DecidableEq α] in
theorem card_orderedRectangle (hd : Disjoint W R) :
    Nat.card (orderedRectangle hd) = W.card * R.card := by
  have h := Nat.card_congr (Equiv.ofInjective (orderedEmbedding hd) (orderedEmbedding hd).injective)
  calc
    Nat.card (orderedRectangle hd) = Nat.card (W × R) := h.symm
    _ = _ := by simp [Nat.card_eq_fintype_card]

omit [Fintype α] in
theorem card_unorderedRectangle (hd : Disjoint W R) :
    Nat.card (unorderedRectangle hd) = W.card * R.card := by
  have h := Nat.card_congr (Equiv.ofInjective (unorderedEmbedding hd) (unorderedEmbedding hd).injective)
  calc
    Nat.card (unorderedRectangle hd) = Nat.card (W × R) := h.symm
    _ = _ := by simp [Nat.card_eq_fintype_card]

end GI.Rectangle
