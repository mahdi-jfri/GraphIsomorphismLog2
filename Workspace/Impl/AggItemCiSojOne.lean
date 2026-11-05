module

public import Workspace.Impl.AggItemCiSojChoice
public import Workspace.Impl.AggItemCiSojPrim

@[expose] public section

/-!
# Testing component sizes at one source vertex

The components of a color in a homogeneous coherent configuration all have the
same size. Thus the imprimitive-pair test needs one component count. Connectivity
also needs one count: the component at the fixed source vertex has the whole
fiber precisely when the color graph is connected.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.CoherentEntrance GI.PairRefinement Equiv Finset

variable {q : ℕ}

/-- The size computed from the raw component labels is the encoded fiber component size. -/
theorem itcs_component_size (X : PairCfg q) (a b x : Fin X.fiber.card) :
    itpSz (itcsLab X (X.col (X.emb rfl a) (X.emb rfl b))) (X.emb rfl x) =
      (colorComponent X.coloring false (X.coloring (false, a, b)) x).card := by
  change (itpBlk _ _).card = _
  rw [itcs_lab_blk, X.comp_emb (X.col_mem_vals a b) false x, Finset.card_map]
  rfl

/-- In any finite undirected color graph, one full component means all points connect. -/
theorem itcs_connected_one {n : ℕ} (c : Coloring n) (side : Bool) (k : Color n) (x₀ : Fin n) :
    (∀ x y, colorReach c side k x y) ↔ (colorComponent c side k x₀).card = n := by
  classical
  constructor
  · intro h
    have he : colorComponent c side k x₀ = univ := by
      ext y
      simp only [mem_colorComponent, mem_univ, iff_true]
      exact h x₀ y
    rw [he, card_univ, Fintype.card_fin]
  · intro h
    have he : colorComponent c side k x₀ = univ :=
      Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
        (by simpa only [card_univ, Fintype.card_fin] using h.ge)
    have reach (y : Fin n) : colorReach c side k x₀ y :=
      (mem_colorComponent _ _ _ _ _).1 (by rw [he]; exact mem_univ y)
    intro x y
    exact (colorReach_equivalence c side k).trans
      ((colorReach_equivalence c side k).symm (reach x)) (reach y)

/-- Exact primitivity test using one component count per off-diagonal pair. -/
theorem itcs_primitive_one (X : PairCfg q) {x₀ : Fin q} (hx : x₀ ∈ X.fiber) :
    PrimitiveColorCuts X.coloring false ↔
      ∀ a b : Fin X.fiber.card, a ≠ b →
        itpSz (itcsLab X (X.col (X.emb rfl a) (X.emb rfl b))) x₀ = X.fiber.card := by
  rw [itcs_cuts_iff]
  have he : x₀ = X.emb rfl (X.idx hx) := (X.emb_idx hx).symm
  constructor
  · intro h a b hab
    rw [he, itcs_component_size]
    exact (itcs_connected_one X.coloring false _ (X.idx hx)).1 (h a b hab)
  · intro h a b hab
    apply (itcs_connected_one X.coloring false _ (X.idx hx)).2
    rw [← itcs_component_size, ← he]
    exact h a b hab

/-- Coherence and homogeneity make all components of an off-diagonal color equally
large. The lower bound of two is automatic for that color. -/
theorem itcs_imp_one (X : PairCfg q) (hX : X.Good deltaB) {x₀ : Fin q} (hx : x₀ ∈ X.fiber)
    (a b : Fin X.fiber.card) :
    ImpPair X a b ↔ a ≠ b ∧
      2 * itpSz (itcsLab X (X.col (X.emb rfl a) (X.emb rfl b))) x₀ ≤ X.fiber.card := by
  have he : x₀ = X.emb rfl (X.idx hx) := (X.emb_idx hx).symm
  rw [he, itcs_component_size]
  constructor
  · intro h
    exact ⟨h.1, (h.2 (X.idx hx)).2⟩
  · rintro ⟨hab, hbound⟩
    refine ⟨hab, fun x => ⟨?_, ?_⟩⟩
    · exact colorComponent_nontrivial X.coloring (PairCfg.coloring_coherent hX) false
        (X.coloring_homogeneous false) a b hab x
    · rw [colorComponent_card_eq X.coloring (PairCfg.coloring_coherent hX) false
        (X.coloring_homogeneous false) _ x (X.idx hx)]
      exact hbound

end GI.Impl
