module

public import Workspace.Impl.AggItemCiSojEdge

@[expose] public section

/-!
# The primitive-cut test as connectivity of the component tables

We test each occurring off-diagonal color. Its graph is connected precisely when
its component labels all agree on the fiber. This tests the literal cut predicate
of the model without enumerating subsets.
-/

namespace GI.Impl

open GI.Algorithm GI.CoherentEntrance GI.PairRefinement GI.Lang Equiv Finset

/-- A finite undirected color relation crosses every proper nonempty cut exactly
when every two vertices are connected. No coherence hypothesis is needed here. -/
theorem itcs_cuts_iff {n : ℕ} (c : Coloring n) (side : Bool) :
    PrimitiveColorCuts c side ↔ ∀ a b : Fin n, a ≠ b →
      ∀ x y, colorReach c side (c (side, a, b)) x y := by
  classical
  constructor
  · intro hp a b hab x y
    by_contra hxy
    let S := colorComponent c side (c (side, a, b)) x
    have hs : S.Nonempty := ⟨x, (mem_colorComponent _ _ _ _ _).2 Relation.ReflTransGen.refl⟩
    have hproper : S ≠ univ := by
      intro he
      have hy : y ∈ S := by rw [he]; exact mem_univ y
      exact hxy ((mem_colorComponent _ _ _ _ _).1 hy)
    obtain ⟨u, hu, v, hv, he⟩ := hp a b hab S hs hproper
    exact hv ((mem_colorComponent _ _ _ _ _).2
      (((mem_colorComponent _ _ _ _ _).1 hu).tail he))
  · intro h a b hab S hs hproper
    obtain ⟨x, hx⟩ := hs
    obtain ⟨y, hy⟩ : ∃ y, y ∉ S := by
      by_contra hno
      exact hproper (eq_univ_of_forall fun y => by by_contra hy; exact hno ⟨y, hy⟩)
    by_contra hcross
    have stay : ∀ z, colorReach c side (c (side, a, b)) x z → z ∈ S := by
      intro z hz
      induction hz with
      | refl => exact hx
      | @tail z w _ he ih =>
        by_contra hw
        exact hcross ⟨z, ih, w, hw, he⟩
    exact hy (stay y (h a b hab x y))

variable {q : ℕ}

/-- Pulling a component through the fiber embedding preserves reachability. -/
theorem itcs_emb_reach (X : PairCfg q) (a b x y : Fin X.fiber.card) :
    X.reach (X.col (X.emb rfl a) (X.emb rfl b)) (X.emb rfl x) (X.emb rfl y) ↔
      colorReach X.coloring false (X.coloring (false, a, b)) x y := by
  have he := X.comp_emb (X.col_mem_vals a b) false x
  change X.comp (X.col (X.emb rfl a) (X.emb rfl b)) (X.emb rfl x) =
    (colorComponent X.coloring false (X.coloring (false, a, b)) x).map (X.emb rfl) at he
  rw [← PairCfg.mem_comp, he]
  constructor
  · intro hy
    obtain ⟨z, hz, hzy⟩ := Finset.mem_map.1 hy
    have hzy := (X.emb rfl).injective hzy
    subst z
    exact (mem_colorComponent _ _ _ _ _).1 hz
  · intro hy
    exact Finset.mem_map_of_mem _ ((mem_colorComponent _ _ _ _ _).2 hy)

/-- The primitive-cut test is exactly a scan of the computed component labels. -/
theorem itcs_primitive_iff (X : PairCfg q) :
    PrimitiveColorCuts X.coloring false ↔
      ∀ a b : Fin X.fiber.card, a ≠ b → ∀ x y : Fin X.fiber.card,
        itcsLab X (X.col (X.emb rfl a) (X.emb rfl b)) (X.emb rfl x) =
          itcsLab X (X.col (X.emb rfl a) (X.emb rfl b)) (X.emb rfl y) := by
  rw [itcs_cuts_iff]
  constructor
  · intro h a b hab x y
    exact (itcs_lab_eq _ _ _ _).2 ((itcs_emb_reach X a b x y).2 (h a b hab x y))
  · intro h a b hab x y
    exact (itcs_emb_reach X a b x y).1 ((itcs_lab_eq _ _ _ _).1 (h a b hab x y))

end GI.Impl
