import Workspace.CoherentSaturatedRelations

namespace GI.CoherentEntrance

open GI.PairRefinement

variable {n : ℕ}

theorem saturated_color_count (c : Coloring n) (hc : Coherent c)
    (side : Bool) (hh : Homogeneous c side) {R : Fin n → Fin n → Prop}
    [DecidableRel R] (hR : ColorSaturated c side R) (x y : Fin n) (k : Color n) :
    (Finset.univ.filter (fun z => R x z ∧ c (side, x, z) = k)).card =
      (Finset.univ.filter (fun z => R y z ∧ c (side, y, z) = k)).card := by
  classical
  by_cases h : ∃ a b, c (side, a, b) = k ∧ R a b
  · obtain ⟨a, b, hab, hRab⟩ := h
    have hf (t : Fin n) :
        Finset.univ.filter (fun z => R t z ∧ c (side, t, z) = k) =
          Finset.univ.filter (fun z => c (side, t, z) = k) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact And.right
      · intro hz
        exact ⟨hR a b t z (hab.trans hz.symm) hRab, hz⟩
    rw [hf x, hf y]
    subst k
    exact rowValency_constant c hc side hh a b x y
  · have hf (t : Fin n) :
        Finset.univ.filter (fun z => R t z ∧ c (side, t, z) = k) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      have hz' := (Finset.mem_filter.mp hz).2
      exact h ⟨t, z, hz'.2, hz'.1⟩
    rw [hf x, hf y]

theorem saturated_row_card_eq (c : Coloring n) (hc : Coherent c)
    (side : Bool) (hh : Homogeneous c side) {R : Fin n → Fin n → Prop}
    [DecidableRel R] (hR : ColorSaturated c side R) (x y : Fin n) :
    (Finset.univ.filter (R x)).card = (Finset.univ.filter (R y)).card := by
  have hs (t : Fin n) :
      (Finset.univ.filter (R t)).card =
        ∑ k : Color n, (Finset.univ.filter (fun z => R t z ∧ c (side, t, z) = k)).card := by
    have h := Finset.card_eq_sum_card_fiberwise
      (f := fun z => c (side, t, z)) (s := Finset.univ.filter (R t))
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
    simpa only [Finset.filter_filter] using h
  rw [hs x, hs y]
  apply Finset.sum_congr rfl
  intro k _
  exact saturated_color_count c hc side hh hR x y k

noncomputable def colorComponent (c : Coloring n) (side : Bool)
    (k : Color n) (x : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (colorReach c side k x)

theorem mem_colorComponent (c : Coloring n) (side : Bool) (k : Color n) (x y : Fin n) :
    y ∈ colorComponent c side k x ↔ colorReach c side k x y := by
  classical
  simp [colorComponent]

theorem colorComponent_card_eq (c : Coloring n) (hc : Coherent c)
    (side : Bool) (hh : Homogeneous c side) (k : Color n) (x y : Fin n) :
    (colorComponent c side k x).card = (colorComponent c side k y).card := by
  classical
  exact saturated_row_card_eq c hc side hh (colorReach_saturated c hc side k) x y

theorem colorComponent_disjoint (c : Coloring n) (side : Bool) (k : Color n)
    (x y : Fin n) (hxy : ¬ colorReach c side k x y) :
    Disjoint (colorComponent c side k x) (colorComponent c side k y) := by
  apply Finset.disjoint_left.mpr
  intro z hx hy
  have he := colorReach_equivalence c side k
  exact hxy (he.trans ((mem_colorComponent c side k x z).mp hx)
    (he.symm ((mem_colorComponent c side k y z).mp hy)))

theorem colorComponent_half (c : Coloring n) (hc : Coherent c)
    (side : Bool) (hh : Homogeneous c side) (k : Color n)
    (a b : Fin n) (hab : ¬ colorReach c side k a b) (x : Fin n) :
    2 * (colorComponent c side k x).card ≤ n := by
  have hd := colorComponent_disjoint c side k a b hab
  have hsum : (colorComponent c side k a).card +
      (colorComponent c side k b).card ≤ n := by
    rw [← Finset.card_union_of_disjoint hd]
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
  rw [colorComponent_card_eq c hc side hh k a x,
    colorComponent_card_eq c hc side hh k b x] at hsum
  omega

theorem colorComponent_nontrivial (c : Coloring n) (hc : Coherent c)
    (side : Bool) (hh : Homogeneous c side) (a b : Fin n) (hab : a ≠ b)
    (x : Fin n) : 2 ≤ (colorComponent c side (c (side, a, b)) x).card := by
  have hp := rowValency_positive c hc side hh a b x
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hp
  have he := (Finset.mem_filter.mp hy).2
  have hxy : x ≠ y := by
    intro h
    subst y
    exact offDiagonal_loop_ne c hc side a b x hab he
  apply Nat.succ_le_of_lt
  apply Finset.one_lt_card.mpr
  refine ⟨x, ?_, y, ?_, hxy⟩
  · exact (mem_colorComponent c side _ x x).mpr Relation.ReflTransGen.refl
  · exact (mem_colorComponent c side _ x y).mpr (Relation.ReflTransGen.single (Or.inl he))

theorem colorReach_stays_in_cut (c : Coloring n) (side : Bool) (k : Color n)
    (S : Finset (Fin n))
    (hcut : ∀ u ∈ S, ∀ v ∉ S, ¬ colorEdge c side k u v)
    {x y : Fin n} (hx : x ∈ S) (hxy : colorReach c side k x y) : y ∈ S := by
  induction hxy with
  | refl => exact hx
  | @tail b d _ hbd ih =>
    by_contra hd
    exact hcut b ih d hd hbd

end GI.CoherentEntrance

#print axioms GI.CoherentEntrance.saturated_row_card_eq
#print axioms GI.CoherentEntrance.colorComponent_card_eq
#print axioms GI.CoherentEntrance.colorComponent_half
#print axioms GI.CoherentEntrance.colorComponent_nontrivial
#print axioms GI.CoherentEntrance.colorReach_stays_in_cut
