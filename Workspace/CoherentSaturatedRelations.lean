module

public import Workspace.CoherentDominantWitness
public import Mathlib.Logic.Relation

@[expose] public section

namespace GI.CoherentEntrance

open GI.PairRefinement

variable {n : ℕ}

/-- A relation is a union of actual pair colors on the selected side. -/
def ColorSaturated (c : Coloring n) (side : Bool) (R : Fin n → Fin n → Prop) : Prop :=
  ∀ a b x y, c (side, a, b) = c (side, x, y) → R a b → R x y

theorem coherent_middle_witness (c : Coloring n) (hc : Coherent c)
    (side : Bool) (a b d x y : Fin n)
    (he : c (side, a, b) = c (side, x, y)) :
    ∃ z, c (side, a, d) = c (side, x, z) ∧
      c (side, d, b) = c (side, z, y) := by
  have hpos : 0 < intersection c (side, a, b)
      (c (side, a, d)) (c (side, d, b)) :=
    Finset.card_pos.mpr ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, rfl⟩⟩
  rw [(hc (side, a, b) (side, x, y) he).2.2] at hpos
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
  exact ⟨z, (Finset.mem_filter.mp hz).2.1.symm,
    (Finset.mem_filter.mp hz).2.2.symm⟩

theorem colorSaturated_eq (c : Coloring n) (hc : Coherent c) (side : Bool) :
    ColorSaturated c side Eq := by
  intro a b x y he hab
  subst b
  have hd := (hc (side, a, a) (side, x, y) he).1
  simpa [GI.PairRefinement.diagonal] using hd.symm

theorem colorSaturated_comp (c : Coloring n) (hc : Coherent c) (side : Bool)
    {R S : Fin n → Fin n → Prop} (hR : ColorSaturated c side R)
    (hS : ColorSaturated c side S) :
    ColorSaturated c side (fun a b => ∃ d, R a d ∧ S d b) := by
  rintro a b x y he ⟨d, hd, hb⟩
  obtain ⟨z, hz, hz'⟩ := coherent_middle_witness c hc side a b d x y he
  exact ⟨z, hR a d x z hz hd, hS d b z y hz' hb⟩

theorem colorSaturated_reflTransGen (c : Coloring n) (hc : Coherent c)
    (side : Bool) {R : Fin n → Fin n → Prop} (hR : ColorSaturated c side R) :
    ColorSaturated c side (Relation.ReflTransGen R) := by
  intro a b x y he hab
  induction hab generalizing x y with
  | refl =>
    have hxy := colorSaturated_eq c hc side a a x y he rfl
    subst y
    exact Relation.ReflTransGen.refl
  | @tail b d hab hbd ih =>
    obtain ⟨z, hz, hz'⟩ := coherent_middle_witness c hc side a d b x y he
    exact (ih x z hz).tail (hR b d z y hz' hbd)

def colorEdge (c : Coloring n) (side : Bool) (k : Color n) (x y : Fin n) : Prop :=
  c (side, x, y) = k ∨ c (side, y, x) = k

theorem colorEdge_saturated (c : Coloring n) (hc : Coherent c)
    (side : Bool) (k : Color n) : ColorSaturated c side (colorEdge c side k) := by
  intro a b x y he hedge
  rcases hedge with h | h
  · exact Or.inl (he.symm.trans h)
  · exact Or.inr (((hc (side, a, b) (side, x, y) he).2.1).symm.trans h)

def colorReach (c : Coloring n) (side : Bool) (k : Color n) : Fin n → Fin n → Prop :=
  Relation.ReflTransGen (colorEdge c side k)

theorem colorReach_saturated (c : Coloring n) (hc : Coherent c)
    (side : Bool) (k : Color n) : ColorSaturated c side (colorReach c side k) :=
  colorSaturated_reflTransGen c hc side (colorEdge_saturated c hc side k)

theorem colorReach_equivalence (c : Coloring n) (side : Bool) (k : Color n) :
    Equivalence (colorReach c side k) where
  refl _ := Relation.ReflTransGen.refl
  symm := by
    intro x y h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hedge ih => exact Relation.ReflTransGen.head (Or.symm hedge) ih
  trans := Relation.ReflTransGen.trans

end GI.CoherentEntrance
