module

public import Workspace.JohnsonAction
public import Workspace.NaturalGiantCentralizer

@[expose] public section

namespace GI.Pairs

open Equiv Equiv.Perm
open scoped Pointwise

variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev OrderedPair (α : Type*) := {p : α × α // p.1 ≠ p.2}

def orderedAction : Perm α →* Perm (OrderedPair α) where
  toFun g :=
    { toFun p := ⟨(g p.1.1, g p.1.2), g.injective.ne p.2⟩
      invFun p := ⟨(g⁻¹ p.1.1, g⁻¹ p.1.2), g.symm.injective.ne p.2⟩
      left_inv p := by apply Subtype.ext; simp
      right_inv p := by apply Subtype.ext; simp }
  map_one' := by ext p <;> rfl
  map_mul' _ _ := by ext p <;> rfl

instance orderedMulAction : MulAction (alternatingGroup α) (OrderedPair α) :=
  MulAction.compHom _ (orderedAction.comp (alternatingGroup α).subtype)

instance unorderedMulAction : MulAction (alternatingGroup α) (GI.Johnson.SubsetVertex α 2) :=
  MulAction.compHom _ ((GI.Johnson.subsetAction 2).comp (alternatingGroup α).subtype)

theorem exists_even_pair_map (h4 : 4 ≤ Fintype.card α) {a b c d : α}
    (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ g : alternatingGroup α, (g : Perm α) a = c ∧ (g : Perm α) b = d := by
  let s : Perm α := swap a c
  let t : Perm α := swap (s b) d * s
  have hsb : s b ≠ c := by
    have ha : s a = c := by simp [s]
    rw [← ha]
    exact s.injective.ne hab.symm
  have hta : t a = c := by
    simp [t, s, mul_apply, swap_apply_of_ne_of_ne hsb.symm hcd]
  have htb : t b = d := by simp [t, mul_apply]
  obtain ⟨u, hu⟩ := GI.NaturalGiant.exists_outside ({c, d} : Finset α)
    (by have h := Finset.card_le_two (a := c) (b := d); omega)
  obtain ⟨v, hv⟩ := GI.NaturalGiant.exists_outside ({c, d, u} : Finset α)
    (by have h := Finset.card_le_three (a := c) (b := d) (c := u); omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu hv
  by_cases ht : sign t = 1
  · exact ⟨⟨t, ht⟩, hta, htb⟩
  · have hsign : sign t = -1 := (Int.units_eq_one_or (sign t)).resolve_left ht
    refine ⟨⟨swap u v * t, ?_⟩, ?_, ?_⟩
    · rw [mem_alternatingGroup, sign_mul, sign_swap (Ne.symm hv.2.2), hsign]
      simp
    · simp [mul_apply, hta, swap_apply_of_ne_of_ne (Ne.symm hu.1) (Ne.symm hv.1)]
    · simp [mul_apply, htb, swap_apply_of_ne_of_ne (Ne.symm hu.2) (Ne.symm hv.2.1)]

theorem ordered_transitive (h4 : 4 ≤ Fintype.card α) (x y : OrderedPair α) :
    ∃ g : alternatingGroup α, g • x = y := by
  obtain ⟨g, hg₁, hg₂⟩ := exists_even_pair_map h4 x.2 y.2
  refine ⟨g, Subtype.ext ?_⟩
  exact Prod.ext hg₁ hg₂

def unorderedOfOrdered (x : OrderedPair α) : GI.Johnson.SubsetVertex α 2 :=
  ⟨{x.1.1, x.1.2}, Finset.card_pair x.2⟩

omit [Fintype α] in
theorem unorderedOfOrdered_surjective :
    Function.Surjective (unorderedOfOrdered (α := α)) := by
  intro s
  obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp s.2
  exact ⟨⟨(a, b), hab⟩, Subtype.ext hs.symm⟩

theorem unorderedOfOrdered_equivariant (g : alternatingGroup α) (x : OrderedPair α) :
    unorderedOfOrdered (g • x) = g • unorderedOfOrdered x := by
  apply Subtype.ext
  change {g.val x.val.1, g.val x.val.2} = g.val • ({x.val.1, x.val.2} : Finset α)
  simp [Finset.smul_finset_def]

theorem unordered_transitive (h4 : 4 ≤ Fintype.card α)
    (x y : GI.Johnson.SubsetVertex α 2) : ∃ g : alternatingGroup α, g • x = y := by
  obtain ⟨u, rfl⟩ := unorderedOfOrdered_surjective x
  obtain ⟨v, rfl⟩ := unorderedOfOrdered_surjective y
  obtain ⟨g, hg⟩ := ordered_transitive h4 u v
  exact ⟨g, by rw [← unorderedOfOrdered_equivariant, hg]⟩

end GI.Pairs
