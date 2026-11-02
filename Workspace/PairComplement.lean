import Workspace.PairStabilizers

namespace GI.Pairs

open Equiv Equiv.Perm
attribute [local instance 2000] Subtype.fintype

variable {α : Type*} [Fintype α] [DecidableEq α]

def complementLabels (a b : α) : Finset α := Finset.univ \ {a, b}

theorem mem_complementLabels (a b x : α) : x ∈ complementLabels a b ↔ x ≠ a ∧ x ≠ b := by
  simp [complementLabels]

/-- The lower group appearing in IR1 is exactly the ordered-pair stabilizer.
This identifies the embedded alternating group on the complement explicitly. -/
theorem complement_alternating_range (a b : α) (hab : a ≠ b) :
    (GI.AlternatingSimple.extend (complementLabels a b)).range = pointwise a b hab := by
  ext g
  constructor
  · rintro ⟨p, rfl⟩
    apply (mem_pointwise a b hab _).mpr
    constructor
    · exact ofSubtype_apply_of_not_mem p.val (by simp [mem_complementLabels])
    · exact ofSubtype_apply_of_not_mem p.val (by simp [mem_complementLabels])
  · intro hg
    obtain ⟨ha, hb⟩ := (mem_pointwise a b hab g).mp hg
    have hpres : ∀ x : α, x ∈ complementLabels a b ↔ g.val x ∈ complementLabels a b := by
      intro x
      simp only [mem_complementLabels]
      have hxA : g.val x ≠ a ↔ x ≠ a := by
        simpa only [ha] using (g.val.injective.ne_iff : g.val x ≠ g.val a ↔ x ≠ a)
      have hxB : g.val x ≠ b ↔ x ≠ b := by
        simpa only [hb] using (g.val.injective.ne_iff : g.val x ≠ g.val b ↔ x ≠ b)
      rw [hxA, hxB]
    have hsupp : ∀ x : α, g.val x ≠ x → x ∈ complementLabels a b := by
      intro x hx
      rw [mem_complementLabels]
      constructor
      · intro h; subst x; exact hx ha
      · intro h; subst x; exact hx hb
    let p : alternatingGroup (complementLabels a b) :=
      ⟨subtypePerm g.val (fun x => (hpres x).symm), by
        rw [mem_alternatingGroup, sign_subtypePerm g.val (fun x => (hpres x).symm) hsupp]
        exact g.property⟩
    refine ⟨p, Subtype.ext ?_⟩
    exact ofSubtype_subtypePerm (fun x => (hpres x).symm) hsupp

theorem support_two_stabilizer_dichotomy (a b : α) (hab : a ≠ b)
    (P : Subgroup (alternatingGroup α))
    (lower : (GI.AlternatingSimple.extend (complementLabels a b)).range ≤ P)
    (upper : P ≤ setwise a b hab) :
    P = pointwise a b hab ∨ P = setwise a b hab := by
  rw [complement_alternating_range a b hab] at lower
  exact stabilizer_dichotomy a b hab P lower upper

end GI.Pairs
