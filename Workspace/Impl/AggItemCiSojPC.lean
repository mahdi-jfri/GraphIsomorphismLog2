module

public import Workspace.Impl.AggItemCiSojPG

@[expose] public section

/-!
# The exact projected coset of each physical rectangle answer

A nonempty physical answer is a coset of the common source automorphism group.
Projection through the representation homomorphism preserves this full coset.
The target twist multiplies its representative and leaves its source group fixed.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Rectangle Equiv Equiv.Perm
open scoped Pointwise

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}
  {W R : Finset (Fin L.q)}

/-- The physical answer, viewed inside the representation subgroup. -/
noncomputable def itcsTypedAnswer (rep : RectRep P₀ S L W R)
    (M N : W → R → Bool) (t : permitted W R) : Set rep.H :=
  {h | h.val ∈ (rep.state M N t).answer}

/-- Inside `H`, every query has the same full source subgroup. -/
theorem itcs_typed_answer_coset (rep : RectRep P₀ S L W R)
    (M N : W → R → Bool) (t : permitted W R) (g : rep.H)
    (hg : g.val ∈ (rep.state M N t).answer) :
    itcsTypedAnswer rep M N t =
      g • (((itcsPhysicalAut rep M).subgroupOf rep.H) : Set rep.H) := by
  have he := answer_eq_smul_aut rep.Δ_inv (show g.val ∈
    answer rep.H rep.Δ (rep.colors M) (rep.colors (RectRep.twistMat t N)) from hg)
  ext h
  change h.val ∈ answer rep.H rep.Δ (rep.colors M)
    (rep.colors (RectRep.twistMat t N)) ↔ _
  rw [he]
  constructor
  · rintro ⟨a, ha, hmul⟩
    exact ⟨⟨a, ha.1⟩, ha, Subtype.ext hmul⟩
  · rintro ⟨a, ha, hmul⟩
    exact ⟨a.val, ha, congrArg Subtype.val hmul⟩

/-- Projecting a nonempty physical answer gives the full permitted coset. -/
theorem itcs_projected_answer_coset (rep : RectRep P₀ S L W R)
    (M N : W → R → Bool) (t : permitted W R) (g : rep.H)
    (hg : g.val ∈ (rep.state M N t).answer) :
    itcsRepMap rep '' itcsTypedAnswer rep M N t =
      itcsRepMap rep g •
        ((((itcsPhysicalAut rep M).subgroupOf rep.H).map (itcsRepMap rep)) :
          Set (permitted W R)) := by
  rw [itcs_typed_answer_coset rep M N t g hg, Set.image_smul_distrib]
  rfl

/-- The twist changes only the representative of the complete projected coset. -/
theorem itcs_twisted_answer_coset (rep : RectRep P₀ S L W R)
    (M N : W → R → Bool) (t : permitted W R) (g : rep.H)
    (hg : g.val ∈ (rep.state M N t).answer) :
    t • (itcsRepMap rep '' itcsTypedAnswer rep M N t) =
      (t * itcsRepMap rep g) •
        ((((itcsPhysicalAut rep M).subgroupOf rep.H).map (itcsRepMap rep)) :
          Set (permitted W R)) := by
  rw [itcs_projected_answer_coset rep M N t g hg, smul_smul]

end GI.Impl
