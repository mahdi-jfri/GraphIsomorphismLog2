import Workspace.Impl.AggItemCiSojQuery

/-!
# The complete permitted matrix transporter from the two physical answers

A representation lifts every permitted matrix map into its physical subgroup,
possibly after removing its recorded twist. We prove the exact transporter set,
not only soundness of one representative. This is the fact needed when the
program projects the answer generators and rebuilds the source overcoset group.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}
  {W R : Finset (Fin L.q)}

/-- The label homomorphism of the representation, with the permitted range made explicit. -/
def itcsRepMap (rep : RectRep P₀ S L W R) : rep.H →* permitted W R where
  toFun h := ⟨L.π ⟨h.val, rep.le h.property⟩, rep.image h.val h.property⟩
  map_one' := by apply Subtype.ext; exact L.π.map_one
  map_mul' h g := by
    apply Subtype.ext
    change L.π ((⟨h.val, rep.le h.property⟩ : S.G) * ⟨g.val, rep.le g.property⟩) =
      L.π ⟨h.val, rep.le h.property⟩ * L.π ⟨g.val, rep.le g.property⟩
    exact L.π.map_mul _ _

/-- Every transporter occurs in the untwisted answer or in the recorded twist answer,
and these are the only permitted transporters. -/
theorem itcs_transporter_answers (rep : RectRep P₀ S L W R) (M N : W → R → Bool)
    (p : permitted W R) :
    MatrixTransports M N p ↔
      (∃ h : rep.H, h.val ∈ (rep.state M N 1).answer ∧ itcsRepMap rep h = p) ∨
      ∃ t ∈ rep.twist, ∃ h : rep.H,
        h.val ∈ (rep.state M N t).answer ∧ t * itcsRepMap rep h = p := by
  constructor
  · intro hp
    rcases rep.lifts p with ⟨h, hh, hπ⟩ | ⟨t, ht, h, hh, hπ⟩
    · have he : itcsRepMap rep ⟨h, hh⟩ = p := Subtype.ext hπ
      left
      refine ⟨⟨h, hh⟩, rep.mem_of_transports hh ?_, he⟩
      have htr := RectRep.transports_untwist (t := (1 : permitted W R)) hp
      simpa only [inv_one, one_mul, ← he] using htr
    · have he : itcsRepMap rep ⟨h, hh⟩ = t⁻¹ * p := Subtype.ext hπ
      right
      refine ⟨t, ht, ⟨h, hh⟩, rep.mem_of_transports hh ?_, ?_⟩
      · have htr := RectRep.transports_untwist (t := t) hp
        simpa only [← he] using htr
      · rw [he, mul_inv_cancel_left]
  · rintro (⟨h, hh, he⟩ | ⟨t, -, h, hh, he⟩)
    · obtain ⟨hh', htr⟩ := rep.transports_of_mem hh
      have ht := RectRep.transports_twist htr
      have hm : (⟨L.π ⟨h.val, rep.le hh'⟩, rep.image h.val hh'⟩ : permitted W R) =
          itcsRepMap rep h := rfl
      simpa only [hm, one_mul, he] using ht
    · obtain ⟨hh', htr⟩ := rep.transports_of_mem hh
      have ht := RectRep.transports_twist htr
      have hm : (⟨L.π ⟨h.val, rep.le hh'⟩, rep.image h.val hh'⟩ : permitted W R) =
          itcsRepMap rep h := rfl
      simpa only [hm, he] using ht

/-- In particular, all permitted source automorphisms are recovered from the two
source--source physical answers. -/
theorem itcs_automorphism_answers (rep : RectRep P₀ S L W R) (M : W → R → Bool)
    (p : permitted W R) :
    MatrixTransports M M p ↔
      (∃ h : rep.H, h.val ∈ (rep.state M M 1).answer ∧ itcsRepMap rep h = p) ∨
      ∃ t ∈ rep.twist, ∃ h : rep.H,
        h.val ∈ (rep.state M M t).answer ∧ t * itcsRepMap rep h = p :=
  itcs_transporter_answers rep M M p

/-- All permitted source automorphisms are differences of one fixed transporter
and the projected physical answers. This uses the complete answer sets. -/
theorem itcs_answer_differences (rep : RectRep P₀ S L W R) (M N : W → R → Bool)
    {p₀ : permitted W R} (hp₀ : MatrixTransports M N p₀) (g : permitted W R) :
    MatrixTransports M M g ↔
      (∃ h : rep.H, h.val ∈ (rep.state M N 1).answer ∧ p₀⁻¹ * itcsRepMap rep h = g) ∨
      ∃ t ∈ rep.twist, ∃ h : rep.H,
        h.val ∈ (rep.state M N t).answer ∧ p₀⁻¹ * (t * itcsRepMap rep h) = g := by
  constructor
  · intro hg
    have hp := matrixTransports_mul hp₀ hg
    rcases (itcs_transporter_answers rep M N (p₀ * g)).1 hp with
      ⟨h, hh, he⟩ | ⟨t, ht, h, hh, he⟩
    · exact Or.inl ⟨h, hh, by rw [he, inv_mul_cancel_left]⟩
    · exact Or.inr ⟨t, ht, h, hh, by rw [he, inv_mul_cancel_left]⟩
  · rintro (⟨h, hh, he⟩ | ⟨t, ht, h, hh, he⟩)
    · have hp := (itcs_transporter_answers rep M N (itcsRepMap rep h)).2
        (Or.inl ⟨h, hh, rfl⟩)
      have hg := matrixTransports_mul (matrixTransports_inv hp₀) hp
      rwa [he] at hg
    · have hp := (itcs_transporter_answers rep M N (t * itcsRepMap rep h)).2
        (Or.inr ⟨t, ht, h, hh, rfl⟩)
      have hg := matrixTransports_mul (matrixTransports_inv hp₀) hp
      rwa [he] at hg

end GI.Impl
