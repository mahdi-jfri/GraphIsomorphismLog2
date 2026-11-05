module

public import Workspace.AltAutEquivalence
public import Workspace.RadicalSocleBasic

@[expose] public section

namespace GI.AlternatingSocle

open GI.RadicalSocle

variable {H S T : Type*} [Group H] [Group S] [Group T]

/-- Transport of automorphisms sends actual inner conjugation to actual
inner conjugation in the target group. -/
theorem automorphism_congr_inner (e : S ≃* T) (s : S) :
    MulAut.congr e (MulAut.conj s) = MulAut.conj (e s) := by
  apply MulEquiv.ext
  intro t
  change e (s * e.symm t * s⁻¹) = e s * t * (e s)⁻¹
  simp only [map_mul, map_inv, e.apply_symm_apply]

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The natural permutation representation is constructed from actual
socle conjugation, a concrete alternating-socle isomorphism, and the
proved natural realization of alternating automorphisms. -/
noncomputable def naturalHom (e : socle H ≃* alternatingGroup A)
    (hdegree : Fintype.card A = 5 ∨ 7 ≤ Fintype.card A) : H →* Equiv.Perm A :=
  (GI.AlternatingAutomorphism.conjugationEquiv hdegree).symm.toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp (socleConjugation (G := H)))

theorem naturalHom_injective [Finite H]
    (radicalFree : ∀ N : Subgroup H, N.Normal → IsSolvable N → N = ⊥)
    (e : socle H ≃* alternatingGroup A)
    (hdegree : Fintype.card A = 5 ∨ 7 ≤ Fintype.card A) :
    Function.Injective (naturalHom e hdegree) :=
  (GI.AlternatingAutomorphism.conjugationEquiv hdegree).symm.injective.comp
    ((MulAut.congr e).injective.comp (socleConjugation_injective radicalFree))

theorem naturalHom_apply_socle (e : socle H ≃* alternatingGroup A)
    (hdegree : Fintype.card A = 5 ∨ 7 ≤ Fintype.card A) (s : socle H) :
    naturalHom e hdegree s.val = (e s : Equiv.Perm A) := by
  change (GI.AlternatingAutomorphism.conjugationEquiv hdegree).symm
    (MulAut.congr e (socleConjugation s.val)) = _
  rw [show socleConjugation s.val = MulAut.conj s from MulAut.conjNormal_val,
    automorphism_congr_inner]
  exact GI.AlternatingAutomorphism.conjugationEquiv_symm_conj hdegree (e s)

/-- The natural image contains the actual alternating subgroup, proved
from images of actual socle elements rather than assumed as model data. -/
theorem alternating_le_natural_range (e : socle H ≃* alternatingGroup A)
    (hdegree : Fintype.card A = 5 ∨ 7 ≤ Fintype.card A) :
    alternatingGroup A ≤ (naturalHom e hdegree).range := by
  intro p hp
  let s := e.symm ⟨p, hp⟩
  refine ⟨s.val, ?_⟩
  rw [naturalHom_apply_socle]
  change (e (e.symm ⟨p, hp⟩) : Equiv.Perm A) = p
  rw [e.apply_symm_apply]

/-- The original acting group is equivalent to its constructed natural
image, allowing transport of its original physical action unchanged. -/
noncomputable def naturalEquiv [Finite H]
    (radicalFree : ∀ N : Subgroup H, N.Normal → IsSolvable N → N = ⊥)
    (e : socle H ≃* alternatingGroup A)
    (hdegree : Fintype.card A = 5 ∨ 7 ≤ Fintype.card A) :
    H ≃* (naturalHom e hdegree).range :=
  MulEquiv.ofBijective (naturalHom e hdegree).rangeRestrict
    ⟨fun _ _ he => naturalHom_injective radicalFree e hdegree (congrArg Subtype.val he), fun p => by
      obtain ⟨h, hh⟩ := p.property
      exact ⟨h, Subtype.ext hh⟩⟩

end GI.AlternatingSocle
