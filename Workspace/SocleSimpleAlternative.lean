import Workspace.RadicalSocleIdempotent
import Workspace.SocleOuter

namespace GI.RadicalSocle

variable {G : Type*} [Group G]

/-- When the socle is the whole finite nontrivial group, at most one
intrinsic minimal normal factor forces the group itself to be simple. -/
theorem simple_of_socle_eq_top_count_le_one [Finite G] [Nontrivial G]
    (hsoc : socle G = ⊤) (hcount : Nat.card (MinimalNormals G) ≤ 1) :
    IsSimpleGroup G := by
  letI := Fintype.ofFinite (MinimalNormals G)
  haveI : Subsingleton (MinimalNormals G) :=
    Fintype.card_le_one_iff_subsingleton.mp (by simpa only [Nat.card_eq_fintype_card] using hcount)
  obtain ⟨N, hN, _⟩ := exists_minimal_normal_le (⊤ : Subgroup G) top_ne_bot
  letI : N.Normal := hN.1
  have hle : socle G ≤ N := by
    apply socle_le_normal
    intro M hM
    have he : (⟨M, hM⟩ : MinimalNormals G) = ⟨N, hN⟩ := Subsingleton.elim _ _
    exact le_of_eq (congrArg Subtype.val he)
  have htop : N = ⊤ := top_unique (hsoc ▸ hle)
  letI : IsSimpleGroup N := minimalNormal_simple_of_socle_eq_top hsoc hN
  let e : N ≃* G := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  exact IsSimpleGroup.isSimpleGroup_of_surjective e.toMonoidHom e.surjective

/-- The actual socle conjugation image contains every actual inner
automorphism. Together with injectivity this gives an almost-simple
embedding whenever the actual socle is nonabelian simple. -/
theorem innerAut_le_socleConjugation_range :
    GI.SocleOuter.innerAut (socle G) ≤ (socleConjugation (G := G)).range := by
  rintro e ⟨s, rfl⟩
  refine ⟨s.val, ?_⟩
  apply MulEquiv.ext
  intro t
  apply Subtype.ext
  rfl

/-- An actual embedding, with the actual inner subgroup inside its image;
no abstract almost-simple representation is supplied as a premise. -/
theorem socle_almost_simple_embedding [Finite G]
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    (simple : IsSimpleGroup (socle G)) :
    IsSimpleGroup (socle G) ∧ Function.Injective (socleConjugation (G := G)) ∧
      GI.SocleOuter.innerAut (socle G) ≤ (socleConjugation (G := G)).range :=
  ⟨simple, socleConjugation_injective radicalFree, innerAut_le_socleConjugation_range⟩

end GI.RadicalSocle
