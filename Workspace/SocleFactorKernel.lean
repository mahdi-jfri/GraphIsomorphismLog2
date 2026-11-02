import Workspace.SocleFactorAction
namespace GI.RadicalSocle

variable {G : Type*} [Group G] [Finite G]

noncomputable def intrinsicProductEquiv
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    (hsoc : socle G = ⊤) : (∀ N : MinimalNormals G, N.val) ≃* G :=
  (socleProductEquiv radicalFree).trans
    ((MulEquiv.subgroupCongr hsoc).trans Subgroup.topEquiv)

theorem intrinsicProductEquiv_single
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    (hsoc : socle G = ⊤) [DecidableEq (MinimalNormals G)]
    (N : MinimalNormals G) (x : N.val) :
    intrinsicProductEquiv radicalFree hsoc (Pi.mulSingle N x) = x := by
  letI := Fintype.ofFinite (MinimalNormals G)
  change socleProductHom (Pi.mulSingle N x) = x
  exact Subgroup.noncommPiCoprod_mulSingle N x

/-- Independent automorphisms of the actual direct factors induce an
automorphism of their whole generated group. -/
noncomputable def coordinateAut
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    (hsoc : socle G = ⊤) (es : ∀ N : MinimalNormals G, MulAut N.val) : MulAut G :=
  (intrinsicProductEquiv radicalFree hsoc).symm.trans
    ((MulEquiv.piCongrRight es).trans (intrinsicProductEquiv radicalFree hsoc))

theorem coordinateAut_on_factor
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    (hsoc : socle G = ⊤) (es : ∀ N : MinimalNormals G, MulAut N.val)
    (N : MinimalNormals G) (x : N.val) :
    coordinateAut radicalFree hsoc es x = es N x := by
  classical
  have hp : (MulEquiv.piCongrRight es) (Pi.mulSingle N x) =
      Pi.mulSingle N (es N x) := by
    funext M
    by_cases hMN : M = N
    · subst M
      simp
    · simp [Pi.mulSingle_eq_of_ne hMN, hMN]
  have hsingle := intrinsicProductEquiv_single radicalFree hsoc N x
  rw [← hsingle]
  change intrinsicProductEquiv radicalFree hsoc
    ((MulEquiv.piCongrRight es) ((intrinsicProductEquiv radicalFree hsoc).symm
      (intrinsicProductEquiv radicalFree hsoc (Pi.mulSingle N x)))) = _
  rw [MulEquiv.symm_apply_apply, hp, intrinsicProductEquiv_single]

theorem coordinateAut_map_factor
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    (hsoc : socle G = ⊤) (es : ∀ N : MinimalNormals G, MulAut N.val)
    (N : MinimalNormals G) :
    N.val.map (coordinateAut radicalFree hsoc es).toMonoidHom = N.val := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    change coordinateAut radicalFree hsoc es (⟨x, hx⟩ : N.val) ∈ N.val
    rw [coordinateAut_on_factor]
    exact (es N ⟨x, hx⟩).property
  · intro y hy
    refine ⟨(es N).symm ⟨y, hy⟩, ((es N).symm ⟨y, hy⟩).property, ?_⟩
    change coordinateAut radicalFree hsoc es ((es N).symm ⟨y, hy⟩ : N.val) = y
    rw [coordinateAut_on_factor, MulEquiv.apply_symm_apply]

noncomputable def coordinateKernelAut
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    (hsoc : socle G = ⊤) (es : ∀ N : MinimalNormals G, MulAut N.val) : FactorKernel G :=
  ⟨coordinateAut radicalFree hsoc es, by
    apply Equiv.ext
    intro N
    apply Subtype.ext
    exact coordinateAut_map_factor radicalFree hsoc es N⟩

theorem factorKernelHom_surjective
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    (hsoc : socle G = ⊤) : Function.Surjective (factorKernelHom (G := G)) := by
  intro es
  refine ⟨coordinateKernelAut radicalFree hsoc es, ?_⟩
  funext N
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  exact coordinateAut_on_factor radicalFree hsoc es N x

/-- The factor-permutation kernel is exactly the product of the
automorphism groups of the actual factors. -/
noncomputable def factorKernelEquiv
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    (hsoc : socle G = ⊤) :
    FactorKernel G ≃* (∀ N : MinimalNormals G, MulAut N.val) :=
  MulEquiv.ofBijective factorKernelHom
    ⟨factorKernelHom_injective hsoc, factorKernelHom_surjective radicalFree hsoc⟩

noncomputable def socleFactorKernelEquiv
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥) :
    FactorKernel (socle G) ≃* (∀ N : MinimalNormals (socle G), MulAut N.val) :=
  factorKernelEquiv (normal_subgroup_radicalFree radicalFree (socle G)) socle_idempotent

end GI.RadicalSocle
