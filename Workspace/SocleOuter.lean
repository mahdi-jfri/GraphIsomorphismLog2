import Workspace.SocleFactorKernel
namespace GI.SocleOuter

open RadicalSocle

variable {G : Type*} [Group G]

/-- The subgroup of actual inner automorphisms. -/
def innerAut (G : Type*) [Group G] : Subgroup (MulAut G) := MulAut.conj.range

theorem conjugate_inner (e : MulAut G) (g : G) :
    e * MulAut.conj g * e⁻¹ = MulAut.conj (e g) := by
  apply MulEquiv.ext
  intro x
  change e (g * e.symm x * g⁻¹) = e g * x * (e g)⁻¹
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]

instance innerAut_normal : (innerAut G).Normal := by
  constructor
  intro e he a
  obtain ⟨g, rfl⟩ := he
  exact ⟨a g, (conjugate_inner a g).symm⟩

abbrev OuterAut (G : Type*) [Group G] := MulAut G ⧸ innerAut G

def factorOuterHom : FactorKernel G →* (∀ N : MinimalNormals G, OuterAut N.val) :=
  Pi.monoidHom (fun N => (QuotientGroup.mk' (innerAut N.val)).comp
    ((Pi.evalMonoidHom (fun N : MinimalNormals G => MulAut N.val) N).comp
      factorKernelHom))

theorem factorOuterHom_ker_iff (e : FactorKernel G) :
    e ∈ (factorOuterHom (G := G)).ker ↔
      ∀ N : MinimalNormals G, ∃ x : N.val, MulAut.conj x = factorKernelRestriction e N := by
  constructor
  · intro he N
    have h := congrFun he N
    exact (QuotientGroup.eq_one_iff (factorKernelRestriction e N)).mp h
  · intro he
    apply funext
    intro N
    exact (QuotientGroup.eq_one_iff (factorKernelRestriction e N)).mpr
      (show factorKernelRestriction e N ∈ innerAut N.val from he N)

section Finite

variable [Finite G]
variable (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
variable (hsoc : socle G = ⊤)

include radicalFree hsoc

theorem factorOuterHom_surjective : Function.Surjective (factorOuterHom (G := G)) := by
  intro out
  choose es hes using fun N : MinimalNormals G =>
    QuotientGroup.mk'_surjective (innerAut N.val) (out N)
  obtain ⟨e, he⟩ := factorKernelHom_surjective radicalFree hsoc es
  refine ⟨e, ?_⟩
  funext N
  have hN := congrFun he N
  exact (congrArg (QuotientGroup.mk' (innerAut N.val)) hN).trans (hes N)

/-- The subgroup removed by the factorwise outer map is the actual image
of the factorwise inner automorphisms, with no Schreier assumption. -/
noncomputable def innerFactorHom :
    (∀ N : MinimalNormals G, N.val) →* FactorKernel G :=
  (factorKernelEquiv radicalFree hsoc).symm.toMonoidHom.comp
    (Pi.monoidHom (fun N : MinimalNormals G =>
      (MulAut.conj : N.val →* MulAut N.val).comp
        (Pi.evalMonoidHom (fun N : MinimalNormals G => N.val) N)))

theorem factorOuterHom_ker_eq_innerFactor_range :
    (factorOuterHom (G := G)).ker = (innerFactorHom radicalFree hsoc).range := by
  ext e
  rw [factorOuterHom_ker_iff]
  constructor
  · intro h
    choose xs hxs using h
    refine ⟨xs, ?_⟩
    apply factorKernelHom_injective hsoc
    change factorKernelEquiv radicalFree hsoc
      ((factorKernelEquiv radicalFree hsoc).symm (fun N => MulAut.conj (xs N))) =
        factorKernelHom e
    rw [MulEquiv.apply_symm_apply]
    exact funext hxs
  · rintro ⟨xs, rfl⟩ N
    refine ⟨xs N, ?_⟩
    have h := (factorKernelEquiv radicalFree hsoc).apply_symm_apply
      (fun N => MulAut.conj (xs N))
    exact (congrFun h N).symm

theorem coordinateAut_conj (xs : ∀ N : MinimalNormals G, N.val) :
    coordinateAut radicalFree hsoc (fun N => MulAut.conj (xs N)) =
      MulAut.conj (intrinsicProductEquiv radicalFree hsoc xs) := by
  apply MulEquiv.ext
  intro g
  change intrinsicProductEquiv radicalFree hsoc
    (xs * (intrinsicProductEquiv radicalFree hsoc).symm g * xs⁻¹) =
      intrinsicProductEquiv radicalFree hsoc xs * g *
        (intrinsicProductEquiv radicalFree hsoc xs)⁻¹
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem innerFactorHom_coe (xs : ∀ N : MinimalNormals G, N.val) :
    (innerFactorHom radicalFree hsoc xs).val =
      MulAut.conj (intrinsicProductEquiv radicalFree hsoc xs) := by
  have he : innerFactorHom radicalFree hsoc xs =
      coordinateKernelAut radicalFree hsoc (fun N => MulAut.conj (xs N)) := by
    apply factorKernelHom_injective hsoc
    calc
      factorKernelHom (innerFactorHom radicalFree hsoc xs) =
          (fun N => MulAut.conj (xs N)) :=
        (factorKernelEquiv radicalFree hsoc).apply_symm_apply _
      _ = factorKernelHom (coordinateKernelAut radicalFree hsoc
          (fun N => MulAut.conj (xs N))) := by
        symm
        funext N
        apply MulEquiv.ext
        intro x
        apply Subtype.ext
        exact coordinateAut_on_factor radicalFree hsoc _ N x
  rw [he]
  exact coordinateAut_conj radicalFree hsoc xs

/-- The inner subgroup in the factorwise description is the actual inner
automorphism subgroup of the whole group, rather than a supplied surrogate. -/
theorem factorOuterHom_ker_eq_inner_comap :
    (factorOuterHom (G := G)).ker = (innerAut G).comap (FactorKernel G).subtype := by
  rw [factorOuterHom_ker_eq_innerFactor_range radicalFree hsoc]
  ext e
  constructor
  · rintro ⟨xs, rfl⟩
    exact ⟨intrinsicProductEquiv radicalFree hsoc xs,
      (innerFactorHom_coe radicalFree hsoc xs).symm⟩
  · rintro ⟨g, hg⟩
    refine ⟨(intrinsicProductEquiv radicalFree hsoc).symm g, ?_⟩
    apply Subtype.ext
    rw [innerFactorHom_coe, MulEquiv.apply_symm_apply]
    exact hg

/-- An exact quotient description, conditional only on the already explicit
semisimple direct-product hypotheses. No solvability of outer groups is
asserted by this construction. -/
noncomputable def factorOuterQuotientEquiv :
    FactorKernel G ⧸ (factorOuterHom (G := G)).ker ≃*
      (∀ N : MinimalNormals G, OuterAut N.val) :=
  QuotientGroup.quotientKerEquivOfSurjective factorOuterHom
    (factorOuterHom_surjective radicalFree hsoc)

end Finite

end GI.SocleOuter
