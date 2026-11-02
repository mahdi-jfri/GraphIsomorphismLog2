import Workspace.SocleFactorAction
import Workspace.ProjectionEnvelope

namespace GI.PrimitiveCartesian

open GI.RadicalSocle

variable {G : Type*} [Group G] [Finite G]

noncomputable local instance : DecidableEq (MinimalNormals G) := Classical.decEq _

abbrev IntrinsicCoordinates (G : Type*) [Group G] := ∀ M : MinimalNormals G, M.val

/-- Intrinsic coordinates from the already proved decomposition into the
actual minimal normal factors, when the socle is the whole group. -/
noncomputable def intrinsicProductEquiv
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    (hsoc : socle G = ⊤) : IntrinsicCoordinates G ≃* G :=
  (socleProductEquiv radicalFree).trans
    ((MulEquiv.subgroupCongr hsoc).trans (Subgroup.topEquiv))

theorem intrinsicProductEquiv_single
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    (hsoc : socle G = ⊤) (M : MinimalNormals G) (x : M.val) :
    intrinsicProductEquiv radicalFree hsoc (Pi.mulSingle M x) = x := by
  classical
  letI := Fintype.ofFinite (MinimalNormals G)
  change socleProductHom (Pi.mulSingle M x) = (x : G)
  unfold socleProductHom
  exact Subgroup.noncommPiCoprod_mulSingle (hcomm := minimalNormals_commute) M x

noncomputable def intrinsicCoordinateAut
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    (hsoc : socle G = ⊤) (e : MulAut G) : MulAut (IntrinsicCoordinates G) :=
  (intrinsicProductEquiv radicalFree hsoc).trans
    (e.trans (intrinsicProductEquiv radicalFree hsoc).symm)

theorem intrinsicCoordinateAut_single
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    (hsoc : socle G = ⊤) (e : MulAut G) (M : MinimalNormals G) (x : M.val) :
    intrinsicCoordinateAut radicalFree hsoc e (Pi.mulSingle M x) =
      Pi.mulSingle (M := fun L : MinimalNormals G => L.val)
        (minimalNormalPerm e M) (e.subgroupMap M.val x) := by
  classical
  apply (intrinsicProductEquiv radicalFree hsoc).injective
  change intrinsicProductEquiv radicalFree hsoc
      ((intrinsicProductEquiv radicalFree hsoc).symm
        (e (intrinsicProductEquiv radicalFree hsoc (Pi.mulSingle M x)))) = _
  rw [MulEquiv.apply_symm_apply, intrinsicProductEquiv_single,
    intrinsicProductEquiv_single]
  rfl

/-- Every automorphism acts on intrinsic coordinates by its actual
permutation of minimal normal factors and actual factor isomorphisms. -/
theorem intrinsicCoordinateAut_apply
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    (hsoc : socle G = ⊤) (e : MulAut G) (M : MinimalNormals G)
    (x : IntrinsicCoordinates G) :
    intrinsicCoordinateAut radicalFree hsoc e x (minimalNormalPerm e M) =
      e.subgroupMap M.val (x M) := by
  classical
  let p := minimalNormalPerm e
  let l : IntrinsicCoordinates G →* (p M).val :=
    (Pi.evalMonoidHom (fun L : MinimalNormals G => L.val) (p M)).comp
      (intrinsicCoordinateAut radicalFree hsoc e).toMonoidHom
  let r : IntrinsicCoordinates G →* (p M).val :=
    (e.subgroupMap M.val).toMonoidHom.comp
      (Pi.evalMonoidHom (fun L : MinimalNormals G => L.val) M)
  have h : l = r := by
    apply MonoidHom.pi_ext
    intro L z
    change intrinsicCoordinateAut radicalFree hsoc e (Pi.mulSingle L z) (p M) =
      e.subgroupMap M.val (Pi.mulSingle (M := fun L : MinimalNormals G => L.val) L z M)
    rw [intrinsicCoordinateAut_single]
    change Pi.mulSingle (M := fun L : MinimalNormals G => L.val)
      (p L) (e.subgroupMap L.val z) (p M) =
        e.subgroupMap M.val (Pi.mulSingle (M := fun L : MinimalNormals G => L.val) L z M)
    by_cases hLM : L = M
    · subst L
      simp only [Pi.mulSingle_eq_same]
    · have hp : p L ≠ p M := fun he => hLM (p.injective he)
      simp only [Pi.mulSingle_eq_of_ne' hLM, Pi.mulSingle_eq_of_ne' hp, map_one]
      rfl
  exact DFunLike.congr_fun h x

theorem intrinsicCoordinateAut_fibers
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    (hsoc : socle G = ⊤) (e : MulAut G) (M : MinimalNormals G)
    (x y : IntrinsicCoordinates G) (hxy : x M = y M) :
    intrinsicCoordinateAut radicalFree hsoc e x (minimalNormalPerm e M) =
      intrinsicCoordinateAut radicalFree hsoc e y (minimalNormalPerm e M) := by
  rw [intrinsicCoordinateAut_apply, intrinsicCoordinateAut_apply, hxy]

theorem intrinsic_projectionEnvelope_map_eq
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    (hsoc : socle G = ⊤) (e : MulAut G) (K : Subgroup (IntrinsicCoordinates G))
    (preserves : K.map (intrinsicCoordinateAut radicalFree hsoc e).toMonoidHom = K) :
    (projectionEnvelope K).map (intrinsicCoordinateAut radicalFree hsoc e).toMonoidHom =
      projectionEnvelope K :=
  projectionEnvelope_map_eq K (intrinsicCoordinateAut radicalFree hsoc e)
    (minimalNormalPerm e) (intrinsicCoordinateAut_fibers radicalFree hsoc e) preserves

end GI.PrimitiveCartesian

#print axioms GI.PrimitiveCartesian.intrinsicProductEquiv
#print axioms GI.PrimitiveCartesian.intrinsicProductEquiv_single
#print axioms GI.PrimitiveCartesian.intrinsicCoordinateAut
#print axioms GI.PrimitiveCartesian.intrinsicCoordinateAut_single
#print axioms GI.PrimitiveCartesian.intrinsicCoordinateAut_apply
#print axioms GI.PrimitiveCartesian.intrinsicCoordinateAut_fibers
#print axioms GI.PrimitiveCartesian.intrinsic_projectionEnvelope_map_eq
