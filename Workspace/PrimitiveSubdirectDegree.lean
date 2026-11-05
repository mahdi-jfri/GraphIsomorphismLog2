module

public import Workspace.SubdirectPhysicalDegree
public import Workspace.BudgetInductionProperCartesian

@[expose] public section

namespace GI.PrimitiveCartesian

open GI.RadicalSocle GI.PrimitiveProducts

variable {G V : Type*} [Group G] [Finite G] [MulAction G V]
  [FaithfulSMul G V] [Nontrivial V] [MulAction.IsPreprimitive G V]

omit [Nontrivial V] in
/-- The actual subdirect branch for a minimal normal subgroup has order
at most the square of the physical degree. Homogeneous coordinates and
the faithful transitive product action are constructed from the proved
intrinsic factor decomposition. -/
theorem minimalNormal_card_le_degree_sq_of_subdirect
    (radicalFree : ∀ K : Subgroup G, K.Normal → IsSolvable K → K = ⊥)
    (N : Subgroup G) [N.Normal] (hN : MinimalNormal N) (a : V) (i : MinimalNormals N)
    (onto : ∀ j : MinimalNormals N, ((MulAction.stabilizer G a).comap
      (minimalCoordinateEmbedding radicalFree N hN)).map
        (Pi.evalMonoidHom (fun M : MinimalNormals N => M.val) j) = ⊤) :
    Nat.card N ≤ Nat.card V ^ 2 := by
  classical
  letI := Fintype.ofFinite (MinimalNormals N)
  letI : IsSimpleGroup i.val := minimalNormal_simple_factors hN i
  let P := MinimalNormals N → i.val
  let phi : P ≃* IntrinsicCoordinates N :=
    MulEquiv.piCongrRight (fun j => minimalNormalFactorEquiv radicalFree hN i j)
  let f := phi.trans (intrinsicProductEquiv (normal_subgroup_radicalFree radicalFree N)
    (minimalNormal_socle_eq_top hN))
  let F := (minimalCoordinateEmbedding radicalFree N hN).comp phi.toMonoidHom
  have hF : Function.Injective F :=
    (normalCoordinateEmbedding_injective N (normal_subgroup_radicalFree radicalFree N)
      (minimalNormal_socle_eq_top hN)).comp phi.injective
  letI : MulAction P V := MulAction.compHom V F
  letI : FaithfulSMul P V := by
    constructor
    intro x y he
    apply hF
    apply eq_of_smul_eq_smul (α := V)
    exact he
  letI : MulAction.IsPretransitive N V :=
    GI.PrimitiveStructure.normal_pretransitive N hN.2.1
  letI : MulAction.IsPretransitive P V := by
    constructor
    intro v w
    obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N v w
    refine ⟨f.symm n, ?_⟩
    change ((f (f.symm n) : N) : G) • v = w
    rw [f.apply_symm_apply]
    exact hn
  have hs : Subdirect (MulAction.stabilizer P a) := by
    intro j s
    have hm : minimalNormalFactorEquiv radicalFree hN i j s ∈
        ((MulAction.stabilizer G a).comap (minimalCoordinateEmbedding radicalFree N hN)).map
          (Pi.evalMonoidHom (fun M : MinimalNormals N => M.val) j) := by
      rw [onto j]
      exact Subgroup.mem_top _
    obtain ⟨z, hz, hzs⟩ := hm
    refine ⟨⟨phi.symm z, ?_⟩, ?_⟩
    · change minimalCoordinateEmbedding radicalFree N hN (phi (phi.symm z)) • a = a
      rw [phi.apply_symm_apply]
      exact hz
    · change (minimalNormalFactorEquiv radicalFree hN i j).symm (z j) = s
      change z j = minimalNormalFactorEquiv radicalFree hN i j s at hzs
      rw [hzs, MulEquiv.symm_apply_apply]
  have hb := subdirect_action_card_le_degree_sq
    (minimalNormal_factors_nonabelian radicalFree hN i) a hs
  rw [← Nat.card_congr f.toEquiv]
  exact hb

end GI.PrimitiveCartesian

namespace GI.BudgetInduction

open GI.RadicalSocle GI.PrimitiveCartesian

/-- Every remaining unsupported nonsimple minimal-normal branch now has
the required quadratic bound on its actual order. -/
theorem unsupported_minimalNormal_order_le_degree_sq {n : ℕ} {A₀ : ℝ}
    (H : Subgroup (Equiv.Perm (Fin n))) [Nontrivial (Fin n)]
    [MulAction.IsPreprimitive H (Fin n)]
    (radicalFree : ∀ K : Subgroup H, K.Normal → IsSolvable K → K = ⊥)
    (N : Subgroup H) [N.Normal] (hN : MinimalNormal N) (a : Fin n)
    (factorCount : 2 ≤ Nat.card (MinimalNormals N))
    (unsupported : ¬ PrimitiveReductionAlternative A₀ H) : Nat.card N ≤ n ^ 2 := by
  letI : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN.2.1
  obtain ⟨K, hK, _⟩ := exists_minimal_normal_le (⊤ : Subgroup N) top_ne_bot
  have h := minimalNormal_card_le_degree_sq_of_subdirect radicalFree N hN a ⟨K, hK⟩
    (unsupported_minimalNormal_projections_surjective H radicalFree N hN a factorCount unsupported)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using h

end GI.BudgetInduction
