module

public import Workspace.SocleFactorKernel
public import Workspace.AlternatingSections

@[expose] public section

namespace GI.SectionCaps

variable {G : Type*} [Group G] {b : ℕ}

/-- Simple alternating quotients of a faithful finite family occur in one
of the component groups, including for every subgroup of the source. -/
theorem faithful_group_family {I : Type*} [Fintype I]
    {D : I → Type*} [∀ i, Group (D i)] (actions : ∀ i, G →* D i)
    (faithful : ∀ g : G, (∀ i, actions i g = 1) → g = 1)
    (bounds : ∀ i, Cap (D i) b) : Cap G b := by
  classical
  intro U k hk q onto
  letI : IsSimpleGroup (alternatingGroup (Fin k)) := AlternatingSimple.isSimple_fin hk
  let component := fun i => (actions i).comp U.subtype
  let kernels := (Finset.univ : Finset I).toList.map (fun i => (component i).ker)
  have normal : ∀ N ∈ kernels, N.Normal := by
    intro N hN
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hN
    infer_instance
  have kills : commonKernel kernels ≤ q.ker := by
    intro u hu
    have one : u.val = 1 := faithful u.val (fun i => by
      have hm : (component i).ker ∈ kernels := List.mem_map.mpr ⟨i, by simp, rfl⟩
      exact (mem_commonKernel_iff kernels u).mp hu _ hm)
    have hu1 : u = 1 := Subtype.ext one
    change q u = 1
    rw [hu1, map_one]
  obtain ⟨N, hN, hbot⟩ := simple_quotient_localization q onto
    (AlternatingSimple.nonabelian_fin hk) kernels normal kills
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hN
  apply quotient_degree_le (bounds i) hk (component i) q onto
  intro u hu
  have hm : q u ∈ (component i).ker.map q := ⟨u, hu, rfl⟩
  simpa only [hbot, Subgroup.mem_bot, MonoidHom.mem_ker] using hm

end GI.SectionCaps

namespace GI.RadicalSocle

variable {G : Type*} [Group G] [Finite G] {b : ℕ}

theorem factorKernel_cap (hsoc : socle G = ⊤)
    (bounds : ∀ N : MinimalNormals G, SectionCaps.Cap (MulAut N.val) b) :
    SectionCaps.Cap (FactorKernel G) b := by
  letI := Fintype.ofFinite (MinimalNormals G)
  let components : ∀ N : MinimalNormals G, FactorKernel G →* MulAut N.val :=
    fun N => (Pi.evalMonoidHom (fun N : MinimalNormals G => MulAut N.val) N).comp
      factorKernelHom
  apply SectionCaps.faithful_group_family components ?_ bounds
  intro e he
  apply factorKernelHom_injective hsoc
  funext N
  exact he N

/-- The full automorphism group is bounded using the actual permutation
degree on its factors and section bounds for the actual factor automorphism
groups. No section bound for those simple automorphism groups is assumed
to have been proved here. -/
theorem automorphism_cap (hsoc : socle G = ⊤)
    (bounds : ∀ N : MinimalNormals G, SectionCaps.Cap (MulAut N.val) b) :
    SectionCaps.Cap (MulAut G) (max b (Nat.card (MinimalNormals G))) := by
  letI := Fintype.ofFinite (MinimalNormals G)
  rw [Nat.card_eq_fintype_card]
  exact SectionCaps.extension minimalNormalAction (factorKernel_cap hsoc bounds)
    SectionCaps.permutations

/-- Applies the actual faithful socle conjugation map. The two remaining
numerical inputs are exposed: factor-automorphism section caps and the
number of actual simple factors of the socle. -/
theorem radicalFree_group_cap
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    (bounds : ∀ N : MinimalNormals (socle G), SectionCaps.Cap (MulAut N.val) b) :
    SectionCaps.Cap G (max b (Nat.card (MinimalNormals (socle G)))) :=
  SectionCaps.of_injective socleConjugation (socleConjugation_injective radicalFree)
    (automorphism_cap socle_idempotent bounds)

theorem radical_quotient_group_cap
    (bounds : ∀ N : MinimalNormals (socle (G ⧸ solvableRadical G)),
      SectionCaps.Cap (MulAut N.val) b) :
    SectionCaps.Cap (G ⧸ solvableRadical G)
      (max b (Nat.card (MinimalNormals (socle (G ⧸ solvableRadical G))))) :=
  radicalFree_group_cap radical_quotient_radicalFree bounds

/-- An order bound from the constructed factor action and exact kernel.
This does not identify the factor count with any permutation degree. -/
theorem automorphism_card_le [Fintype (MinimalNormals G)]
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    (hsoc : socle G = ⊤) :
    Nat.card (MulAut G) ≤
      (∏ N : MinimalNormals G, Nat.card (MulAut N.val)) *
        (Nat.card (MinimalNormals G)).factorial := by
  have hkernel : Nat.card (FactorKernel G) =
      ∏ N : MinimalNormals G, Nat.card (MulAut N.val) := by
    rw [Nat.card_congr (factorKernelEquiv radicalFree hsoc).toEquiv, Nat.card_pi]
  have hrange : Nat.card (minimalNormalAction (G := G)).range ≤
      (Nat.card (MinimalNormals G)).factorial := by
    rw [← Nat.card_perm]
    exact Nat.card_le_card_of_injective _ Subtype.val_injective
  calc
    Nat.card (MulAut G) = Nat.card (FactorKernel G) *
        Nat.card (minimalNormalAction (G := G)).range := by
      rw [← (minimalNormalAction (G := G)).ker.card_mul_index, Subgroup.index_ker]
    _ ≤ (∏ N : MinimalNormals G, Nat.card (MulAut N.val)) *
        (Nat.card (MinimalNormals G)).factorial := by
      rw [hkernel]
      exact Nat.mul_le_mul_left _ hrange

end GI.RadicalSocle
