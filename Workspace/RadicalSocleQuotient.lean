import Workspace.RadicalSocleBasic

namespace GI.RadicalSocle

variable {G Q : Type*} [Group G] [Group Q]

def preimageHom (f : G →* Q) (N : Subgroup Q) : N.comap f →* N where
  toFun g := ⟨f g, g.property⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' g h := Subtype.ext (map_mul f (g : G) (h : G))

/-- Solvability of a preimage is proved from its actual kernel and image. -/
theorem solvable_preimage (f : G →* Q) (N : Subgroup Q)
    [IsSolvable f.ker] [IsSolvable N] : IsSolvable (N.comap f) := by
  have hle : f.ker ≤ N.comap f := by
    intro g hg
    change f g ∈ N
    rw [show f g = 1 from hg]
    exact N.one_mem
  let embed := Subgroup.inclusion hle
  apply solvable_of_ker_le_range embed (preimageHom f N)
  intro g hg
  have hf : f g = 1 := congrArg (fun z : N => (z : Q)) hg
  exact ⟨⟨g, hf⟩, rfl⟩

def MaximalSolvableNormal (R : Subgroup G) : Prop :=
  R.Normal ∧ IsSolvable R ∧ ∀ N : Subgroup G,
    N.Normal → IsSolvable N → R ≤ N → N = R

theorem exists_maximal_solvable_normal (G : Type*) [Group G] [Finite G] :
    ∃ R : Subgroup G, MaximalSolvableNormal R := by
  classical
  let candidates : Set (Subgroup G) := {N | N.Normal ∧ IsSolvable N}
  have hnonempty : candidates.Nonempty := ⟨⊥, inferInstance, inferInstance⟩
  obtain ⟨R, hR, hmax⟩ := Set.Finite.exists_maximalFor id candidates
    (Set.toFinite candidates) hnonempty
  exact ⟨R, hR.1, hR.2, fun N hN hs hle => le_antisymm (hmax ⟨hN, hs⟩ hle) hle⟩

/-- Factoring out a maximal solvable normal subgroup leaves no nontrivial
solvable normal subgroup. The extension argument is proved, not assumed. -/
theorem quotient_radicalFree_of_maximal (R : Subgroup G) [R.Normal]
    [IsSolvable R]
    (maximal : ∀ N : Subgroup G, N.Normal → IsSolvable N → R ≤ N → N = R) :
    ∀ N : Subgroup (G ⧸ R), N.Normal → IsSolvable N → N = ⊥ := by
  intro N hN hsolv
  letI := hN
  letI := hsolv
  let q := QuotientGroup.mk' R
  let M := N.comap q
  letI : M.Normal := hN.comap q
  haveI : IsSolvable q.ker := by
    dsimp only [q]
    rw [QuotientGroup.ker_mk']
    infer_instance
  haveI : IsSolvable M := solvable_preimage q N
  have hle : R ≤ M := by
    intro r hr
    change q r ∈ N
    rw [show q r = 1 from (QuotientGroup.eq_one_iff r).mpr hr]
    exact N.one_mem
  have hM : M = R := maximal M inferInstance inferInstance hle
  apply (Subgroup.eq_bot_iff_forall N).mpr
  intro n hn
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective R n
  have hg : g ∈ M := hn
  rw [hM] at hg
  exact (QuotientGroup.eq_one_iff g).mpr hg

/-- This is the actual solvable radical, selected as a maximal normal
solvable subgroup; the greatest-subgroup property is proved below. -/
noncomputable def solvableRadical (G : Type*) [Group G] [Finite G] : Subgroup G :=
  Classical.choose (exists_maximal_solvable_normal G)

theorem solvableRadical_maximal [Finite G] : MaximalSolvableNormal (solvableRadical G) :=
  Classical.choose_spec (exists_maximal_solvable_normal G)

instance solvableRadical_normal [Finite G] : (solvableRadical G).Normal :=
  solvableRadical_maximal.1

instance solvableRadical_solvable [Finite G] : IsSolvable (solvableRadical G) :=
  solvableRadical_maximal.2.1

theorem radical_quotient_radicalFree [Finite G] :
    ∀ N : Subgroup (G ⧸ solvableRadical G), N.Normal → IsSolvable N → N = ⊥ :=
  quotient_radicalFree_of_maximal (solvableRadical G) solvableRadical_maximal.2.2

/-- Every solvable normal subgroup lies in the constructed radical. Hence
the choice above is unique and agrees with the usual solvable radical. -/
theorem le_solvableRadical [Finite G] (N : Subgroup G) [N.Normal] [IsSolvable N] :
    N ≤ solvableRadical G := by
  let q := QuotientGroup.mk' (solvableRadical G)
  haveI : (N.map q).Normal := (inferInstance : N.Normal).map q
    (QuotientGroup.mk'_surjective (solvableRadical G))
  haveI : IsSolvable (N.map q) := solvable_of_surjective (q.subgroupMap_surjective N)
  have he := radical_quotient_radicalFree (N.map q) inferInstance inferInstance
  intro n hn
  have hm : q n ∈ N.map q := ⟨n, hn, rfl⟩
  rw [he, Subgroup.mem_bot] at hm
  exact (QuotientGroup.eq_one_iff n).mp hm

theorem solvableRadical_eq_of_greatest [Finite G] (R : Subgroup G) [R.Normal] [IsSolvable R]
    (greatest : ∀ N : Subgroup G, N.Normal → IsSolvable N → N ≤ R) :
    R = solvableRadical G :=
  (le_solvableRadical R).antisymm (greatest _ inferInstance inferInstance)

/-- The actual radical quotient has trivial centralizer of its actual
socle. This is the first unconditional structural step of Appendix A.24. -/
theorem radical_quotient_socle_centralizer [Finite G] :
    Subgroup.centralizer (socle (G ⧸ solvableRadical G) : Set (G ⧸ solvableRadical G)) = ⊥ :=
  socle_centralizer_eq_bot radical_quotient_radicalFree

/-- The conjugation map from the radical quotient into the automorphism
group of its socle is an actual injective group homomorphism. -/
theorem radical_quotient_socleConjugation_injective [Finite G] :
    Function.Injective (socleConjugation (G := G ⧸ solvableRadical G)) :=
  socleConjugation_injective radical_quotient_radicalFree

theorem radical_quotient_card_le_socle_aut [Finite G] :
    Nat.card (G ⧸ solvableRadical G) ≤ Nat.card (MulAut (socle (G ⧸ solvableRadical G))) :=
  Nat.card_le_card_of_injective _ radical_quotient_socleConjugation_injective

end GI.RadicalSocle
