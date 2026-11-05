module

public import Workspace.RadicalSocleQuotient
public import Mathlib.GroupTheory.Commutator.Basic

@[expose] public section

namespace GI.RadicalSocle

variable {G : Type*} [Group G]

theorem MinimalNormal.map {N : Subgroup G} (hN : MinimalNormal N) (e : G ≃* G) :
    MinimalNormal (N.map e.toMonoidHom) := by
  refine ⟨hN.1.map e.toMonoidHom e.surjective, ?_, ?_⟩
  · intro hz
    exact hN.2.1 ((Subgroup.map_eq_bot_iff_of_injective N
      (f := e.toMonoidHom) e.injective).mp hz)
  · intro K hK hle
    have hpre : K.comap e.toMonoidHom ≤ N := by
      have h := Subgroup.comap_mono hle (f := e.toMonoidHom)
      rwa [Subgroup.comap_map_eq_self_of_injective e.injective] at h
    rcases hN.2.2 (K.comap e.toMonoidHom) (hK.comap e.toMonoidHom) hpre with hb | he
    · left
      have h := congrArg (fun S : Subgroup G => S.map e.toMonoidHom) hb
      simpa only [Subgroup.map_comap_eq_self_of_surjective
        (f := e.toMonoidHom) e.surjective, Subgroup.map_bot] using h
    · right
      have h := congrArg (fun S : Subgroup G => S.map e.toMonoidHom) he
      simpa only [Subgroup.map_comap_eq_self_of_surjective
        (f := e.toMonoidHom) e.surjective] using h

instance socle_characteristic : (socle G).Characteristic := by
  apply Subgroup.characteristic_iff_map_le.mpr
  intro e
  unfold socle
  rw [Subgroup.map_normalClosure _ _ e.surjective]
  apply Subgroup.normalClosure_mono
  rintro _ ⟨g, ⟨N, hN, hg⟩, rfl⟩
  exact ⟨N.map e.toMonoidHom, hN.map e, ⟨g, hg, rfl⟩⟩

/-- Distinct minimal normal subgroups have trivial intersection. -/
theorem minimalNormal_inf_eq_bot {M N : Subgroup G}
    (hM : MinimalNormal M) (hN : MinimalNormal N) (hne : M ≠ N) : M ⊓ N = ⊥ := by
  letI := hM.1
  letI := hN.1
  rcases hM.2.2 (M ⊓ N) inferInstance inf_le_left with hb | he
  · exact hb
  · have hMN : M ≤ N := by rw [← he]; exact inf_le_right
    rcases hN.2.2 M hM.1 hMN with hzero | hsame
    · exact (hM.2.1 hzero).elim
    · exact (hne hsame).elim

/-- Distinct minimal normal subgroups commute element by element. -/
theorem minimalNormal_commute {M N : Subgroup G}
    (hM : MinimalNormal M) (hN : MinimalNormal N) (hne : M ≠ N)
    (m : M) (n : N) : (m : G) * (n : G) = (n : G) * (m : G) := by
  letI := hM.1
  letI := hN.1
  have hm := Subgroup.commutator_le_inf M N
    (Subgroup.commutator_mem_commutator m.property n.property)
  rw [minimalNormal_inf_eq_bot hM hN hne, Subgroup.mem_bot] at hm
  exact commutatorElement_eq_one_iff_mul_comm.mp hm

/-- Minimal normal subgroups are characteristically simple. The stronger
decomposition into isomorphic simple direct factors is not assumed here. -/
theorem minimalNormal_characteristic_subgroup {N : Subgroup G} (hN : MinimalNormal N)
    (K : Subgroup N) [K.Characteristic] : K = ⊥ ∨ K = ⊤ := by
  letI := hN.1
  have hle : K.map N.subtype ≤ N := by
    rintro _ ⟨k, _, rfl⟩
    exact k.property
  rcases hN.2.2 (K.map N.subtype) inferInstance hle with hb | he
  · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective K N.subtype_injective).mp hb)
  · right
    apply Subgroup.map_injective N.subtype_injective
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact he

theorem minimalNormal_not_solvable
    (radicalFree : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {N : Subgroup G} (hN : MinimalNormal N) : ¬ Group.IsSolvable N :=
  fun hs => hN.2.1 (radicalFree N hN.1 hs)

theorem minimalNormal_nonabelian
    (radicalFree : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {N : Subgroup G} (hN : MinimalNormal N) : ∃ x y : N, x * y ≠ y * x := by
  classical
  by_contra hn
  push Not at hn
  exact minimalNormal_not_solvable radicalFree hN (isSolvable_of_comm hn)

theorem minimalNormal_center_eq_bot
    (radicalFree : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {N : Subgroup G} (hN : MinimalNormal N) : Subgroup.center N = ⊥ := by
  rcases minimalNormal_characteristic_subgroup hN (Subgroup.center N) with hb | ht
  · exact hb
  · obtain ⟨x, y, hxy⟩ := minimalNormal_nonabelian radicalFree hN
    have hy : y ∈ Subgroup.center N := by rw [ht]; exact Subgroup.mem_top y
    exact (hxy ((Subgroup.mem_center_iff.mp hy) x)).elim

instance solvableRadical_characteristic [Finite G] : (solvableRadical G).Characteristic := by
  apply Subgroup.characteristic_iff_map_le.mpr
  intro e
  let R := solvableRadical G
  haveI : (R.map e.toMonoidHom).Normal :=
    (inferInstance : R.Normal).map e.toMonoidHom e.surjective
  haveI : Group.IsSolvable (R.map e.toMonoidHom) :=
    solvable_of_surjective (e.toMonoidHom.subgroupMap_surjective R)
  exact le_solvableRadical (R.map e.toMonoidHom)

end GI.RadicalSocle
