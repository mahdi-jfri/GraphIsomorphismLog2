module

public import Workspace.SmallDegreeBudget
public import Workspace.AlternatingSimple
public import Workspace.OrbitLocalization
public import Workspace.QuotientImage

@[expose] public section

namespace GI.SectionCaps

/-- Every alternating section of the actual group has degree at most b. -/
def Cap (G : Type*) [Group G] (b : ℕ) : Prop :=
  ∀ (U : Subgroup G) (k : ℕ), 5 ≤ k →
    ∀ q : U →* alternatingGroup (Fin k), Function.Surjective q → k ≤ b

variable {G H A : Type*} [Group G] [Group H] [Group A] {b c k : ℕ}

theorem degree_le (bound : Cap G b) (hk : 5 ≤ k)
    (q : G →* alternatingGroup (Fin k)) (onto : Function.Surjective q) : k ≤ b := by
  apply bound ⊤ k hk (q.comp (⊤ : Subgroup G).subtype)
  intro s
  obtain ⟨g, hg⟩ := onto s
  exact ⟨⟨g, Subgroup.mem_top g⟩, hg⟩

theorem quotient_degree_le (bound : Cap H b) (hk : 5 ≤ k)
    (p : A →* H) (q : A →* alternatingGroup (Fin k))
    (onto : Function.Surjective q) (kills : p.ker ≤ q.ker) : k ≤ b := by
  have kr : p.rangeRestrict.ker ≤ q.ker := fun a ha => kills (congrArg Subtype.val ha)
  let descended := HomDescent.factor p.rangeRestrict (QuotientImage.range_surjective p) q kr
  exact bound p.range k hk descended
    (HomDescent.factor_surjective _ _ _ _ onto)

theorem of_injective (f : G →* H) (injective : Function.Injective f)
    (bound : Cap H b) : Cap G b := by
  intro U k hk q onto
  apply quotient_degree_le bound hk (f.comp U.subtype) q onto
  intro u hu
  have h : (u : G) = 1 := injective (by simpa using hu)
  have hu1 : u = 1 := Subtype.ext h
  change q u = 1
  rw [hu1, map_one]

theorem subgroup (bound : Cap G b) (U : Subgroup G) : Cap U b :=
  of_injective U.subtype Subtype.val_injective bound

def preimage (f : G →* H) (U : Subgroup H) : U.comap f →* U where
  toFun g := ⟨f g.val, g.property⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' g h := Subtype.ext (map_mul f g.val h.val)

theorem of_surjective (f : G →* H) (onto : Function.Surjective f)
    (bound : Cap G b) : Cap H b := by
  intro U k hk q qonto
  apply bound (U.comap f) k hk (q.comp (preimage f U))
  intro s
  obtain ⟨u, hu⟩ := qonto s
  obtain ⟨g, hg⟩ := onto u.val
  have hmem : g ∈ U.comap f := by change f g ∈ U; rw [hg]; exact u.property
  refine ⟨⟨g, hmem⟩, ?_⟩
  change q (preimage f U ⟨g, hmem⟩) = s
  have he : preimage f U ⟨g, hmem⟩ = u := Subtype.ext hg
  rw [he, hu]

theorem permutations {V : Type*} [Fintype V] : Cap (Equiv.Perm V) (Fintype.card V) := by
  intro U k hk q onto
  by_contra h
  exact no_alternating_surjection_of_small_order hk (Nat.lt_of_not_ge h)
    (permutation_subgroup_card_le_factorial U) q onto

/-- Alternating sections in an extension occur in the kernel or image. -/
theorem extension (f : G →* H) (kernelBound : Cap f.ker b) (imageBound : Cap H c) :
    Cap G (max b c) := by
  intro U k hk q onto
  let p := f.comp U.subtype
  letI : IsSimpleGroup (alternatingGroup (Fin k)) := AlternatingSimple.isSimple_fin hk
  have hn : (p.ker.map q).Normal := (inferInstance : p.ker.Normal).map q onto
  rcases hn.eq_bot_or_eq_top with hbot | htop
  · apply (quotient_degree_le imageBound hk p q onto ?_).trans (le_max_right b c)
    intro u hu
    have hm : q u ∈ p.ker.map q := ⟨u, hu, rfl⟩
    simpa only [hbot, Subgroup.mem_bot, MonoidHom.mem_ker] using hm
  · let embed : p.ker →* f.ker :=
      { toFun := fun u => ⟨u.val.val, u.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have he : Function.Injective embed := by
      intro u v huv
      have hv : u.val.val = v.val.val := congrArg (fun z : f.ker => z.val) huv
      exact Subtype.ext (Subtype.ext hv)
    have ho : Function.Surjective (q.comp p.ker.subtype) := by
      intro s
      have hm : s ∈ p.ker.map q := by rw [htop]; exact Subgroup.mem_top s
      obtain ⟨u, hu, hus⟩ := hm
      exact ⟨⟨u, hu⟩, hus⟩
    exact (degree_le (of_injective embed he kernelBound) hk _ ho).trans (le_max_left b c)

theorem faithful_family {I : Type*} [Fintype I] {D : I → Type*} [∀ i, Fintype (D i)]
    (actions : ∀ i, G →* Equiv.Perm (D i))
    (faithful : ∀ g : G, (∀ i, actions i g = 1) → g = 1)
    (degrees : ∀ i, Fintype.card (D i) ≤ b) : Cap G b := by
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
  apply (quotient_degree_le permutations hk (component i) q onto ?_).trans (degrees i)
  intro u hu
  have hm : q u ∈ (component i).ker.map q := ⟨u, hu, rfl⟩
  simpa only [hbot, Subgroup.mem_bot, MonoidHom.mem_ker] using hm

end GI.SectionCaps
