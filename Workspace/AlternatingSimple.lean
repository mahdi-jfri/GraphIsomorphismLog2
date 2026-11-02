import Workspace.OrbitBudget

namespace GI
namespace AlternatingSimple

open Equiv Equiv.Perm Subgroup

-- Use the same subtype enumeration as `ofSubtype` and its sign/support lemmas.
attribute [local instance 2000] Subtype.fintype

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

def relabel (e : α ≃ β) : alternatingGroup α ≃* alternatingGroup β where
  toFun p := ⟨e.permCongr p, by
    rw [mem_alternatingGroup, sign_permCongr]
    exact mem_alternatingGroup.mp p.property⟩
  invFun p := ⟨e.symm.permCongr p, by
    rw [mem_alternatingGroup, sign_permCongr]
    exact mem_alternatingGroup.mp p.property⟩
  left_inv p := by apply Subtype.ext; ext x; simp
  right_inv p := by apply Subtype.ext; ext x; simp
  map_mul' p q := Subtype.ext ((relabelPerm e).map_mul p q)

def extend (s : Finset α) : alternatingGroup s →* alternatingGroup α where
  toFun p := ⟨ofSubtype (p : Perm s), by
    rw [mem_alternatingGroup, sign_ofSubtype]
    exact mem_alternatingGroup.mp p.property⟩
  map_one' := Subtype.ext (map_one ofSubtype)
  map_mul' p q := Subtype.ext (map_mul ofSubtype (p : Perm s) (q : Perm s))

theorem extend_injective (s : Finset α) : Function.Injective (extend s) := by
  intro p q h
  exact Subtype.ext (ofSubtype_injective (congrArg Subtype.val h))

theorem simple_of_card_five (h : Fintype.card α = 5) : IsSimpleGroup (alternatingGroup α) := by
  let e : Fin 5 ≃ α := (Fintype.equivFinOfCardEq h).symm
  letI : Nontrivial (alternatingGroup α) :=
    alternatingGroup.nontrivial_of_three_le_card (by omega)
  exact IsSimpleGroup.isSimpleGroup_of_surjective (relabel e).toMonoidHom (relabel e).surjective

/-- A nonidentity permutation fails to commute with a three-cycle which
shares a point with its conjugate. Their commutator moves at most five points. -/
theorem small_commutator (h5 : 5 ≤ Fintype.card α) (f : alternatingGroup α) (hf : f ≠ 1) :
    ∃ t : alternatingGroup α,
      f * t * f⁻¹ * t⁻¹ ≠ 1 ∧ ((f * t * f⁻¹ * t⁻¹ : alternatingGroup α) : Perm α).support.card ≤ 5 := by
  have hmove : ∃ a : α, (f : Perm α) a ≠ a := by
    by_contra hn
    push Not at hn
    apply hf
    apply Subtype.ext
    ext a
    exact hn a
  obtain ⟨a, ha⟩ := hmove
  have hbex : ∃ b : α, b ∉ ({a, (f : Perm α) a, (f : Perm α) ((f : Perm α) a)} : Finset α) := by
    by_contra hn
    push Not at hn
    have heq : ({a, (f : Perm α) a, (f : Perm α) ((f : Perm α) a)} : Finset α) = Finset.univ :=
      Finset.eq_univ_iff_forall.mpr hn
    have hc := Finset.card_le_three (a := a) (b := (f : Perm α) a)
      (c := (f : Perm α) ((f : Perm α) a))
    rw [heq, Finset.card_univ] at hc
    omega
  obtain ⟨b, hb⟩ := hbex
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
  let t₀ : Perm α := swap a b * swap a ((f : Perm α) a)
  have ht₀ : IsThreeCycle t₀ := isThreeCycle_swap_mul_swap_same (Ne.symm hb.1) ha.symm hb.2.1
  let t : alternatingGroup α := ⟨t₀, ht₀.mem_alternatingGroup⟩
  have hta : t₀ a = (f : Perm α) a := by
    change (swap a b) ((swap a ((f : Perm α) a)) a) = (f : Perm α) a
    rw [swap_apply_left, swap_apply_of_ne_of_ne ha (Ne.symm hb.2.1)]
  have htfa : t₀ ((f : Perm α) a) = b := by simp [t₀]
  refine ⟨t, ?_, ?_⟩
  · intro heq
    have hm : f * t = t * f := by
      have hh := congrArg (fun q : alternatingGroup α => q * t * f) heq
      simpa [mul_assoc] using hh
    have he := congrArg (fun q : alternatingGroup α => (q : Perm α) a) hm
    change (f : Perm α) (t₀ a) = t₀ ((f : Perm α) a) at he
    rw [hta, htfa] at he
    exact hb.2.2 he.symm
  · have hts : t₀.support ⊆ ({a, b, (f : Perm α) a} : Finset α) := by
      intro x hx
      have hh := support_mul_le (swap a b) (swap a ((f : Perm α) a)) hx
      simp only [support_swap (Ne.symm hb.1), support_swap ha.symm,
        Finset.sup_eq_union, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        or_assoc] at hh
      rcases hh with rfl | rfl | rfl | rfl <;> simp
    have hs : ((f * t * f⁻¹ * t⁻¹ : alternatingGroup α) : Perm α).support ⊆
        ({a, b, (f : Perm α) a, (f : Perm α) b, (f : Perm α) ((f : Perm α) a)} : Finset α) := by
      intro x hx
      have hh := support_mul_le ((f : Perm α) * t₀ * (f : Perm α)⁻¹) t₀⁻¹ hx
      rw [support_conj, support_inv] at hh
      rcases Finset.mem_union.mp hh with hh | hh
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hh
        have hy' := hts hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy'
        rcases hy' with rfl | rfl | rfl <;> simp
      · have hh' := hts hh
        simp only [Finset.mem_insert, Finset.mem_singleton] at hh'
        rcases hh' with rfl | rfl | rfl <;> simp
    exact (Finset.card_le_card hs).trans Finset.card_le_five

/-- Simplicity on five points detects any nonidentity normal-subgroup element
whose support has at most five points. -/
theorem normal_eq_top_of_small (h5 : 5 ≤ Fintype.card α)
    (N : Subgroup (alternatingGroup α)) [N.Normal]
    (g : alternatingGroup α) (hg : g ∈ N) (hne : g ≠ 1)
    (hsmall : (g : Perm α).support.card ≤ 5) : N = ⊤ := by
  obtain ⟨s, hs, _, hcard⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ (g : Perm α).support) hsmall (by simpa using h5)
  have hcs : Fintype.card s = 5 := by simpa using hcard
  letI : IsSimpleGroup (alternatingGroup s) := simple_of_card_five hcs
  let inv := isInvariant_of_support_le hs
  let r₀ : Perm s := (g : Perm α).subtypePerm inv
  have hr₀ : r₀ ∈ alternatingGroup s := by
    rw [mem_alternatingGroup]
    change sign ((g : Perm α).subtypePerm inv) = 1
    rw [sign_subtypePerm _ inv (fun x hx => hs (mem_support.mpr hx))]
    exact mem_alternatingGroup.mp g.property
  let r : alternatingGroup s := ⟨r₀, hr₀⟩
  have her : extend s r = g := by
    apply Subtype.ext
    exact ofSubtype_subtypePerm inv (fun x hx => hs (mem_support.mpr hx))
  have hr : r ∈ N.comap (extend s) := by
    change extend s r ∈ N
    rwa [her]
  have hNtop : N.comap (extend s) = ⊤ := by
    rcases (inferInstance : (N.comap (extend s)).Normal).eq_bot_or_eq_top with hb | ht
    · exfalso
      have hr1 : r = 1 := by simpa [hb] using hr
      apply hne
      rw [← her, hr1, map_one]
    · exact ht
  let e : Fin 5 ≃ s := (Fintype.equivFinOfCardEq hcs).symm
  have h01 : e (0 : Fin 5) ≠ e 1 := fun h => (by decide : (0 : Fin 5) ≠ 1) (e.injective h)
  have h02 : e (0 : Fin 5) ≠ e 2 := fun h => (by decide : (0 : Fin 5) ≠ 2) (e.injective h)
  have h12 : e (1 : Fin 5) ≠ e 2 := fun h => (by decide : (1 : Fin 5) ≠ 2) (e.injective h)
  let u₀ : Perm s := swap (e 0) (e 1) * swap (e 0) (e 2)
  have hu₀ : IsThreeCycle u₀ := isThreeCycle_swap_mul_swap_same h01 h02 h12
  let u : alternatingGroup s := ⟨u₀, hu₀.mem_alternatingGroup⟩
  have huN : extend s u ∈ N := by
    have hu : u ∈ N.comap (extend s) := by rw [hNtop]; exact mem_top _
    exact hu
  have hu3 : IsThreeCycle ((extend s u : alternatingGroup α) : Perm α) := by
    rw [← card_support_eq_three_iff]
    change (ofSubtype u₀).support.card = 3
    rw [support_ofSubtype, Finset.card_map]
    exact hu₀.card_support
  have hcl : normalClosure ({extend s u} : Set (alternatingGroup α)) = ⊤ :=
    hu3.alternating_normalClosure h5
  apply top_le_iff.mp
  rw [← hcl]
  exact normalClosure_le_normal (Set.singleton_subset_iff.mpr huN)

/-- General simplicity of alternating groups, derived from the checked
five-point theorem and the normal closure of three-cycles. -/
theorem isSimple (h5 : 5 ≤ Fintype.card α) : IsSimpleGroup (alternatingGroup α) := by
  letI : Nontrivial (alternatingGroup α) :=
    alternatingGroup.nontrivial_of_three_le_card (by omega)
  refine ⟨fun N hN => ?_⟩
  letI := hN
  by_cases hb : N = ⊥
  · exact Or.inl hb
  · right
    rw [eq_bot_iff_forall] at hb
    push Not at hb
    obtain ⟨f, hf, hf1⟩ := hb
    obtain ⟨t, ht1, hsmall⟩ := small_commutator h5 f hf1
    have hm : f * t * f⁻¹ * t⁻¹ ∈ N := by
      have hh := N.mul_mem hf (hN.conj_mem f⁻¹ (N.inv_mem hf) t)
      simpa only [mul_assoc] using hh
    exact normal_eq_top_of_small h5 N _ hm ht1 hsmall

theorem nonabelian (h5 : 5 ≤ Fintype.card α) :
    ∃ f t : alternatingGroup α, f * t ≠ t * f := by
  letI : Nontrivial (alternatingGroup α) :=
    alternatingGroup.nontrivial_of_three_le_card (by omega)
  obtain ⟨f, hf⟩ := exists_ne (1 : alternatingGroup α)
  obtain ⟨t, ht, _⟩ := small_commutator h5 f hf
  refine ⟨f, t, fun h => ht ?_⟩
  rw [h]
  simp [mul_assoc]

theorem isSimple_fin {k : ℕ} (hk : 5 ≤ k) : IsSimpleGroup (alternatingGroup (Fin k)) :=
  isSimple (by simpa using hk)

theorem nonabelian_fin {k : ℕ} (hk : 5 ≤ k) :
    ∃ f t : alternatingGroup (Fin k), f * t ≠ t * f :=
  nonabelian (by simpa using hk)

end AlternatingSimple
end GI
