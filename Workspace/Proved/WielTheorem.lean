module

public import Workspace.Proved.WielLemma
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

set_option linter.style.haveILetI false

namespace GI.Proved

open scoped Pointwise commutatorElement IsMulCommutative

variable {Ω : Type*}

/-- If an abelian subgroup `S ≤ G` normalizes a nontrivial finite abelian subgroup `M ≤ G`,
acts faithfully on `M` by conjugation, and acts transitively on `M \ {1}` by conjugation,
then `S` is cyclic. -/
theorem isCyclic_of_comm_transitive_aut {G : Type*} [Group G]
    (M S : Subgroup G) [Finite M] [Finite S] [Nontrivial M]
    (hM_comm : ∀ x y : M, x * y = y * x)
    (hS_comm : ∀ x y : S, x * y = y * x)
    (hnorm : ∀ s : S, ∀ m : M, s.val * m.val * s.val⁻¹ ∈ M)
    (hfaith : ∀ s₁ s₂ : S,
      (∀ m : M, s₁.val * m.val * s₁.val⁻¹ = s₂.val * m.val * s₂.val⁻¹) → s₁ = s₂)
    (htrans : ∀ m₁ m₂ : M, m₁ ≠ 1 → m₂ ≠ 1 →
      ∃ s : S, s.val * m₁.val * s.val⁻¹ = m₂.val) :
    IsCyclic S := by
  classical
  letI : CommGroup M :=
    { (inferInstance : Group M) with mul_comm := hM_comm }
  let V := Additive M
  haveI : Nontrivial V := inferInstanceAs (Nontrivial (Additive M))
  haveI : Finite V := inferInstanceAs (Finite (Additive M))
  let conjM (s : S) : M →* M :=
    { toFun := fun m => ⟨s.val * m.val * s.val⁻¹, hnorm s m⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun m₁ m₂ => by apply Subtype.ext; simp [mul_assoc] }
  let toEnd (s : S) : Module.End ℤ V :=
    AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (conjM s))
  have htoEnd_apply (s : S) (m : M) :
      toEnd s (Additive.ofMul m) = Additive.ofMul (conjM s m) := rfl
  have hcomm_range : ∀ x ∈ Set.range toEnd, ∀ y ∈ Set.range toEnd, x * y = y * x := by
    rintro _ ⟨s₁, rfl⟩ _ ⟨s₂, rfl⟩
    apply LinearMap.ext
    intro v
    obtain ⟨m, rfl⟩ : ∃ m : M, Additive.ofMul m = v := ⟨Additive.toMul v, rfl⟩
    change toEnd s₁ (toEnd s₂ (Additive.ofMul m)) = toEnd s₂ (toEnd s₁ (Additive.ofMul m))
    rw [htoEnd_apply, htoEnd_apply, htoEnd_apply, htoEnd_apply]
    congr 1
    apply Subtype.ext
    have hs12 : s₁.val * s₂.val = s₂.val * s₁.val := congrArg Subtype.val (hS_comm s₁ s₂)
    calc s₁.val * (s₂.val * m.val * s₂.val⁻¹) * s₁.val⁻¹
      _ = (s₁.val * s₂.val) * m.val * (s₁.val * s₂.val)⁻¹ := by group
      _ = (s₂.val * s₁.val) * m.val * (s₂.val * s₁.val)⁻¹ := by rw [hs12]
      _ = s₂.val * (s₁.val * m.val * s₁.val⁻¹) * s₂.val⁻¹ := by group
  let R : Subalgebra ℤ (Module.End ℤ V) := Algebra.adjoin ℤ (Set.range toEnd)
  haveI : IsMulCommutative R :=
    Algebra.isMulCommutative_adjoin ℤ (fun x hx y hy _ => hcomm_range x hx y hy)
  have hdom : ∀ b : R, b = 0 ∨ ∀ v : V, b.val v = 0 → v = 0 := by
    intro b
    by_cases hinj : ∀ v : V, b.val v = 0 → v = 0
    · exact Or.inr hinj
    · left
      push Not at hinj
      obtain ⟨v₀, hv₀_ker, hv₀_ne⟩ := hinj
      apply Subtype.ext
      apply LinearMap.ext
      intro w
      by_cases hw : w = 0
      · subst hw; exact map_zero b.val
      · have hm₀_ne : Additive.toMul v₀ ≠ 1 := hv₀_ne
        have hmw_ne : Additive.toMul w ≠ 1 := hw
        obtain ⟨s, hs⟩ := htrans (Additive.toMul v₀) (Additive.toMul w) hm₀_ne hmw_ne
        have hsw : toEnd s v₀ = w := by
          change Additive.ofMul (conjM s (Additive.toMul v₀)) = w
          have hcm : conjM s (Additive.toMul v₀) = Additive.toMul w := Subtype.ext hs
          rw [hcm]
          rfl
        let s' : R := ⟨toEnd s, Algebra.subset_adjoin ⟨s, rfl⟩⟩
        have hbs : b * s' = s' * b := mul_comm' b s'
        have hbs_val : b.val (s'.val v₀) = s'.val (b.val v₀) :=
          congrArg (fun u : R => u.val v₀) hbs
        change b.val w = 0
        rw [← hsw]
        change b.val (s'.val v₀) = 0
        rw [hbs_val, hv₀_ker, map_zero]
  haveI : Nontrivial R := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h1 : ((0 : R) : Module.End ℤ V) = ((1 : R) : Module.End ℤ V) := congrArg Subtype.val h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    apply hv
    have h2 := congrArg (fun f : Module.End ℤ V => f v) h1
    simpa using h2.symm
  haveI : NoZeroDivisors R := by
    refine ⟨fun {x y} hxy => ?_⟩
    rcases hdom x with hx | hx
    · exact Or.inl hx
    · right
      apply Subtype.ext
      apply LinearMap.ext
      intro v
      have h1 := congrArg (fun z : R => z.val v) hxy
      exact hx _ (by simpa using h1)
  haveI : IsDomain R := NoZeroDivisors.to_isDomain R
  let f : S →* R :=
    { toFun := fun s => ⟨toEnd s, Algebra.subset_adjoin ⟨s, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        apply LinearMap.ext
        intro v
        change toEnd 1 v = v
        obtain ⟨m, rfl⟩ : ∃ m : M, Additive.ofMul m = v := ⟨Additive.toMul v, rfl⟩
        rw [htoEnd_apply]
        congr 1
        apply Subtype.ext
        change (1 : S).val * m.val * (1 : S).val⁻¹ = m.val
        simp
      map_mul' := fun s₁ s₂ => by
        apply Subtype.ext
        apply LinearMap.ext
        intro v
        obtain ⟨m, rfl⟩ : ∃ m : M, Additive.ofMul m = v := ⟨Additive.toMul v, rfl⟩
        change toEnd (s₁ * s₂) (Additive.ofMul m) = toEnd s₁ (toEnd s₂ (Additive.ofMul m))
        rw [htoEnd_apply, htoEnd_apply, htoEnd_apply]
        congr 1
        apply Subtype.ext
        change (s₁ * s₂).val * m.val * (s₁ * s₂).val⁻¹ =
          s₁.val * (s₂.val * m.val * s₂.val⁻¹) * s₁.val⁻¹
        simp [mul_assoc] }
  have hf : Function.Injective f := by
    intro s₁ s₂ hs
    apply hfaith
    intro m
    have hm := congrArg (fun u : R => Additive.toMul (u.val (Additive.ofMul m))) hs
    exact congrArg Subtype.val hm
  exact isCyclic_of_injective_ringHom f hf

/-- Wielandt's theorem (Satz 1, Math. Z. 74 (1960), 297–298) on a general finite type `Ω`:
any 8-transitive subgroup of `Equiv.Perm Ω` (`8 ≤ Fintype.card Ω`) contains `alternatingGroup Ω`. -/
theorem eightTransitiveContainsAlt_fintype [Fintype Ω] [DecidableEq Ω]
    (h8 : 8 ≤ Fintype.card Ω) (G : Subgroup (Equiv.Perm Ω)) (hG : WielTransitive 8 G) :
    alternatingGroup Ω ≤ G := by
  by_contra halt
  have h7 : 7 ≤ Fintype.card Ω := by omega
  have hG7 : WielTransitive 7 G := hG.mono (by decide) h8
  let emptyEmb : Fin 0 ↪ Ω := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  obtain ⟨γ₆, _⟩ := exists_disjoint_embedding emptyEmb 6 (by omega)
  let γ : Fin 5 ↪ Ω := (Fin.castSuccEmb (n := 5)).trans γ₆
  let ω₀ : Ω := γ₆ 5
  have hω₀ : ω₀ ∉ Set.range γ := by
    rintro ⟨i, hi⟩
    have h := γ₆.injective hi
    have hval := congrArg Fin.val h
    change i.val = 5 at hval
    omega
  obtain ⟨h10, M, hMG, hM_fix, hM_norm, hM_comm, hM_not_cyc, hM_inj, hM_surj⟩ :=
    wielandt_lemma h7 hG7 halt γ
  let Ω' := {x : Ω // x ≠ ω₀}
  have h7' : 7 ≤ Fintype.card Ω' := by
    have hcard : Fintype.card Ω' = (Finset.univ.erase ω₀).card := by
      rw [← Fintype.card_coe]
      exact Fintype.card_congr
        ⟨fun x => ⟨x.val, Finset.mem_erase.mpr ⟨x.property, Finset.mem_univ _⟩⟩,
         fun x => ⟨x.val, (Finset.mem_erase.mp x.property).1⟩,
         fun _ => rfl, fun _ => rfl⟩
    rw [hcard, Finset.card_erase_of_mem (Finset.mem_univ ω₀), Finset.card_univ]
    omega
  let G' : Subgroup (Equiv.Perm Ω') := G.comap Equiv.Perm.ofSubtype
  have hG'7 : WielTransitive 7 G' := by
    intro a b
    let cω : Fin 1 ↪ Ω := ⟨fun _ => ω₀, fun i j _ => Subsingleton.elim i j⟩
    have ha_disj : ∀ (i : Fin 7) (j : Fin 1), (a.trans (Function.Embedding.subtype _)) i ≠ cω j :=
      fun i _ => (a i).property
    have hb_disj : ∀ (i : Fin 7) (j : Fin 1), (b.trans (Function.Embedding.subtype _)) i ≠ cω j :=
      fun i _ => (b i).property
    let eqv : Fin 8 ≃ Fin (7 + 1) := finCongr (by decide)
    let a₈ : Fin 8 ↪ Ω :=
      eqv.toEmbedding.trans (appendEmbedding (a.trans (Function.Embedding.subtype _)) cω ha_disj)
    let b₈ : Fin 8 ↪ Ω :=
      eqv.toEmbedding.trans (appendEmbedding (b.trans (Function.Embedding.subtype _)) cω hb_disj)
    obtain ⟨g, hgG, hgab⟩ := hG a₈ b₈
    have hg_apply : ∀ j : Fin (7 + 1),
        g (appendEmbedding (a.trans (Function.Embedding.subtype _)) cω ha_disj j) =
          appendEmbedding (b.trans (Function.Embedding.subtype _)) cω hb_disj j := by
      intro j
      have hj := hgab (eqv.symm j)
      simpa only [a₈, b₈, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
        Equiv.apply_symm_apply] using hj
    have hgω₀ : g ω₀ = ω₀ := by
      have h := hg_apply (Fin.natAdd 7 0)
      rw [appendEmbedding_natAdd, appendEmbedding_natAdd] at h
      exact h
    have hg_sub : ∀ x : Ω, g x ≠ ω₀ ↔ x ≠ ω₀ :=
      fun x => ⟨fun hx h => hx (h ▸ hgω₀), fun hx h => hx (g.injective (h.trans hgω₀.symm))⟩
    let g' : Equiv.Perm Ω' := g.subtypePerm hg_sub
    have hofSub : Equiv.Perm.ofSubtype g' = g := by
      ext x
      by_cases hx : x ≠ ω₀
      · exact Equiv.Perm.ofSubtype_apply_of_mem g' hx
      · push Not at hx
        subst hx
        rw [Equiv.Perm.ofSubtype_apply_of_not_mem g' (not_not.mpr rfl), hgω₀]
    refine ⟨g', ?_, ?_⟩
    · rw [Subgroup.mem_comap, hofSub]
      exact hgG
    · intro i
      apply Subtype.ext
      have hi := hg_apply (Fin.castAdd 1 i)
      rw [appendEmbedding_castAdd, appendEmbedding_castAdd] at hi
      exact hi
  let γ' : Fin 5 ↪ Ω' :=
    ⟨fun i => ⟨γ i, fun h => hω₀ ⟨i, h⟩⟩, fun i j h => γ.injective (congrArg Subtype.val h)⟩
  have halt' : ¬ alternatingGroup Ω' ≤ G' := by
    intro hle
    haveI : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    have hprim : MulAction.IsPreprimitive G Ω := (hG7.mono (by decide) h7).wielTwoTrans.isPreprimitive
    let c' : Equiv.Perm Ω' := Equiv.swap (γ' 0) (γ' 1) * Equiv.swap (γ' 0) (γ' 2)
    have h01' : γ' 0 ≠ γ' 1 := fun h => by
      have hc := γ'.injective h; revert hc; decide
    have h02' : γ' 0 ≠ γ' 2 := fun h => by
      have hc := γ'.injective h; revert hc; decide
    have h12' : γ' 1 ≠ γ' 2 := fun h => by
      have hc := γ'.injective h; revert hc; decide
    have h3' : c'.IsThreeCycle := Equiv.Perm.isThreeCycle_swap_mul_swap_same h01' h02' h12'
    have hc'_alt : c' ∈ alternatingGroup Ω' :=
      Equiv.Perm.mem_alternatingGroup.mpr h3'.sign
    have hc'_G : Equiv.Perm.ofSubtype c' ∈ G := hle hc'_alt
    have hof_c' : Equiv.Perm.ofSubtype c' = Equiv.swap (γ 0) (γ 1) * Equiv.swap (γ 0) (γ 2) := by
      change Equiv.Perm.ofSubtype (Equiv.swap (γ' 0) (γ' 1) * Equiv.swap (γ' 0) (γ' 2)) = _
      rw [map_mul, Equiv.Perm.ofSubtype_swap_eq, Equiv.Perm.ofSubtype_swap_eq]
      rfl
    have h3 : (Equiv.Perm.ofSubtype c').IsThreeCycle := by
      rw [hof_c']
      exact Equiv.Perm.isThreeCycle_swap_mul_swap_same
        (fun h => h01' (Subtype.ext h))
        (fun h => h02' (Subtype.ext h))
        (fun h => h12' (Subtype.ext h))
    exact halt (GI.Bochert.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim h3 hc'_G)
  obtain ⟨_, M', hM'G', hM'_fix, _, hM'_comm, hM'_not_cyc, _, hM'_surj⟩ :=
    wielandt_lemma h7' hG'7 halt' γ'
  let S : Subgroup (Equiv.Perm Ω) := M'.map Equiv.Perm.ofSubtype
  let eS : M' →* S := Equiv.Perm.ofSubtype.subgroupMap M'
  have heS_bijective : Function.Bijective eS :=
    ⟨fun x y h => Subtype.ext (Equiv.Perm.ofSubtype_injective (congrArg Subtype.val h)),
      Equiv.Perm.ofSubtype.subgroupMap_surjective M'⟩
  have hS_not_cyc : ¬ IsCyclic S := by
    intro hcycS
    apply hM'_not_cyc
    obtain ⟨g, hg⟩ := hcycS.exists_generator
    obtain ⟨g₀, rfl⟩ := heS_bijective.surjective g
    refine ⟨⟨g₀, fun x₀ => ?_⟩⟩
    obtain ⟨k, hk⟩ := hg (eS x₀)
    refine ⟨k, heS_bijective.injective ?_⟩
    change eS (g₀ ^ k) = eS x₀
    rw [map_zpow]
    exact hk
  have hS_comm : ∀ x y : S, x * y = y * x := by
    intro x y
    obtain ⟨x₀, rfl⟩ := heS_bijective.surjective x
    obtain ⟨y₀, rfl⟩ := heS_bijective.surjective y
    rw [← map_mul, ← map_mul, hM'_comm x₀ y₀]
  have hS_G : S ≤ G := by
    rintro _ ⟨s, hs, rfl⟩
    exact hM'G' hs
  have hS_fix_ω₀ : ∀ s : S, (s : Equiv.Perm Ω) ω₀ = ω₀ := by
    rintro ⟨_, ⟨s, _, rfl⟩⟩
    exact Equiv.Perm.ofSubtype_apply_of_not_mem s (not_not.mpr rfl)
  have hS_fix_γ : ∀ s : S, ∀ i : Fin 5, (s : Equiv.Perm Ω) (γ i) = γ i := by
    rintro ⟨_, ⟨s, hs, rfl⟩⟩ i
    have hmem : (γ' i).val ≠ ω₀ := (γ' i).property
    change Equiv.Perm.ofSubtype s (γ' i).val = (γ' i).val
    rw [Equiv.Perm.ofSubtype_apply_of_mem s hmem, hM'_fix s hs i]
  have hnorm : ∀ s : S, ∀ m : M, s.val * m.val * s.val⁻¹ ∈ M :=
    fun s m => hM_norm s.val (hS_G s.property) (hS_fix_γ s) m.val m.property
  have hconj_ω₀ : ∀ (s : S) (m : M),
      (s.val * m.val * s.val⁻¹ : Equiv.Perm Ω) ω₀ = s.val (m.val ω₀) := by
    intro s m
    have hs_inv : s.val⁻¹ ω₀ = ω₀ :=
      s.val.injective (by rw [s.val.apply_inv_self, hS_fix_ω₀ s])
    change s.val (m.val (s.val⁻¹ ω₀)) = s.val (m.val ω₀)
    rw [hs_inv]
  have hfaith : ∀ s₁ s₂ : S,
      (∀ m : M, s₁.val * m.val * s₁.val⁻¹ = s₂.val * m.val * s₂.val⁻¹) → s₁ = s₂ := by
    intro s₁ s₂ h
    apply Subtype.ext
    ext z
    by_cases hz : z ∈ Set.range γ
    · obtain ⟨i, rfl⟩ := hz
      rw [hS_fix_γ s₁ i, hS_fix_γ s₂ i]
    · obtain ⟨m, hm⟩ := hM_surj ω₀ z hω₀ hz
      have hm_eq := congrArg (fun p : Equiv.Perm Ω => p ω₀) (h m)
      rw [hconj_ω₀ s₁ m, hconj_ω₀ s₂ m, hm] at hm_eq
      exact hm_eq
  have htrans : ∀ m₁ m₂ : M, m₁ ≠ 1 → m₂ ≠ 1 →
      ∃ s : S, s.val * m₁.val * s.val⁻¹ = m₂.val := by
    intro m₁ m₂ hm₁ hm₂
    have hm₁_ω₀ : m₁.val ω₀ ≠ ω₀ :=
      fun h => hm₁ (hM_inj ω₀ hω₀ (h.trans (Equiv.Perm.one_apply ω₀).symm))
    have hm₂_ω₀ : m₂.val ω₀ ≠ ω₀ :=
      fun h => hm₂ (hM_inj ω₀ hω₀ (h.trans (Equiv.Perm.one_apply ω₀).symm))
    have hm₁_γ : ⟨m₁.val ω₀, hm₁_ω₀⟩ ∉ Set.range γ' := by
      rintro ⟨i, hi⟩
      have hi' : m₁.val ω₀ = γ i := (congrArg Subtype.val hi).symm
      have hinv : m₁.val⁻¹ (γ i) = γ i := hM_fix m₁.val⁻¹ (M.inv_mem m₁.property) i
      have hω₀_eq : ω₀ = γ i := by
        calc ω₀ = m₁.val⁻¹ (m₁.val ω₀) := (m₁.val.inv_apply_self ω₀).symm
          _ = m₁.val⁻¹ (γ i) := by rw [hi']
          _ = γ i := hinv
      exact hω₀ ⟨i, hω₀_eq.symm⟩
    have hm₂_γ : ⟨m₂.val ω₀, hm₂_ω₀⟩ ∉ Set.range γ' := by
      rintro ⟨i, hi⟩
      have hi' : m₂.val ω₀ = γ i := (congrArg Subtype.val hi).symm
      have hinv : m₂.val⁻¹ (γ i) = γ i := hM_fix m₂.val⁻¹ (M.inv_mem m₂.property) i
      have hω₀_eq : ω₀ = γ i := by
        calc ω₀ = m₂.val⁻¹ (m₂.val ω₀) := (m₂.val.inv_apply_self ω₀).symm
          _ = m₂.val⁻¹ (γ i) := by rw [hi']
          _ = γ i := hinv
      exact hω₀ ⟨i, hω₀_eq.symm⟩
    obtain ⟨s₀, hs₀⟩ := hM'_surj ⟨m₁.val ω₀, hm₁_ω₀⟩ ⟨m₂.val ω₀, hm₂_ω₀⟩ hm₁_γ hm₂_γ
    let s : S := eS s₀
    refine ⟨s, ?_⟩
    have hs_apply : s.val (m₁.val ω₀) = m₂.val ω₀ := by
      change Equiv.Perm.ofSubtype s₀.val (m₁.val ω₀) = m₂.val ω₀
      rw [Equiv.Perm.ofSubtype_apply_of_mem s₀.val hm₁_ω₀]
      exact congrArg Subtype.val hs₀
    have hconj_eq : (⟨s.val * m₁.val * s.val⁻¹, hnorm s m₁⟩ : M) = m₂ := by
      apply hM_inj ω₀ hω₀
      change (s.val * m₁.val * s.val⁻¹ : Equiv.Perm Ω) ω₀ = m₂.val ω₀
      rw [hconj_ω₀ s m₁, hs_apply]
    exact congrArg Subtype.val hconj_eq
  haveI : Nontrivial M := by
    by_contra hnot
    rw [not_nontrivial_iff_subsingleton] at hnot
    exact hM_not_cyc ⟨⟨1, fun x => ⟨0, Subsingleton.elim _ _⟩⟩⟩
  exact hS_not_cyc (isCyclic_of_comm_transitive_aut M S hM_comm hS_comm hnorm hfaith htrans)

/-- Wielandt's theorem (Satz 1, Math. Z. 74 (1960), 297–298):
every 8-transitive subgroup of `Equiv.Perm (Fin n)` (`8 ≤ n`) contains `alternatingGroup (Fin n)`. -/
theorem eightTransitiveContainsAlt :
    ∀ (n : ℕ), 8 ≤ n → ∀ (G : Subgroup (Equiv.Perm (Fin n))),
      (∀ a b : Fin 8 ↪ Fin n, ∃ g ∈ G, ∀ i, g (a i) = b i) →
      alternatingGroup (Fin n) ≤ G := by
  intro n hn G hG
  exact eightTransitiveContainsAlt_fintype (by rw [Fintype.card_fin]; exact hn) G hG

end GI.Proved
