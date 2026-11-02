import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Generators of the label group of `P_T`

For a set `T` of labels, `P_T` is the part of `G` whose label permutation maps `T` to itself
and is even on `T` (`GI.LocalGroups.Pgrp`). Labels move by even permutations, so the label
group of `P_T` is `M_T = Alt(T) × Alt(Tᶜ)`. The program builds `P_T` with the cited task
**Preimage**, which needs explicit generators of `M_T`. This file gives them.

* `cyc u v w = (u w v)`, the 3-cycle `swap u v * swap u w`.
* `cycGen T t`: for `t < q³`, write `t = u q² + v q + w`; the 3-cycle `cyc u v w` when `u, v, w`
  are distinct and on the same side of `T`, and `1` otherwise.
* `closure_cycGens`: the `cycGen T t` generate `MT T`.
* `mem_MT`: `σ ∈ MT T` exactly when `σ` maps `T` to itself, is even on `T`, and is even.
-/

namespace GI.Impl

open Equiv Equiv.Perm

variable {q : ℕ}

/-- The 3-cycle `u ↦ w ↦ v ↦ u`. -/
def cyc (u v w : Fin q) : Perm (Fin q) := swap u v * swap u w

/-- The even permutations of one side `p`, as permutations of the labels. -/
def sideAlt (p : Fin q → Prop) [DecidablePred p] : Subgroup (Perm (Fin q)) :=
  (alternatingGroup (Subtype p)).map (ofSubtype : Perm (Subtype p) →* Perm (Fin q))

theorem mem_sideAlt {p : Fin q → Prop} [DecidablePred p] {σ : Perm (Fin q)} :
    σ ∈ sideAlt p ↔ ∃ τ : Perm (Subtype p), sign τ = 1 ∧ ofSubtype τ = σ := by
  simp only [sideAlt, Subgroup.mem_map, mem_alternatingGroup]

/-- `M_T = Alt(T) × Alt(Tᶜ)`, as a subgroup of the permutations of the labels. -/
def MT (T : Finset (Fin q)) : Subgroup (Perm (Fin q)) :=
  sideAlt (fun i => i ∈ T) ⊔ sideAlt (fun i => i ∉ T)

/-- The 3-cycles on one side `p` (`p = (· ∈ T)` or its complement). -/
def sideCycles (p : Fin q → Prop) : Set (Perm (Fin q)) :=
  {σ | ∃ u v w, u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ p u ∧ p v ∧ p w ∧ σ = cyc u v w}

theorem closure_sideCycles (p : Fin q → Prop) [DecidablePred p] :
    Subgroup.closure (sideCycles p) = sideAlt p := by
  rw [sideAlt, ← closure_three_cycles_eq_alternating, MonoidHom.map_closure]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨u, v, w, huv, huw, hvw, hu, hv, hw, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨swap ⟨u, hu⟩ ⟨v, hv⟩ * swap ⟨u, hu⟩ ⟨w, hw⟩,
      isThreeCycle_swap_mul_swap_same (by simpa using huv) (by simpa using huw)
        (by simpa using hvw), ?_⟩
    simp [cyc, ofSubtype_swap_eq]
  · rw [Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    apply Subgroup.subset_closure
    obtain ⟨a, ha⟩ : g.support.Nonempty := by
      rw [← Finset.card_pos, hg.card_support]; norm_num
    have hnd := hg.nodup_iff_mem_support.2 ha
    have heq := hg.eq_swap_mul_swap_iff_mem_support.2 ha
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
      not_false_eq_true, List.nodup_nil, and_true] at hnd
    obtain ⟨⟨h1, h2⟩, h3⟩ := hnd
    refine ⟨g a, a, g (g a), fun h => h1 (Subtype.ext h).symm, fun h => h3 (Subtype.ext h),
      fun h => h2 (Subtype.ext h), (g a).2, a.2, (g (g a)).2, ?_⟩
    have e : (ofSubtype : Perm (Subtype p) →* Perm (Fin q)) g =
        swap (a : Fin q) (g a) * swap ((g a : Subtype p) : Fin q) (g (g a)) := by
      conv_lhs => rw [heq]
      rw [map_mul, ofSubtype_swap_eq, ofSubtype_swap_eq]
    rw [e, cyc, swap_comm]

/-- The generator of the triple `(u, v, w)`: the 3-cycle `cyc u v w` when the three labels are
distinct and on the same side of `T`, and `1` otherwise. -/
def cycGen (T : Finset (Fin q)) (u v w : Fin q) : Perm (Fin q) :=
  if u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ (u ∈ T ↔ v ∈ T) ∧ (v ∈ T ↔ w ∈ T) then cyc u v w else 1

/-- **The generators of `M_T`.** -/
theorem closure_cycGens (T : Finset (Fin q)) :
    Subgroup.closure {σ | ∃ u v w, cycGen T u v w = σ} = MT T := by
  rw [MT, ← closure_sideCycles, ← closure_sideCycles, ← Subgroup.closure_union]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨u, v, w, rfl⟩
    unfold cycGen
    split_ifs with h
    · obtain ⟨huv, huw, hvw, h1, h2⟩ := h
      apply Subgroup.subset_closure
      by_cases hu : u ∈ T
      · exact Or.inl ⟨u, v, w, huv, huw, hvw, hu, h1.1 hu, h2.1 (h1.1 hu), rfl⟩
      · exact Or.inr ⟨u, v, w, huv, huw, hvw, hu, fun hv => hu (h1.2 hv),
          fun hw => hu (h1.2 (h2.2 hw)), rfl⟩
    · exact Subgroup.one_mem _
  · rw [Subgroup.closure_le]
    rintro _ (⟨u, v, w, huv, huw, hvw, hu, hv, hw, rfl⟩ | ⟨u, v, w, huv, huw, hvw, hu, hv, hw, rfl⟩)
    · apply Subgroup.subset_closure
      refine ⟨u, v, w, ?_⟩
      rw [cycGen, if_pos ⟨huv, huw, hvw, iff_of_true hu hv, iff_of_true hv hw⟩]
    · apply Subgroup.subset_closure
      refine ⟨u, v, w, ?_⟩
      rw [cycGen, if_pos ⟨huv, huw, hvw, iff_of_false hu hv, iff_of_false hv hw⟩]

/-- The permutations that map `T` to itself and are even on `T` and even. -/
def KT (T : Finset (Fin q)) : Subgroup (Perm (Fin q)) where
  carrier := {σ | ∃ h : ∀ c, σ c ∈ T ↔ c ∈ T, sign (σ.subtypePerm h) = 1 ∧ sign σ = 1}
  one_mem' := ⟨fun c => Iff.rfl, by
    have : (1 : Perm (Fin q)).subtypePerm (p := (· ∈ T)) (fun c => Iff.rfl) = 1 := by
      ext; rfl
    rw [this, map_one, map_one]; exact ⟨rfl, rfl⟩⟩
  mul_mem' := by
    rintro σ τ ⟨hσ, s1, s2⟩ ⟨hτ, t1, t2⟩
    have h : ∀ c, (σ * τ) c ∈ T ↔ c ∈ T := fun c => (hσ (τ c)).trans (hτ c)
    refine ⟨h, ?_, by rw [map_mul, s2, t2, one_mul]⟩
    have : (σ * τ).subtypePerm h = σ.subtypePerm hσ * τ.subtypePerm hτ := by ext; rfl
    rw [this, map_mul, s1, t1, one_mul]
  inv_mem' := by
    rintro σ ⟨hσ, s1, s2⟩
    have h : ∀ c, σ⁻¹ c ∈ T ↔ c ∈ T := fun c => by
      have := hσ (σ⁻¹ c); simpa using this.symm
    refine ⟨h, ?_, by rw [map_inv, s2, inv_one]⟩
    have : σ⁻¹.subtypePerm h = (σ.subtypePerm hσ)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]; ext x; simp
    rw [this, map_inv, s1, inv_one]

/-- **`M_T` is the group of the permutations that map `T` to itself and are even on `T` and
even.** -/
theorem MT_eq_KT (T : Finset (Fin q)) : MT T = KT T := by
  apply le_antisymm
  · apply sup_le
    · intro σ hσ
      obtain ⟨τ, hτ, rfl⟩ := mem_sideAlt.1 hσ
      have h : ∀ c, (ofSubtype τ : Perm (Fin q)) c ∈ T ↔ c ∈ T := fun c =>
        ofSubtype_apply_mem_iff_mem τ c
      refine ⟨h, ?_, by rw [sign_ofSubtype]; convert hτ⟩
      have : (ofSubtype τ : Perm (Fin q)).subtypePerm h = τ := subtypePerm_ofSubtype τ
      rw [this]; convert hτ
    · intro σ hσ
      obtain ⟨τ, hτ, rfl⟩ := mem_sideAlt.1 hσ
      have h : ∀ c, (ofSubtype τ : Perm (Fin q)) c ∈ T ↔ c ∈ T := fun c => by
        have := ofSubtype_apply_mem_iff_mem τ c
        exact not_iff_not.1 this
      refine ⟨h, ?_, by rw [sign_ofSubtype]; convert hτ⟩
      have : (ofSubtype τ : Perm (Fin q)).subtypePerm h = 1 := by
        refine Equiv.ext fun ⟨x, hx⟩ => Subtype.ext ?_
        exact ofSubtype_apply_of_not_mem τ (not_not.2 hx)
      rw [this, map_one]
  · rintro σ ⟨h, s1, s2⟩
    have h' : ∀ c, σ c ∉ T ↔ c ∉ T := fun c => not_congr (h c)
    set τ1 := σ.subtypePerm h with hτ1
    set τ2 := σ.subtypePerm (p := fun c => c ∉ T) h' with hτ2
    have hσ : σ = (ofSubtype τ1 : Perm (Fin q)) * ofSubtype τ2 := by
      refine Equiv.ext fun x => ?_
      by_cases hx : x ∈ T
      · rw [Perm.mul_apply, ofSubtype_apply_of_not_mem τ2 (not_not.2 hx),
          ofSubtype_apply_of_mem τ1 hx]
        rfl
      · rw [Perm.mul_apply, ofSubtype_apply_of_mem τ2 hx]
        show σ x = (ofSubtype τ1 : Perm (Fin q)) (σ x)
        rw [ofSubtype_apply_of_not_mem τ1 ((h' x).2 hx)]
    have s3 : sign τ2 = 1 := by
      have := s2
      rw [hσ, map_mul, sign_ofSubtype, sign_ofSubtype, s1, one_mul] at this
      exact this
    rw [hσ]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (mem_sideAlt.2 ⟨τ1, by convert s1, rfl⟩))
      (Subgroup.mem_sup_right (mem_sideAlt.2 ⟨τ2, s3, rfl⟩))

end GI.Impl
