import Workspace.CompositionFactors
import Workspace.RadicalSocleHomogeneous
import Workspace.RadicalSocleQuotient
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Nilpotent

/-!
# `a(X)` is at most the order of a solvable subgroup

For a finite group `X`, `a(X)` is the product of the orders of the abelian composition factors
(`GI.Composition.aFac`). We prove that `X` has a solvable subgroup `S` with `a(X) ≤ |S|`
(`GI.Proved.solvAFac_le_solvable`).

[GMP, Section 6] states this and derives it from their Theorem 6.4, which uses CFSG. We use the
elementary argument instead, by strong induction on `|X|`.
* If `X` has a nontrivial solvable normal subgroup `N`, take the preimage of a good subgroup of
  `X/N`.
* Otherwise a minimal normal subgroup `N` is a power of a nonabelian simple group, so
  `a(N) = 1`. For a Sylow subgroup `P` of `N`, the Frattini argument gives `X = N_X(P) N`, and
  `N_X(P)` is proper. So `a(X) = a(X/N) ≤ a(N_X(P))`, and induction applies to `N_X(P)`.
-/

namespace GI.Proved

open GI.Cited GI.Composition GI.RadicalSocle

universe u

section

variable {X : Type u} [Group X] [Finite X]

/-- A minimal normal subgroup of a group with no nontrivial solvable normal subgroup has no
abelian composition factor. -/
theorem solvAFac_minimalNormal
    (radicalFree : ∀ N : Subgroup X, N.Normal → IsSolvable N → N = ⊥)
    {N : Subgroup X} (hN : MinimalNormal N) : aFac N = 1 := by
  obtain ⟨K, hKs, hKn, ⟨e⟩⟩ := minimalNormal_exists_simple_power radicalFree hN
  letI := Fintype.ofFinite (MinimalNormals N)
  haveI := hKs
  have h := pi_compositionProducts (MinimalNormals N) (fun _ => K.val)
  have ha : ∏ _L : MinimalNormals N, aFac K.val = 1 := by
    have h1 : aFac K.val = 1 := by
      apply aFac_of_simple
      obtain ⟨x, y, hxy⟩ := hKn
      exact fun hc => hxy (hc x y)
    simp [h1]
  rw [ha] at h
  exact aFac_eq (congr h e)

/-- If `Y ⊔ N = ⊤` with `N` normal, then `a(X/N) ≤ a(Y)`. -/
theorem solvAFac_quotient_le_of_sup {N : Subgroup X} [N.Normal] (Y : Subgroup X)
    (hsup : Y ⊔ N = ⊤) : aFac (X ⧸ N) ≤ aFac Y := by
  let f : Y →* X ⧸ N := (QuotientGroup.mk' N).comp Y.subtype
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
    have hx : x ∈ Y ⊔ N := hsup ▸ Subgroup.mem_top x
    obtain ⟨y, hy, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    refine ⟨⟨y, hy⟩, ?_⟩
    change (QuotientGroup.mk' N) y = (QuotientGroup.mk' N) (y * n)
    simp only [map_mul, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).mpr hn, mul_one]
  have hr : f.range = ⊤ := MonoidHom.range_eq_top.mpr hf
  have h := aFac_ker_range f
  rw [aFac_congr ((MulEquiv.subgroupCongr hr).trans Subgroup.topEquiv)] at h
  rw [h]
  exact Nat.le_mul_of_pos_left _ aFac_pos

/-- The order of the preimage of a subgroup of a quotient. -/
theorem solvAFac_card_comap_mk (N : Subgroup X) [N.Normal] (T : Subgroup (X ⧸ N)) :
    Nat.card (T.comap (QuotientGroup.mk' N)) = Nat.card N * Nat.card T := by
  have hi : (T.comap (QuotientGroup.mk' N)).index = T.index :=
    Subgroup.index_comap_of_surjective T (QuotientGroup.mk'_surjective N)
  have h1 := Subgroup.card_mul_index (T.comap (QuotientGroup.mk' N))
  have h2 := Subgroup.card_mul_index T
  have h3 := Subgroup.card_mul_index N
  rw [Subgroup.index_eq_card] at h3
  have hpos : 0 < T.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  rw [hi] at h1
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1, mul_assoc, h2, h3]

/-- A proper subgroup has smaller order. -/
theorem solvAFac_card_lt {Y : Subgroup X} (hY : Y ≠ ⊤) : Nat.card Y < Nat.card X := by
  have h := Subgroup.card_mul_index Y
  have h1 : Y.index ≠ 1 := fun h1 => hY (Subgroup.index_eq_one.mp h1)
  have h2 : Y.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h3 : 0 < Nat.card Y := Nat.card_pos
  rw [← h]
  exact lt_mul_of_one_lt_right h3 (by omega)

end

/-- **`a(X)` is at most the order of a solvable subgroup.** Every finite group `X` has a
solvable subgroup `S` with `a(X) ≤ |S|`. -/
theorem solvAFac_le_solvable_aux : ∀ (n : ℕ) (X : Type u) [Group X] [Finite X],
    Nat.card X = n → ∃ S : Subgroup X, IsSolvable S ∧ aFac X ≤ Nat.card S := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X _ _ hX
  by_cases hrad : ∃ N : Subgroup X, N.Normal ∧ IsSolvable N ∧ N ≠ ⊥
  · -- A nontrivial solvable normal subgroup: pass to the quotient.
    obtain ⟨N, hNn, hNs, hNb⟩ := hrad
    have hlt : Nat.card (X ⧸ N) < n := by
      rw [← hX]
      have h := Subgroup.card_mul_index N
      rw [Subgroup.index_eq_card] at h
      have h2 : 1 < Nat.card N := by
        rw [Subgroup.one_lt_card_iff_ne_bot]; exact hNb
      have h3 : 0 < Nat.card (X ⧸ N) := Nat.card_pos
      rw [← h]
      exact lt_mul_left h3 h2
    obtain ⟨T, hTs, hT⟩ := ih _ hlt (X ⧸ N) rfl
    refine ⟨T.comap (QuotientGroup.mk' N), ?_, ?_⟩
    · haveI : IsSolvable (QuotientGroup.mk' N).ker := by
        rw [QuotientGroup.ker_mk']; exact hNs
      exact solvable_preimage (QuotientGroup.mk' N) T
    · rw [solvAFac_card_comap_mk, aFac_mul N]
      exact Nat.mul_le_mul aFac_le_card hT
  · -- No nontrivial solvable normal subgroup.
    push Not at hrad
    have radicalFree : ∀ N : Subgroup X, N.Normal → IsSolvable N → N = ⊥ :=
      fun N h1 h2 => hrad N h1 h2
    by_cases htriv : (⊤ : Subgroup X) = ⊥
    · refine ⟨⊥, inferInstance, ?_⟩
      have hs : Subsingleton X := by
        rw [← Subgroup.subsingleton_iff]
        exact subsingleton_of_bot_eq_top htriv.symm
      rw [aFac_eq (CompositionProducts.trivial X)]
      exact Nat.card_pos
    obtain ⟨N, hN, -⟩ := exists_minimal_normal_le (⊤ : Subgroup X) htriv
    haveI := hN.1
    have hNa : aFac N = 1 := solvAFac_minimalNormal radicalFree hN
    have hNne : Nat.card N ≠ 1 := by
      intro h
      exact hN.2.1 (Subgroup.card_eq_one.mp h)
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hNne
    haveI : Fact p.Prime := ⟨hp⟩
    let P : Sylow p N := default
    let P' : Subgroup X := (P : Subgroup N).map N.subtype
    let Y : Subgroup X := Subgroup.normalizer (P' : Set X)
    have hsup : Y ⊔ N = ⊤ := Sylow.normalizer_sup_eq_top P
    have hY : Y ≠ ⊤ := by
      intro hYt
      haveI : P'.Normal := Subgroup.normalizer_eq_top_iff.mp hYt
      have hP'N : P' ≤ N := Subgroup.map_subtype_le _
      have hP'b : P' ≠ ⊥ := by
        intro hb
        exact P.ne_bot_of_dvd_card hpd
          ((Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).mp hb)
      have hP'eq : P' = N := (hN.2.2 P' inferInstance hP'N).resolve_left hP'b
      have hPs : IsSolvable (P : Subgroup N) := by
        haveI := P.isPGroup'.isNilpotent
        infer_instance
      have hP's : IsSolvable P' :=
        solvable_of_surjective (f := ((P : Subgroup N).equivMapOfInjective N.subtype
          N.subtype_injective).toMonoidHom) (MulEquiv.surjective _)
      exact hN.2.1 (radicalFree N hN.1 (hP'eq ▸ hP's))
    have hlt : Nat.card Y < n := by
      rw [← hX]
      exact solvAFac_card_lt hY
    obtain ⟨S, hSs, hS⟩ := ih _ hlt Y rfl
    refine ⟨S.map Y.subtype, ?_, ?_⟩
    · exact solvable_of_surjective (f := (S.equivMapOfInjective Y.subtype
        Y.subtype_injective).toMonoidHom) (MulEquiv.surjective _)
    · rw [Subgroup.card_map_of_injective Y.subtype_injective, aFac_mul N, hNa, one_mul]
      exact (solvAFac_quotient_le_of_sup Y hsup).trans hS

/-- **`a(X)` is at most the order of a solvable subgroup.** -/
theorem solvAFac_le_solvable (X : Type u) [Group X] [Finite X] :
    ∃ S : Subgroup X, IsSolvable S ∧ aFac X ≤ Nat.card S :=
  solvAFac_le_solvable_aux _ X rfl

end GI.Proved
