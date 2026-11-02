import Workspace.Cited.GMP
import Workspace.CompositionFactors
import Workspace.SmallSimple
import Workspace.SocleOuter
import Workspace.RadicalSocleDecomposition

/-!
# Lemma A.21: `|Q/Rad(Q)| ≤ b(Q)²`

The proof follows the paper. For the radical-free quotient `Q₀` with socle
`E = T₁ × ⋯ × T_t`:

* `Q₀` acts faithfully on `E` by conjugation (`C_{Q₀}(E) = 1`);
* the action on the simple factors has image `P ≤ Sym(t)`, with kernel `K`;
* `K` maps to `∏ Out(T_i)` with kernel exactly `E`;
* so `a(Q₀) ≤ a(E) · ∏ |Out(T_i)| · a(P) = ∏ |Out(T_i)| · a(P)`;
* [GMP, Proposition 6.1] and [GMP, Lemma 7.7] with `|T_i| ≥ 34` give `a(Q₀) ≤ |E|`;
* `|E| = b(E) ≤ b(Q₀) = b(Q)`, and `|Q₀| = a(Q₀) b(Q₀)`.

The paper writes "since every `|T_i| ≥ 60`"; the computation only needs `|T_i| ≥ 34`
(`GI.SmallSimple.thirtyfour_le_card`, proved without the classification).

The cited results are stated for groups in `Type`; `outBound_univ`, `abelianFactors_univ`
move them to any universe along isomorphisms.
-/

namespace GI.RadicalFreeOrder

open GI.Cited GI.Composition GI.RadicalSocle GI.SocleOuter

universe u

/-! ### Moving the cited bounds to any universe -/

/-- The index of the inner automorphisms is an isomorphism invariant. -/
theorem outIndex_congr {A B : Type*} [Group A] [Group B] (f : A ≃* B) :
    (MulAut.conj : A →* MulAut A).range.index = (MulAut.conj : B →* MulAut B).range.index := by
  have hconj : ∀ a : A, MulAut.congr f (MulAut.conj a) = MulAut.conj (f a) := by
    intro a
    ext y
    simp [MulAut.congr_apply, MulAut.conj_apply]
  have h : (MulAut.conj : A →* MulAut A).range =
      (MulAut.conj : B →* MulAut B).range.comap (MulAut.congr f).toMonoidHom := by
    ext x
    simp only [MonoidHom.mem_range, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨f a, (hconj a).symm⟩
    · rintro ⟨b, hb⟩
      refine ⟨f.symm b, (MulAut.congr f).injective ?_⟩
      rw [hconj, MulEquiv.apply_symm_apply, hb]
  rw [h, Subgroup.index_comap_of_surjective _ (MulAut.congr f).surjective]

/-- [GMP, Lemma 7.7] for a finite nonabelian simple group in any universe. -/
theorem outBound_univ (hOut : GMPOutBound) (T : Type u) [Group T] [Finite T]
    [IsSimpleGroup T] (hT : ∃ x y : T, x * y ≠ y * x) :
    ((MulAut.conj : T →* MulAut T).range.index : ℝ) ≤ 2 * Real.sqrt (Nat.card T) := by
  let f : Shrink.{0} T ≃* T := Shrink.mulEquiv
  haveI : IsSimpleGroup (Shrink.{0} T) := f.isSimpleGroup
  haveI : Finite (Shrink.{0} T) := Finite.of_equiv T f.symm.toEquiv
  have hT' : ∃ x y : Shrink.{0} T, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hT
    refine ⟨f.symm x, f.symm y, fun h => hxy ?_⟩
    have := congrArg f h
    simpa using this
  have h := hOut (Shrink.{0} T) inferInstance hT'
  rwa [outIndex_congr f, Nat.card_congr f.toEquiv] at h

/-- [GMP, Proposition 6.1] for a permutation group on any finite type with `t ≥ 1` points. -/
theorem abelianFactors_univ (hAb : GMPAbelianFactors) {α : Type u} [Finite α]
    (ht : 1 ≤ Nat.card α) (P : Subgroup (Equiv.Perm α)) :
    (aFac P : ℝ) ≤ (24 : ℝ) ^ (((Nat.card α : ℝ) - 1) / 3) := by
  let e : α ≃ Fin (Nat.card α) := Finite.equivFin α
  let φ := e.permCongrHom
  let P' := P.map φ.toMonoidHom
  have h : CompositionProducts P' (aFac P) (bFac P) := congr (spec P) (φ.subgroupMap P)
  exact hAb _ ht P' _ _ h

/-! ### The structure of a radical-free group -/

section Structure

variable {G : Type u} [Group G] [Finite G]
  (rf : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)

/-- The socle `E` as a group. -/
local notation "E" => socle G

omit [Finite G] in
/-- Conjugation by an element of `E` is the inner automorphism of `E`. -/
theorem socleConjugation_of_mem (ε : E) :
    socleConjugation (G := G) (ε : G) = MulAut.conj ε :=
  MulAut.conjNormal_val

omit [Finite G] in
/-- An inner automorphism of `E` fixes every minimal normal subgroup of `E`. -/
theorem minimalNormalAction_conj (ε : E) : minimalNormalAction (MulAut.conj ε) = 1 := by
  ext N : 1
  apply Subtype.ext
  change N.val.map (MulAut.conj ε).toMonoidHom = N.val
  haveI : N.val.Normal := N.property.1
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (inferInstance : N.val.Normal).conj_mem x hx ε
  · intro x hx
    refine ⟨ε⁻¹ * x * ε, ?_, ?_⟩
    · simpa using (inferInstance : N.val.Normal).conj_mem x hx ε⁻¹
    · simp [MulAut.conj_apply, mul_assoc]

/-- The action of `G` on the simple factors of its socle. -/
noncomputable def factorAction : G →* Equiv.Perm (MinimalNormals E) :=
  minimalNormalAction.comp socleConjugation

omit [Finite G] in
theorem socle_le_factorAction_ker : E ≤ (factorAction (G := G)).ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  change minimalNormalAction (socleConjugation x) = 1
  rw [socleConjugation_of_mem ⟨x, hx⟩]
  exact minimalNormalAction_conj _

/-- The kernel of the factor action acts on `E` fixing every factor. -/
noncomputable def kernelToFactorKernel :
    (factorAction (G := G)).ker →* FactorKernel E :=
  ((socleConjugation (G := G)).comp (factorAction (G := G)).ker.subtype).codRestrict _
    (fun k => k.2)

/-- The map from the kernel `K` of the factor action to `∏ Out(T_i)`. -/
noncomputable def kernelToOuter :
    (factorAction (G := G)).ker →* ∀ N : MinimalNormals E, OuterAut N.val :=
  (factorOuterHom (G := E)).comp kernelToFactorKernel

/-- The inclusion of `E` into the kernel `K`. -/
noncomputable def socleToKernel : E →* (factorAction (G := G)).ker :=
  Subgroup.inclusion socle_le_factorAction_ker

include rf in
/-- The kernel of `K → ∏ Out(T_i)` is exactly `E`. -/
theorem kernelToOuter_ker : (kernelToOuter (G := G)).ker = (socleToKernel (G := G)).range := by
  have rfE := normal_subgroup_radicalFree rf (socle G)
  have hsoc : socle (socle G) = ⊤ := socle_idempotent
  ext k
  rw [MonoidHom.mem_ker]
  change (factorOuterHom (G := E)) (kernelToFactorKernel k) = 1 ↔ _
  rw [← MonoidHom.mem_ker, factorOuterHom_ker_eq_inner_comap rfE hsoc, Subgroup.mem_comap]
  change socleConjugation (k : G) ∈ innerAut E ↔ _
  constructor
  · rintro ⟨ε, hε⟩
    refine ⟨ε, Subtype.ext ?_⟩
    change (ε : G) = k
    apply socleConjugation_injective rf
    rw [socleConjugation_of_mem, hε]
  · rintro ⟨ε, rfl⟩
    exact ⟨ε, (socleConjugation_of_mem ε).symm⟩

include rf in
theorem nonabelian_factor (N : MinimalNormals E) : ¬ ∀ x y : N.val, x * y = y * x := by
  obtain ⟨x, y, h⟩ := socle_intrinsic_factor_nonabelian rf N
  exact fun hc => h (hc x y)

include rf in
/-- `E` has no abelian composition factor and `b(E) = |E|`. -/
theorem socle_compositionProducts : CompositionProducts E 1 (Nat.card E) := by
  letI := Fintype.ofFinite (MinimalNormals E)
  haveI := fun N : MinimalNormals E => socle_intrinsic_factor_simple N
  have h := pi_compositionProducts (MinimalNormals E) (fun N => N.val)
  have ha : ∏ N : MinimalNormals E, aFac N.val = 1 :=
    Finset.prod_eq_one (fun N _ => aFac_of_simple (nonabelian_factor rf N))
  have hb : ∏ N : MinimalNormals E, bFac N.val = Nat.card E := by
    rw [← Nat.card_congr (socleIntrinsicProductEquiv rf).toEquiv, Nat.card_pi]
    exact Finset.prod_congr rfl (fun N _ => bFac_of_simple (nonabelian_factor rf N))
  rw [ha, hb] at h
  exact congr h (socleIntrinsicProductEquiv rf)

include rf in
theorem aFac_socle : aFac E = 1 := aFac_eq (socle_compositionProducts rf)

include rf in
theorem bFac_socle : bFac E = Nat.card E := bFac_eq (socle_compositionProducts rf)

include rf in
/-- `|E| ≤ b(G)`. -/
theorem card_socle_le_bFac : Nat.card E ≤ bFac G := by
  rw [bFac_mul E, bFac_socle rf]
  exact Nat.le_mul_of_pos_right _ bFac_pos

include rf in
/-- `a(G) ≤ ∏ |Out(T_i)| · a(P)`. -/
theorem aFac_le_outer_mul :
    aFac G ≤ Nat.card (∀ N : MinimalNormals E, OuterAut N.val) *
      aFac (factorAction (G := G)).range := by
  have h1 := aFac_ker_range (factorAction (G := G))
  have h2 := aFac_ker_range (kernelToOuter (G := G))
  have h3 : aFac (kernelToOuter (G := G)).ker = 1 := by
    rw [aFac_congr (MulEquiv.subgroupCongr (kernelToOuter_ker rf)),
      ← aFac_congr (MonoidHom.ofInjective (f := socleToKernel (G := G))
        (Subgroup.inclusion_injective _)), aFac_socle rf]
  have h4 : aFac (kernelToOuter (G := G)).range ≤
      Nat.card (∀ N : MinimalNormals E, OuterAut N.val) := by
    exact aFac_le_card.trans (Subgroup.card_le_card_group _)
  rw [h1, h2, h3, one_mul]
  exact Nat.mul_le_mul_right _ h4

theorem nontrivial_factors [Nontrivial G] : 1 ≤ Nat.card (MinimalNormals E) := by
  obtain ⟨M, hM, -⟩ := exists_minimal_normal_le (⊤ : Subgroup G) top_ne_bot
  have hE : socle G ≠ ⊥ := fun h => hM.2.1 (le_bot_iff.mp (h ▸ minimalNormal_le_socle hM))
  haveI : Nontrivial E := (Subgroup.nontrivial_iff_ne_bot _).mpr hE
  obtain ⟨N, hN, -⟩ := exists_minimal_normal_le (⊤ : Subgroup E) top_ne_bot
  haveI : Nonempty (MinimalNormals E) := ⟨⟨N, hN⟩⟩
  exact Nat.one_le_iff_ne_zero.mpr Finite.card_pos.ne'

/-- The numeric step: `o ≤ 2 √n`, `n ≥ 34` and `c³ = 24` give `o c ≤ n`. -/
theorem factor_numeric {o n : ℝ} (ho : o ≤ 2 * Real.sqrt n) (hn : 34 ≤ n) :
    o * (24 : ℝ) ^ ((1 : ℝ) / 3) ≤ n := by
  set c : ℝ := (24 : ℝ) ^ ((1 : ℝ) / 3) with hc
  have hc0 : 0 ≤ c := by positivity
  have hc3 : c ^ 3 = 24 := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hc2 : c ^ 2 ≤ 8.5 := by
    by_contra h
    push Not at h
    have : (8.5 : ℝ) ^ 3 < (c ^ 2) ^ 3 := by
      apply pow_lt_pow_left₀ h (by norm_num) (by norm_num)
    have h6 : (c ^ 2) ^ 3 = 576 := by rw [← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, hc3]; norm_num
    rw [h6] at this
    norm_num at this
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg n
  -- `2 c √n ≤ n` because `(2c)² ≤ 34 ≤ n = √n²`
  have h2c : 2 * c ≤ Real.sqrt n := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  calc o * c ≤ 2 * Real.sqrt n * c := mul_le_mul_of_nonneg_right ho hc0
    _ = Real.sqrt n * (2 * c) := by ring
    _ ≤ Real.sqrt n * Real.sqrt n := mul_le_mul_of_nonneg_left h2c hs0
    _ = n := by rw [← sq, hsq]

include rf in
/-- **`a(Q₀) ≤ |E|`**, from [GMP, Proposition 6.1] and [GMP, Lemma 7.7]. -/
theorem aFac_le_card_socle (hAb : GMPAbelianFactors) (hOut : GMPOutBound) [Nontrivial G] :
    aFac G ≤ Nat.card E := by
  letI := Fintype.ofFinite (MinimalNormals E)
  haveI := fun N : MinimalNormals E => socle_intrinsic_factor_simple N
  have ht := nontrivial_factors (G := G)
  set t := Nat.card (MinimalNormals E)
  -- the cited bounds
  have hP := abelianFactors_univ hAb ht (factorAction (G := G)).range
  have hO : ∀ N : MinimalNormals E,
      (Nat.card (OuterAut N.val) : ℝ) ≤ 2 * Real.sqrt (Nat.card N.val) := by
    intro N
    have h := outBound_univ hOut N.val (socle_intrinsic_factor_nonabelian rf N)
    rwa [Subgroup.index] at h
  have h34 : ∀ N : MinimalNormals E, (34 : ℝ) ≤ Nat.card N.val := by
    intro N
    exact_mod_cast GI.SmallSimple.thirtyfour_le_card (nonabelian_factor rf N)
  -- `24^{(t-1)/3} ≤ c^t`
  have hpow : (24 : ℝ) ^ (((t : ℝ) - 1) / 3) ≤ ((24 : ℝ) ^ ((1 : ℝ) / 3)) ^ t := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hE : (Nat.card E : ℝ) = ∏ N : MinimalNormals E, (Nat.card N.val : ℝ) := by
    rw [← Nat.card_congr (socleIntrinsicProductEquiv rf).toEquiv, Nat.card_pi]
    push_cast
    rfl
  have hmain : (aFac G : ℝ) ≤ Nat.card E := by
    calc (aFac G : ℝ)
        ≤ (∏ N : MinimalNormals E, (Nat.card (OuterAut N.val) : ℝ)) *
            aFac (factorAction (G := G)).range := by
          have h := aFac_le_outer_mul rf (G := G)
          rw [Nat.card_pi] at h
          exact_mod_cast h
      _ ≤ (∏ N : MinimalNormals E, (Nat.card (OuterAut N.val) : ℝ)) *
            ((24 : ℝ) ^ ((1 : ℝ) / 3)) ^ t := by
          apply mul_le_mul_of_nonneg_left (hP.trans hpow)
          positivity
      _ = ∏ N : MinimalNormals E,
            ((Nat.card (OuterAut N.val) : ℝ) * (24 : ℝ) ^ ((1 : ℝ) / 3)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
            ← Nat.card_eq_fintype_card]
      _ ≤ ∏ N : MinimalNormals E, (Nat.card N.val : ℝ) := by
          apply Finset.prod_le_prod (fun N _ => by positivity)
          exact fun N _ => factor_numeric (hO N) (h34 N)
      _ = Nat.card E := hE.symm
  exact_mod_cast hmain

include rf in
/-- **Lemma A.21 for a radical-free group:** `|G| ≤ b(G)²`. -/
theorem card_le_bFac_sq (hAb : GMPAbelianFactors) (hOut : GMPOutBound) :
    Nat.card G ≤ bFac G ^ 2 := by
  by_cases hG : Subsingleton G
  · rw [Nat.card_unique]
    exact Nat.one_le_pow _ _ bFac_pos
  rw [not_subsingleton_iff_nontrivial] at hG
  rw [← aFac_mul_bFac, sq]
  exact Nat.mul_le_mul_right _
    ((aFac_le_card_socle rf hAb hOut).trans (card_socle_le_bFac rf))

end Structure

/-- **Lemma A.21** (`lem:radical-free-order`): `|Q/Rad(Q)| ≤ b(Q)²`. -/
theorem card_radical_quotient_le (hAb : GMPAbelianFactors) (hOut : GMPOutBound)
    (Q : Type u) [Group Q] [Finite Q] :
    Nat.card (Q ⧸ solvableRadical Q) ≤ bFac Q ^ 2 := by
  have h := card_le_bFac_sq (radical_quotient_radicalFree (G := Q)) hAb hOut
  rwa [bFac_mul (solvableRadical Q) (X := Q), bFac_of_solvable, one_mul]

end GI.RadicalFreeOrder
